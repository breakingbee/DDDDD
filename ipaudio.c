#define _GNU_SOURCE
/*
 * ipaudio.c - IPAudio 1.2 for the Formuler Wegoo / Icone (Hi3798MV200)
 *
 * Same architecture as MatchZap:
 *   - this program reads the remote (/dev/input), runs the menu logic and only writes a small text description of
 *     the screen to overlay.txt; IpaHud.jar draws it (status bar top-left, panel on the right, like the Enigma plugin)
 *   - the real work is done by IpaCtl.jar, a small helper that runs as user "system" (uid 1000) and calls the
 *     launcher's DvbApi: external audio (command 343) and video delay (command 141). It also runs a local relay
 *     (127.0.0.1:17901) that your stream passes through: audio delay (aDelay), stream status, anti-drift and
 *     automatic recovery. This program talks to the helper over 127.0.0.1:17900 with one text line per command
 *   - UI only opens on a long press of the open key (default BLUE), never when the plugin is started
 *
 * Keys while the panel is open:
 *   UP/DOWN        move  (rows: vDelay, server, streams)  — video delay is at the TOP
 *   LEFT/RIGHT     vDelay: -/+ 0.5 s; server: next/prev server; stream row: also adjusts vDelay
 *   OK             play the stream under the cursor (restores that stream's saved vDelay)
 *   RED            reset vDelay to 0
 *   YELLOW         original audio (stop external)
 *   GREEN          reload playlist
 *   BLUE (short)   while open: toggle live info (bitrate / reconnects)
 *   BACK           close
 *
 * aDelay (IP audio delay) REMOVED — did not work on this STB; vDelay (video) kept via DvbApi 141.
 *
 * Build (NDK, same as MatchZap):
 *   armv7a-linux-androideabi21-clang -O2 -fPIE -pie -o IPAudio ipaudio.c
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <strings.h>
#include <stdarg.h>
#include <unistd.h>
#include <fcntl.h>
#include <dirent.h>
#include <signal.h>
#include <poll.h>
#include <time.h>
#include <errno.h>
#include <ctype.h>
#include <sys/ioctl.h>
#include <sys/file.h>
#include <sys/wait.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <sys/socket.h>
#include <netinet/in.h>
#include <arpa/inet.h>
#include <linux/input.h>

#ifndef DATA_DIR
#define DATA_DIR     "/data/plugin/IPAudio_data"
#endif
#define LOG_PATH     DATA_DIR "/ipaudio.log"
#define CFG_PATH     DATA_DIR "/config.txt"
#define CTL_LOG      DATA_DIR "/ipactl.log"
#define LIST_PATH    DATA_DIR "/playlist.txt"
#define DELAYS_PATH  DATA_DIR "/delays.txt"
#define LAST_PATH    DATA_DIR "/last.txt"
#define OVL_PATH     DATA_DIR "/overlay.txt"
#define LOCK_PATH    DATA_DIR "/ipaudio.lock"
#define HUD_JAR      DATA_DIR "/IpaHud.jar"
#define CTL_JAR      DATA_DIR "/IpaCtl.jar"
#define HUD_CLASS    "lab.ipa.IpaHud"
#define VERSION      "1.2"
#define CTL_CLASS    "lab.ipa.IpaCtl"
#ifndef AUTORUN
#define AUTORUN      "/data/plugin/autorun.sh"
#endif
#define AUTORUN_LINE "/data/plugin/IPAudio --boot >/dev/null 2>&1 &"

#ifndef KEY_RED
#define KEY_RED 0x18e
#endif
#ifndef KEY_GREEN
#define KEY_GREEN 0x18f
#endif
#ifndef KEY_YELLOW
#define KEY_YELLOW 0x190
#endif
#ifndef KEY_BLUE
#define KEY_BLUE 0x191
#endif
#ifndef KEY_CENTER
#define KEY_CENTER 0x1c
#endif
#ifndef KEY_OK
#define KEY_OK 0x160
#endif
#ifndef KEY_BACK
#define KEY_BACK 158
#endif
#ifndef EVIOCGRAB
#define EVIOCGRAB _IOW('E', 0x90, int)
#endif

#define MAX_ENT    220
#define MAX_SRV    16
#define MAX_DELAYS 96
#define VISIBLE    5
#define MAX_HALF   90            /* 45.0 s, the launcher's own limit */
#define MAX_AHALF  40            /* aDelay up to 20.0 s */
#define LONG_MS    700
#define IDLE_CLOSE 60            /* seconds without a key before the panel closes itself */
#define MAX_DEV    16

typedef struct { char title[72]; char url[256]; int id; int srv; int builtin; } Ent;
typedef struct { char name[40]; int builtin; } Srv;
typedef struct { char url[256]; int half; int ahalf; } Dly;
typedef struct { int valid; char state[12]; int pct, kbps, buf, reconn, skips, recovers; char fmt[8]; char msg[100]; } Stat;

static volatile int g_run = 1;
static int g_sim = 0;                   /* --sim: no inputs, no HUD, keys come from stdin */
static int g_port = 17900;
static int g_slot = 10;                 /* helper slot used for your own links */
static int g_open_key = KEY_BLUE;
static int g_relay_cfg = 1;             /* config relay=on: play through the relay (aDelay, status, anti-drift) */
static int g_anti = 1, g_drift_ms = 600, g_auto = 1;
static int g_minibar = 2;               /* config minibar: 0 off, 1 auto (a few seconds after events), 2 on (always while audio plays) */
static time_t g_bar_until = 0;
static int g_bar_shown = 0;
static char g_bar_last[520] = "";

static Ent g_ent[MAX_ENT];
static int g_nent = 0;
static Srv g_srv[MAX_SRV];
static int g_nsrv = 0;
static Dly g_dly[MAX_DELAYS];
static int g_ndly = 0;

static int g_menu_open = 0;
static int g_cur_srv = 0;
static int g_view[MAX_ENT], g_nview = 0;   /* entries of the selected server */
static int g_sel = 0;                      /* 0 = vDelay, 1 = server, 2..g_nview+1 = streams */
static int g_live_info = 1;                /* show bitrate / reconnect live info */
static int g_half = 0;                     /* current video delay, half seconds */
static int g_ahalf = 0;                    /* current audio delay, half seconds (needs the relay) */
static int g_play_relayed = 0;             /* the playing stream goes through the relay */
static Stat g_stat;                        /* last STATUS from the helper */
static time_t g_stat_poll = 0, g_toast_until = 0;
static int g_play = -1;                    /* index in g_ent of the stream we started, -1 none */
static int g_active_id = 0;                /* external track id the middleware reports (0 = none) */
static char g_status[120] = "";
static time_t g_last_key = 0;
static int g_need_load = 0;                /* panel is open but the helper has not answered yet */
static time_t g_load_t0 = 0, g_last_render = 0;

static int g_fds[MAX_DEV];
static int g_nfds = 0;

/* ================================================================ logging */
static void logmsg(const char *msg) {
    FILE *f;
    time_t t = time(NULL);
    struct tm tm;
    char ts[32];
    if (g_sim) { fprintf(stderr, "log: %s\n", msg); return; }
    localtime_r(&t, &tm);
    strftime(ts, sizeof ts, "%Y-%m-%d %H:%M:%S", &tm);
    mkdir(DATA_DIR, 0755);
    f = fopen(LOG_PATH, "a");
    if (f) { fprintf(f, "%s %s\n", ts, msg); fclose(f); }
}

static void logf_(const char *fmt, ...) {
    char buf[512];
    va_list ap;
    va_start(ap, fmt);
    vsnprintf(buf, sizeof buf, fmt, ap);
    va_end(ap);
    logmsg(buf);
}

static void on_signal(int s) { (void)s; g_run = 0; }

static void trim(char *s) {
    size_t n = strlen(s);
    char *p = s;
    while (n > 0 && (s[n - 1] == '\n' || s[n - 1] == '\r' || s[n - 1] == ' ' || s[n - 1] == '\t')) s[--n] = 0;
    while (*p == ' ' || *p == '\t') p++;
    if (p != s) memmove(s, p, strlen(p) + 1);
}

/* ================================================================ config / state files */
static void load_config(void) {
    FILE *f = fopen(CFG_PATH, "r");
    char line[200];
    if (!f) return;
    while (fgets(line, sizeof line, f)) {
        char *eq;
        trim(line);
        if (line[0] == '#' || !(eq = strchr(line, '='))) continue;
        *eq = 0;
        trim(line);
        trim(eq + 1);
        if (strcmp(line, "open_key") == 0) {
            const char *v = eq + 1;
            if (strcasecmp(v, "red") == 0) g_open_key = KEY_RED;
            else if (strcasecmp(v, "green") == 0) g_open_key = KEY_GREEN;
            else if (strcasecmp(v, "yellow") == 0) g_open_key = KEY_YELLOW;
            else if (strcasecmp(v, "blue") == 0) g_open_key = KEY_BLUE;
        } else if (strcmp(line, "slot") == 0) {
            int v = atoi(eq + 1);
            if (v >= 1 && v <= 99) g_slot = v;
        } else if (strcmp(line, "port") == 0) {
            int v = atoi(eq + 1);
            if (v > 1024 && v < 65535) g_port = v;
        } else if (strcmp(line, "relay") == 0) {
            g_relay_cfg = (strcasecmp(eq + 1, "off") != 0);
        } else if (strcmp(line, "anti_drift") == 0) {
            g_anti = (strcasecmp(eq + 1, "off") != 0);
        } else if (strcmp(line, "drift_ms") == 0) {
            int v = atoi(eq + 1);
            if (v >= 200 && v <= 5000) g_drift_ms = v;
        } else if (strcmp(line, "auto_recover") == 0) {
            g_auto = (strcasecmp(eq + 1, "off") != 0);
        } else if (strcmp(line, "minibar") == 0) {
            g_minibar = strcasecmp(eq + 1, "off") == 0 ? 0 : (strcasecmp(eq + 1, "auto") == 0 ? 1 : 2);
        }
    }
    fclose(f);
}

static int dly_find(const char *url) {
    int i;
    for (i = 0; i < g_ndly; i++) if (strcmp(g_dly[i].url, url) == 0) return i;
    return -1;
}

static int dly_slot(const char *url) {
    int i = dly_find(url);
    if (i < 0) {
        if (g_ndly >= MAX_DELAYS) { memmove(&g_dly[0], &g_dly[1], sizeof(Dly) * (MAX_DELAYS - 1)); g_ndly = MAX_DELAYS - 1; }
        i = g_ndly++;
        snprintf(g_dly[i].url, sizeof g_dly[i].url, "%s", url);
        g_dly[i].half = g_half;
        g_dly[i].ahalf = g_ahalf;
    }
    return i;
}

static void dly_set_v(const char *url, int half) { g_dly[dly_slot(url)].half = half; }
static void dly_set_a(const char *url, int ahalf) { g_dly[dly_slot(url)].ahalf = ahalf; }

static void load_delays(void) {
    FILE *f = fopen(DELAYS_PATH, "r");
    char line[400];
    g_ndly = 0;
    if (!f) return;
    while (fgets(line, sizeof line, f)) {
        char *tab = strchr(line, '\t');
        int v = 0, a = 0, i;
        if (!tab) continue;
        *tab = 0;
        trim(line);
        if (!line[0]) continue;
        sscanf(tab + 1, "%d %d", &v, &a);
        if (g_ndly >= MAX_DELAYS) break;
        i = g_ndly++;
        snprintf(g_dly[i].url, sizeof g_dly[i].url, "%.255s", line);
        g_dly[i].half = v;
        g_dly[i].ahalf = a;
    }
    fclose(f);
}

static void save_delays(void) {
    FILE *f;
    int i;
    char tmp[256];
    snprintf(tmp, sizeof tmp, "%s.tmp", DELAYS_PATH);
    if (g_sim) return;
    f = fopen(tmp, "w");
    if (!f) return;
    for (i = 0; i < g_ndly; i++) fprintf(f, "%s\t%d\t%d\n", g_dly[i].url, g_dly[i].half, g_dly[i].ahalf);
    fclose(f);
    rename(tmp, DELAYS_PATH);
}

/* ================================================================ helper (IpaCtl) client */
static int ctl_cmd(const char *cmd, char *out, size_t n) {
    int fd, rc = -1;
    struct sockaddr_in a;
    struct timeval tv = {3, 0};
    size_t got = 0;
    char line[600];
    out[0] = 0;
    fd = socket(AF_INET, SOCK_STREAM, 0);
    if (fd < 0) return -1;
    setsockopt(fd, SOL_SOCKET, SO_RCVTIMEO, &tv, sizeof tv);
    setsockopt(fd, SOL_SOCKET, SO_SNDTIMEO, &tv, sizeof tv);
    memset(&a, 0, sizeof a);
    a.sin_family = AF_INET;
    a.sin_port = htons((unsigned short)g_port);
    a.sin_addr.s_addr = htonl(INADDR_LOOPBACK);
    if (connect(fd, (struct sockaddr *)&a, sizeof a) != 0) { close(fd); return -1; }
    snprintf(line, sizeof line, "%s\n", cmd);
    if (write(fd, line, strlen(line)) < 0) { close(fd); return -1; }
    while (got + 1 < n) {
        ssize_t r = read(fd, out + got, n - 1 - got);
        if (r <= 0) break;
        got += (size_t)r;
        out[got] = 0;
        if (strstr(out, "\nEND\n")) break;
    }
    close(fd);
    out[got] = 0;
    if (strncmp(out, "OK", 2) == 0 && strstr(out, "\nEND\n")) rc = 0;
    return rc;
}

/* find a running process by command line (does not depend on busybox pgrep) */
static int proc_find(const char *n1, const char *n2) {
    DIR *d = opendir("/proc");
    struct dirent *e;
    int found = 0;
    if (!d) return 0;
    while ((e = readdir(d))) {
        char path[300], buf[2048];
        int fd;
        ssize_t r, i;
        if (e->d_name[0] < '1' || e->d_name[0] > '9') continue;
        if (atoi(e->d_name) == (int)getpid()) continue;
        snprintf(path, sizeof path, "/proc/%s/cmdline", e->d_name);
        fd = open(path, O_RDONLY | O_CLOEXEC);
        if (fd < 0) continue;
        r = read(fd, buf, sizeof buf - 1);
        close(fd);
        if (r <= 0) continue;
        for (i = 0; i < r; i++) if (buf[i] == 0) buf[i] = ' ';
        buf[r] = 0;
        if (strstr(buf, n1) && (!n2 || strstr(buf, n2)) && strncmp(buf, "sh ", 3) != 0 && strstr(buf, "/bin/sh") == NULL) {
            found = atoi(e->d_name);
            break;
        }
    }
    closedir(d);
    return found;
}

static time_t g_ctl_launch = 0;

/* Start an app_process Java program detached, without /bin/sh (static glibc's system() uses /bin/sh, which does not
 * exist on Android - this was the reason the HUD and the helper never started in 1.0). Returns 0 when exec worked. */
static int launch_app_process(const char *jar, const char *class_name, const char *arg1, const char *arg2, const char *log_path) {
    const char *app = access("/system/bin/app_process32", X_OK) == 0 ? "/system/bin/app_process32" : "/system/bin/app_process";
    int p[2], child_errno = 0, status;
    ssize_t r;
    pid_t child;

    if (pipe(p) != 0) return -1;
    if (fcntl(p[1], F_SETFD, FD_CLOEXEC) != 0) {
        int e = errno;
        close(p[0]); close(p[1]); errno = e;
        return -1;
    }
    child = fork();
    if (child < 0) {
        int e = errno;
        close(p[0]); close(p[1]); errno = e;
        return -1;
    }
    if (child == 0) {
        pid_t grandchild;
        int logfd;
        char *argv[6];
        int argc = 0;

        close(p[0]);
        if (setsid() < 0) {
            child_errno = errno;
            (void)write(p[1], &child_errno, sizeof child_errno);
            _exit(127);
        }
        grandchild = fork();
        if (grandchild < 0) {
            child_errno = errno;
            (void)write(p[1], &child_errno, sizeof child_errno);
            _exit(127);
        }
        if (grandchild > 0) _exit(0);

        logfd = open(log_path, O_WRONLY | O_CREAT | O_APPEND, 0644);
        if (logfd >= 0) {
            (void)dup2(logfd, STDOUT_FILENO);
            (void)dup2(logfd, STDERR_FILENO);
            if (logfd > STDERR_FILENO) close(logfd);
        }
        if (setenv("CLASSPATH", jar, 1) != 0) {
            child_errno = errno;
            dprintf(STDERR_FILENO, "IPAudio: setenv CLASSPATH failed: %s\n", strerror(child_errno));
            (void)write(p[1], &child_errno, sizeof child_errno);
            _exit(127);
        }
        argv[argc++] = (char *)app;
        argv[argc++] = (char *)"/system/bin";
        argv[argc++] = (char *)class_name;
        if (arg1) argv[argc++] = (char *)arg1;
        if (arg2) argv[argc++] = (char *)arg2;
        argv[argc] = NULL;
        execv(app, argv);
        child_errno = errno;
        dprintf(STDERR_FILENO, "IPAudio: exec %s failed: %s\n", app, strerror(child_errno));
        (void)write(p[1], &child_errno, sizeof child_errno);
        _exit(127);
    }
    close(p[1]);
    while (waitpid(child, &status, 0) < 0) {
        if (errno == EINTR) continue;
        { int e = errno; close(p[0]); errno = e; return -1; }
    }
    do { r = read(p[0], &child_errno, sizeof child_errno); } while (r < 0 && errno == EINTR);
    close(p[0]);
    if (r == (ssize_t)sizeof child_errno) { errno = child_errno; return -1; }
    if (r < 0) return -1;
    return 0;
}

/* start the helper unless it was started a moment ago or is still alive */
static void ctl_launch(void) {
    time_t now = time(NULL);
    int pid;
    if (g_sim) return;
    if (access(CTL_JAR, R_OK) != 0) { logmsg("no IpaCtl.jar"); return; }
    if (g_ctl_launch && now - g_ctl_launch < 8) return;
    pid = proc_find(CTL_CLASS, NULL);
    if (pid) {
        if (g_ctl_launch && now - g_ctl_launch < 25) return;     /* still starting */
        logf_("helper process %d does not answer, restarting it", pid);
        kill(pid, SIGKILL);
        sleep(1);
    }
    if (launch_app_process(CTL_JAR, CTL_CLASS, "--uid=1000", "--gid=3003", CTL_LOG) != 0) {
        logf_("helper launch failed: %s", strerror(errno));
        return;
    }
    g_ctl_launch = now;
    logmsg("helper app_process started");
}

/* ================================================================ overlay + HUD */
static void ovl_write(const char *s) {
    char tmp[256];
    FILE *f;
    snprintf(tmp, sizeof tmp, "%s.tmp", OVL_PATH);
    f = fopen(tmp, "w");
    if (!f) return;
    fputs(s, f);
    fclose(f);
    chmod(tmp, 0644);
    rename(tmp, OVL_PATH);
}

static void hud_start(void) {
    if (g_sim) return;
    if (access(HUD_JAR, R_OK) != 0) { logmsg("no IpaHud.jar"); return; }
    if (proc_find(HUD_CLASS, NULL)) return;
    if (launch_app_process(HUD_JAR, HUD_CLASS, OVL_PATH, NULL, LOG_PATH) != 0) {
        logf_("HUD launch failed: %s", strerror(errno));
        return;
    }
    logmsg("HUD app_process started");
}

static void hud_stop(void) {
    int pid, tries = 0;
    if (g_sim) return;
    ovl_write("[HIDE]");
    while ((pid = proc_find(HUD_CLASS, NULL)) && tries++ < 5) { kill(pid, SIGTERM); usleep(150000); }
}

/* ================================================================ stream list */
static int add_srv(const char *name, int builtin) {
    int i;
    for (i = 0; i < g_nsrv; i++) if (strcmp(g_srv[i].name, name) == 0) return i;
    if (g_nsrv >= MAX_SRV) return g_nsrv - 1;
    snprintf(g_srv[g_nsrv].name, sizeof g_srv[g_nsrv].name, "%s", name);
    g_srv[g_nsrv].builtin = builtin;
    return g_nsrv++;
}

static void add_ent(int srv, const char *title, const char *url, int id, int builtin) {
    Ent *e;
    if (g_nent >= MAX_ENT) return;
    e = &g_ent[g_nent++];
    snprintf(e->title, sizeof e->title, "%s", title);
    snprintf(e->url, sizeof e->url, "%s", url);
    e->id = id;
    e->srv = srv;
    e->builtin = builtin;
}

static int url_ok(const char *u) {
    const char *p;
    if (strncmp(u, "http://", 7) != 0 && strncmp(u, "https://", 8) != 0) return 0;
    for (p = u; *p; p++) {
        unsigned char c = (unsigned char)*p;
        if (c <= 0x20 || c == '"' || c == '\'' || c == '`' || c == '$' || c == ';' || c == '|' || c == '\\' || c == '<' || c == '>')
            return 0;
    }
    return 1;
}

static void load_playlist(void) {
    FILE *f = fopen(LIST_PATH, "r");
    char line[512];
    int srv = -1;
    if (!f) return;
    while (fgets(line, sizeof line, f)) {
        char *bar;
        trim(line);
        if (!line[0] || strncmp(line, "//", 2) == 0) continue;
        if (line[0] == '#' || line[0] == '[') {
            char *name = line + 1;
            char *rb;
            if (line[0] == '[' && (rb = strchr(name, ']'))) *rb = 0;
            trim(name);
            if (name[0]) srv = add_srv(name, 0);
            continue;
        }
        bar = strchr(line, '|');
        if (!bar) continue;
        *bar = 0;
        trim(line);
        trim(bar + 1);
        if (!line[0] || !url_ok(bar + 1)) { logf_("playlist: skipped line '%s'", line); continue; }
        if (srv < 0) srv = add_srv("My links", 0);
        add_ent(srv, line, bar + 1, 0, 0);
    }
    fclose(f);
}

/* LIST reply: "OK <count> <currentId>" then id|title|url|delay lines, TAIL, END */
static int load_builtin(void) {
    static char buf[24576];
    char *save = NULL, *ln;
    int srv, first = 1, n = 0;
    if (ctl_cmd("LIST", buf, sizeof buf) != 0) return -1;
    srv = add_srv("Built-in", 1);
    for (ln = strtok_r(buf, "\n", &save); ln; ln = strtok_r(NULL, "\n", &save)) {
        char *a, *b, *c;
        if (first) {
            int cnt = 0, cur = 0;
            first = 0;
            if (sscanf(ln, "OK %d %d", &cnt, &cur) == 2) g_active_id = cur;
            continue;
        }
        if (strcmp(ln, "END") == 0 || strncmp(ln, "TAIL", 4) == 0) break;
        a = strchr(ln, '|');
        if (!a) continue;
        *a++ = 0;
        b = strchr(a, '|');
        if (!b) continue;
        *b++ = 0;
        c = strchr(b, '|');
        if (!c) continue;
        *c = 0;
        if (url_ok(b)) { add_ent(srv, a, b, atoi(ln), 1); n++; }
    }
    return n;
}

static void rebuild_view(void) {
    int i;
    g_nview = 0;
    for (i = 0; i < g_nent; i++) if (g_ent[i].srv == g_cur_srv) g_view[g_nview++] = i;
}

static void load_all(void) {
    char keep_name[40] = "";
    char keep_url[256] = "";
    int n;
    if (g_cur_srv >= 0 && g_cur_srv < g_nsrv) snprintf(keep_name, sizeof keep_name, "%s", g_srv[g_cur_srv].name);
    if (g_play >= 0 && g_play < g_nent) snprintf(keep_url, sizeof keep_url, "%s", g_ent[g_play].url);
    g_nent = 0;
    g_nsrv = 0;
    g_play = -1;
    load_playlist();
    n = load_builtin();
    if (n < 0) snprintf(g_status, sizeof g_status, "helper not answering - built-in streams unavailable");
    g_cur_srv = 0;
    if (keep_name[0]) {
        int i;
        for (i = 0; i < g_nsrv; i++) if (strcmp(g_srv[i].name, keep_name) == 0) g_cur_srv = i;
    }
    if (keep_url[0]) {
        int i;
        for (i = 0; i < g_nent; i++) if (strcmp(g_ent[i].url, keep_url) == 0) g_play = i;
    }
    rebuild_view();
    logf_("loaded %d streams in %d servers", g_nent, g_nsrv);
}

static void read_state(void) {
    char buf[256];
    int e = -1, x = 0, d1 = 0, d2 = 0;
    if (ctl_cmd("STATE", buf, sizeof buf) == 0 && sscanf(buf, "OK %d %d %d %d", &e, &x, &d1, &d2) == 4 && e == 0) {
        g_half = d1 + d2;
        if (g_half < 0) g_half = 0;
        if (g_half > MAX_HALF) g_half = MAX_HALF;
    }
}

/* ================================================================ render */
#define APPEND(...) do { if (n < (int)sizeof out - 1) n += snprintf(out + n, sizeof out - n, __VA_ARGS__); \
                         if (n > (int)sizeof out - 1) n = (int)sizeof out - 1; } while (0)

static void fmt_delay(char *dst, size_t n, int half) { snprintf(dst, n, "%d.%d s", half / 2, (half % 2) * 5); }

/* plain text for the HUD protocol: no emoji, no '|', no control characters */
static void plain_text(char *dst, size_t n, const char *src) {
    size_t o = 0;
    const unsigned char *p = (const unsigned char *)src;
    while (*p && o + 4 < n) {
        if (*p >= 0xF0) { p++; while ((*p & 0xC0) == 0x80) p++; continue; }          /* emoji / flags */
        if (*p == 0xEF && p[1] == 0xB8 && p[2] == 0x8F) { p += 3; continue; }
        if (*p == '|') { dst[o++] = '/'; p++; continue; }
        if (*p < 0x20) { p++; continue; }
        dst[o++] = (char)*p++;
    }
    dst[o] = 0;
    {
        char *q = dst;
        while (*q == ' ') q++;
        if (q != dst) memmove(dst, q, strlen(q) + 1);
    }
}

/* one-line audio status, like the Enigma plugin's "Playing X | Buffer: 100% (268 kbps) - stable" */
static const char *status_text(char *out, size_t n) {
    char t[200], dl[24], kb[24] = "", extra[96] = "";
    Ent *e = (g_play >= 0 && g_play < g_nent && g_active_id != 0) ? &g_ent[g_play] : NULL;
    if (!e) { snprintf(out, n, "original audio"); return "#90A4AE"; }
    plain_text(t, sizeof t, e->title);
    if (!g_play_relayed) { snprintf(out, n, "Playing %s \xC2\xB7 direct (no aDelay / status)", t); return "#69F0AE"; }
    if (!g_stat.valid) { snprintf(out, n, "Playing %s", t); return "#69F0AE"; }
    if (g_stat.kbps > 0) snprintf(kb, sizeof kb, " \xC2\xB7 %d kbps", g_stat.kbps);
    if (strcmp(g_stat.state, "PLAYING") == 0) {
        if (g_half > 0) { fmt_delay(dl, sizeof dl, g_half); snprintf(extra + strlen(extra), sizeof extra - strlen(extra), " \xC2\xB7 vDelay %s", dl); }
        if (g_ahalf > 0) { fmt_delay(dl, sizeof dl, g_ahalf); snprintf(extra + strlen(extra), sizeof extra - strlen(extra), " \xC2\xB7 aDelay %s", dl); }
        snprintf(out, n, "Playing %s%s \xC2\xB7 %s%s", t, kb, (g_stat.reconn > 0 && g_stat.recovers + g_stat.reconn > 2) ? "unstable" : "stable", extra);
        return "#69F0AE";
    }
    if (strcmp(g_stat.state, "BUFFERING") == 0) { snprintf(out, n, "Buffering %s \xC2\xB7 %d%%%s", t, g_stat.pct, kb); return "#FFAB40"; }
    if (strcmp(g_stat.state, "WAITING") == 0) { snprintf(out, n, "%s \xC2\xB7 stream OK%s - waiting for the TV player to connect", t, kb); return "#FFAB40"; }
    if (strcmp(g_stat.state, "CONNECTING") == 0) { snprintf(out, n, "Connecting to %s ...", t); return "#FFAB40"; }
    if (strcmp(g_stat.state, "STALLED") == 0) { snprintf(out, n, "No data from %s - reconnecting", t); return "#FF5252"; }
    if (strcmp(g_stat.state, "ERROR") == 0) { snprintf(out, n, "Error: %s - retrying (%d)", g_stat.msg[0] ? g_stat.msg : "stream unreachable", g_stat.reconn); return "#FF5252"; }
    if (strcmp(g_stat.state, "DIRECT") == 0 || strcmp(g_stat.state, "HLS") == 0) { snprintf(out, n, "Playing %s \xC2\xB7 %s", t, g_stat.msg[0] ? g_stat.msg : "direct mode, no aDelay / status"); return "#FFAB40"; }
    snprintf(out, n, "%s \xC2\xB7 %s", t, g_stat.state);
    return "#90A4AE";
}

/* badge on the playing row, like the "100% - 258k" meter in the Enigma list */
static const char *row_badge(char *out, size_t n) {
    out[0] = 0;
    if (!g_play_relayed || !g_stat.valid) return "#69F0AE";
    if (strcmp(g_stat.state, "PLAYING") == 0) { snprintf(out, n, "100%% - %dk", g_stat.kbps); return "#69F0AE"; }
    if (strcmp(g_stat.state, "BUFFERING") == 0) { snprintf(out, n, "%d%%", g_stat.pct); return "#FFAB40"; }
    if (strcmp(g_stat.state, "STALLED") == 0 || strcmp(g_stat.state, "ERROR") == 0) { snprintf(out, n, "%s", g_stat.state); return "#FF5252"; }
    snprintf(out, n, "%s", g_stat.state);
    return "#FFAB40";
}

#define LARR "\xE2\x97\x80"
#define RARR "\xE2\x96\xB6"

static void render_menu(void) {
    char out[12000], tbuf[320], pt[320], dl[24], badge[48], nm[240], sub[400];
    const char *col;
    int n = 0, top, i;
    /* selection map: 0=vDelay, 1=server, 2..g_nview+1 = stream index (g_sel-2) */
    int vrow = 0, srow = 1;

    if (g_status[0]) { plain_text(tbuf, sizeof tbuf, g_status); col = "#FFAB40"; }
    else { char raw[320]; col = status_text(raw, sizeof raw); plain_text(tbuf, sizeof tbuf, raw); }
    APPEND("BAR|%s|%s\n", col, tbuf);
    APPEND("PANEL|iP AUDIO+|v" VERSION "\n");

    /* ---- Delay FIRST (top of panel) — video delay only ---- */
    APPEND("SEC|Delay\n");
    fmt_delay(dl, sizeof dl, g_half);
    if (g_sel == vrow) APPEND("KV|S|vDelay|" LARR " %s " RARR "\n", dl);
    else APPEND("KV||vDelay|%s\n", dl);
    APPEND("INFO|#90A4AE|video delay (same API as yellow-button menu)\n");

    APPEND("SEC|Server\n");
    plain_text(nm, sizeof nm, g_nsrv ? g_srv[g_cur_srv].name : "none");
    if (g_sel == srow) APPEND("KV|S|Selected server|" LARR " %s " RARR "\n", nm);
    else APPEND("KV||Selected server|%s\n", nm);

    APPEND("SEC|Audio\n");
    if (g_nview == 0) {
        APPEND("INFO|#CFD8DC|No streams. Edit playlist.txt and press GREEN.\n");
    } else {
        int cur = (g_sel >= 2 && g_sel <= g_nview + 1) ? (g_sel - 2) : 0;
        top = cur - VISIBLE / 2;
        if (top > g_nview - VISIBLE) top = g_nview - VISIBLE;
        if (top < 0) top = 0;
        if (top > 0) APPEND("INFO|#546E7A|%d more above\n", top);
        for (i = top; i < g_nview && i < top + VISIBLE; i++) {
            Ent *e = &g_ent[g_view[i]];
            int playing = (g_view[i] == g_play && g_active_id != 0);
            char flags[4] = "";
            if (g_sel == i + 2) strcat(flags, "S");
            if (playing) strcat(flags, "P");
            plain_text(nm, sizeof nm, e->title);
            plain_text(pt, sizeof pt, g_srv[e->srv].name);
            snprintf(sub, sizeof sub, "%s", pt);
            badge[0] = 0;
            col = "#69F0AE";
            if (playing) {
                col = row_badge(badge, sizeof badge);
                if (g_live_info && g_stat.valid) {
                    if (g_play_relayed && strcmp(g_stat.state, "PLAYING") == 0)
                        snprintf(sub, sizeof sub, "%d kbps \xC2\xB7 %s \xC2\xB7 reconn %d",
                                 g_stat.kbps,
                                 (g_stat.reconn > 0 && g_stat.recovers + g_stat.reconn > 2) ? "unstable" : "stable",
                                 g_stat.reconn);
                    else
                        snprintf(sub, sizeof sub, "%s \xC2\xB7 %s",
                                 g_stat.state[0] ? g_stat.state : "live",
                                 g_stat.kbps > 0 ? "see live info" : pt);
                }
            }
            APPEND("ITEM|%s|%d|%s|%s|%s|%s\n", flags, i + 1, nm, sub, badge, col);
        }
        if (top + VISIBLE < g_nview) APPEND("INFO|#546E7A|%d more below\n", g_nview - top - VISIBLE);
    }

    /* live info block when playing */
    if (g_live_info && g_active_id != 0) {
        APPEND("SEC|Live\n");
        if (g_stat.valid) {
            APPEND("INFO|#B0BEC5|state %s \xC2\xB7 %d kbps \xC2\xB7 recovers %d \xC2\xB7 reconnects %d\n",
                   g_stat.state[0] ? g_stat.state : "?", g_stat.kbps, g_stat.recovers, g_stat.reconn);
            APPEND("INFO|#78909C|anti-drift %s (%d)  auto-recover %s (%d)\n",
                   g_anti ? "ON" : "OFF", g_stat.skips, g_auto ? "ON" : "OFF", g_stat.recovers);
        } else {
            APPEND("INFO|#90A4AE|live stats when relay reports status (direct play = limited)\n");
        }
    }

    APPEND("LEG|<font color='#FF5252'>&#9679;</font> Reset vDelay &nbsp; <font color='#69F0AE'>&#9679;</font> Reload &nbsp; "
           "<font color='#FFD600'>&#9679;</font> Original audio &nbsp; <font color='#29B6F6'>&#9679;</font> Live info / Exit<br/>"
           "OK play \xC2\xB7 LEFT/RIGHT vDelay\n");
    ovl_write(out);
}

/* ================================================================ actions */
static void grab_inputs(int on) {
    int i;
    for (i = 0; i < g_nfds; i++) ioctl(g_fds[i], EVIOCGRAB, on);
}

static void set_delay(int half) {
    char cmd[40], buf[160];
    if (half < 0) half = 0;
    if (half > MAX_HALF) half = MAX_HALF;
    g_half = half;
    snprintf(cmd, sizeof cmd, "DELAY %d", half);
    if (ctl_cmd(cmd, buf, sizeof buf) != 0) snprintf(g_status, sizeof g_status, "delay not applied (helper)");
    else g_status[0] = 0;
    if (g_play >= 0 && g_play < g_nent) dly_set_v(g_ent[g_play].url, half);
    g_bar_until = time(NULL) + 6;
}

/* audio delay: handled by the relay; the helper restarts the stream about a second after the last change */
static void set_adelay(int half) {
    char cmd[40], buf[160];
    if (half < 0) half = 0;
    if (half > MAX_AHALF) half = MAX_AHALF;
    g_ahalf = half;
    if (g_play >= 0 && g_play < g_nent) dly_set_a(g_ent[g_play].url, half);
    if (g_play >= 0 && g_active_id != 0) {
        if (!g_play_relayed) { snprintf(g_status, sizeof g_status, "aDelay needs the relay (config relay=on, helper updated)"); return; }
        snprintf(cmd, sizeof cmd, "ADELAY %d", half);
        if (ctl_cmd(cmd, buf, sizeof buf) != 0) snprintf(g_status, sizeof g_status, "aDelay not applied (%.50s)", buf[0] ? buf : "helper");
        else g_status[0] = 0;
    }
}

static void play_entry(int ei) {
    char cmd[400], buf[200];
    Ent *e = &g_ent[ei];
    int id = e->builtin ? e->id : g_slot;
    int di = dly_find(e->url);
    int ah = di >= 0 ? g_dly[di].ahalf : g_ahalf;      /* each stream keeps its own delays */
    int vh = di >= 0 ? g_dly[di].half : g_half;
    int relayed = 0;
    char note[120] = "";

    if (g_relay_cfg) {
        snprintf(cmd, sizeof cmd, "PLAY %d %d %s", id, ah, e->url);
        if (ctl_cmd(cmd, buf, sizeof buf) == 0 && strstr(buf, "err=0") != NULL) relayed = 1;
        else logf_("PLAY failed (%.80s), trying direct", buf);
    }
    if (!relayed) {
        snprintf(cmd, sizeof cmd, "SET %d %s", id, e->url);
        if (ctl_cmd(cmd, buf, sizeof buf) != 0 || strstr(buf, "err=0") == NULL) {
            snprintf(g_status, sizeof g_status, "could not start the stream (%.60s)", buf[0] ? buf : "no answer");
            logf_("SET failed: %s", buf);
            return;
        }
        if (g_relay_cfg) snprintf(note, sizeof note, "relay unavailable - playing directly (no aDelay / status)");
        ah = 0;
    }
    g_play = ei;
    g_active_id = id;
    g_play_relayed = relayed;
    g_ahalf = ah;
    g_stat.valid = 0;
    g_stat_poll = 0;
    g_status[0] = 0;
    set_delay(vh);
    if (note[0] && !g_status[0]) snprintf(g_status, sizeof g_status, "%s", note);
    g_bar_until = time(NULL) + 8;
    logf_("playing '%s' id %d relay=%d vdelay %d adelay %d", e->title, id, relayed, g_half, g_ahalf);
}

static void audio_off(void) {
    char buf[160];
    if (ctl_cmd("OFF", buf, sizeof buf) != 0 || strstr(buf, "err=0") == NULL) {
        snprintf(g_status, sizeof g_status, "original audio request failed (%.60s)", buf[0] ? buf : "no answer");
        logf_("OFF failed: %s", buf);
        return;
    }
    g_active_id = 0;
    g_play_relayed = 0;
    g_stat.valid = 0;
    g_status[0] = 0;
    logmsg("external audio off requested");
}

static void save_last(void) {
    FILE *f;
    if (g_sim || g_nsrv == 0) return;
    f = fopen(LAST_PATH, "w");
    if (!f) return;
    fprintf(f, "server=%s\n", g_srv[g_cur_srv].name);
    fclose(f);
}

static void restore_last(void) {
    FILE *f = fopen(LAST_PATH, "r");
    char line[120];
    int i;
    if (!f) return;
    if (fgets(line, sizeof line, f)) {
        trim(line);
        if (strncmp(line, "server=", 7) == 0)
            for (i = 0; i < g_nsrv; i++) if (strcmp(g_srv[i].name, line + 7) == 0) g_cur_srv = i;
    }
    fclose(f);
    rebuild_view();
}

/* tell the helper how anti-drift / auto-recover are configured */
static void push_config(void) {
    char cmd[64], buf[96];
    snprintf(cmd, sizeof cmd, "DRIFT %s %d", g_anti ? "on" : "off", g_drift_ms);
    ctl_cmd(cmd, buf, sizeof buf);
    snprintf(cmd, sizeof cmd, "AUTO %s", g_auto ? "on" : "off");
    ctl_cmd(cmd, buf, sizeof buf);
}

static void menu_open(void) {
    char buf[64];
    g_status[0] = 0;
    g_need_load = 0;
    g_toast_until = 0;
    hud_start();
    if (ctl_cmd("PING", buf, sizeof buf) == 0) {
        push_config();
        load_all();
        restore_last();
        read_state();
    } else {                                   /* show your own links right away, bring the helper up in the background */
        load_all();
        restore_last();
        g_need_load = 1;
        g_load_t0 = time(NULL);
        g_ctl_launch = 0;
        ctl_launch();
        snprintf(g_status, sizeof g_status, "starting helper...");
    }
    g_sel = 0;  /* open on vDelay (top) */
    g_menu_open = 1;
    g_last_key = time(NULL);
    grab_inputs(1);
    render_menu();
    logmsg("menu open");
}

/* status bar while the panel is closed ("mini bar"): always, or for a few seconds after events, or never */
static void bar_apply(int force) {
    char raw[320], t[320], out[500];
    const char *col;
    time_t now = time(NULL);
    int want = 0;
    if (g_menu_open) return;
    if (g_toast_until && now < g_toast_until) return;
    if (g_play >= 0 && g_play < g_nent && g_active_id != 0) {
        if (g_minibar == 2) want = 1;
        else if (g_minibar == 1 && now < g_bar_until) want = 1;
    }
    if (want) {
        col = status_text(raw, sizeof raw);
        plain_text(t, sizeof t, raw);
        snprintf(out, sizeof out, "BAR|%s|%s\n", col, t);
        if (force || strcmp(out, g_bar_last) != 0) {
            if (!g_bar_shown) hud_start();
            ovl_write(out);
            snprintf(g_bar_last, sizeof g_bar_last, "%s", out);
            g_bar_shown = 1;
        }
    } else if (g_bar_shown) {
        ovl_write("[FADE]");
        g_bar_shown = 0;
        g_bar_last[0] = 0;
    }
}

/* short message on the status bar while the panel is closed (errors, recovery) */
static void toast(const char *color, const char *text) {
    char out[400], t[300];
    plain_text(t, sizeof t, text);
    snprintf(out, sizeof out, "BAR|%s|%s\n", color, t);
    hud_start();
    ovl_write(out);
    g_bar_shown = 1;
    g_bar_last[0] = 0;
    g_toast_until = time(NULL) + 6;
}

/* poll the relay status; refresh the panel when it changed, toast problems when the panel is closed */
static void status_poll(void) {
    char buf[600], *line, *f[10];
    char prev[12];
    Stat s;
    int nf = 0, changed;
    time_t now = time(NULL);
    if (g_play < 0 || g_active_id == 0 || !g_play_relayed) return;
    if (now - g_stat_poll < (g_menu_open ? 1 : 3)) return;
    g_stat_poll = now;
    if (ctl_cmd("STATUS", buf, sizeof buf) != 0) { g_stat.valid = 0; return; }
    line = buf + 3;                                    /* skip "OK " */
    { char *nl = strchr(line, '\n'); if (nl) *nl = 0; }
    f[nf++] = line;
    for (; *line && nf < 10; line++) if (*line == '|') { *line = 0; f[nf++] = line + 1; }
    if (nf < 8) return;
    memset(&s, 0, sizeof s);
    s.valid = 1;
    snprintf(s.state, sizeof s.state, "%s", f[0]);
    s.pct = atoi(f[1]);
    s.kbps = atoi(f[2]);
    s.buf = atoi(f[3]);
    s.reconn = atoi(f[4]);
    s.skips = atoi(f[5]);
    snprintf(s.fmt, sizeof s.fmt, "%s", f[6]);
    snprintf(s.msg, sizeof s.msg, "%s", f[7]);
    s.recovers = nf >= 9 ? atoi(f[8]) : 0;
    changed = !g_stat.valid || strcmp(s.state, g_stat.state) != 0 || s.pct / 10 != g_stat.pct / 10 || s.kbps / 20 != g_stat.kbps / 20 ||
              s.reconn != g_stat.reconn || s.skips != g_stat.skips || s.recovers != g_stat.recovers || strcmp(s.msg, g_stat.msg) != 0;
    snprintf(prev, sizeof prev, "%s", g_stat.valid ? g_stat.state : "");
    g_stat = s;
    if (changed && strcmp(prev, s.state) != 0) logf_("audio status %s -> %s (%s)", prev[0] ? prev : "-", s.state, s.msg);
    if (g_menu_open) { if (changed) render_menu(); return; }
    if (strcmp(prev, s.state) != 0) g_bar_until = now + 8;
    if (strcmp(prev, s.state) != 0) {
        int bad_now = strcmp(s.state, "ERROR") == 0 || strcmp(s.state, "STALLED") == 0;
        int bad_before = strcmp(prev, "ERROR") == 0 || strcmp(prev, "STALLED") == 0;
        if (bad_now) { char t[160]; snprintf(t, sizeof t, "Audio problem: %s", s.msg[0] ? s.msg : "no data"); toast("#FF5252", t); }
        else if (bad_before && strcmp(s.state, "PLAYING") == 0) toast("#69F0AE", "Audio recovered");
        else if (strcmp(s.state, "HLS") == 0 || strcmp(s.state, "DIRECT") == 0) toast("#FFAB40", "HLS stream: direct mode (no aDelay / status)");
    }
}

/* finish loading once the helper answers */
static void tick_load(void) {
    char buf[64];
    long el;
    if (!g_menu_open || !g_need_load) return;
    el = (long)(time(NULL) - g_load_t0);
    if (ctl_cmd("PING", buf, sizeof buf) == 0) {
        g_need_load = 0;
        g_status[0] = 0;
        push_config();
        load_all();
        read_state();
        render_menu();
        logf_("helper ready after %ld s", el);
        return;
    }
    if (el >= 30) {
        g_need_load = 0;
        snprintf(g_status, sizeof g_status, "helper not answering - see ipactl.log (GREEN = retry)");
        logf_("helper still not answering after %ld s, process=%d", el, proc_find(CTL_CLASS, NULL));
        render_menu();
        return;
    }
    if (time(NULL) != g_last_render) {
        g_last_render = time(NULL);
        ctl_launch();
        snprintf(g_status, sizeof g_status, "starting helper... %ld s", el);
        render_menu();
    }
}

/* called every ~300 ms */
static void tick(void) {
    tick_load();
    status_poll();
    if (!g_menu_open && g_toast_until && time(NULL) >= g_toast_until) g_toast_until = 0;
    bar_apply(0);
}

static void menu_close(void) {
    g_menu_open = 0;
    grab_inputs(0);
    save_delays();
    save_last();
    g_bar_until = time(NULL) + 6;
    g_bar_shown = 1;                 /* the panel is on screen: bar_apply replaces it or fades it out */
    g_bar_last[0] = 0;
    bar_apply(1);
    logmsg("menu close");
}

static void move(int dir) {
    int rows = g_nview + 2;  /* 0=vDelay, 1=server, 2..streams */
    g_sel = (g_sel + rows + dir) % rows;
}

/* many remotes send F1..F4 for the colour keys (MatchZap treats F1 as RED the same way) */
static int norm_code(int c) {
    if (c == KEY_F1) return KEY_RED;
    if (c == KEY_F2) return KEY_GREEN;
    if (c == KEY_F3) return KEY_YELLOW;
    if (c == KEY_F4) return KEY_BLUE;
    return c;
}

static int g_dbg_left = 40;      /* log the first key presses seen while the panel is closed, to identify remote buttons */

static void handle_key(int code, int value, int *down, struct timespec *t0) {
    int raw = code;
    if (code == KEY_ESC) return;       /* your remote sends an extra "key 1" after every button press */
    code = norm_code(code);
    if (!g_menu_open && value == 1 && g_dbg_left > 0) {
        g_dbg_left--;
        logf_("closed: key %d (as %d) open_key=%d", raw, code, g_open_key);
    }
    if (g_menu_open) {
        int is_ok = (code == KEY_ENTER || code == KEY_OK || code == KEY_CENTER);
        if (value == 0) return;
        g_last_key = time(NULL);
        if (value == 1) logf_("key %d", code);
        if (code == KEY_UP) { move(-1); render_menu(); }
        else if (code == KEY_DOWN) { move(1); render_menu(); }
        else if (code == KEY_LEFT || code == KEY_RIGHT) {
            int dir = (code == KEY_RIGHT) ? 1 : -1;
            if (g_sel == 1) {
                /* server row */
                if (g_nsrv > 1) {
                    g_cur_srv = (g_cur_srv + g_nsrv + dir) % g_nsrv;
                    rebuild_view();
                    save_last();
                }
            } else {
                /* vDelay row (0) or any stream row: adjust video delay */
                set_delay(g_half + dir);
            }
            render_menu();
        } else if (value == 1 && is_ok) {
            if (g_sel >= 2 && g_sel <= g_nview + 1) play_entry(g_view[g_sel - 2]);
            else if (g_sel == 1 && g_nview > 0) g_sel = 2; /* OK on server -> first stream */
            render_menu();
        } else if (value == 1 && code == KEY_RED) {
            set_delay(0);
            render_menu();
        } else if (value == 1 && code == KEY_YELLOW) {
            audio_off();
            render_menu();
        } else if (value == 1 && code == KEY_GREEN) {
            char pb[64];
            load_all();
            if (ctl_cmd("PING", pb, sizeof pb) == 0) { read_state(); snprintf(g_status, sizeof g_status, "reloaded"); }
            else { g_need_load = 1; g_load_t0 = time(NULL); g_ctl_launch = 0; ctl_launch(); snprintf(g_status, sizeof g_status, "starting helper..."); }
            g_sel = 0; /* vDelay on top */
            render_menu();
        } else if (value == 1 && code == KEY_BLUE) {
            /* short BLUE while panel open = toggle live info (bitrate) */
            g_live_info = !g_live_info;
            snprintf(g_status, sizeof g_status, g_live_info ? "live info ON" : "live info OFF");
            render_menu();
        } else if (value == 1 && code == KEY_BACK) {
            menu_close();
        }
        return;
    }

    /* panel closed: only a long press of the open key opens it */
    if (code != g_open_key) return;
    if (value == 1) {
        *down = 1;
        clock_gettime(CLOCK_MONOTONIC, t0);
    } else if (value == 2 && *down) {
        *down = 0;
        menu_open();
    } else if (value == 0 && *down) {
        struct timespec t1;
        long ms;
        clock_gettime(CLOCK_MONOTONIC, &t1);
        ms = (t1.tv_sec - t0->tv_sec) * 1000L + (t1.tv_nsec - t0->tv_nsec) / 1000000L;
        *down = 0;
        if (ms >= LONG_MS) menu_open();
    }
}

/* ================================================================ input */
static void open_inputs(void) {
    DIR *d = opendir("/dev/input");
    struct dirent *e;
    g_nfds = 0;
    if (!d) return;
    while ((e = readdir(d)) && g_nfds < MAX_DEV) {
        char path[300];
        int fd;
        if (strncmp(e->d_name, "event", 5) != 0) continue;
        snprintf(path, sizeof path, "/dev/input/%s", e->d_name);
        fd = open(path, O_RDONLY | O_NONBLOCK | O_CLOEXEC);
        if (fd >= 0) g_fds[g_nfds++] = fd;
    }
    closedir(d);
}

static void input_loop(void) {
    struct pollfd pfd[MAX_DEV];
    struct input_event ev;
    struct timespec t0 = {0, 0};
    int down = 0, i, r;
    for (;;) {
        if (!g_run) break;
        if (g_nfds == 0) {
            open_inputs();
            if (g_nfds == 0) { sleep(1); continue; }
        }
        for (i = 0; i < g_nfds; i++) { pfd[i].fd = g_fds[i]; pfd[i].events = POLLIN; pfd[i].revents = 0; }
        r = poll(pfd, g_nfds, 300);
        if (r > 0) {
            for (i = 0; i < g_nfds; i++) {
                if (!(pfd[i].revents & POLLIN)) continue;
                while (read(g_fds[i], &ev, sizeof ev) == (ssize_t)sizeof ev)
                    if (ev.type == EV_KEY) handle_key((int)ev.code, (int)ev.value, &down, &t0);
            }
        }
        tick();
        if (g_menu_open && time(NULL) - g_last_key > IDLE_CLOSE) {   /* never leave the remote grabbed */
            logmsg("menu closed by idle timeout");
            menu_close();
        }
    }
    if (g_menu_open) grab_inputs(0);
    for (i = 0; i < g_nfds; i++) close(g_fds[i]);
}

/* ================================================================ boot / main */
static int single_instance(void) {
    int fd;
    char pid[32];
    mkdir(DATA_DIR, 0755);
    fd = open(LOCK_PATH, O_RDWR | O_CREAT, 0644);
    if (fd < 0) return 1;
    fcntl(fd, F_SETFD, FD_CLOEXEC);
    if (flock(fd, LOCK_EX | LOCK_NB) != 0) { close(fd); return 0; }
    (void)ftruncate(fd, 0);
    snprintf(pid, sizeof pid, "%d\n", (int)getpid());
    (void)write(fd, pid, strlen(pid));
    return 1;
}

static char *slurp(const char *path, size_t max) {
    FILE *f = fopen(path, "r");
    char *b;
    size_t n;
    if (!f) return NULL;
    b = malloc(max + 1);
    if (!b) { fclose(f); return NULL; }
    n = fread(b, 1, max, f);
    fclose(f);
    b[n] = 0;
    return b;
}

static void ensure_autorun(void) {
    char *buf = slurp(AUTORUN, 256 * 1024);
    FILE *f;
    int existed = (access(AUTORUN, F_OK) == 0);
    if (buf && strstr(buf, "/data/plugin/IPAudio ")) { free(buf); return; }
    free(buf);
    f = fopen(AUTORUN, "a");
    if (!f) { logmsg("autorun append failed"); return; }
    if (!existed) fputs("#!/system/bin/sh\n", f);
    fprintf(f, "\n%s\n", AUTORUN_LINE);
    fclose(f);
    chmod(AUTORUN, 0755);
    logmsg("autorun line added");
}

/* --sim: read key names from stdin (up down left right ok back red green yellow blue, "open") and print the overlay */
static int sim_main(void) {
    char tok[64];
    int down = 0;
    struct timespec t0 = {0, 0};
    g_sim = 1;
    load_config();
    load_delays();
    menu_open();
    printf("%s\n----\n", slurp(OVL_PATH, 16384));
    while (scanf("%63s", tok) == 1) {
        int code = -1;
        if (strcmp(tok, "up") == 0) code = KEY_UP;
        else if (strcmp(tok, "down") == 0) code = KEY_DOWN;
        else if (strcmp(tok, "left") == 0) code = KEY_LEFT;
        else if (strcmp(tok, "right") == 0) code = KEY_RIGHT;
        else if (strcmp(tok, "ok") == 0) code = KEY_OK;
        else if (strcmp(tok, "back") == 0) code = KEY_BACK;
        else if (strcmp(tok, "red") == 0) code = KEY_RED;
        else if (strcmp(tok, "green") == 0) code = KEY_GREEN;
        else if (strcmp(tok, "yellow") == 0) code = KEY_YELLOW;
        else if (strcmp(tok, "tick") == 0) { tick(); printf(">> tick (need_load=%d)\n%s\n----\n", g_need_load, slurp(OVL_PATH, 16384)); continue; }
        else if (strcmp(tok, "esc") == 0) code = KEY_ESC;
        else if (strcmp(tok, "blue") == 0) code = KEY_BLUE;
        else if (strcmp(tok, "f1") == 0) code = KEY_F1;
        else if (strcmp(tok, "f2") == 0) code = KEY_F2;
        else if (strcmp(tok, "f3") == 0) code = KEY_F3;
        else if (strcmp(tok, "f4") == 0) code = KEY_F4;
        if (code < 0) continue;
        handle_key(code, 1, &down, &t0);
        handle_key(code, 0, &down, &t0);
        printf(">> %s   (open=%d sel=%d half=%d play=%d)\n%s\n----\n", tok, g_menu_open, g_sel, g_half, g_play,
               g_menu_open ? slurp(OVL_PATH, 16384) : "[closed]");
    }
    return 0;
}

int main(int argc, char **argv) {
    if (argc > 1 && strcmp(argv[1], "--sim") == 0) return sim_main();
    if (argc > 2 && strcmp(argv[1], "--find") == 0) { printf("%d\n", proc_find(argv[2], argc > 3 ? argv[3] : NULL)); return 0; }
    signal(SIGTERM, on_signal);
    signal(SIGINT, on_signal);
    mkdir(DATA_DIR, 0755);
    if (!single_instance()) return 0;
    load_config();
    load_delays();
    logmsg("IPAudio " VERSION " start (panel opens only on a long press of the open key)");
    ensure_autorun();
    open_inputs();
    input_loop();
    hud_stop();
    logmsg("IPAudio exit");
    return 0;
}
