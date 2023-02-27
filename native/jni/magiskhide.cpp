#include <unistd.h>
#include <fcntl.h>
#include <signal.h>
#include <pthread.h>
#include <sys/ptrace.h>
#include <sys/inotify.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <sys/mount.h>
#include <vector>
#include <bitset>
#include <sys/syscall.h>
#include <sys/stat.h>
#include <sys/poll.h>
#include <dirent.h>
#include <map>
#include <dirent.h>

#include "utils.hpp"
#include "magiskhide_util.hpp"
#include "logging.hpp"

using namespace std;

static int inotify_fd = -1;

static void new_zygote(int pid);

std::map<int, std::vector<std::string>> uid_proc_map;

pthread_t monitor_thread;

static int fork_pid = -1;
static int system_server_pid = -1;
static bool is_process(int pid);

#include "procfp.hpp"

/******************
 * Data structures
 ******************/

#define PID_MAX 32768
struct pid_set {
    bitset<PID_MAX>::const_reference operator[](size_t pos) const { return set[pos - 1]; }
    bitset<PID_MAX>::reference operator[](size_t pos) { return set[pos - 1]; }
    void reset() { set.reset(); }
private:
    bitset<PID_MAX> set;
};

// true if pid is monitored
static pid_set attaches;

// zygote pid -> mnt ns
static map<int, struct stat> zygote_map;

// handle list
static vector<int> pid_list;

// process stat
static map<int, struct stat> pid_map;

/********
 * Utils
 ********/

static void kill_usap_zygote() {
    crawl_procfs([=](int pid) -> bool {
        char path[128];
        char cmdline[1024];
        snprintf(path, 127, "/proc/%d/cmdline", pid);
        FILE *fp = fopen(path, "re");
        if (fp == nullptr)
            return true;
        fgets(cmdline, sizeof(cmdline), fp);
        fclose(fp);
        if (strcmp(cmdline, "usap32") == 0 || strcmp(cmdline, "usap64") == 0) {
            LOGD("proc_monitor: kill PID=[%d] (%s)\n", pid, cmdline);
            kill(pid, SIGKILL);
        }
        return true;
    });
}
 
static void update_uid_map() {
    const char *APP_DATA = "/data/user_de";
    DIR *dirfp = opendir(APP_DATA);
    if (dirfp == nullptr) {
        APP_DATA = "/data/user";
        dirfp = opendir(APP_DATA);
    }
    if (dirfp == nullptr)
        return;
    LOGI("hide: rescanning apps\n");
    struct dirent *_data *dp;
    struct stat st;
    char buf[4098];
    // for each user
    while ((_data = readdir(dirfp)) != nullptr) {
        snprintf(buf, sizeof(buf) - 1, "%s/%s", APP_DATA, _data->d_name);
        if (strcmp(_data->d_name, ".") == 0 || strcmp(_data->d_name, "..") == 0 ||
            stat(buf, &st) != 0 || !S_ISDIR(st.st_mode))
            continue;
        DIR *dirfp2 = opendir(APP_DATA);
        if (dirfp2 == nullptr) continue;
        // for each package
        while ((dp = readdir(dirfp)) != nullptr) {
            snprintf(buf, sizeof(buf) - 1, "%s/%s/%s", APP_DATA, _data->d_name, dp->d_name);
            if (strcmp(dp->d_name, ".") == 0 || strcmp(dp->d_name, "..") == 0 ||
                stat(buf, &st) != 0 || !S_ISDIR(st.st_mode))
                continue;
            auto it = uid_proc_map.find(st.st_uid % 100000);
            if (it == uid_proc_map.end()) {
                std::vector<std::string> init;
                init.emplace_back(std::string(dp->d_name));
                uid_proc_map[st.st_uid] = init;
                LOGV("proc_monitor: add map uid=[%d] [%s]\n", st.st_uid % 100000, dp->d_name);
            } else {
                bool found = false;
                for (int i = 0; i < it->second.size(); i++) {
                    if (it->second[i] == std::string(dp->d_name)) {
                        found = true;
                        break;
                    }
                }
                if (!found) { 
                    it->second.emplace_back(std::string(dp->d_name));
                    LOGV("proc_monitor: update map uid=[%d] [%s]\n", st.st_uid % 100000, dp->d_name);
                }
            }
        }
        closedir(dirfp2);
    }
    closedir(dirfp);    
}

static inline int read_ns(const int pid, struct stat *st) {
    char path[32];
    sprintf(path, "/proc/%d/ns/mnt", pid);
    return stat(path, st);
}

static bool is_proc_alive(int pid) {
    auto it = pid_map.find(pid);
    char path[128];
    struct stat st;
    sprintf(path, "/proc/%d", pid);
    if (stat(path, &st))
        return false;
    if (it != pid_map.end() &&
        it->second.st_dev == st.st_dev &&
        it->second.st_ino == st.st_ino)
        return true;
    return false;
}

static bool is_zygote_done() {
    return zygote_map.size() >= 1;
}

static inline bool read_file(const char *file, char *buf, int count){
    FILE *fp = fopen(file, "re");
    if (!fp) return false;
    fread(buf, count, 1, fp);
    fclose(fp);
    return true;
}

static bool check_process(int pid, const char *process, const char *context, const char *exe) {
    char path[128];
    char buf[1024];
    ssize_t len;

    if (!process) goto check_context;
    sprintf(path, "/proc/%d/cmdline", pid);
    if (!read_file(path,buf,sizeof(buf)) ||
        strcmp(buf, process) != 0)
        return false;

    check_context:
    if (!context) goto check_exe;
    sprintf(path, "/proc/%d/attr/current", pid);
    if (!read_file(path,buf,sizeof(buf)) || 
        !strstr(buf, context))
        return false;
    
    check_exe:
    if (!exe) goto final;
    sprintf(path, "/proc/%d/exe", pid);
    len = readlink(path, buf, sizeof(buf)-1);
    if (len != -1) {
      buf[len] = '\0';
    }
    if (strcmp(buf, exe) != 0)
        return false;

    final:
    return true;
}

static bool check_process2(int pid, const char *process, const char *context, const char *exe) {
    return check_process(pid, process, (access("/sys/fs/selinux", F_OK) == 0)? context : nullptr, exe);
}

static bool is_zygote(int pid){
    return (check_process(pid, nullptr, nullptr, "/system/bin/app_process")
            || check_process(pid,  nullptr, nullptr, "/system/bin/app_process32")
            || check_process(pid, nullptr, nullptr, "/system/bin/app_process64"))
            && (check_process2(pid, "zygote", "u:r:zygote:s0", nullptr)  
            || check_process2(pid, "zygote64", "u:r:zygote:s0", nullptr)
            || check_process2(pid, "zygote32", "u:r:zygote:s0", nullptr));
}

static bool check_map(int pid) {
    auto it = pid_map.find(pid);
    char path[128];
    struct stat st;
    sprintf(path, "/proc/%d", pid);
    if (stat(path, &st))
        return false;
    if (it != pid_map.end()) {
        if (it->second.st_dev == st.st_dev &&
            it->second.st_ino == st.st_ino)
            return false;
        it->second = st;
    } else {
        pid_map[pid] = st;
    }
    return true;
}

static void check_zygote() {
    crawl_procfs([](int pid) -> bool {
        if (!is_process(pid))
            goto not_zygote;

        if (is_zygote(pid) && parse_ppid(pid) == 1 && system_server_pid > 0) {
            new_zygote(pid);
            return true;
        }
        if (check_process2(pid, "system_server", "u:r:system_server:s0", nullptr)
            && is_zygote(parse_ppid(pid)) && check_map(pid)) {
            system_server_pid = pid;
        }

        not_zygote:
        zygote_map.erase(pid);
        return true;
    });
    if (is_zygote_done()) {
        // Stop periodic scanning
        timeval val { .tv_sec = 0, .tv_usec = 0 };
        itimerval interval { .it_interval = val, .it_value = val };
        setitimer(ITIMER_REAL, &interval, nullptr);
    }
}

#define APP_PROC "/system/bin/app_process"

static void setup_inotify() {
    inotify_fd = xinotify_init1(IN_CLOEXEC);
    if (inotify_fd < 0)
        return;

    // Setup inotify asynchronous I/O
    fcntl(inotify_fd, F_SETFL, O_ASYNC);
    struct f_owner_ex ex = {
        .type = F_OWNER_TID,
        .pid = gettid()
    };
    fcntl(inotify_fd, F_SETOWN_EX, &ex);

    // Monitor packages.xml
    inotify_add_watch(inotify_fd, "/data/system", IN_CLOSE_WRITE);

    // Monitor app installation
    inotify_add_watch(inotify_fd, APP_DATA_DIR, IN_CREATE);
    DIR *dirfp = opendir(APP_DATA_DIR);
    if (dirfp) {
   	    char buf[4098];
        struct dirent *dp;
        while ((dp = readdir(dirfp)) != nullptr) {
            ssprintf(buf, sizeof(buf) - 1, "%s/%s", APP_DATA_DIR, dp->d_name);
            if (strcmp(dp->d_name, ".") == 0 || strcmp(dp->d_name, "..") == 0)
                continue;
            LOGD("proc_monitor: monitor userspace ID=[%s]\n", dp->d_name);
            inotify_add_watch(inotify_fd, buf, IN_ATTRIB);
        }
        closedir(dirfp);
    }

    // Monitor app_process
    if (access(APP_PROC "32", F_OK) == 0) {
        inotify_add_watch(inotify_fd, APP_PROC "32", IN_ACCESS);
        if (access(APP_PROC "64", F_OK) == 0)
            inotify_add_watch(inotify_fd, APP_PROC "64", IN_ACCESS);
    } else {
        inotify_add_watch(inotify_fd, APP_PROC, IN_ACCESS);
    }
}

/************************
 * Async signal handlers
 ************************/

static void inotify_event(int) {
    // Make sure we can actually read stuffs
    // or else the whole thread will be blocked.
    struct pollfd pfd = {
        .fd = inotify_fd,
        .events = POLLIN,
        .revents = 0
    };
    if (poll(&pfd, 1, 0) <= 0)
        return;  // Nothing to read
    char buf[512];
    auto event = reinterpret_cast<struct inotify_event *>(buf);
    read(inotify_fd, buf, sizeof(buf));
    if (event->mask & IN_CREATE) {
        std::string path = std::string(APP_DATA_DIR) + "/" + event->name;
        LOGD("proc_monitor: monitor userspace ID=[%s]\n", event->name);
        inotify_add_watch(inotify_fd, path.data(), IN_ATTRIB);
        return;
    }
    if ((event->mask & IN_CLOSE_WRITE) && strcmp(event->name, "packages.xml") == 0)
        new_daemon_thread(&update_uid_map);
    check_zygote();
}

//UNUSED FUNCTION
static void term_thread(int) {
    LOGD("proc_monitor: cleaning up\n");
    zygote_map.clear();
    pid_map.clear();
    attaches.reset();
    close(inotify_fd);
    inotify_fd = -1;
    fork_pid = -1;
    system_server_pid = -1;
    for (int i = 0; i < pid_list.size(); i++) {
        LOGD("proc_monitor: kill PID=[%d]\n", pid_list[i]);
        kill(pid_list[i], SIGKILL);
    }
    pid_list.clear();
    // Restore all signal handlers that was set
    sigset_t set;
    sigfillset(&set);
    pthread_sigmask(SIG_BLOCK, &set, nullptr);
    struct sigaction act{};
    act.sa_handler = SIG_DFL;
    sigaction(SIGTERMTHRD, &act, nullptr);
    sigaction(SIGIO, &act, nullptr);
    sigaction(SIGALRM, &act, nullptr);
    LOGD("proc_monitor: terminate\n");
    pthread_exit(nullptr);
}

/******************
 * Ptrace Madness
 ******************/

// Ptrace is super tricky, preserve all excessive logging in code
// but disable when actually building for usage (you won't want
// your logcat spammed with new thread events from all apps)

#ifdef DEBUG
#define PTRACE_LOG(fmt, args...) if (trace_log) LOGD("PID=[%d] " fmt, pid, ##args);
#else
#define PTRACE_LOG(...)
#endif

static void detach_pid(int pid, int signal = 0) {
    attaches[pid] = false;
    ptrace(PTRACE_DETACH, pid, 0, signal);
    PTRACE_LOG("detach\n");
}

static bool check_pid(int pid) {
    char path[128];
    char cmdline[1024];
    struct stat st;

    sprintf(path, "/proc/%d", pid);
    if (stat(path, &st)) {
        // Process died unexpectedly, ignore
        detach_pid(pid);
        return true;
    }

    int uid = st.st_uid;

    // UID hasn't changed
    if (uid == 0)
        return false;

    sprintf(path, "/proc/%d/cmdline", pid);
    if (auto f = fopen(path, "re")) {
        fgets(cmdline, sizeof(cmdline), f);
        fclose(f);
    } else {
        // Process died unexpectedly, ignore
        detach_pid(pid);
        return true;
    }

    if (cmdline == "zygote"sv || cmdline == "zygote32"sv || cmdline == "zygote64"sv ||
        cmdline == "usap32"sv || cmdline == "usap64"sv || cmdline == "<pre-initialized>"sv)
        return false;

    PTRACE_LOG("cmdline=[%s]\n", cmdline);

    if (!is_hide_target(uid, cmdline, 95))
        goto not_target;

    // Ensure ns is separated
    read_ns(pid, &st);
    for (auto &zit : zygote_map) {
        if (zit.second.st_ino == st.st_ino &&
            zit.second.st_dev == st.st_dev) {
            // ns not separated, abort
            LOGW("proc_monitor: skip [%s] PID=[%d] UID=[%d]\n", cmdline, pid, uid);
            goto not_target;
        }
    }

    // Detach but the process should still remain stopped
    // The hide daemon will resume the process after hiding it
    LOGI("proc_monitor: [%s] PID=[%d] UID=[%d]\n", cmdline, pid, uid);
    detach_pid(pid);
    kill(pid, SIGSTOP);
    hide_daemon(pid);
    return true;

not_target:
    PTRACE_LOG("[%s] is not our target\n", cmdline);
    detach_pid(pid);
    return true;
}

static bool is_process(int pid) {
    char buf[128];
    char key[32];
    int tgid;
    sprintf(buf, "/proc/%d/status", pid);
    auto fp = fopen(buf, "re");
    // PID is dead
    if (!fp)
        return false;
    while (fgets(buf, sizeof(buf), fp)) {
        sscanf(buf, "%s", key);
        if (key == "Tgid:"sv) {
            sscanf(buf, "%*s %d", &tgid);
            fclose(fp);
            return tgid == pid;
        }
    }
    fclose(fp);
    return false;
}

static void new_zygote(int pid) {
    struct stat st;
    if (read_ns(pid, &st))
        return;

    auto it = zygote_map.find(pid);
    if (it != zygote_map.end()) {
        // Update namespace info
        it->second = st;
        return;
    }

    if (!check_map(pid))
        return;

    LOGD("proc_monitor: zygote PID=[%d]\n", pid);
    zygote_map[pid] = st;

    LOGD("proc_monitor: ptrace zygote PID=[%d]\n", pid);
    xptrace(PTRACE_ATTACH, pid);

    waitpid(pid, nullptr, __WALL | __WNOTHREAD);
    xptrace(PTRACE_SETOPTIONS, pid, nullptr,
            PTRACE_O_TRACEFORK | PTRACE_O_TRACEVFORK | PTRACE_O_TRACEEXIT);
    xptrace(PTRACE_CONT, pid);
}

#define DETACH_AND_CONT { detach_pid(pid); continue; }

int wait_for_syscall(pid_t pid) {
    int status;
    while (1) {
        ptrace(PTRACE_SYSCALL, pid, 0, 0);
        //PTRACE_LOG("wait for syscall\n");
        int child = waitpid(pid, &status, 0);
        if (child < 0)
            return 1;
        if (WIFSTOPPED(status) && WSTOPSIG(status) & 0x80) {
            //PTRACE_LOG("make a syscall\n");
            return 0;
        }
        if (WIFSTOPPED(status) && WSTOPSIG(status) == SIGSEGV) {
            // google chrome?
            PTRACE_LOG("SIGSEGV from child\n");
            return 1;
        }
        if (WIFEXITED(status)) {
            PTRACE_LOG("exited\n");
            return 1;
        }
    }
}

static std::string get_content(int pid, const char *file) {
    char buf[1024];
    sprintf(buf, "/proc/%d/%s", pid, file);
    FILE *fp = fopen(buf, "re");
    if (fp) {
        fgets(buf, sizeof(buf), fp);
        fclose(fp);
        return std::string(buf);
    }
    return std::string("");
}

void do_check_fork() {
    int pid = fork_pid;
    fork_pid = 0;
    if (pid <= 0)
        return;
    // wait until thread detach this pid
    for (int i = 0; i < 10000 && ptrace(PTRACE_ATTACH, pid) < 0; i++)
        usleep(100);
    PTRACE_LOG("pass to thread\n");
    bool allow = false;
    bool checked = false;
    pid_list.emplace_back(pid);
    waitpid(pid, 0, 0);
    xptrace(PTRACE_SETOPTIONS, pid, nullptr, PTRACE_O_TRACESYSGOOD);
    struct stat st{};
    char path[128];
    for (int syscall_num = -1;;) {
        if (wait_for_syscall(pid) != 0)
            break;
        {
            if (checked) goto CHECK_PROC;
            sprintf(path, "/proc/%d", pid);
            stat(path, &st);
            PTRACE_LOG("UID=[%d]\n", st.st_uid);
            if (st.st_uid == 0)
                continue;
            if ((st.st_uid % 100000) >= 90000) {
                PTRACE_LOG("is isolated process\n");
                goto CHECK_PROC;
            }
            // check if UID is on list
            {
                bool found = false;
                auto it = uid_proc_map.find(st.st_uid % 100000);
                // not found in map
                if (it == uid_proc_map.end())
                    break;
                for (int i = 0; i < it->second.size(); i++) {
                    if (find_proc_from_pkg(it->second[i].data(), it->second[i].data(), true)) {
                        found = true;
                        break;
                    }
                }
                // not found in database
                if (!found) break;
            }

            CHECK_PROC:
            checked = true;
            if (!allow && (
                 // app zygote
                 strstr(get_content(pid, "attr/current").data(), "u:r:app_zygote:s0") ||
                 // until pre-initialized
                 get_content(pid, "cmdline") == "<pre-initialized>"))
                 allow = true;
            if (allow && check_pid(pid))
                break;
        }
    }
    // just in case
    PTRACE_LOG("detach\n");
    ptrace(PTRACE_DETACH, pid);
    auto it = find(pid_list.begin(), pid_list.end(), pid);
    if (it != pid_list.end())
        pid_list.erase(it);
}

void proc_monitor() {
    monitor_thread = pthread_self();

    // Backup original mask
    sigset_t orig_mask;
    pthread_sigmask(SIG_SETMASK, nullptr, &orig_mask);

    sigset_t unblock_set;
    sigemptyset(&unblock_set);
    sigaddset(&unblock_set, SIGTERMTHRD);
    sigaddset(&unblock_set, SIGIO);
    sigaddset(&unblock_set, SIGALRM);

    struct sigaction act{};
    sigfillset(&act.sa_mask);
    act.sa_handler = SIG_IGN;
    sigaction(SIGTERMTHRD, &act, nullptr);
    sigaction(SIGIO, &act, nullptr);
    sigaction(SIGALRM, &act, nullptr);

    // Temporary unblock to clear pending signals
    pthread_sigmask(SIG_UNBLOCK, &unblock_set, nullptr);
    pthread_sigmask(SIG_SETMASK, &orig_mask, nullptr);

    act.sa_handler = term_thread;
    sigaction(SIGTERMTHRD, &act, nullptr);
    act.sa_handler = inotify_event;
    sigaction(SIGIO, &act, nullptr);
    act.sa_handler = [](int){ check_zygote(); };
    sigaction(SIGALRM, &act, nullptr);

    zygote_map.clear();
    pid_map.clear();
    setup_inotify();
    attaches.reset();

    // First try find existing system server
    check_zygote();

    start_monitor:
    pthread_sigmask(SIG_UNBLOCK, &unblock_set, nullptr);
    // wait until system_server start
    while (system_server_pid == -1)
        sleep(1);
    if (!is_proc_alive(system_server_pid)) {
        system_server_pid = -1;
        pid_map.clear();
        goto start_monitor;
    }
    // now ptrace zygote
    LOGI("proc_monitor: system server PID=[%d]\n", system_server_pid);
    pthread_sigmask(SIG_SETMASK, &orig_mask, nullptr);
    // First try find existing zygotes
    check_zygote();
    if (!is_zygote_done()) {
        // Periodic scan every 250ms
        timeval val { .tv_sec = 0, .tv_usec = 250000 };
        itimerval interval { .it_interval = val, .it_value = val };
        setitimer(ITIMER_REAL, &interval, nullptr);
    }
    update_uid_map();
    kill_usap_zygote();

    for (int status;;) {
        pthread_sigmask(SIG_UNBLOCK, &unblock_set, nullptr);

        const int pid = waitpid(-1, &status, __WALL | __WNOTHREAD);
        if (pid < 0) {
            if (errno == ECHILD) {
                // Nothing to wait yet, sleep and wait till signal interruption
                LOGD("proc_monitor: nothing to monitor, wait for signal\n");
                struct timespec ts = {
                    .tv_sec = INT_MAX,
                    .tv_nsec = 0
                };
                nanosleep(&ts, nullptr);
                goto start_monitor;
            }
            continue;
        }

        pthread_sigmask(SIG_SETMASK, &orig_mask, nullptr);

        if (!WIFSTOPPED(status) /* Ignore if not ptrace-stop */)
            DETACH_AND_CONT;

        int event = WEVENT(status);
        int signal = WSTOPSIG(status);

        if (signal == SIGTRAP && event) {
            unsigned long msg;
            xptrace(PTRACE_GETEVENTMSG, pid, nullptr, &msg);
            if (zygote_map.count(pid)) {
                // Zygote event
                switch (event) {
                    case PTRACE_EVENT_FORK:
                    case PTRACE_EVENT_VFORK:
                        PTRACE_LOG("zygote forked: [%lu]\n", msg);
                        attaches[msg] = true;
                        break;
                    case PTRACE_EVENT_EXIT:
                        PTRACE_LOG("zygote exited with status: [%lu]\n", msg);
                        [[fallthrough]];
                    default:
                        zygote_map.erase(pid);
                        DETACH_AND_CONT;
                }
            } else {
                DETACH_AND_CONT;
            }
            xptrace(PTRACE_CONT, pid);
        } else if (signal == SIGSTOP) {
            if (!attaches[pid]) {
                // Double check if this is actually a process
                attaches[pid] = is_process(pid);
            }
            if (attaches[pid]) {
                // This is a process, continue monitoring
                attaches[pid] = false;
                detach_pid(pid);
                fork_pid = pid;
                new_daemon_thread(&do_check_fork);
            } else {
                // This is a thread, do NOT monitor
                PTRACE_LOG("SIGSTOP from thread\n");
                DETACH_AND_CONT;
            }
        } else {
            // Not caused by us, resend signal
            xptrace(PTRACE_CONT, pid, nullptr, signal);
            PTRACE_LOG("signal [%d]\n", signal);
        }
    }
}
