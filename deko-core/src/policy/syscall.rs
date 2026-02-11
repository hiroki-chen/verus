#![allow(non_upper_case_globals)]

use deko_macros::with_atomic_pred;
use deko_std::deko_rwlock_write_atomic_data;
use deko_std::mem::PAGE_SIZE;
use deko_std::prelude::collections::hashmap::HashMap;
use deko_std::prelude::{PhysAddr, VirtAddr, VADDR_UPPER_MASK};
use deko_std::std_extra::allocator::AllocatorWrapper;
use deko_std::sync::DekoOnceCell;
use deko_std::wf::WellFormed;
use vstd::prelude::*;

use crate::guest::{DekoGuestServError, DekoGuestServResult, DekoGuestServResultCode};
use crate::mm::frame_allocator::DekoAllocatorApi;
use crate::policy::userapp::{copy_from_user, is_docker_request, IS_DOCKER_RUNNING};
// use crate::policy::userapp::copy_from_guest_user;
use crate::policy::DekoSyscallBody;
use crate::{die, kdebug, kerror, kinfo, ktrace, kwarn, vec};

verus! {

type DekoSyscall = VirtAddr;

with_atomic_pred!(
    DekoSyscall,
    (),
    fields: { },
    perm_fields: { },
    data.wf() && data.view() >= VADDR_UPPER_MASK // No need to make it page-aligned.
);

pub exec static DEKO_VMPL1_SYSCALL_TRAMPOLINE: DekoOnceCell<VirtAddr, (), DekoSyscallPred>
    ensures
        DEKO_VMPL1_SYSCALL_TRAMPOLINE.wf(),
{
    DekoOnceCell::new(Ghost(DekoSyscallPred {  }))
}

/// The names of syscalls indexed by their syscall numbers.
///
/// https://codeberg.org/koutheir/syscall-numbers/src/branch/main/src/x86_64.rs
pub(crate) exec static SYS_CALL_NAME: &'static [&'static str] = &[
    "read",
    "write",
    "open",
    "close",
    "stat",
    "fstat",
    "lstat",
    "poll",
    "lseek",
    "mmap",
    "mprotect",
    "munmap",
    "brk",
    "rt_sigaction",
    "rt_sigprocmask",
    "rt_sigreturn",
    "ioctl",
    "pread64",
    "pwrite64",
    "readv",
    "writev",
    "access",
    "pipe",
    "select",
    "sched_yield",
    "mremap",
    "msync",
    "mincore",
    "madvise",
    "shmget",
    "shmat",
    "shmctl",
    "dup",
    "dup2",
    "pause",
    "nanosleep",
    "getitimer",
    "alarm",
    "setitimer",
    "getpid",
    "sendfile",
    "socket",
    "connect",
    "accept",
    "sendto",
    "recvfrom",
    "sendmsg",
    "recvmsg",
    "shutdown",
    "bind",
    "listen",
    "getsockname",
    "getpeername",
    "socketpair",
    "setsockopt",
    "getsockopt",
    "clone",
    "fork",
    "vfork",
    "execve",
    "exit",
    "wait4",
    "kill",
    "uname",
    "semget",
    "semop",
    "semctl",
    "shmdt",
    "msgget",
    "msgsnd",
    "msgrcv",
    "msgctl",
    "fcntl",
    "flock",
    "fsync",
    "fdatasync",
    "truncate",
    "ftruncate",
    "getdents",
    "getcwd",
    "chdir",
    "fchdir",
    "rename",
    "mkdir",
    "rmdir",
    "creat",
    "link",
    "unlink",
    "symlink",
    "readlink",
    "chmod",
    "fchmod",
    "chown",
    "fchown",
    "lchown",
    "umask",
    "gettimeofday",
    "getrlimit",
    "getrusage",
    "sysinfo",
    "times",
    "ptrace",
    "getuid",
    "syslog",
    "getgid",
    "setuid",
    "setgid",
    "geteuid",
    "getegid",
    "setpgid",
    "getppid",
    "getpgrp",
    "setsid",
    "setreuid",
    "setregid",
    "getgroups",
    "setgroups",
    "setresuid",
    "getresuid",
    "setresgid",
    "getresgid",
    "getpgid",
    "setfsuid",
    "setfsgid",
    "getsid",
    "capget",
    "capset",
    "rt_sigpending",
    "rt_sigtimedwait",
    "rt_sigqueueinfo",
    "rt_sigsuspend",
    "sigaltstack",
    "utime",
    "mknod",
    "uselib",
    "personality",
    "ustat",
    "statfs",
    "fstatfs",
    "sysfs",
    "getpriority",
    "setpriority",
    "sched_setparam",
    "sched_getparam",
    "sched_setscheduler",
    "sched_getscheduler",
    "sched_get_priority_max",
    "sched_get_priority_min",
    "sched_rr_get_interval",
    "mlock",
    "munlock",
    "mlockall",
    "munlockall",
    "vhangup",
    "modify_ldt",
    "pivot_root",
    "_sysctl",
    "prctl",
    "arch_prctl",
    "adjtimex",
    "setrlimit",
    "chroot",
    "sync",
    "acct",
    "settimeofday",
    "mount",
    "umount2",
    "swapon",
    "swapoff",
    "reboot",
    "sethostname",
    "setdomainname",
    "iopl",
    "ioperm",
    "create_module",
    "init_module",
    "delete_module",
    "get_kernel_syms",
    "query_module",
    "quotactl",
    "nfsservctl",
    "getpmsg",
    "putpmsg",
    "afs_syscall",
    "tuxcall",
    "security",
    "gettid",
    "readahead",
    "setxattr",
    "lsetxattr",
    "fsetxattr",
    "getxattr",
    "lgetxattr",
    "fgetxattr",
    "listxattr",
    "llistxattr",
    "flistxattr",
    "removexattr",
    "lremovexattr",
    "fremovexattr",
    "tkill",
    "time",
    "futex",
    "sched_setaffinity",
    "sched_getaffinity",
    "set_thread_area",
    "io_setup",
    "io_destroy",
    "io_getevents",
    "io_submit",
    "io_cancel",
    "get_thread_area",
    "lookup_dcookie",
    "epoll_create",
    "epoll_ctl_old",
    "epoll_wait_old",
    "remap_file_pages",
    "getdents64",
    "set_tid_address",
    "restart_syscall",
    "semtimedop",
    "fadvise64",
    "timer_create",
    "timer_settime",
    "timer_gettime",
    "timer_getoverrun",
    "timer_delete",
    "clock_settime",
    "clock_gettime",
    "clock_getres",
    "clock_nanosleep",
    "exit_group",
    "epoll_wait",
    "epoll_ctl",
    "tgkill",
    "utimes",
    "vserver",
    "mbind",
    "set_mempolicy",
    "get_mempolicy",
    "mq_open",
    "mq_unlink",
    "mq_timedsend",
    "mq_timedreceive",
    "mq_notify",
    "mq_getsetattr",
    "kexec_load",
    "waitid",
    "add_key",
    "request_key",
    "keyctl",
    "ioprio_set",
    "ioprio_get",
    "inotify_init",
    "inotify_add_watch",
    "inotify_rm_watch",
    "migrate_pages",
    "openat",
    "mkdirat",
    "mknodat",
    "fchownat",
    "futimesat",
    "newfstatat",
    "unlinkat",
    "renameat",
    "linkat",
    "symlinkat",
    "readlinkat",
    "fchmodat",
    "faccessat",
    "pselect6",
    "ppoll",
    "unshare",
    "set_robust_list",
    "get_robust_list",
    "splice",
    "tee",
    "sync_file_range",
    "vmsplice",
    "move_pages",
    "utimensat",
    "epoll_pwait",
    "signalfd",
    "timerfd_create",
    "eventfd",
    "fallocate",
    "timerfd_settime",
    "timerfd_gettime",
    "accept4",
    "signalfd4",
    "eventfd2",
    "epoll_create1",
    "dup3",
    "pipe2",
    "inotify_init1",
    "preadv",
    "pwritev",
    "rt_tgsigqueueinfo",
    "perf_event_open",
    "recvmmsg",
    "fanotify_init",
    "fanotify_mark",
    "prlimit64",
    "name_to_handle_at",
    "open_by_handle_at",
    "clock_adjtime",
    "syncfs",
    "sendmmsg",
    "setns",
    "getcpu",
    "process_vm_readv",
    "process_vm_writev",
    "kcmp",
    "finit_module",
    "sched_setattr",
    "sched_getattr",
    "renameat2",
    "seccomp",
    "getrandom",
    "memfd_create",
    "kexec_file_load",
    "bpf",
    "execveat",
    "userfaultfd",
    "membarrier",
    "mlock2",
    "copy_file_range",
    "preadv2",
    "pwritev2",
    "pkey_mprotect",
    "pkey_alloc",
    "pkey_free",
    "statx",
    "io_pgetevents",
    "rseq",
    "",
    "",
    "",
    "",
    "",
    "",
    "",
    "",
    "",
    "",
    "",
    "",
    "",
    "",
    "",
    "",
    "",
    "",
    "",
    "",
    "",
    "",
    "",
    "",
    "",
    "",
    "",
    "",
    "",
    "",
    "",
    "",
    "",
    "",
    "",
    "",
    "",
    "",
    "",
    "",
    "",
    "",
    "",
    "",
    "",
    "",
    "",
    "",
    "",
    "",
    "",
    "",
    "",
    "",
    "",
    "",
    "",
    "",
    "",
    "",
    "",
    "",
    "",
    "",
    "",
    "",
    "",
    "",
    "",
    "",
    "",
    "",
    "",
    "",
    "",
    "",
    "",
    "",
    "",
    "",
    "",
    "",
    "",
    "",
    "",
    "",
    "",
    "",
    "",
    "pidfd_send_signal",
    "io_uring_setup",
    "io_uring_enter",
    "io_uring_register",
    "open_tree",
    "move_mount",
    "fsopen",
    "fsconfig",
    "fsmount",
    "fspick",
    "pidfd_open",
    "clone3",
    "close_range",
    "openat2",
    "pidfd_getfd",
    "faccessat2",
    "process_madvise",
    "epoll_pwait2",
    "mount_setattr",
    "",
    "landlock_create_ruleset",
    "landlock_add_rule",
    "landlock_restrict_self",
    "memfd_secret",
    "process_mrelease",
    "futex_waitv",
    "set_mempolicy_home_node",
    "cachestat",
    "fchmodat2",
];

pub const SYS_read: u64 = 0x0;

pub const SYS_write: u64 = 0x1;

pub const SYS_open: u64 = 0x2;

pub const SYS_close: u64 = 0x3;

pub const SYS_stat: u64 = 0x4;

pub const SYS_fstat: u64 = 0x5;

pub const SYS_lstat: u64 = 0x6;

pub const SYS_poll: u64 = 0x7;

pub const SYS_lseek: u64 = 0x8;

pub const SYS_mmap: u64 = 0x9;

pub const SYS_mprotect: u64 = 0xa;

pub const SYS_munmap: u64 = 0xb;

pub const SYS_brk: u64 = 0xc;

pub const SYS_rt_sigaction: u64 = 0xd;

pub const SYS_rt_sigprocmask: u64 = 0xe;

pub const SYS_rt_sigreturn: u64 = 0xf;

pub const SYS_ioctl: u64 = 0x10;

pub const SYS_pread64: u64 = 0x11;

pub const SYS_pwrite64: u64 = 0x12;

pub const SYS_readv: u64 = 0x13;

pub const SYS_writev: u64 = 0x14;

pub const SYS_access: u64 = 0x15;

pub const SYS_pipe: u64 = 0x16;

pub const SYS_select: u64 = 0x17;

pub const SYS_sched_yield: u64 = 0x18;

pub const SYS_mremap: u64 = 0x19;

pub const SYS_msync: u64 = 0x1a;

pub const SYS_mincore: u64 = 0x1b;

pub const SYS_madvise: u64 = 0x1c;

pub const SYS_shmget: u64 = 0x1d;

pub const SYS_shmat: u64 = 0x1e;

pub const SYS_shmctl: u64 = 0x1f;

pub const SYS_dup: u64 = 0x20;

pub const SYS_dup2: u64 = 0x21;

pub const SYS_pause: u64 = 0x22;

pub const SYS_nanosleep: u64 = 0x23;

pub const SYS_getitimer: u64 = 0x24;

pub const SYS_alarm: u64 = 0x25;

pub const SYS_setitimer: u64 = 0x26;

pub const SYS_getpid: u64 = 0x27;

pub const SYS_sendfile: u64 = 0x28;

pub const SYS_socket: u64 = 0x29;

pub const SYS_connect: u64 = 0x2a;

pub const SYS_accept: u64 = 0x2b;

pub const SYS_sendto: u64 = 0x2c;

pub const SYS_recvfrom: u64 = 0x2d;

pub const SYS_sendmsg: u64 = 0x2e;

pub const SYS_recvmsg: u64 = 0x2f;

pub const SYS_shutdown: u64 = 0x30;

pub const SYS_bind: u64 = 0x31;

pub const SYS_listen: u64 = 0x32;

pub const SYS_getsockname: u64 = 0x33;

pub const SYS_getpeername: u64 = 0x34;

pub const SYS_socketpair: u64 = 0x35;

pub const SYS_setsockopt: u64 = 0x36;

pub const SYS_getsockopt: u64 = 0x37;

pub const SYS_clone: u64 = 0x38;

pub const SYS_fork: u64 = 0x39;

pub const SYS_vfork: u64 = 0x3a;

pub const SYS_execve: u64 = 0x3b;

pub const SYS_exit: u64 = 0x3c;

pub const SYS_wait4: u64 = 0x3d;

pub const SYS_kill: u64 = 0x3e;

pub const SYS_uname: u64 = 0x3f;

pub const SYS_semget: u64 = 0x40;

pub const SYS_semop: u64 = 0x41;

pub const SYS_semctl: u64 = 0x42;

pub const SYS_shmdt: u64 = 0x43;

pub const SYS_msgget: u64 = 0x44;

pub const SYS_msgsnd: u64 = 0x45;

pub const SYS_msgrcv: u64 = 0x46;

pub const SYS_msgctl: u64 = 0x47;

pub const SYS_fcntl: u64 = 0x48;

pub const SYS_flock: u64 = 0x49;

pub const SYS_fsync: u64 = 0x4a;

pub const SYS_fdatasync: u64 = 0x4b;

pub const SYS_truncate: u64 = 0x4c;

pub const SYS_ftruncate: u64 = 0x4d;

pub const SYS_getdents: u64 = 0x4e;

pub const SYS_getcwd: u64 = 0x4f;

pub const SYS_chdir: u64 = 0x50;

pub const SYS_fchdir: u64 = 0x51;

pub const SYS_rename: u64 = 0x52;

pub const SYS_mkdir: u64 = 0x53;

pub const SYS_rmdir: u64 = 0x54;

pub const SYS_creat: u64 = 0x55;

pub const SYS_link: u64 = 0x56;

pub const SYS_unlink: u64 = 0x57;

pub const SYS_symlink: u64 = 0x58;

pub const SYS_readlink: u64 = 0x59;

pub const SYS_chmod: u64 = 0x5a;

pub const SYS_fchmod: u64 = 0x5b;

pub const SYS_chown: u64 = 0x5c;

pub const SYS_fchown: u64 = 0x5d;

pub const SYS_lchown: u64 = 0x5e;

pub const SYS_umask: u64 = 0x5f;

pub const SYS_gettimeofday: u64 = 0x60;

pub const SYS_getrlimit: u64 = 0x61;

pub const SYS_getrusage: u64 = 0x62;

pub const SYS_sysinfo: u64 = 0x63;

pub const SYS_times: u64 = 0x64;

pub const SYS_ptrace: u64 = 0x65;

pub const SYS_getuid: u64 = 0x66;

pub const SYS_syslog: u64 = 0x67;

pub const SYS_getgid: u64 = 0x68;

pub const SYS_setuid: u64 = 0x69;

pub const SYS_setgid: u64 = 0x6a;

pub const SYS_geteuid: u64 = 0x6b;

pub const SYS_getegid: u64 = 0x6c;

pub const SYS_setpgid: u64 = 0x6d;

pub const SYS_getppid: u64 = 0x6e;

pub const SYS_getpgrp: u64 = 0x6f;

pub const SYS_setsid: u64 = 0x70;

pub const SYS_setreuid: u64 = 0x71;

pub const SYS_setregid: u64 = 0x72;

pub const SYS_getgroups: u64 = 0x73;

pub const SYS_setgroups: u64 = 0x74;

pub const SYS_setresuid: u64 = 0x75;

pub const SYS_getresuid: u64 = 0x76;

pub const SYS_setresgid: u64 = 0x77;

pub const SYS_getresgid: u64 = 0x78;

pub const SYS_getpgid: u64 = 0x79;

pub const SYS_setfsuid: u64 = 0x7a;

pub const SYS_setfsgid: u64 = 0x7b;

pub const SYS_getsid: u64 = 0x7c;

pub const SYS_capget: u64 = 0x7d;

pub const SYS_capset: u64 = 0x7e;

pub const SYS_rt_sigpending: u64 = 0x7f;

pub const SYS_rt_sigtimedwait: u64 = 0x80;

pub const SYS_rt_sigqueueinfo: u64 = 0x81;

pub const SYS_rt_sigsuspend: u64 = 0x82;

pub const SYS_sigaltstack: u64 = 0x83;

pub const SYS_utime: u64 = 0x84;

pub const SYS_mknod: u64 = 0x85;

pub const SYS_uselib: u64 = 0x86;

pub const SYS_personality: u64 = 0x87;

pub const SYS_ustat: u64 = 0x88;

pub const SYS_statfs: u64 = 0x89;

pub const SYS_fstatfs: u64 = 0x8a;

pub const SYS_sysfs: u64 = 0x8b;

pub const SYS_getpriority: u64 = 0x8c;

pub const SYS_setpriority: u64 = 0x8d;

pub const SYS_sched_setparam: u64 = 0x8e;

pub const SYS_sched_getparam: u64 = 0x8f;

pub const SYS_sched_setscheduler: u64 = 0x90;

pub const SYS_sched_getscheduler: u64 = 0x91;

pub const SYS_sched_get_priority_max: u64 = 0x92;

pub const SYS_sched_get_priority_min: u64 = 0x93;

pub const SYS_sched_rr_get_interval: u64 = 0x94;

pub const SYS_mlock: u64 = 0x95;

pub const SYS_munlock: u64 = 0x96;

pub const SYS_mlockall: u64 = 0x97;

pub const SYS_munlockall: u64 = 0x98;

pub const SYS_vhangup: u64 = 0x99;

pub const SYS_modify_ldt: u64 = 0x9a;

pub const SYS_pivot_root: u64 = 0x9b;

pub const SYS__sysctl: u64 = 0x9c;

pub const SYS_prctl: u64 = 0x9d;

pub const SYS_arch_prctl: u64 = 0x9e;

pub const SYS_adjtimex: u64 = 0x9f;

pub const SYS_setrlimit: u64 = 0xa0;

pub const SYS_chroot: u64 = 0xa1;

pub const SYS_sync: u64 = 0xa2;

pub const SYS_acct: u64 = 0xa3;

pub const SYS_settimeofday: u64 = 0xa4;

pub const SYS_mount: u64 = 0xa5;

pub const SYS_umount2: u64 = 0xa6;

pub const SYS_swapon: u64 = 0xa7;

pub const SYS_swapoff: u64 = 0xa8;

pub const SYS_reboot: u64 = 0xa9;

pub const SYS_sethostname: u64 = 0xaa;

pub const SYS_setdomainname: u64 = 0xab;

pub const SYS_iopl: u64 = 0xac;

pub const SYS_ioperm: u64 = 0xad;

pub const SYS_create_module: u64 = 0xae;

pub const SYS_init_module: u64 = 0xaf;

pub const SYS_delete_module: u64 = 0xb0;

pub const SYS_get_kernel_syms: u64 = 0xb1;

pub const SYS_query_module: u64 = 0xb2;

pub const SYS_quotactl: u64 = 0xb3;

pub const SYS_nfsservctl: u64 = 0xb4;

pub const SYS_getpmsg: u64 = 0xb5;

pub const SYS_putpmsg: u64 = 0xb6;

pub const SYS_afs_syscall: u64 = 0xb7;

pub const SYS_tuxcall: u64 = 0xb8;

pub const SYS_security: u64 = 0xb9;

pub const SYS_gettid: u64 = 0xba;

pub const SYS_readahead: u64 = 0xbb;

pub const SYS_setxattr: u64 = 0xbc;

pub const SYS_lsetxattr: u64 = 0xbd;

pub const SYS_fsetxattr: u64 = 0xbe;

pub const SYS_getxattr: u64 = 0xbf;

pub const SYS_lgetxattr: u64 = 0xc0;

pub const SYS_fgetxattr: u64 = 0xc1;

pub const SYS_listxattr: u64 = 0xc2;

pub const SYS_llistxattr: u64 = 0xc3;

pub const SYS_flistxattr: u64 = 0xc4;

pub const SYS_removexattr: u64 = 0xc5;

pub const SYS_lremovexattr: u64 = 0xc6;

pub const SYS_fremovexattr: u64 = 0xc7;

pub const SYS_tkill: u64 = 0xc8;

pub const SYS_time: u64 = 0xc9;

pub const SYS_futex: u64 = 0xca;

pub const SYS_sched_setaffinity: u64 = 0xcb;

pub const SYS_sched_getaffinity: u64 = 0xcc;

pub const SYS_set_thread_area: u64 = 0xcd;

pub const SYS_io_setup: u64 = 0xce;

pub const SYS_io_destroy: u64 = 0xcf;

pub const SYS_io_getevents: u64 = 0xd0;

pub const SYS_io_submit: u64 = 0xd1;

pub const SYS_io_cancel: u64 = 0xd2;

pub const SYS_get_thread_area: u64 = 0xd3;

pub const SYS_lookup_dcookie: u64 = 0xd4;

pub const SYS_epoll_create: u64 = 0xd5;

pub const SYS_epoll_ctl_old: u64 = 0xd6;

pub const SYS_epoll_wait_old: u64 = 0xd7;

pub const SYS_remap_file_pages: u64 = 0xd8;

pub const SYS_getdents64: u64 = 0xd9;

pub const SYS_set_tid_address: u64 = 0xda;

pub const SYS_restart_syscall: u64 = 0xdb;

pub const SYS_semtimedop: u64 = 0xdc;

pub const SYS_fadvise64: u64 = 0xdd;

pub const SYS_timer_create: u64 = 0xde;

pub const SYS_timer_settime: u64 = 0xdf;

pub const SYS_timer_gettime: u64 = 0xe0;

pub const SYS_timer_getoverrun: u64 = 0xe1;

pub const SYS_timer_delete: u64 = 0xe2;

pub const SYS_clock_settime: u64 = 0xe3;

pub const SYS_clock_gettime: u64 = 0xe4;

pub const SYS_clock_getres: u64 = 0xe5;

pub const SYS_clock_nanosleep: u64 = 0xe6;

pub const SYS_exit_group: u64 = 0xe7;

pub const SYS_epoll_wait: u64 = 0xe8;

pub const SYS_epoll_ctl: u64 = 0xe9;

pub const SYS_tgkill: u64 = 0xea;

pub const SYS_utimes: u64 = 0xeb;

pub const SYS_vserver: u64 = 0xec;

pub const SYS_mbind: u64 = 0xed;

pub const SYS_set_mempolicy: u64 = 0xee;

pub const SYS_get_mempolicy: u64 = 0xef;

pub const SYS_mq_open: u64 = 0xf0;

pub const SYS_mq_unlink: u64 = 0xf1;

pub const SYS_mq_timedsend: u64 = 0xf2;

pub const SYS_mq_timedreceive: u64 = 0xf3;

pub const SYS_mq_notify: u64 = 0xf4;

pub const SYS_mq_getsetattr: u64 = 0xf5;

pub const SYS_kexec_load: u64 = 0xf6;

pub const SYS_waitid: u64 = 0xf7;

pub const SYS_add_key: u64 = 0xf8;

pub const SYS_request_key: u64 = 0xf9;

pub const SYS_keyctl: u64 = 0xfa;

pub const SYS_ioprio_set: u64 = 0xfb;

pub const SYS_ioprio_get: u64 = 0xfc;

pub const SYS_inotify_init: u64 = 0xfd;

pub const SYS_inotify_add_watch: u64 = 0xfe;

pub const SYS_inotify_rm_watch: u64 = 0xff;

pub const SYS_migrate_pages: u64 = 0x100;

pub const SYS_openat: u64 = 0x101;

pub const SYS_mkdirat: u64 = 0x102;

pub const SYS_mknodat: u64 = 0x103;

pub const SYS_fchownat: u64 = 0x104;

pub const SYS_futimesat: u64 = 0x105;

pub const SYS_newfstatat: u64 = 0x106;

pub const SYS_unlinkat: u64 = 0x107;

pub const SYS_renameat: u64 = 0x108;

pub const SYS_linkat: u64 = 0x109;

pub const SYS_symlinkat: u64 = 0x10a;

pub const SYS_readlinkat: u64 = 0x10b;

pub const SYS_fchmodat: u64 = 0x10c;

pub const SYS_faccessat: u64 = 0x10d;

pub const SYS_pselect6: u64 = 0x10e;

pub const SYS_ppoll: u64 = 0x10f;

pub const SYS_unshare: u64 = 0x110;

pub const SYS_set_robust_list: u64 = 0x111;

pub const SYS_get_robust_list: u64 = 0x112;

pub const SYS_splice: u64 = 0x113;

pub const SYS_tee: u64 = 0x114;

pub const SYS_sync_file_range: u64 = 0x115;

pub const SYS_vmsplice: u64 = 0x116;

pub const SYS_move_pages: u64 = 0x117;

pub const SYS_utimensat: u64 = 0x118;

pub const SYS_epoll_pwait: u64 = 0x119;

pub const SYS_signalfd: u64 = 0x11a;

pub const SYS_timerfd_create: u64 = 0x11b;

pub const SYS_eventfd: u64 = 0x11c;

pub const SYS_fallocate: u64 = 0x11d;

pub const SYS_timerfd_settime: u64 = 0x11e;

pub const SYS_timerfd_gettime: u64 = 0x11f;

pub const SYS_accept4: u64 = 0x120;

pub const SYS_signalfd4: u64 = 0x121;

pub const SYS_eventfd2: u64 = 0x122;

pub const SYS_epoll_create1: u64 = 0x123;

pub const SYS_dup3: u64 = 0x124;

pub const SYS_pipe2: u64 = 0x125;

pub const SYS_inotify_init1: u64 = 0x126;

pub const SYS_preadv: u64 = 0x127;

pub const SYS_pwritev: u64 = 0x128;

pub const SYS_rt_tgsigqueueinfo: u64 = 0x129;

pub const SYS_perf_event_open: u64 = 0x12a;

pub const SYS_recvmmsg: u64 = 0x12b;

pub const SYS_fanotify_init: u64 = 0x12c;

pub const SYS_fanotify_mark: u64 = 0x12d;

pub const SYS_prlimit64: u64 = 0x12e;

pub const SYS_name_to_handle_at: u64 = 0x12f;

pub const SYS_open_by_handle_at: u64 = 0x130;

pub const SYS_clock_adjtime: u64 = 0x131;

pub const SYS_syncfs: u64 = 0x132;

pub const SYS_sendmmsg: u64 = 0x133;

pub const SYS_setns: u64 = 0x134;

pub const SYS_getcpu: u64 = 0x135;

pub const SYS_process_vm_readv: u64 = 0x136;

pub const SYS_process_vm_writev: u64 = 0x137;

pub const SYS_kcmp: u64 = 0x138;

pub const SYS_finit_module: u64 = 0x139;

pub const SYS_sched_setattr: u64 = 0x13a;

pub const SYS_sched_getattr: u64 = 0x13b;

pub const SYS_renameat2: u64 = 0x13c;

pub const SYS_seccomp: u64 = 0x13d;

pub const SYS_getrandom: u64 = 0x13e;

pub const SYS_memfd_create: u64 = 0x13f;

pub const SYS_kexec_file_load: u64 = 0x140;

pub const SYS_bpf: u64 = 0x141;

pub const SYS_execveat: u64 = 0x142;

pub const SYS_userfaultfd: u64 = 0x143;

pub const SYS_membarrier: u64 = 0x144;

pub const SYS_mlock2: u64 = 0x145;

pub const SYS_copy_file_range: u64 = 0x146;

pub const SYS_preadv2: u64 = 0x147;

pub const SYS_pwritev2: u64 = 0x148;

pub const SYS_pkey_mprotect: u64 = 0x149;

pub const SYS_pkey_alloc: u64 = 0x14a;

pub const SYS_pkey_free: u64 = 0x14b;

pub const SYS_statx: u64 = 0x14c;

pub const SYS_io_pgetevents: u64 = 0x14d;

pub const SYS_rseq: u64 = 0x14e;

pub const SYS_pidfd_send_signal: u64 = 0x1a8;

pub const SYS_io_uring_setup: u64 = 0x1a9;

pub const SYS_io_uring_enter: u64 = 0x1aa;

pub const SYS_io_uring_register: u64 = 0x1ab;

pub const SYS_open_tree: u64 = 0x1ac;

pub const SYS_move_mount: u64 = 0x1ad;

pub const SYS_fsopen: u64 = 0x1ae;

pub const SYS_fsconfig: u64 = 0x1af;

pub const SYS_fsmount: u64 = 0x1b0;

pub const SYS_fspick: u64 = 0x1b1;

pub const SYS_pidfd_open: u64 = 0x1b2;

pub const SYS_clone3: u64 = 0x1b3;

pub const SYS_close_range: u64 = 0x1b4;

pub const SYS_openat2: u64 = 0x1b5;

pub const SYS_pidfd_getfd: u64 = 0x1b6;

pub const SYS_faccessat2: u64 = 0x1b7;

pub const SYS_process_madvise: u64 = 0x1b8;

pub const SYS_epoll_pwait2: u64 = 0x1b9;

pub const SYS_mount_setattr: u64 = 0x1ba;

pub const SYS_landlock_create_ruleset: u64 = 0x1bc;

pub const SYS_landlock_add_rule: u64 = 0x1bd;

pub const SYS_landlock_restrict_self: u64 = 0x1be;

pub const SYS_memfd_secret: u64 = 0x1bf;

pub const SYS_process_mrelease: u64 = 0x1c0;

pub const SYS_futex_waitv: u64 = 0x1c1;

pub const SYS_set_mempolicy_home_node: u64 = 0x1c2;

pub const SYS_cachestat: u64 = 0x1c3;

pub const SYS_fchmodat2: u64 = 0x1c4;

/// The entry point for analyzing syscalls for security purposes.
///
/// This function should be called by the IFC engine!
#[verus_spec(
    requires
)]
pub fn analysis_syscall(syscall_body: DekoSyscallBody) -> DekoGuestServResult<()> {
    if core::hint::unlikely(syscall_body.rax as usize >= SYS_CALL_NAME.len()) {
        return Err(DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidParam));
    }
    kinfo!("Syscall invoked: ", SYS_CALL_NAME[syscall_body.rax as usize]);

    match syscall_body.rax {
        // In June 2023, Google's security team reported that 60% of the exploits submitted
        // to their bug bounty program in 2022 were exploits of io_uring vulnerabilities.
        //
        // As a result, io_uring was disabled for apps in Android, and disabled entirely in
        // ChromeOS as well as Google servers. Docker also consequently disabled io_uring
        // from their default seccomp profile.
        SYS_io_uring_setup | SYS_io_uring_register | SYS_io_uring_enter => {
            kerror!("For safety reasons this syscall is forbidden: ", SYS_CALL_NAME[syscall_body.rax as usize]);

            die("");
        },
        _ => Ok(()),
    }
}

// #[verus_spec(r =>
//     requires
// )]
// fn exit_group(syscall_body: DekoSyscallBody) -> DekoGuestServResult<()> {
//     let exit_code = syscall_body.rdi;
//     if exit_code > 255 {
//         return Err(DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidParam));
//     }
//     let cr3 = PhysAddr(syscall_body.cr3);
//     // Search for the process in the process table; if found,
//     // delete it (or marking as "exit pending".)
//     Ok(())
// }
// /// Called by the docker runtime to change the root filesystem of a container.
// ///
// /// Typically the mount process goes like this:
// ///
// /// - `chdir(rootfs)`
// /// - `pivot_root(".", ".")`
// /// - `umount(".", MNT_DETACH)`
// #[verus_spec(r =>
//     requires
// )]
// fn do_pivot_root(syscall_body: DekoSyscallBody) -> DekoGuestServResult<()> {
//     let new_root = syscall_body.rdi;
//     let put_old = syscall_body.rsi;
//     if core::hint::unlikely(
//         new_root >= 0x8000_0000_0000 - 128 || new_root == 0 || put_old >= 0x8000_0000_0000 - 128
//             || put_old == 0 || syscall_body.cr3 % PAGE_SIZE != 0 || syscall_body.cr3
//             >= 0x000f_ffff_ffff_f000u64 - PAGE_SIZE,
//     ) {
//         return Err(DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidParam));
//     }
//     let mut new_root_buf = vec![0u8;128];
//     let mut put_old_buf = vec![0u8;128];
//     copy_from_user(
//         PhysAddr(syscall_body.cr3),
//         VirtAddr(new_root),
//         new_root_buf.as_mut_ptr(),  // because we cannot unsize slice due to verus limitations.
//         128,
//     )?;
//     copy_from_user(
//         PhysAddr(syscall_body.cr3),
//         VirtAddr(put_old),
//         put_old_buf.as_mut_ptr(),  // because we cannot unsize slice due to verus limitations.
//         128,
//     )?;
//     let new_root = core::ffi::CStr::from_bytes_until_nul(&new_root_buf).map_err(
//         |_e| DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidParam),
//     )?.to_str().map_err(|_e| DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidParam))?;
//     let put_old = core::ffi::CStr::from_bytes_until_nul(&put_old_buf).map_err(
//         |_e| DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidParam),
//     )?.to_str().map_err(|_e| DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidParam))?;
//     kinfo!(
//         "pivot_root called with new_root=", new_root,
//         ", put_old=", put_old
//     );
//     Ok(())
// }
// /// Unlike [`do_sys_execve`] which takes path to the binary, this system call
// /// is used to execute a binary relative to a directory file descriptor. This
// /// is used to mitigate the risk of CVE-2019-5736-like attacks.
// #[verus_spec(r =>
//     requires
// )]
// fn do_sys_execveat(syscall_body: DekoSyscallBody) -> DekoGuestServResult<()> {
//     let fd = syscall_body.rdi;
//     let pathname_ptr = syscall_body.rsi;
//     if core::hint::unlikely(
//         pathname_ptr >= 0x8000_0000_0000 - 128 || pathname_ptr == 0 || syscall_body.cr3 % PAGE_SIZE
//             != 0 || syscall_body.cr3 >= 0x000f_ffff_ffff_f000u64 - PAGE_SIZE,
//     ) {
//         return Err(DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidParam));
//     }
//     analyze_execve(PhysAddr(syscall_body.cr3), VirtAddr(pathname_ptr), Some(fd))
// }
// /// This should be intercepted at the VMPL0 level.
// ///
// /// A typical trigger of this function goes from the docker runtime calling `execve`
// /// in the guest, which traps to the trampoline, which then calls this function.
// #[verus_spec(r =>
//     requires
// )]
// fn do_sys_execve(syscall_body: DekoSyscallBody) -> DekoGuestServResult<()> {
//     kdebug!(
//         "execve called with filename", syscall_body.rdi=>hex,
//         "argv", syscall_body.rsi=>hex,
//         "envp", syscall_body.rdx=>hex
//     );
//     if core::hint::unlikely(
//         syscall_body.rdi >= 0x8000_0000_0000 - 128 || syscall_body.rdi == 0 || syscall_body.cr3
//             % PAGE_SIZE != 0 || syscall_body.cr3 >= 0x000f_ffff_ffff_f000u64 - PAGE_SIZE,
//     ) {
//         return Err(DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidParam));
//     }
//     analyze_execve(PhysAddr(syscall_body.cr3), VirtAddr(syscall_body.rdi), None)
// }
// #[verus_spec(r =>
//     requires
//         guest_cr3@ % PAGE_SIZE == 0,
//         guest_cr3@ + PAGE_SIZE < 0x000f_ffff_ffff_f000u64,
//         path@ + 128 < 0x8000_0000_0000,
//         path@ != 0,
// )]
// fn analyze_execve(guest_cr3: PhysAddr, path: VirtAddr, fd: Option<u64>) -> Result<
//     (),
//     DekoGuestServError,
// > {
//     let mut filename = vec![0u8;128];
//     copy_from_user(
//         guest_cr3,
//         path,
//         filename.as_mut_ptr(),  // because we cannot unsize slice due to verus limitations.
//         128,
//     )?;
//     if let Ok(f) = core::ffi::CStr::from_bytes_until_nul(&filename) {
//         if let Ok(fname_str) = f.to_str() {
//             kinfo!("The container is trying to execve filename=", fname_str);
//         } else {
//             // This is rare but possible.
//             kwarn!("execve filename (invalid utf8)", &filename);
//         }
//     } else {
//         kwarn!("execve filename (non-utf8)");
//     }
//     Ok(())
// }
} // verus!
