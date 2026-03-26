#![allow(non_upper_case_globals)]

use deko_macros::with_atomic_pred;
use deko_std::mem::PAGE_SIZE;
use deko_std::prelude::collections::hashmap::HashMap;
use deko_std::prelude::{PhysAddr, VirtAddr, VADDR_LOWER_MASK, VADDR_UPPER_MASK};
use deko_std::std_extra::allocator::AllocatorWrapper;
use deko_std::sync::DekoOnceCell;
use deko_std::wf::WellFormed;
use deko_std::{deko_bitflags, deko_rwlock_read_atomic_data, deko_rwlock_write_atomic_data};
use vstd::prelude::*;

use crate::cpu::regs::write_fs_base;
use crate::cpu::DekoCpuCtx;
use crate::guest::{
    copy_from_user, request_vmpl2_timer_event, take_vmpl1_deferred_timer_event, DekoGuestServError,
    DekoGuestServResult, DekoGuestServResultCode,
};
use crate::mm::frame_allocator::DekoAllocatorApi;
use crate::policy::userapp::{
    is_docker_request, DekoSignalActionShadow, DEKO_SHADOW_APP_LIST, IS_DOCKER_RUNNING,
};
// use crate::policy::userapp::copy_from_guest_user;
use crate::policy::DekoSyscallBody;
use crate::snp::rmpadjust;
use crate::{die, kdebug, kerror, kinfo, ktrace, kwarn, vec};

verus! {

pub const ARCH_SET_GS: u64 = 0x1001;
pub const ARCH_SET_FS: u64 = 0x1002;
pub const ARCH_GET_FS: u64 = 0x1003;
pub const ARCH_GET_GS: u64 = 0x1004;
pub const ARCH_MAP_VDSO_X32: u64 = 0x3001;
pub const ARCH_MAP_VDSO_32: u64 = 0x3002;

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

pub const PROT_READ: u64 = 0x1;

pub const PROT_WRITE: u64 = 0x2;

pub const PROT_EXEC: u64 = 0x4;

pub const PROT_SEM: u64 = 0x8;

pub const PROT_NONE: u64 = 0x0;

pub const MAP_SHARED: u64 = 0x01;

pub const MAP_PRIVATE: u64 = 0x02;

pub const MAP_FIXED: u64 = 0x10;

pub const MREMAP_MAYMOVE: u64 = 0x01;

pub const MREMAP_FIXED: u64 = 0x02;

pub const MAP_ANONYMOUS: u64 = 0x20;

pub const MAP_TYPE_MASK: u64 = 0x0f;

const DEKO_LINUX_SIGSET_SIZE: u64 = 8;

#[derive(Clone, Copy)]
#[repr(C)]
struct DekoLinuxSigAction {
    handler: u64,
    flags: u64,
    restorer: u64,
    mask: u64,
}

impl DekoLinuxSigAction {
    #[inline(always)]
    const fn empty() -> Self {
        Self { handler: 0, flags: 0, restorer: 0, mask: 0 }
    }
}

fn get_active_pid() -> DekoGuestServResult<u32> {
    let (cpu, Tracked(cpu_perm)) = DekoCpuCtx::this_cpu();
    let cpu_borrow = cpu.borrow(Tracked(&cpu_perm.ptr_perm));
    let ext_vmpl1 = cpu_borrow.ext_vmpl1.as_ref().ok_or(DekoGuestServError::FatalError)?;

    ext_vmpl1.current_pid.ok_or(DekoGuestServError::FatalError)
}

fn get_buf_va() -> DekoGuestServResult<VirtAddr> {
    let active_pid = get_active_pid()?;

    // Check the shared buffer.
    deko_rwlock_read_atomic_data! {
        DEKO_SHADOW_APP_LIST,
        app_list,
        __,
        {
            if let Some(ref app_list) = app_list {
                if core::hint::unlikely(!app_list.contains_key(&active_pid)) {
                    kerror!("The active PID ", active_pid, " is not in the app list");
                    Err(DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidParam))
                } else {
                    let app = app_list.get(&active_pid).unwrap();
                    proof {
                        assert(app.wf()) by {
                            assert(app_list.wf());
                            assert(forall |k: u32| #[trigger] app_list@.contains_key(k) ==> app_list@[k].wf() && k.wf());
                            assert(app_list@.contains_key(active_pid));
                        }
                    }
                    match app.ext.shared_buf.get() {
                        Some(buf) => Ok(*buf),
                        None => {
                            kerror!("The shared buffer for PID ", active_pid, " is not initialized");
                            Err(DekoGuestServError::FatalError)
                        },
                    }
                }
            } else {
                kerror!("The app list is not initialized");
                Err(DekoGuestServError::FatalError)
            }
        }
    }
}

#[verus_spec(r =>
    ensures
        r is Ok ==> {
            &&& addr == 0 || 0 < addr
            &&& addr == 0 || (addr as int) + (len as int) <= 0x8000_0000_0000int
        }
)]
#[inline]
fn validate_user_read_ptr(addr: u64, len: usize) -> DekoGuestServResult<()> {
    if addr == 0 {
        return Ok(());
    }

    let end = match addr.checked_add(len as u64) {
        Some(v) => v,
        None => {
            kerror!("user pointer overflow: ", addr => hex);
            return Err(DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidParam));
        },
    };
    if addr >= 0x8000_0000_0000 || end > 0x8000_0000_0000 || end <= addr {
        kerror!("invalid user pointer range: ", addr => hex, end => hex);
        return Err(DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidParam));
    }

    Ok(())
}

fn shadow_rt_sigaction(
    pid: u32,
    signum: u32,
    action: DekoSignalActionShadow,
) -> DekoGuestServResult<()> {
    if signum == 0 || signum >= 65 {
        return Err(DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidParam));
    }
    let sig_idx = signum as usize;

    deko_rwlock_write_atomic_data! {
        DEKO_SHADOW_APP_LIST,
        app_list,
        __,
        {
            if let Some(mut app_list_inner) = app_list {
                if !app_list_inner.contains_key(&pid) {
                    app_list = Some(app_list_inner);
                    Err(DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidParam))
                } else {
                    let mut app = app_list_inner.remove(&pid).unwrap();
                    app.ext.sigactions[sig_idx] = action;
                    app_list_inner.insert(pid, app);
                    app_list = Some(app_list_inner);
                    Ok(())
                }
            } else {
                Err(DekoGuestServError::FatalError)
            }
        }
    }
}

/// Moves the syscall arguments to the shared buffer for the VMPL2 handler to process this request.
#[verus_spec(

)]
fn move_to_shared_buf(syscall_body: &mut DekoSyscallBody) -> DekoGuestServResult<()> {
    let buf_va = get_buf_va()?;

    unsafe {
        buf_va.copy_nonoverlapping(syscall_body);
    }

    Ok(())
}

/// The entry point for analyzing syscalls for security purposes.
///
/// This function should be called by the IFC engine!
#[verus_spec(
    requires
)]
pub fn analyze_and_prepare_syscall(syscall_body: &mut DekoSyscallBody) -> DekoGuestServResult<()> {
    if core::hint::unlikely(syscall_body.rax as usize >= SYS_CALL_NAME.len()) {
        return Err(DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidParam));
    }

    kdebug!("Syscall invoked: ", SYS_CALL_NAME[syscall_body.rax as usize]);
    kdebug!("Syscall body", syscall_body);

    match syscall_body.rax {
        SYS_read => { analyze_syscall_read(syscall_body)? },
        // Memory-related system calls
        SYS_mmap => { analyze_syscall_mmap(syscall_body)? },
        SYS_mprotect => { analyze_syscall_mprotect(syscall_body)? },
        SYS_munmap => { analyze_syscall_munmap(syscall_body)? },
        SYS_brk => { analyze_syscall_brk(syscall_body)? },
        SYS_mremap => { analyze_syscall_mremap(syscall_body)? },
        SYS_write => { analyze_syscall_write(syscall_body)? },
        // Thread/Process related system calls
        SYS_clone3 | SYS_clone | SYS_fork | SYS_vfork => {},
        // Filesystem.
        // In June 2023, Google's security team reported that 60% of the exploits submitted
        // to their bug bounty program in 2022 were exploits of io_uring vulnerabilities.
        //
        // As a result, io_uring was disabled for apps in Android, and disabled entirely in
        // ChromeOS as well as Google servers. Docker also consequently disabled io_uring
        // from their default seccomp profile.
        SYS_io_uring_setup | SYS_io_uring_register | SYS_io_uring_enter => {
            kerror!("For safety reasons these syscall(s) is forbidden: ", SYS_CALL_NAME[syscall_body.rax as usize]);

            die("");
        },
        SYS_exit | SYS_exit_group => { analyze_syscall_exit(syscall_body)? },
        _ => (),
    }

    move_to_shared_buf(syscall_body)
}

pub fn sysret_epilogue(syscall_body: &mut DekoSyscallBody) -> DekoGuestServResult<()> {
    let syscall_num = syscall_body.rax;
    let buf_va = get_buf_va()?;

    let handled_syscall_body = unsafe { buf_va.read::<DekoSyscallBody>() };

    // For some special system calls we need some extra checks and processings.
    match syscall_num {
        SYS_mmap => syscall_mmap_ret(syscall_body, &handled_syscall_body),
        SYS_arch_prctl => syscall_arch_prctl_ret(syscall_body, &handled_syscall_body),
        _ => {
            syscall_body.rax = handled_syscall_body.rax;

            Ok(())
        },
    }?;

    if take_vmpl1_deferred_timer_event() {
        request_vmpl2_timer_event()?;
    }

    Ok(())
}

fn syscall_arch_prctl_ret(
    syscall_body: &mut DekoSyscallBody,
    handled_syscall_body: &DekoSyscallBody,
) -> DekoGuestServResult<()> {
    syscall_body.rax = handled_syscall_body.rax;

    if handled_syscall_body.rax != 0 {
        return Ok(());
    }

    let flag = syscall_body.rdi;
    match flag {
        ARCH_SET_FS => {
            write_fs_base(syscall_body.rsi);
        },
        // These requests are handled entirely by Linux and do not require
        // any extra VMPL1 shadow-state updates on successful return.
        ARCH_SET_GS | ARCH_GET_FS | ARCH_GET_GS | ARCH_MAP_VDSO_X32 | ARCH_MAP_VDSO_32 => {},
        _ => {
            kerror!("`arch_prctl` called with unknown flag: ", flag=>hex);
            return Err(DekoGuestServError::FatalError);
        },
    }

    Ok(())
}

fn syscall_rt_sigaction_ret(
    syscall_body: &mut DekoSyscallBody,
    handled_syscall_body: &DekoSyscallBody,
) -> DekoGuestServResult<()> {
    syscall_body.rax = handled_syscall_body.rax;
    if handled_syscall_body.rax != 0 {
        return Ok(());
    }

    let act_addr = syscall_body.rsi;
    if act_addr == 0 {
        return Ok(());
    }
    let signum = syscall_body.rdi;
    if signum == 0 || signum >= 65 {
        return Err(DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidParam));
    }
    validate_user_read_ptr(act_addr, core::mem::size_of::<DekoLinuxSigAction>())?;
    let guest_cr3 = syscall_body.cr3;
    let guest_cr3_end = match guest_cr3.checked_add(PAGE_SIZE) {
        Some(v) => v,
        None => return Err(DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidParam)),
    };
    if guest_cr3 == 0 || guest_cr3 % PAGE_SIZE != 0 || guest_cr3_end >= 0x000f_ffff_ffff_f000u64 {
        return Err(DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidParam));
    }

    let mut action = DekoLinuxSigAction::empty();
    copy_from_user(
        PhysAddr(guest_cr3),
        VirtAddr(act_addr),
        deko_std::ptr::addr_of_ref(&action),
        core::mem::size_of::<DekoLinuxSigAction>(),
    )?;
    let pid = get_active_pid()?;

    shadow_rt_sigaction(
        pid,
        signum as u32,
        DekoSignalActionShadow {
            installed: true,
            handler: action.handler,
            flags: action.flags,
            restorer: action.restorer,
            mask: action.mask,
        },
    )
}

fn syscall_write_ret(
    syscall_body: &mut DekoSyscallBody,
    handled_syscall_body: &DekoSyscallBody,
) -> DekoGuestServResult<()> {
    syscall_body.rax = handled_syscall_body.rax;

    Ok(())
}

/// The epilogue for the `mmap` syscall, which checks the return value of `mmap` and updates memory accordingly.
/// Note that this does two things:
///
/// - Revoke the access permissions `(!(rwx))` for VMPL2.
/// - Adds the memory region to the shadowed memory management for the guest.
///
/// To prevent potential page fault problems, we require that the guest must call `fix_user_fault` or similar
/// functions _in advance_ to pin the memory pages for the `mmap` syscall.
#[verus_spec(r =>
    ensures
        r is Ok ==> {
            true
        }
)]
fn syscall_mmap_ret(
    syscall_body: &mut DekoSyscallBody,
    handled_syscall_body: &DekoSyscallBody,
) -> DekoGuestServResult<()> {
    syscall_body.rax = handled_syscall_body.rax;

    kdebug!("returned from mmap: ", handled_syscall_body.rax=>hex);

    Ok(())
}

/// Prototype:
///
/// ssize_t write(int fd, const void *buf, size_t count);
#[verus_spec()]
fn analyze_syscall_write(syscall_body: &mut DekoSyscallBody) -> DekoGuestServResult<()> {
    Ok(())
}

/// Prototype:
///
/// void *mmap(void *addr, size_t length, int prot, int flags, int fd, off_t offset);
///
/// mmap() creates a new mapping in the virtual address space of the calling process. The starting address for the new
/// mapping is specified in `addr`. The length argument specifies the length of the mapping.
#[verus_spec(r =>
    ensures
        r is Ok ==> {
            true
        }
)]
fn analyze_syscall_mmap(syscall_body: &mut DekoSyscallBody) -> DekoGuestServResult<()> {
    let addr = syscall_body.rdi;  // hint
    let length = syscall_body.rsi;
    let prot = syscall_body.rdx;
    let flags = syscall_body.r10;
    let fd = syscall_body.r8 as i32;
    let offset = syscall_body.r9;
    let is_anon = flags & MAP_ANONYMOUS != 0;
    let is_shared = flags & MAP_SHARED != 0;
    let is_private = flags & MAP_PRIVATE != 0;

    // `mmap` with zero length is invalid.
    if core::hint::unlikely(length == 0) {
        kerror!("mmap length is 0");
        return Err(DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidParam));
    }
    let aligned_length = match length.checked_add(PAGE_SIZE - 1) {
        Some(l) => l & !(PAGE_SIZE as u64 - 1),
        None => {
            kerror!("mmap length is too large: ", length=>hex);
            return Err(DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidParam));
        },
    };

    if flags & MAP_FIXED != 0 {
        if addr % PAGE_SIZE != 0 {
            kerror!("MAP_FIXED used but addr is not page aligned: ", addr=>hex);
            return Err(DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidParam));
        }
    }
    if addr != 0 {
        let end_addr = match addr.checked_add(aligned_length) {
            Some(val) => val,
            None => {
                kerror!("mmap addr + length overflow");
                return Err(DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidParam));
            },
        };

        if end_addr > VADDR_LOWER_MASK {
            kerror!("mmap requested address out of user space bounds: ", end_addr=>hex);
            return Err(DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidParam));
        }
    }

    if offset % PAGE_SIZE != 0 {
        kerror!("mmap offset is not page aligned: ", offset=>hex);
        return Err(DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidParam));
    }

    if core::hint::unlikely((prot & PROT_WRITE != 0) && (prot & PROT_EXEC != 0)) {
        kerror!("mmap W^X violation: prot=", prot=>hex);
        return Err(DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidParam));
    }

    if (flags & MAP_TYPE_MASK) == 0 || (is_shared && is_private) {
        kerror!("mmap requires exactly one mapping type: flags=", flags=>hex);
        return Err(DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidParam));
    }

    if is_anon {
        if fd != -1 {
            kerror!("anonymous mmap requires fd=-1: fd=", fd as u64 => hex);
            return Err(DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidParam));
        }
        if offset != 0 {
            kerror!("anonymous mmap requires zero offset: ", offset=>hex);
            return Err(DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidParam));
        }
    }

    // First IFC policy for mmap: disallow writable shared mappings because
    // they create an immediate shared mutable channel with the untrusted side.
    if is_shared && (prot & PROT_WRITE != 0) {
        // kerror!("shared writable mmap is forbidden by IFC policy");
        kwarn!("shared writable mmap is forbidden by IFC policy, but allowing it for compatibility for now");
        // return Err(DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidParam));
    }

    syscall_body.rsi = aligned_length;

    Ok(())
}

#[verus_spec()]
fn analyze_syscall_mprotect(syscall_body: &mut DekoSyscallBody) -> DekoGuestServResult<()> {
    let addr = syscall_body.rdi;
    let length = syscall_body.rsi;
    let prot = syscall_body.rdx;

    if core::hint::unlikely(length == 0) {
        kerror!("mprotect length is 0");
        return Err(DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidParam));
    }
    if addr % PAGE_SIZE != 0 {
        kerror!("mprotect addr is not page aligned: ", addr=>hex);
        return Err(DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidParam));
    }
    let aligned_length = match length.checked_add(PAGE_SIZE - 1) {
        Some(l) => l & !(PAGE_SIZE as u64 - 1),
        None => {
            kerror!("mprotect length is too large: ", length=>hex);
            return Err(DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidParam));
        },
    };
    let end_addr = match addr.checked_add(aligned_length) {
        Some(val) => val,
        None => {
            kerror!("mprotect addr + length overflow");
            return Err(DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidParam));
        },
    };
    if end_addr > VADDR_LOWER_MASK {
        kerror!("mprotect requested range out of user space bounds: ", end_addr=>hex);
        return Err(DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidParam));
    }
    if (prot & PROT_WRITE != 0) && (prot & PROT_EXEC != 0) {
        kerror!("mprotect W^X violation: prot=", prot=>hex);
        return Err(DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidParam));
    }

    syscall_body.rsi = aligned_length;
    Ok(())
}

#[verus_spec()]
fn analyze_syscall_munmap(syscall_body: &mut DekoSyscallBody) -> DekoGuestServResult<()> {
    let addr = syscall_body.rdi;
    let length = syscall_body.rsi;

    if core::hint::unlikely(length == 0) {
        kerror!("munmap length is 0");
        return Err(DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidParam));
    }
    if addr % PAGE_SIZE != 0 {
        kerror!("munmap addr is not page aligned: ", addr=>hex);
        return Err(DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidParam));
    }
    let aligned_length = match length.checked_add(PAGE_SIZE - 1) {
        Some(l) => l & !(PAGE_SIZE as u64 - 1),
        None => {
            kerror!("munmap length is too large: ", length=>hex);
            return Err(DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidParam));
        },
    };
    let end_addr = match addr.checked_add(aligned_length) {
        Some(val) => val,
        None => {
            kerror!("munmap addr + length overflow");
            return Err(DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidParam));
        },
    };
    if end_addr > VADDR_LOWER_MASK {
        kerror!("munmap requested range out of user space bounds: ", end_addr=>hex);
        return Err(DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidParam));
    }

    syscall_body.rsi = aligned_length;
    Ok(())
}

#[verus_spec()]
fn analyze_syscall_brk(syscall_body: &mut DekoSyscallBody) -> DekoGuestServResult<()> {
    let addr = syscall_body.rdi;

    if addr != 0 && addr >= VADDR_LOWER_MASK {
        kerror!("brk requested address out of user space bounds: ", addr=>hex);
        return Err(DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidParam));
    }

    Ok(())
}

#[verus_spec()]
fn analyze_syscall_mremap(syscall_body: &mut DekoSyscallBody) -> DekoGuestServResult<()> {
    let old_addr = syscall_body.rdi;
    let old_length = syscall_body.rsi;
    let new_length = syscall_body.rdx;
    let flags = syscall_body.r10;

    if core::hint::unlikely(old_length == 0) {
        kerror!("mremap old_length is 0");
        return Err(DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidParam));
    }
    if core::hint::unlikely(new_length == 0) {
        kerror!("mremap new_length is 0");
        return Err(DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidParam));
    }
    if old_addr % PAGE_SIZE != 0 {
        kerror!("mremap old_addr is not page aligned: ", old_addr=>hex);
        return Err(DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidParam));
    }
    let aligned_old_length = match old_length.checked_add(PAGE_SIZE - 1) {
        Some(l) => l & !(PAGE_SIZE as u64 - 1),
        None => {
            kerror!("mremap old_length is too large: ", old_length=>hex);
            return Err(DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidParam));
        },
    };
    let aligned_new_length = match new_length.checked_add(PAGE_SIZE - 1) {
        Some(l) => l & !(PAGE_SIZE as u64 - 1),
        None => {
            kerror!("mremap new_length is too large: ", new_length=>hex);
            return Err(DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidParam));
        },
    };
    let old_end = match old_addr.checked_add(aligned_old_length) {
        Some(val) => val,
        None => {
            kerror!("mremap old_addr + old_length overflow");
            return Err(DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidParam));
        },
    };
    if old_end > VADDR_LOWER_MASK {
        kerror!("mremap old range out of user space bounds: ", old_end=>hex);
        return Err(DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidParam));
    }
    if flags & MREMAP_FIXED != 0 {
        let new_addr = syscall_body.r8;
        if new_addr % PAGE_SIZE != 0 {
            kerror!("mremap new_addr is not page aligned: ", new_addr=>hex);
            return Err(DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidParam));
        }
        let new_end = match new_addr.checked_add(aligned_new_length) {
            Some(val) => val,
            None => {
                kerror!("mremap new_addr + new_length overflow");
                return Err(DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidParam));
            },
        };
        if new_end > VADDR_LOWER_MASK {
            kerror!("mremap new range out of user space bounds: ", new_end=>hex);
            return Err(DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidParam));
        }
        if flags & MREMAP_MAYMOVE == 0 {
            kerror!("mremap uses MREMAP_FIXED without MREMAP_MAYMOVE: flags=", flags=>hex);
            return Err(DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidParam));
        }
    }

    syscall_body.rsi = aligned_old_length;
    syscall_body.rdx = aligned_new_length;
    Ok(())
}

#[verus_spec()]
fn analyze_syscall_rt_sigaction(syscall_body: &mut DekoSyscallBody) -> DekoGuestServResult<()> {
    let signum = syscall_body.rdi;
    let act = syscall_body.rsi;
    let oldact = syscall_body.rdx;
    let sigsetsize = syscall_body.r10;

    if signum == 0 || signum >= 65 {
        kerror!("invalid rt_sigaction signum: ", signum);
        return Err(DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidParam));
    }
    if sigsetsize != DEKO_LINUX_SIGSET_SIZE {
        kerror!("unexpected rt_sigaction sigsetsize: ", sigsetsize);
        return Err(DekoGuestServError::SoftError(DekoGuestServResultCode::InvalidParam));
    }

    validate_user_read_ptr(act, core::mem::size_of::<DekoLinuxSigAction>())?;
    validate_user_read_ptr(oldact, core::mem::size_of::<DekoLinuxSigAction>())?;

    Ok(())
}

fn analyze_syscall_exit(syscall_body: &mut DekoSyscallBody) -> DekoGuestServResult<()> {
    let exit_code = syscall_body.rdi as u8;

    // Now we need to un-register this application as this
    // has been killed or exited.

    Ok(())
}

#[verus_spec()]
fn analyze_syscall_read(syscall_body: &mut DekoSyscallBody) -> DekoGuestServResult<()> {
    Ok(())
}

#[verus_spec()]
fn analyze_syscall_clone(syscall_body: &mut DekoSyscallBody) -> DekoGuestServResult<()> {
    Ok(())
}

} // verus!
