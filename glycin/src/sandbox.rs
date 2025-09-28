// Copyright (c) 2024 GNOME Foundation Inc.

use std::fs::{canonicalize, DirEntry, File};
use std::io::{self, BufRead, BufReader, Seek};
use std::os::fd::{AsRawFd, BorrowedFd};
use std::os::unix::net::UnixStream;
use std::os::unix::process::{CommandExt, ExitStatusExt};
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::sync::Arc;

use gio::glib;
use libseccomp::error::SeccompError;
use libseccomp::{ScmpAction, ScmpFilterContext, ScmpSyscall};
use memfd::{Memfd, MemfdOptions};
use nix::sys::resource;

use crate::config::{ConfigEntry, ImageLoaderConfig};
use crate::util::{self, new_async_mutex, spawn_blocking, AsyncMutex};
use crate::{Error, SandboxMechanism};

type SystemSetupStore = Arc<Result<SystemSetup, Arc<io::Error>>>;

static SYSTEM_SETUP: AsyncMutex<Option<SystemSetupStore>> = new_async_mutex(None);

/// List of allowed syscalls
///
/// All syscalls are blocked by default via seccomp. Only the following syscalls
/// are allowed. The feature is only available for sandboxes using bubblewrap.
const ALLOWED_SYSCALLS: &[&str] = &[
    "access",
    "arch_prctl",
    "arm_fadvise64_64",
    "brk",
    "capget",
    "capset",
    "chdir",
    "clock_getres",
    "clock_gettime",
    "clock_gettime64",
    "clone",
    "clone3",
    "close",
    "connect",
    "creat",
    "dup",
    "epoll_create",
    "epoll_create1",
    "epoll_ctl",
    "epoll_pwait",
    "epoll_wait",
    "eventfd",
    "eventfd2",
    "execve",
    "exit",
    "exit_group",
    "faccessat",
    "fadvise64",
    "fadvise64_64",
    "fchdir",
    "fcntl",
    "fcntl",
    "fcntl64",
    "fstat",
    "fstatfs",
    "fstatfs64",
    "ftruncate",
    "ftruncate64",
    "futex",
    "futex_time64",
    "get_mempolicy",
    "getcwd",
    "getdents64",
    "getegid",
    "getegid32",
    "geteuid",
    "geteuid32",
    "getgid",
    "getgid32",
    "getpid",
    "getppid",
    "getpriority",
    "getrandom",
    "gettid",
    "gettimeofday",
    "getuid",
    "getuid32",
    "ioctl",
    "madvise",
    "membarrier",
    "memfd_create",
    "mmap",
    "mmap2",
    "mprotect",
    "mremap",
    "munmap",
    "newfstatat",
    "open",
    "openat",
    "pipe",
    "pipe2",
    "pivot_root",
    "poll",
    "ppoll",
    "ppoll_time64",
    "prctl",
    "pread64",
    "prlimit64",
    "read",
    "readlink",
    "readlinkat",
    "recv",
    "recvfrom",
    "recvmsg",
    "rseq",
    "rt_sigaction",
    "rt_sigprocmask",
    "rt_sigreturn",
    "sched_getaffinity",
    "sched_yield",
    "sendmsg",
    "sendto",
    "set_mempolicy",
    "set_mempolicy",
    "set_robust_list",
    "set_thread_area",
    "set_tid_address",
    "set_tls",
    "setpriority",
    "sigaltstack",
    "signalfd4",
    "socket",
    "socketcall",
    "stat",
    "statfs",
    "statfs64",
    "statx",
    "sysinfo",
    "tgkill",
    "timerfd_create",
    "timerfd_settime",
    "timerfd_settime64",
    "ugetrlimit",
    "uname",
    "unshare",
    "wait4",
    "write",
    "writev",
];

/// Extra syscalls only allowed with fontconfig
///
/// We are only allowing them for fontconfig since generally we don't want to
/// allow such filesystem operations. But seccomp needs them for cache
/// operations.
const ALLOWED_SYSCALLS_FONTCONFIG: &[&str] = &[
    "chmod",
    "link",
    "linkat",
    "rename",
    "renameat",
    "renameat2",
    "unlink",
    "unlinkat",
];

const INHERITED_ENVIRONMENT_VARIABLES: &[&str] = &["RUST_BACKTRACE", "RUST_LOG", "XDG_RUNTIME_DIR"];

pub struct Sandbox {
    sandbox_mechanism: SandboxMechanism,
    config_entry: ConfigEntry,
    dbus_socket: UnixStream,
    ro_bind_extra: Vec<PathBuf>,
}

static_assertions::assert_impl_all!(Sandbox: Send, Sync);

pub struct SpawnedSandbox {
    pub command: Command,
    // Keep seccomp fd alive until process exits (not used in native_sandbox)
    pub _seccomp_fd: Option<Memfd>,
    pub _dbus_socket: UnixStream,
}

static_assertions::assert_impl_all!(SpawnedSandbox: Send, Sync);

impl Sandbox {
    pub fn new(
        sandbox_mechanism: SandboxMechanism,
        config_entry: ConfigEntry,
        dbus_socket: UnixStream,
    ) -> Self {
        Self {
            sandbox_mechanism,
            config_entry,
            dbus_socket,
            ro_bind_extra: Vec::new(),
        }
    }

    fn exec(&self) -> &Path {
        self.config_entry.exec()
    }

    pub fn add_ro_bind(&mut self, path: PathBuf) {
        self.ro_bind_extra.push(path);
    }

    pub async fn spawn(self) -> Result<SpawnedSandbox, Error> {
        let dbus_fd = self.dbus_socket.as_raw_fd();

        let mut shared_fds = Vec::new();

        let (mut command, seccomp_fd) = match self.sandbox_mechanism {
            SandboxMechanism::NativeSandbox => {
                // This replaces the previous Bwrap mechanism
                let command = self.native_sandbox_command().await?;
                (command, None)
            }
            SandboxMechanism::FlatpakSpawn => {
                let command = self.flatpak_spawn_command();
                (command, None)
            }
            SandboxMechanism::NotSandboxed => {
                eprintln!("WARNING: Glycin running without sandbox.");
                let command = self.no_sandbox_command();
                (command, None)
            }
        };

        command.arg("--dbus-fd");
        command.arg(dbus_fd.to_string());

        command.stdin(Stdio::piped());
        command.stderr(Stdio::piped());
        command.stdout(Stdio::piped());

        shared_fds.push(self.dbus_socket.as_raw_fd());

        unsafe {
            command.pre_exec(move || {
                libc::close_range(3, libc::c_uint::MAX, libc::CLOSE_RANGE_CLOEXEC as i32);

                // Allow FDs to be passed to child process
                for raw_fd in &shared_fds {
                    let fd = BorrowedFd::borrow_raw(*raw_fd);
                    if let Ok(flags) = nix::fcntl::fcntl(&fd, nix::fcntl::FcntlArg::F_GETFD) {
                        let mut flags = nix::fcntl::FdFlag::from_bits_truncate(flags);
                        flags.remove(nix::fcntl::FdFlag::FD_CLOEXEC);
                        let _ = nix::fcntl::fcntl(&fd, nix::fcntl::FcntlArg::F_SETFD(flags));
                    }
                }

                Ok(())
            });
        }

        Ok(SpawnedSandbox {
            command,
            _seccomp_fd: seccomp_fd,
            _dbus_socket: self.dbus_socket,
        })
    }

    /// Native sandbox: directly apply seccomp filter before launching execve
    async fn native_sandbox_command(&self) -> Result<Command, Error> {
        let mut command = Command::new(self.exec());

        command.env_clear();

        // Inherit some environment variables
        for key in INHERITED_ENVIRONMENT_VARIABLES {
            if let Some(val) = std::env::var_os(key) {
                command.env(key, val);
            }
        }

        let config_entry = self.config_entry.clone();

//        fn allow_open_readonly(filter: &mut libseccomp::ScmpFilterContext) -> Result<(), std::io::Error> {
//            use libseccomp::{ScmpAction, ScmpSyscall, ScmpArgCompare, ScmpCompareOp};
//
//            // Allow open with O_RDONLY only (flags == 0)
//            let open_sys = ScmpSyscall::from_name("open")
//                .map_err(|e| std::io::Error::new(std::io::ErrorKind::Other, format!("seccomp: {e:?}")))?;
//            filter.add_rule_conditional(
//                ScmpAction::Allow,
//                open_sys,
//                &[ScmpArgCompare::new(1, ScmpCompareOp::Eq, libc::O_RDONLY as u64)],
//            ).map_err(|e| std::io::Error::new(std::io::ErrorKind::Other, format!("seccomp: {e:?}")))?;
//
//            // Allow openat with O_RDONLY only (flags == 0)
//            let openat_sys = ScmpSyscall::from_name("openat")
//                .map_err(|e| std::io::Error::new(std::io::ErrorKind::Other, format!("seccomp: {e:?}")))?;
//            filter.add_rule_conditional(
//                ScmpAction::Allow,
//                openat_sys,
//                &[ScmpArgCompare::new(2, ScmpCompareOp::Eq, libc::O_RDONLY as u64)],
//            ).map_err(|e| std::io::Error::new(std::io::ErrorKind::Other, format!("seccomp: {e:?}")))?;
//
//            Ok(())
//        }
//
//        // --- Helper function for filtered socket() ---
//        fn allow_af_unix_socket(filter: &mut libseccomp::ScmpFilterContext) -> Result<(), std::io::Error> {
//            use libseccomp::{ScmpAction, ScmpSyscall, ScmpArgCompare, ScmpCompareOp};
//
//            // Allow socket(AF_UNIX, ...), i.e., domain == AF_UNIX (1)
//            let socket_sys = ScmpSyscall::from_name("socket")
//                .map_err(|e| std::io::Error::new(std::io::ErrorKind::Other, format!("seccomp: {e:?}")))?;
//            filter.add_rule_conditional(
//                ScmpAction::Allow,
//                socket_sys,
//                &[ScmpArgCompare::new(0, ScmpCompareOp::Eq, libc::AF_UNIX as u64)],
//            ).map_err(|e| std::io::Error::new(std::io::ErrorKind::Other, format!("seccomp: {e:?}")))?;
//
//            Ok(())
//        }


        unsafe {
            command.pre_exec(move || {
                // Set memory limit
                Self::set_memory_limit();

                // Rebuild and load seccomp filter in child
                let filter = {
                    // Reconstruct the filter as in seccomp_filter()
                    let mut filter = if std::env::var("GLYCIN_SECCOMP_DEFAULT_ACTION")
                        .ok()
                        .as_deref()
                        == Some("KILL_PROCESS")
                    {
                        libseccomp::ScmpFilterContext::new(libseccomp::ScmpAction::KillProcess)
                            .map_err(|e| std::io::Error::new(std::io::ErrorKind::Other, format!("seccomp: {e:?}")))?
                    } else {
                        libseccomp::ScmpFilterContext::new(libseccomp::ScmpAction::Trap)
                            .map_err(|e| std::io::Error::new(std::io::ErrorKind::Other, format!("seccomp: {e:?}")))?
                    };

                    let mut syscalls = vec![ALLOWED_SYSCALLS];
                    if config_entry.fontconfig() {
                        syscalls.push(ALLOWED_SYSCALLS_FONTCONFIG);
                    }

                    for syscall_name in syscalls.into_iter().flatten() {
                        let syscall = libseccomp::ScmpSyscall::from_name(syscall_name)
                            .map_err(|e| std::io::Error::new(std::io::ErrorKind::Other, format!("seccomp: {e:?}")))?;
                        filter.add_rule(libseccomp::ScmpAction::Allow, syscall)
                            .map_err(|e| std::io::Error::new(std::io::ErrorKind::Other, format!("seccomp: {e:?}")))?;
                    }
                    filter
                };

                filter.load().map_err(|e| {
                    std::io::Error::new(std::io::ErrorKind::Other, format!("seccomp: {e:?}"))
                })?;

                Ok(())
            });
        }

        Ok(command)
    }

    fn flatpak_spawn_command(&self) -> Command {
        let mut command = Command::new("flatpak-spawn");

        let memory_limit = Self::memory_limit();
        let dbus_fd = self.dbus_socket.as_raw_fd();

        tracing::debug!("Setting prlimit to {memory_limit} bytes");

        command.args([
            "--sandbox",
            // die with parent
            "--watch-bus",
            // change working directory to something that exists
            "--directory=/",
        ]);

        // Start from a clean environment
        //
        // It's not really cleared due to this issue but nothing we can do about this:
        // <https://github.com/flatpak/flatpak/issues/5271>
        command.env_clear();

        // Inherit some environment variables
        for key in INHERITED_ENVIRONMENT_VARIABLES {
            if let Some(val) = std::env::var_os(key) {
                command.env(key, val);
            }
        }

        // Forward dbus connection
        command.arg(format!("--forward-fd={dbus_fd}"));

        // Start loader with memory limit
        command.arg("prlimit");
        command.arg(format!("--as={memory_limit}"));

        // Loader binary
        command.arg(self.exec());

        // Let flatpak-spawn die if the thread calling it exits
        unsafe {
            command.pre_exec(|| {
                nix::sys::prctl::set_pdeathsig(nix::sys::signal::SIGKILL).map_err(Into::into)
            });
        }

        command
    }

    fn no_sandbox_command(&self) -> Command {
        let mut command = Command::new(self.exec());

        command.env_clear();

        // Inherit some environment variables
        for key in INHERITED_ENVIRONMENT_VARIABLES {
            if let Some(val) = std::env::var_os(key) {
                command.env(key, val);
            }
        }

        // Set sandbox memory limit
        unsafe {
            command.pre_exec(|| {
                nix::sys::prctl::set_pdeathsig(nix::sys::signal::SIGKILL).map_err(Into::into)
            });
        }

        command
    }

    /// Memory limit in bytes that should be applied to sandboxes
    fn memory_limit() -> resource::rlim_t {
        // Lookup free memory
        if let Some(mem_available) = Self::mem_available() {
            Self::calculate_memory_limit(mem_available)
        } else {
            tracing::warn!("glycin: Unable to determine available memory via /proc/meminfo");

            // Default to 1 GB memory limit
            const { (1024 as resource::rlim_t).pow(3) }
        }
    }

    /// Try to determine how much memory is available on the system
    fn mem_available() -> Option<resource::rlim_t> {
        if let Ok(file) = File::open("/proc/meminfo") {
            let meminfo = BufReader::new(file);
            let mut total_avail_kb: Option<resource::rlim_t> = None;

            for line in meminfo.lines().map_while(Result::ok) {
                if line.starts_with("MemAvailable:") || line.starts_with("SwapFree:") {
                    tracing::trace!("Using /proc/meminfo: {line}");
                    if let Some(mem_avail_kb) = line
                        .split(' ')
                        .filter(|x| !x.is_empty())
                        .nth(1)
                        .and_then(|x| x.parse::<resource::rlim_t>().ok())
                    {
                        total_avail_kb =
                            Some(total_avail_kb.unwrap_or(0).saturating_add(mem_avail_kb));
                    }
                }
            }

            if let Some(total_avail_kb) = total_avail_kb {
                let mem_available = total_avail_kb.saturating_mul(1024);

                return Some(mem_available);
            }
        }

        None
    }

    /// Calculate memory that the sandbox will be allowed to use
    fn calculate_memory_limit(mem_available: resource::rlim_t) -> resource::rlim_t {
        // Consider max of 20 GB free RAM for use
        let mem_considered = resource::rlim_t::min(
            mem_available,
            const { (1024 as resource::rlim_t).pow(3).saturating_mul(20) },
        )
        // Keep at least 200 MB free
        .saturating_sub(1024 * 1024 * 200);

        // Allow usage of 80% of considered memory
        (mem_considered as f64 * 0.8) as resource::rlim_t
    }

    /// Set memory limit for the current process
    fn set_memory_limit() {
        let limit = Self::memory_limit();

        let msg = b"Setting process memory limit\n";
        unsafe {
            let _ = libc::write(libc::STDERR_FILENO, msg.as_ptr() as *const _, msg.len());
        }

        if resource::setrlimit(resource::Resource::RLIMIT_AS, limit, limit).is_err() {
            let msg = b"Error setrlimit(RLIMIT_AS)\n";
            unsafe {
                let _ = libc::write(libc::STDERR_FILENO, msg.as_ptr() as *const _, msg.len());
            }
        }
    }

    fn seccomp_filter(&self) -> Result<ScmpFilterContext, SeccompError> {
        // Using `KillProcess` allows rejected syscalls to be logged by auditd. But it
        // doesn't work with tools like valgrind. That's why it's not used by default.
        let mut filter = if std::env::var("GLYCIN_SECCOMP_DEFAULT_ACTION")
            .ok()
            .as_deref()
            == Some("KILL_PROCESS")
        {
            ScmpFilterContext::new(ScmpAction::KillProcess)?
        } else {
            ScmpFilterContext::new(ScmpAction::Trap)?
        };

        let mut syscalls = vec![ALLOWED_SYSCALLS];
        if self.config_entry.fontconfig() {
            // Enable some write operations for fontconfig to update its cache
            syscalls.push(ALLOWED_SYSCALLS_FONTCONFIG);
        }

        for syscall_name in syscalls.into_iter().flatten() {
            let syscall = ScmpSyscall::from_name(syscall_name)?;
            filter.add_rule(ScmpAction::Allow, syscall)?;
        }

        Ok(filter)
    }

    /// Make seccomp filters available under FD
    ///
    /// Bubblewrap supports taking an fd to seccomp filters in the BPF format.
    #[deprecated(note = "No longer used; native_sandbox applies filter directly")]
    fn seccomp_export_bpf(_filter: &ScmpFilterContext) -> Result<Memfd, Error> {
        Err(Error::from(io::Error::new(
            io::ErrorKind::Other,
            "seccomp_export_bpf is not used in native_sandbox",
        )))
    }

    /// Returns `true` if native_sandbox syscalls are blocked
    pub async fn check_native_sandbox_syscalls_blocked() -> bool {
        //TODO: check seccomp here
        true
    }

    async fn check_native_sandbox_syscalls_blocked_internal() -> Result<bool, Error> {
        let config_entry = ConfigEntry::Loader(ImageLoaderConfig {
            exec: PathBuf::from("/bin/true"),
            expose_base_dir: false,
            fontconfig: false,
        });

        let (dbus_socket, _) = UnixStream::pair()?;
        let sandbox = Self::new(SandboxMechanism::NativeSandbox, config_entry, dbus_socket);

        let mut command = sandbox.native_sandbox_command().await?;

        tracing::debug!("Testing native_sandbox availability with: {command:?}");

        let output = spawn_blocking(move || command.output()).await?;

        tracing::debug!("native_sandbox availability test returned: {output:?}");

        if output.status.success() {
            Ok(false)
        } else {
            if matches!(output.status.signal(), Some(libc::SIGSYS)) {
                tracing::debug!("native_sandbox syscalls not available: Terminated with SIGSYS");
                Ok(true)
            } else {
                Ok(false)
            }
        }
    }
}

#[derive(Debug, Default)]
struct SystemSetup {
    // Dirs that need to be symlinked (UsrMerge)
    lib_symlinks: Vec<(PathBuf, PathBuf)>,
    // Dirs that need mounting (not UsrMerged)
    lib_dirs: Vec<PathBuf>,
}

impl SystemSetup {
    async fn cached() -> SystemSetupStore {
        let mut system_setup = SYSTEM_SETUP.lock().await;

        if let Some(arc) = &*system_setup {
            arc.clone()
        } else {
            let arc = Arc::new(Self::new().await.map_err(Arc::new));

            *system_setup = Some(arc.clone());

            arc
        }
    }

    async fn new() -> io::Result<SystemSetup> {
        let mut system = SystemSetup::default();

        system.load_lib_dirs().await?;

        Ok(system)
    }

    async fn load_lib_dirs(&mut self) -> io::Result<()> {
        let dir_content = std::fs::read_dir("/");

        match dir_content {
            Ok(dir_content) => {
                for entry in dir_content {
                    if let Err(err) = self.add_dir(entry).await {
                        tracing::warn!("Unable to access entry in root directory (/): {err}");
                    }
                }
            }
            Err(err) => {
                tracing::error!("Unable to list root directory (/) entries: {err}");
            }
        }

        Ok(())
    }

    async fn add_dir(&mut self, entry: io::Result<DirEntry>) -> io::Result<()> {
        let entry = entry?;
        let path = entry.path();

        if let Some(last_segment) = path.file_name() {
            if last_segment.as_encoded_bytes().starts_with(b"lib") {
                let metadata = entry.metadata()?;
                if metadata.is_dir() {
                    // Lib dirs like /lib
                    self.lib_dirs.push(entry.path());
                } else if metadata.is_symlink() {
                    // Symlinks like /lib -> /usr/lib
                    let target = canonicalize(&path)?;
                    // Only use symlinks that link somewhere into /usr/
                    if target.starts_with("/usr/") {
                        self.lib_symlinks.push((path, target));
                    }
                }
            }
        };

        Ok(())
    }
}
