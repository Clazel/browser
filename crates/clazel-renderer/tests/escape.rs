//! Sandbox escape attempts from a real sandboxed process (phase-2.md item
//! 2.16): `clazel-adversary` enters the sandbox as the renderer does, makes
//! one call that would reach something other than its socket, and the test
//! judges how it ended.
//!
//! - **macOS (Seatbelt):** the call returns an error (`DENIED`, exit 0).
//! - **Linux (seccomp):** the filter kills the process with `SIGSYS` (signal
//!   31) on the forbidden call; *only* that passes. An error return is a
//!   failure there (it would mean the call got past seccomp), and so is a
//!   renderer that fails closed before the call (`FAILED-CLOSED`): the test
//!   cannot show anything then, which is what happens on a runner that
//!   restricts unprivileged user namespaces (see the 2.16 section of
//!   docs/phases/phase-2.md). The Linux half has not been run (written on a
//!   Mac; CI is its first run).
//!
//! Each attempt first runs unsandboxed (`control`) against a target of its own
//! and must succeed, so a denial is the sandbox's and not a wrong path. Not
//! covered, because neither `std` nor `clazel-sys` can express them: `fork`
//! and `ptrace` of a sibling.

use std::fs;
use std::net::TcpListener;
use std::os::unix::net::UnixListener;
use std::os::unix::process::ExitStatusExt;
use std::path::PathBuf;
use std::process::{Command, Output};

use clazel_renderer::escape::Attempt;

const ADVERSARY: &str = env!("CARGO_BIN_EXE_clazel-adversary");
/// `SIGSYS`, which seccomp's `SECCOMP_RET_KILL_PROCESS` raises.
const SIGSYS: i32 = 31;

/// A scratch directory with a short path (a Unix socket's path is limited to
/// about 100 bytes, which `CARGO_TARGET_TMPDIR` can exceed).
fn scratch(attempt: Attempt) -> PathBuf {
    let dir = std::env::temp_dir().join(format!(
        "clazel-escape-{}-{}",
        std::process::id(),
        attempt.name()
    ));
    let _ = fs::remove_dir_all(&dir);
    let _ = fs::create_dir_all(&dir);
    dir
}

fn adversary(mode: &str, attempt: Attempt, target: &str) -> Output {
    let out = Command::new(ADVERSARY)
        .args([mode, attempt.name(), target])
        .output();
    assert!(out.is_ok(), "cannot run {ADVERSARY}: {out:?}");
    out.unwrap_or(Output {
        status: ExitStatusExt::from_raw(0),
        stdout: Vec::new(),
        stderr: Vec::new(),
    })
}

fn text(out: &Output) -> String {
    format!(
        "status {:?}, stdout {:?}, stderr {:?}",
        out.status,
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    )
}

/// What a listener the test keeps alive and the target for `attempt` are.
/// Returns the target the control run and the sandboxed run use.
fn targets(
    attempt: Attempt,
    dir: &std::path::Path,
) -> (String, String, Vec<Box<dyn std::any::Any>>) {
    let p = |name: &str| dir.join(name).to_string_lossy().into_owned();
    let mut keep: Vec<Box<dyn std::any::Any>> = Vec::new();
    let (control, sandboxed) = match attempt {
        Attempt::OpenCookieJar => {
            let jar = p("cookie-jar");
            let _ = fs::write(&jar, "session=secret");
            (jar.clone(), jar)
        }
        Attempt::OpenFile => ("/etc/hosts".to_owned(), "/etc/hosts".to_owned()),
        Attempt::CreateFile => (p("control-new-file"), p("new-file")),
        Attempt::TcpConnect => {
            let listener = TcpListener::bind("127.0.0.1:0");
            let addr = listener
                .as_ref()
                .ok()
                .and_then(|l| l.local_addr().ok())
                .map_or_else(String::new, |a| a.to_string());
            keep.push(Box::new(listener));
            (addr.clone(), addr)
        }
        Attempt::TcpListen => ("127.0.0.1:0".to_owned(), "127.0.0.1:0".to_owned()),
        Attempt::UdpBind => ("127.0.0.1:0".to_owned(), "127.0.0.1:0".to_owned()),
        Attempt::UnixConnect => {
            let listener = UnixListener::bind(p("sock"));
            keep.push(Box::new(listener));
            (p("sock"), p("sock"))
        }
        Attempt::UnixListen => (p("control-listen"), p("listen")),
        Attempt::Execve => ("/bin/echo".to_owned(), "/bin/echo".to_owned()),
    };
    (control, sandboxed, keep)
}

fn escape_attempt_is_stopped(attempt: Attempt) {
    let dir = scratch(attempt);
    let (control_target, target, _keep) = targets(attempt, &dir);

    let control = adversary("control", attempt, &control_target);
    assert!(
        control.status.code() == Some(3)
            && String::from_utf8_lossy(&control.stdout).starts_with("ESCAPED"),
        "{}: the attempt does not even work outside the sandbox, so a denial would prove nothing: {}",
        attempt.name(),
        text(&control)
    );

    let sandboxed = adversary("escape", attempt, &target);
    let stdout = String::from_utf8_lossy(&sandboxed.stdout).into_owned();
    let stderr = String::from_utf8_lossy(&sandboxed.stderr);
    assert!(
        !stderr.contains("FAILED-CLOSED"),
        "{}: the renderer failed closed before the attempt, so nothing was tried: {}",
        attempt.name(),
        text(&sandboxed)
    );
    assert!(
        !stdout.contains("ESCAPED"),
        "{}: ESCAPED: {}",
        attempt.name(),
        text(&sandboxed)
    );
    let how = if cfg!(target_os = "linux") {
        // Only a seccomp kill passes: an error return means the call got past it.
        assert_eq!(
            sandboxed.status.signal(),
            Some(SIGSYS),
            "{}: {}",
            attempt.name(),
            text(&sandboxed)
        );
        "killed by SIGSYS".to_owned()
    } else {
        assert!(
            sandboxed.status.code() == Some(0) && stdout.starts_with("DENIED"),
            "{}: {}",
            attempt.name(),
            text(&sandboxed)
        );
        format!("error return: {}", stdout.trim())
    };
    println!("escape: {} stopped ({how})", attempt.name());
    // The attempt left nothing behind that it should not have made.
    assert!(
        !dir.join("new-file").exists() && !dir.join("listen").exists(),
        "{}: the sandboxed process created a file",
        attempt.name()
    );
    let _ = fs::remove_dir_all(&dir);
}

macro_rules! escape_tests {
    ($($name:ident: $attempt:expr,)*) => {$(
        #[test]
        #[cfg_attr(miri, ignore = "spawns a process and calls the OS sandbox")]
        fn $name() {
            escape_attempt_is_stopped($attempt);
        }
    )*};
}

escape_tests! {
    cannot_open_the_cookie_jars_would_be_file: Attempt::OpenCookieJar,
    cannot_open_any_file: Attempt::OpenFile,
    cannot_create_a_file: Attempt::CreateFile,
    cannot_connect_to_a_tcp_listener: Attempt::TcpConnect,
    cannot_listen_on_a_tcp_port: Attempt::TcpListen,
    cannot_bind_a_udp_socket: Attempt::UdpBind,
    cannot_connect_to_a_unix_socket: Attempt::UnixConnect,
    cannot_create_a_unix_socket: Attempt::UnixListen,
    cannot_execute_a_program: Attempt::Execve,
}
