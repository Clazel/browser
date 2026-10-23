//! `clazel URL SCRIPT`: open a tab at URL running SCRIPT (operations, one per
//! line, in `clazel-renderer`'s format) and print what the renderer and the
//! kernel say to each other. The renderer is `$CLAZEL_RENDERER`, or
//! `clazel-renderer` next to this binary.

use std::path::PathBuf;
use std::process::{Command, ExitCode};
use std::time::Duration;

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().collect();
    let (Some(url), Some(script)) = (args.get(1), args.get(2)) else {
        eprintln!("usage: clazel URL SCRIPT");
        return ExitCode::from(2);
    };
    let renderer: PathBuf = std::env::var_os("CLAZEL_RENDERER").map(PathBuf::from).unwrap_or_else(|| {
        std::env::current_exe().map_or_else(|_| PathBuf::from("clazel-renderer"), |p| p.with_file_name("clazel-renderer"))
    });
    let mut host = clazel::Host::new(move |_| Command::new(&renderer));
    host.open_tab(url, script);
    if host.live() == 0 {
        eprintln!("clazel: the kernel did not start a renderer for {url}");
        return ExitCode::FAILURE;
    }
    if host.run(Duration::from_secs(30)) {
        ExitCode::SUCCESS
    } else {
        eprintln!("clazel: a renderer is still running after 30 s");
        ExitCode::FAILURE
    }
}
