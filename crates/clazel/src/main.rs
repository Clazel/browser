//! `clazel URL SCRIPT`: open a tab at URL running SCRIPT (operations, one per
//! line, in `clazel-renderer`'s format) and print what the renderer and the
//! kernel say to each other. The renderer is `$CLAZEL_RENDERER`, or
//! `clazel-renderer` next to this binary.

use std::process::{Command, ExitCode};
use std::time::Duration;

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().collect();
    let (Some(url), Some(script)) = (args.get(1), args.get(2)) else {
        eprintln!("usage: clazel URL SCRIPT");
        return ExitCode::from(2);
    };
    let next_to_me = std::env::current_exe().map(|p| p.with_file_name("clazel-renderer"));
    let renderer = std::env::var_os("CLAZEL_RENDERER")
        .map(Into::into)
        .or(next_to_me.ok());
    let mut host = clazel::Host::new(move |_| Command::new(renderer.clone().unwrap_or_default()));
    host.open_tab(url, script);
    if host.live() > 0 && host.run(Duration::from_secs(30)) {
        return ExitCode::SUCCESS;
    }
    eprintln!("clazel: no renderer started for {url}, or one is still running after 30 s");
    ExitCode::FAILURE
}
