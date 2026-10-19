#!/usr/bin/env bash
# Installs every pinned tool in scripts/toolchains.env, so that
# `scripts/setup.sh && scripts/verify.sh` works on a machine that has only
# rustup. Safe to re-run: tools already at the pinned version are skipped.
# Never uses sudo.
#
# Downloads are checked against scripts/checksums.txt before use.
#
# Supported: macOS arm64, macOS x86-64, Linux x86-64.
#
# Where things go (override with the environment variables shown):
#   CLAZEL_TOOLS_DIR  Verus releases and the download cache
#                     (default ~/.local/share/clazel-tools)
#   CLAZEL_BIN_DIR    `verus` and `cargo-verus` links
#                     (default $CARGO_HOME/bin, which rustup puts on PATH)
#   KANI_HOME         Kani's bundle (Kani's own variable; default ~/.kani)
#   CARGO_INSTALL_ROOT  where `cargo install` puts Kani's launcher (cargo's own)
set -euo pipefail
cd "$(dirname "$0")/.."
# shellcheck source=toolchains.env
. scripts/toolchains.env

TOOLS_DIR=${CLAZEL_TOOLS_DIR:-$HOME/.local/share/clazel-tools}
BIN_DIR=${CLAZEL_BIN_DIR:-${CARGO_HOME:-$HOME/.cargo}/bin}
DOWNLOADS=$TOOLS_DIR/downloads
KANI_DIR=${KANI_HOME:-$HOME/.kani}/kani-$KANI_VERSION

say() { printf '==> %s\n' "$*"; }
die() { printf 'setup.sh: error: %s\n' "$*" >&2; exit 1; }

for tool in rustup cargo curl unzip tar; do
  command -v "$tool" >/dev/null || die "$tool is required but not installed"
done

case "$(uname -s)-$(uname -m)" in
  Darwin-arm64)  VERUS_PLATFORM=arm64-macos; KANI_TARGET=aarch64-apple-darwin ;;
  Darwin-x86_64) VERUS_PLATFORM=x86-macos;   KANI_TARGET=x86_64-apple-darwin ;;
  Linux-x86_64)  VERUS_PLATFORM=x86-linux;   KANI_TARGET=x86_64-unknown-linux-gnu ;;
  Linux-aarch64) die "Verus publishes no Linux arm64 release; building Verus from source is not automated yet" ;;
  *)             die "unsupported platform: $(uname -s) $(uname -m)" ;;
esac

sha256() {
  if command -v sha256sum >/dev/null; then sha256sum "$1" | cut -d' ' -f1
  else shasum -a 256 "$1" | cut -d' ' -f1; fi
}

# fetch URL NAME: download NAME into the cache (reusing a cached copy only
# if it still matches) and check it against scripts/checksums.txt.
fetch() {
  local url=$1 name=$2 dest want got
  dest=$DOWNLOADS/$name
  want=$(awk -v f="$name" '$2 == f { print $1 }' scripts/checksums.txt)
  [ -n "$want" ] || die "no checksum for $name in scripts/checksums.txt"
  mkdir -p "$DOWNLOADS"
  if [ -f "$dest" ] && [ "$(sha256 "$dest")" = "$want" ]; then
    say "using cached $name (checksum ok)"
    return
  fi
  say "downloading $name"
  curl -fSL --retry 3 --progress-bar -o "$dest.part" "$url"
  got=$(sha256 "$dest.part")
  if [ "$got" != "$want" ]; then
    rm -f "$dest.part"
    die "checksum mismatch for $name: expected $want, got $got. Nothing was installed."
  fi
  mv "$dest.part" "$dest"
  say "checksum ok: $name"
}

# 1. Rust: the pinned stable (builds, clippy, Verus) and nightly (Miri).
say "Rust $RUST_TOOLCHAIN"
rustup toolchain install "$RUST_TOOLCHAIN" --profile minimal --component rustfmt --component clippy
say "Rust $MIRI_NIGHTLY with Miri"
rustup toolchain install "$MIRI_NIGHTLY" --profile minimal --component miri --component rust-src
cargo "+$MIRI_NIGHTLY" miri setup

# 2. Kani. Its launcher comes from crates.io (cargo checks crate checksums
#    against the registry index); its bundle is downloaded here and
#    checksummed, rather than by `cargo kani setup`, which would not check it.
# (Output is captured before grep: `cmd | grep -q` fails under pipefail.)
installed=$(cargo install --list)
if grep -qx "kani-verifier v$KANI_VERSION:" <<<"$installed" && [ -d "$KANI_DIR" ]; then
  say "Kani $KANI_VERSION already installed"
else
  say "Kani $KANI_VERSION"
  cargo install --locked kani-verifier --version "$KANI_VERSION"
  bundle=kani-$KANI_VERSION-$KANI_TARGET.tar.gz
  fetch "https://github.com/model-checking/kani/releases/download/kani-$KANI_VERSION/$bundle" "$bundle"
  rm -rf "$KANI_DIR"
  cargo kani setup --use-local-bundle "$DOWNLOADS/$bundle"
fi

# 3. Verus, unpacked into its own versioned directory and linked into BIN_DIR.
verus_dir=$TOOLS_DIR/verus-$VERUS_VERSION
if [ -x "$verus_dir/verus" ]; then
  say "Verus $VERUS_VERSION already unpacked"
else
  say "Verus $VERUS_VERSION"
  zip=verus-$VERUS_VERSION-$VERUS_PLATFORM.zip
  fetch "https://github.com/verus-lang/verus/releases/download/release/$VERUS_VERSION/$zip" "$zip"
  staging=$(mktemp -d "$TOOLS_DIR/.unpack.XXXXXX")
  unzip -q "$DOWNLOADS/$zip" -d "$staging"
  [ -x "$staging/verus-$VERUS_PLATFORM/verus" ] || die "unexpected layout in $zip"
  rm -rf "$verus_dir"
  mv "$staging/verus-$VERUS_PLATFORM" "$verus_dir"
  rmdir "$staging"
fi
mkdir -p "$BIN_DIR"
for bin in verus cargo-verus; do
  link=$BIN_DIR/$bin
  if [ -e "$link" ] && [ ! -L "$link" ]; then
    die "$link exists and is not a symlink; remove it and re-run"
  fi
  ln -sfn "$verus_dir/$bin" "$link"
done

# 4. Report what is now installed, so a mismatch is visible right away.
say "installed:"
rustc "+$RUST_TOOLCHAIN" --version
kani_version=$(cargo kani --version)
printf '%s\n' "${kani_version%%$'\n'*}"
"$BIN_DIR/verus" --version 2>&1 | grep -E '^\s*Version:'
case ":$PATH:" in
  *":$BIN_DIR:"*) ;;
  *) say "note: add $BIN_DIR to PATH so cargo finds verus and cargo-verus" ;;
esac
say "done. Next: scripts/verify.sh"
