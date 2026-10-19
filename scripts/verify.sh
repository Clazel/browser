#!/usr/bin/env bash
# Runs every check in docs/VERIFICATION.md. The checks live in xtask/;
# this wrapper keeps the documented command the same. Exit codes:
#   0  all checks ran and passed
#   1  a check failed
#   2  no failures, but some checks were skipped because a tool is missing
#      (never report this as "verified")
set -uo pipefail
cd "$(dirname "$0")/.."
exec cargo xtask verify "$@"
