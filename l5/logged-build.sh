#!/usr/bin/env bash
# logged-build.sh NAME [saltbuild args...] — run ONE saltbuild invocation into l5/logs/NAME.log.
#
# WHY: C6 for layer L5 (amend-24) is counted by counting `saltbuild EXIT=` lines across l5/logs/*.log.
# A run whose log is written over is a run the count can no longer see. On 2026-11-01 three runs were lost that way
# (build-029 twice; RESULTS-4), so B.C6 counts LOGGED runs only and two per-program C6 figures are the author's.
# This wrapper makes the rule a refusal rather than a habit:
#   - NAME must be new: an existing logs/NAME.log is REFUSED (rc 3) before saltbuild is touched;
#   - the log is opened with noclobber, so a race between two invocations cannot overwrite either;
#   - the wrapper's rc is saltbuild's own rc (never a pipe stage's).
# Judge the build by the log's `saltbuild EXIT=N` line, as the build law says, never by this script's output.
set -u
here=$(cd "$(dirname "$0")" && pwd)
lean=$here
name=${1:?usage: logged-build.sh NAME [saltbuild args...]}
shift
case $name in
  */*|*.log|'') echo "logged-build: NAME is a bare name (no slash, no .log): '$name'" >&2; exit 2 ;;
esac
logs=${LOGDIR:-$here/logs}   # LOGDIR exists for the selftest only; a real run never sets it
log="$logs/$name.log"
if [ -e "$log" ]; then
  echo "logged-build: REFUSED — $log exists; every saltbuild run gets its own log (C6 counts logged runs)" >&2
  exit 3
fi
sb=${SALTBUILD:-$here/../../saltbuild.sh}
[ -x "$sb" ] || { echo "logged-build: saltbuild not found at $sb" >&2; exit 4; }
set -o noclobber
: > "$log" || { echo "logged-build: REFUSED — could not create $log without clobbering" >&2; exit 3; }
# 2026-11-23 (axiom receipts are a TRIPLE): one header line (mode, targets or imports, library-source hash, start) BEFORE saltbuild,
# so harness/axiom_gate.py can check from the logs that a build covered the audit's imports over the same sources. A failed header is
# written as such and the gate refuses that log as a receipt; it never blocks the build.
python3 -I "$(git -C "$here" rev-parse --show-toplevel)/harness/build_header.py" "$lean" "$@" >> "$log" 2>/dev/null \
  || echo "logged-build: header FAILED (axiom_gate.py refuses this log as a receipt)" >> "$log"
cd "$lean" && "$sb" "$@" >> "$log" 2>&1
rc=$?
python3 -I "$(git -C "$here" rev-parse --show-toplevel)/harness/build_header.py" --end >> "$log" 2>/dev/null || true   # h2c F2: build END < audit START
grep -F 'saltbuild EXIT=' "$log" | tail -1
exit $rc
