#!/usr/bin/env bash
# logged-build.sh NAME [saltbuild args...] — run ONE saltbuild invocation into bridge/logs/NAME.log.
#
# WHY: the bridge's runs (STATUS-vir 286) is counted by counting `saltbuild EXIT=` lines across bridge/logs/*.log.
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
cd "$lean" && "$sb" "$@" >> "$log" 2>&1
rc=$?
grep -F 'saltbuild EXIT=' "$log" | tail -1
exit $rc
