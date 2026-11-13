#!/usr/bin/env bash
# logged-build.sh NAME [saltbuild args...] — run ONE saltbuild invocation into k7/logs/NAME.log.
#
# WHY: K5 runs (STATUS-vir 295) are counted by counting `saltbuild EXIT=` lines across k5/logs/*.log.
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
# From k7-001 on (k5/LOGS-FILTER.md; k7 uses it from its first log, compiler/DECLARATIONS-K7.md): saltbuild writes to a raw file outside the tree, and the committed log is
# that file with each REPLAYED module's re-printed warning body replaced by one hash line (tools/replay_filter.py). Header lines,
# every line containing "error", and the `saltbuild EXIT=` line are copied byte for byte. If the filter fails, the RAW log is kept.
raw=$(mktemp "${TMPDIR:-/tmp}/logged-build-$name.XXXXXX") || { echo "logged-build: no raw temp file" >&2; exit 5; }
cd "$lean" && "$sb" "$@" >| "$raw" 2>&1
rc=$?
if ! python3 -I "$here/../k5/tools/replay_filter.py" "$raw" - >> "$log"; then
  echo "logged-build: replay_filter FAILED; the raw log is kept whole" >&2
  : >| "$log"; cat "$raw" >> "$log"
fi
rm -f -- "${raw:?}"
grep -F 'saltbuild EXIT=' "$log" | tail -1
exit $rc
