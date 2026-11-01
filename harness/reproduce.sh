#!/bin/bash
# vir: re-derive EVERY committed count file from the arms' artifacts and diff (STATUS-vir row 30).
# rc 0 = every file reproduces byte-for-byte; rc 1 = a named file does not; rc 2 = an input is missing.
# Usage: harness/reproduce.sh [MOJAVE_ROOT]   (a dir holding clones of vir-metaprl and vir-arm-tools; both are read at pinned shas)
# LIMIT, printed with the verdict: it re-derives what count.py extracts. It does not rebuild Lean (judge a
# build by its saltbuild EXIT line) and does not re-run MetaPRL's verdict.sh; rows marked Q stay Q.
set -u
V=$(cd "$(dirname "$0")/.." && pwd)
M0=${1:-$HOME/projects/claude/seats/mojave}
C="$V/harness/count.py"
[ -d "$V/lean" ] && [ -d "$M0/vir-metaprl" ] || { echo "REPRODUCE MISSING-INPUT lean=$V/lean metaprl=$M0"; exit 2; }
# FINDINGS V-F2: the MetaPRL arm is read at PINNED commits, never from its working tree (which carries
# uncommitted edits). Both repos are cloned at the pins into a scratch dir; override with the env vars.
METAPRL_SHA=${METAPRL_SHA:-81e0317b0c2b356491cffcb06f771d89a524761f}
# Since 2026-11-01 the arm's tools are a snapshot INSIDE the metaprl branch (theories/vir/vir-arm-tools), so one pin covers
# both. TOOLS_SHA, if set, reads a separate vir-arm-tools clone instead (the layout before the snapshot).
M=$(mktemp -d "${TMPDIR:-/tmp}/vir-repro-mj.XXXXXX")
git clone -q --no-checkout "$M0/vir-metaprl" "$M/vir-metaprl" 2>/dev/null && git -C "$M/vir-metaprl" checkout -q "$METAPRL_SHA" 2>/dev/null \
  || { echo "REPRODUCE MISSING-INPUT vir-metaprl at $METAPRL_SHA (from $M0/vir-metaprl)"; exit 2; }
if [ -n "${TOOLS_SHA:-}" ]; then
  git clone -q --no-checkout "$M0/vir-arm-tools" "$M/vir-arm-tools" 2>/dev/null && git -C "$M/vir-arm-tools" checkout -q "$TOOLS_SHA" 2>/dev/null \
    || { echo "REPRODUCE MISSING-INPUT vir-arm-tools at $TOOLS_SHA"; exit 2; }
else
  [ -d "$M/vir-metaprl/theories/vir/vir-arm-tools" ] || { echo "REPRODUCE MISSING-INPUT no theories/vir/vir-arm-tools at $METAPRL_SHA"; exit 2; }
  ln -s "$M/vir-metaprl/theories/vir/vir-arm-tools" "$M/vir-arm-tools"
fi
echo "  PINNED   metaprl vir-metaprl@${METAPRL_SHA:0:12} vir-arm-tools@${TOOLS_SHA:-in-tree} (from $M0)"
fail=0; n=0
chk() {  # chk <committed-file> <count.py args...>
  local f=$1; shift; n=$((n+1))
  if [ ! -f "$f" ]; then echo "  MISSING  ${f#$V/}"; fail=1; return; fi
  if python3 "$C" "$@" | cmp -s - "$f"; then echo "  SAME     ${f#$V/}"
  else echo "  DIFF     ${f#$V/}"; python3 "$C" "$@" | diff "$f" - | sed 's/^/           /'; fail=1; fi
}
chk "$V/lean/out/counts.tsv"                    --arm lean --program 1 "$V/lean"
chk "$V/lean/out/counts-program2.tsv"           --arm lean --program 2 "$V/lean"
chk "$V/lean/out/counts-program3.tsv"           --arm lean --program 3 "$V/lean"
chk "$V/harness/metaprl-counts-2026-11-01.tsv"  --arm metaprl --program 1 "$M"
chk "$V/harness/metaprl-counts-program2.tsv"    --arm metaprl --program 2 "$M"
chk "$V/harness/metaprl-counts-program3.tsv"    --arm metaprl --program 3 "$M"
# the spike: branch spike/o95-router of github.com/jyh/x86lean (pins are the rewritten spike shas; old d7e992c = 87a17ab, 7241997 = adbf22f)
SP=${SPIKE:-$HOME/projects/claude/x86lean}
if [ -d "$SP/.git" ]; then chk "$V/harness/compiler-counts.tsv" --arm compiler --sha 87a17abad077cc33eefab5895c786f4f70586a0b --compose "$V/compose" --compose-sha 1740c5678264d216703c39748f496fe99aa27178 "$SP"
  # row 53: the two-call cost, at spike adbf22f (old 7241997) (Router/MultiCall.lean) + vir ed68a89 (compose/RateLimit.lean)
  chk "$V/harness/compiler-counts-multicall.tsv" --arm compiler --sha adbf22f995d226e700b5d45735cab2b04d509112 --compose "$V/compose" --compose-sha ed68a898723f2ef392ae05ccb97f696898e0695a "$SP"
else echo "  MISSING  spike repo $SP (compiler rows not re-derived)"; fail=1; fi
# row 46: the axiom gate over the newest compose audit and the clean-rebuild Lean audit
for L in "$(ls "$V"/compose/logs/audit-*.log 2>/dev/null | sort | tail -1)" "$V/lean/repro/audit-control-002.log"; do
  NC=   # row 48: vir's Lean audit now has a control run (AuditControl.lean); --no-control stays in the tool, unused here
  n=$((n+1)); python3 "$V/harness/axiom_gate.py" $NC "$L" > "${TMPDIR:-/tmp}/vir-ag.$$" 2>&1; r=$?   # rc of the GATE, not of a pipe
  sed 's/^/  /' "${TMPDIR:-/tmp}/vir-ag.$$"; [ $r -eq 0 ] || fail=1
done
echo "REPRODUCE files=$n rc=$fail (limit: extraction only; no rebuild, no verdict re-run; Q rows stay Q)"
exit $fail
