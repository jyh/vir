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
METAPRL_SHA=${METAPRL_SHA:-26b4e01d6d8ddb2ba1641323ae4b5610a2ab53ef}
TOOLS_SHA=${TOOLS_SHA:-b754500}
M=$(mktemp -d "${TMPDIR:-/tmp}/vir-repro-mj.XXXXXX")
for pair in "vir-metaprl:$METAPRL_SHA" "vir-arm-tools:$TOOLS_SHA"; do
  r=${pair%%:*}; s=${pair#*:}
  git clone -q --no-checkout "$M0/$r" "$M/$r" 2>/dev/null && git -C "$M/$r" checkout -q "$s" 2>/dev/null \
    || { echo "REPRODUCE MISSING-INPUT $r at $s (from $M0/$r)"; exit 2; }
done
echo "  PINNED   metaprl vir-metaprl@${METAPRL_SHA:0:12} vir-arm-tools@${TOOLS_SHA:0:12} (from $M0)"
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
SP=${SPIKE:-$HOME/projects/claude/wt/x86lean/o95-spike}
if [ -d "$SP/.git" ]; then chk "$V/harness/compiler-counts.tsv" --arm compiler --sha d7e992c802fcb430fafb50e41b5b7d36d9cd860c --compose "$V/compose" --compose-sha 1740c5678264d216703c39748f496fe99aa27178 "$SP"
  # row 53: the two-call cost, at spike 7241997 (Router/MultiCall.lean) + vir ed68a89 (compose/RateLimit.lean)
  chk "$V/harness/compiler-counts-multicall.tsv" --arm compiler --sha 724199731b33deab888ca747e08aa59585a1c27d --compose "$V/compose" --compose-sha ed68a898723f2ef392ae05ccb97f696898e0695a "$SP"
else echo "  MISSING  spike repo $SP (compiler rows not re-derived)"; fail=1; fi
# row 46: the axiom gate over the newest compose audit and the clean-rebuild Lean audit
for L in "$(ls "$V"/compose/logs/audit-*.log 2>/dev/null | sort | tail -1)" "$V/lean/repro/audit-control-002.log"; do
  NC=   # row 48: vir's Lean audit now has a control run (AuditControl.lean); --no-control stays in the tool, unused here
  n=$((n+1)); python3 "$V/harness/axiom_gate.py" $NC "$L" > "${TMPDIR:-/tmp}/vir-ag.$$" 2>&1; r=$?   # rc of the GATE, not of a pipe
  sed 's/^/  /' "${TMPDIR:-/tmp}/vir-ag.$$"; [ $r -eq 0 ] || fail=1
done
echo "REPRODUCE files=$n rc=$fail (limit: extraction only; no rebuild, no verdict re-run; Q rows stay Q)"
exit $fail
