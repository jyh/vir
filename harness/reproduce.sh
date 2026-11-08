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
# row 64 (amend-10, B′): the MetaPRL B′ arm at its own pin, public jyh/metaprl mojave/vir-arm since 2026-11-02 (a fast-forward
# of METAPRL_SHA). B is still read at METAPRL_SHA above, so no B row moves.
BPRIME_SHA=${BPRIME_SHA:-93ff6b7c08b7dc3a88c5de797b82b00cbc507e72}
git clone -q --no-checkout "$M0/vir-metaprl" "$M/bp/vir-metaprl" 2>/dev/null && git -C "$M/bp/vir-metaprl" checkout -q "$BPRIME_SHA" 2>/dev/null \
  || { echo "REPRODUCE MISSING-INPUT vir-metaprl at $BPRIME_SHA (B′)"; exit 2; }
echo "  PINNED   metaprl B′ vir-metaprl@${BPRIME_SHA:0:12}"
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
# amend-10: the Lean B′ mirror (lean/VIRB), read from its own logs
chk "$V/lean/VIRB/out/counts-bp.tsv" --arm leanbp "$V/lean/VIRB"
chk "$V/virp/out/counts-p.tsv" --arm leanp "$V/virp"
# amend-13: layer L1, the Lean arm (l1/VIRL1), read from its own logs AT THE SHA THAT WROTE ITS COUNTS (W3's extension commits
# and their logs must not move L1's close record: the row-45 defect, met again at W3 (i)/(ii)). The sha is DERIVED from git.
L1SHA=$(git -C "$V" log -1 --format=%H -- l1/out/counts-l1.tsv)
mkdir -p "$M/l1at" && git -C "$V" archive "$L1SHA" l1 | tar -x -C "$M/l1at" \
  || { echo "REPRODUCE MISSING-INPUT l1/ at $L1SHA"; exit 2; }
echo "  PINNED   l1/ at its counts commit ${L1SHA:0:12}"
chk "$V/l1/out/counts-l1.tsv" --arm l1 "$M/l1at/l1"
# amend-15: W3 on the Lean arm, one file per extension commit, each read from git at its pinned shas
chk "$V/l1/out/counts-w3-i.tsv"  --arm v3l1 --base b156167 --ext 21c2b97 --prefix l1/VIRL1 "$V"
chk "$V/l1/out/counts-w3-ii.tsv" --arm v3l1 --base 21c2b97 --ext ba9c696 --prefix l1/VIRL1 "$V"
# amend-17: W3 (iii), the BLIND extension (the sum type), on the Lean arm
chk "$V/l1/out/counts-w3-iii.tsv" --arm v3l1 --base 2fccab7 --ext 8c3320f --prefix l1/VIRL1 "$V"
# amend-16: layer L2, the Lean arm (l2/VIRL2), read from its own logs AT THE SHA THAT WROTE ITS COUNTS (derived from git, as L1)
L2SHA=$(git -C "$V" log -1 --format=%H -- l2/out/counts-l2.tsv)
mkdir -p "$M/l2at" && git -C "$V" archive "$L2SHA" l2 | tar -x -C "$M/l2at" \
  || { echo "REPRODUCE MISSING-INPUT l2/ at $L2SHA"; exit 2; }
echo "  PINNED   l2/ at its counts commit ${L2SHA:0:12}"
chk "$V/l2/out/counts-l2.tsv" --arm l2 "$M/l2at/l2"
# amend-16 Y2 = amend-13 W8: L1's definitions unedited from 37c209e to the Lean L2-closed sha
chk "$V/l2/out/counts-w8.tsv" --arm w8 --base 37c209e --ext dc95b53 --prefix l1/VIRL1 "$V"
chk "$V/harness/metaprl-counts-bprime.tsv" --arm metaprlbp "$M/bp"
# chk2 <committed-file> <shell command printing the file>: for count files that are TWO count.py calls concatenated
chk2() {
  local f=$1; shift; n=$((n+1))
  if [ ! -f "$f" ]; then echo "  MISSING  ${f#$V/}"; fail=1; return; fi
  if bash -c "$*" | cmp -s - "$f"; then echo "  SAME     ${f#$V/}"
  else echo "  DIFF     ${f#$V/}"; bash -c "$*" | diff "$f" - | sed 's/^/           /'; fail=1; fi
}
# amend-19: the Lean induction rule, read from l1/ AT ITS COUNTS COMMIT (later l1 logs must not move it), plus I1 by W8
INDSHA=$(git -C "$V" log -1 --format=%H -- l1/out/counts-ind.tsv)
mkdir -p "$M/indat" && git -C "$V" archive "$INDSHA" l1 | tar -x -C "$M/indat" \
  || { echo "REPRODUCE MISSING-INPUT l1/ at $INDSHA"; exit 2; }
echo "  PINNED   l1/ (amend-19) at its counts commit ${INDSHA:0:12}"
chk2 "$V/l1/out/counts-ind.tsv" "python3 '$C' --arm ind '$M/indat/l1' && python3 '$C' --arm w8 --base d6cb991 --ext 93efc67 --prefix l1/VIRL1 '$V' | sed 's/^w8\tW8\./ind\tIND.I1.W8./'"
# amend-18: layer L3, the Lean arm (l3/VIRL3), at its counts commit; Z1 = W8 over L2 and over L1, dc95b53 -> that commit
L3SHA=$(git -C "$V" log -1 --format=%H -- l3/out/counts-l3.tsv)
mkdir -p "$M/l3at" && git -C "$V" archive "$L3SHA" l3 | tar -x -C "$M/l3at" \
  || { echo "REPRODUCE MISSING-INPUT l3/ at $L3SHA"; exit 2; }
echo "  PINNED   l3/ at its counts commit ${L3SHA:0:12}"
chk "$V/l3/out/counts-l3.tsv" --arm l3 "$M/l3at/l3"
chk2 "$V/l3/out/counts-z1.tsv" "python3 '$C' --arm w8 --base dc95b53 --ext 037dddc --prefix l2/VIRL2 '$V' && python3 '$C' --arm w8 --base dc95b53 --ext 037dddc --prefix l1/VIRL1 '$V' | sed 's/\tW8\./\tW8.l1./'"
# the Lean L4 column (STATUS 168), at the sealed Lean tip's files; W8 from L3-closed to L4-closed on each lower layer
chk "$V/l4/out/counts-l4.tsv" --arm l4 "$V/l4"
chk2 "$V/l4/out/counts-q1.tsv" "for p in l1:VIRL1 l2:VIRL2 l3:VIRL3; do d=\${p%%:*}; python3 '$C' --arm w8 --base 7f82f94 --ext 400f863 --prefix \$d/\${p##*:} '$V' | sed \"s/\tW8\./\tQ1.\$d.W8./\"; done"
# row 46: the axiom gate over the newest compose audit and the clean-rebuild Lean audit
for L in "$(ls "$V"/compose/logs/audit-*.log 2>/dev/null | sort | tail -1)" "$V/lean/repro/audit-control-002.log"; do
  NC=   # row 48: vir's Lean audit now has a control run (AuditControl.lean); --no-control stays in the tool, unused here
  n=$((n+1)); python3 "$V/harness/axiom_gate.py" $NC "$L" > "${TMPDIR:-/tmp}/vir-ag.$$" 2>&1; r=$?   # rc of the GATE, not of a pipe
  sed 's/^/  /' "${TMPDIR:-/tmp}/vir-ag.$$"; [ $r -eq 0 ] || fail=1
done
echo "REPRODUCE files=$n rc=$fail (limit: extraction only; no rebuild, no verdict re-run; Q rows stay Q)"
exit $fail
