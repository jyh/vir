#!/bin/bash
# vir: re-derive EVERY committed count file from the arms' artifacts and diff (STATUS-vir row 30).
# rc 0 = every file reproduces byte-for-byte; rc 1 = a named file does not; rc 2 = an input is missing.
# Usage: harness/reproduce.sh [MOJAVE_ROOT]   (default ~/projects/claude/seats/mojave)
# LIMIT, printed with the verdict: it re-derives what count.py extracts. It does not rebuild Lean (judge a
# build by its saltbuild EXIT line) and does not re-run MetaPRL's verdict.sh; rows marked Q stay Q.
set -u
V=$(cd "$(dirname "$0")/.." && pwd)
M=${1:-$HOME/projects/claude/seats/mojave}
C="$V/harness/count.py"
[ -d "$V/lean" ] && [ -d "$M/vir-metaprl" ] || { echo "REPRODUCE MISSING-INPUT lean=$V/lean metaprl=$M"; exit 2; }
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
if [ -d "$SP/.git" ]; then chk "$V/harness/compiler-counts.tsv" --arm compiler --sha 2c0b05943f520ca99bf77bfd8cb1c9f6d3686a59 --compose "$V/compose" "$SP"
else echo "  MISSING  spike repo $SP (compiler rows not re-derived)"; fail=1; fi
echo "REPRODUCE files=$n rc=$fail (limit: extraction only; no rebuild, no verdict re-run; Q rows stay Q)"
exit $fail
