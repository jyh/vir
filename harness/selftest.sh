#!/bin/bash
# vir harness selftest. Expected counts are DERIVED from how the fixture is built (idiom law 1), never typed.
# Arms: (1) an empty arm reads 0 with state EMPTY, never an error; (2) a fixture with N casts, K aux rules,
# one non-standard axiom and B build logs reads exactly those; (3) RED BACKWARDS: the same run with the cast
# regex broken (the mutant) must FAIL arm 2.  rc 0 = every arm as expected.
set -u
H=$(cd "$(dirname "$0")" && pwd)
F=$(mktemp -d "${TMPDIR:-/tmp}/virharness.XXXXXX")
fail=0
say() { echo "$1"; }

# (1) empty arm
out=$(python3 "$H/count.py" --arm lean "$F/none"); rc=$?
if [ $rc -eq 0 ] && [ "$(printf '%s\n' "$out" | awk -F'\t' '$4=="EMPTY" && $3==0' | wc -l | tr -d ' ')" -ge 5 ] \
   && ! printf '%s\n' "$out" | awk -F'\t' '$4=="MEASURED"' | grep -q .; then say "ARM1 empty-arm OK"; else say "ARM1 empty-arm FAIL rc=$rc"; fail=1; fi

# (2) a fixture whose counts are fixed by its construction
N=7; K=3; B=4
mkdir -p "$F/a/out" "$F/a/VIR" "$F/a/logs"
: > "$F/a/out/terms.txt"
toks=(HEq cast Eq.mpr ▸ Eq.rec heq_of_eq Nat.sub_sub)
i=0; while [ $i -lt $N ]; do printf 'theorem t%d := %s x  -- decoy: castle Eq.mprX recast\n' $i "${toks[$((i % ${#toks[@]}))]}" >> "$F/a/out/terms.txt"; i=$((i+1)); done
: > "$F/a/VIR/Rules.lean"
i=0; while [ $i -lt $K ]; do printf 'theorem aux_r%d : True := trivial\n' $i >> "$F/a/VIR/Rules.lean"; i=$((i+1)); done
printf 'theorem aux_unused : True := trivial\n' >> "$F/a/VIR/Rules.lean"
uses=""; i=0; while [ $i -lt $K ]; do uses="$uses aux_r$i"; i=$((i+1)); done
printf 'theorem router_fusion : True := by\n  have := (by omega)\n  exact%s\n' "$uses" >> "$F/a/VIR/Rules.lean"
printf 'theorem router_fusion_casesplit : True := by\n  exact aux_unused (by omega)\n' >> "$F/a/VIR/Rules.lean"
printf "'slice_fuse' depends on axioms: [propext, Classical.choice, Quot.sound, sorryAx]\n" > "$F/a/out/axioms.txt"
i=0; while [ $i -lt $B ]; do printf 'noise\nsaltbuild EXIT=%d\n' $((i % 2)) > "$F/a/logs/b$i.log"; i=$((i+1)); done

check2() { # $1 = count.py path
  local o; o=$(python3 "$1" --arm lean "$F/a") || return 1
  local g; g() { printf '%s\n' "$o" | awk -F'\t' -v c="$1" '$2==c{print $3}'; }
  [ "$(g C1)" = "$N" ] && [ "$(g C3)" = "$K" ] && [ "$(g C3declared)" = "$((K+1))" ] && [ "$(g C4)" = 1 ] \
    && [ "$(g C6)" = "$B" ] && [ "$(g C2cond)" = 1 ] && [ "$(g C2)" = 1 ] 
}
if check2 "$H/count.py"; then say "ARM2 fixture OK (C1=$N C3=$K C4=1 C6=$B)"; else say "ARM2 fixture FAIL"; fail=1; fi

# (3) mutant: drop HEq from the cast class; arm 2 must go red
sed 's/(HEq|cast|/(cast|/' "$H/count.py" > "$F/mutant.py"
if cmp -s "$H/count.py" "$F/mutant.py"; then say "ARM3 mutant NOT PLANTED (sed matched nothing)"; fail=1
elif check2 "$F/mutant.py"; then say "ARM3 mutant SURVIVED (the check cannot fail)"; fail=1
else say "ARM3 mutant KILLED"; fi

find "${F:?}" -delete
echo "SELFTEST rc=$fail"
exit $fail
