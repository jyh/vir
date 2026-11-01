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

# (4) the MetaPRL extractor on a fixture whose counts come from its construction
W=2; A=3; U=2; R=5
M="$F/m"; mkdir -p "$M/vir-metaprl/theories/vir" "$M/vir-arm-tools/steps"
: > "$M/vir-metaprl/theories/vir/vir.ml"
i=0; while [ $i -lt $A ]; do printf 'interactive_rw aux_m%d : x <--> x\n' $i >> "$M/vir-metaprl/theories/vir/vir.ml"; i=$((i+1)); done
printf 'prim_rw unproven : y <--> y\n' >> "$M/vir-metaprl/theories/vir/vir.ml"
: > "$M/vir-arm-tools/steps/c2-router.mp"
i=0; while [ $i -lt $U ]; do printf 'refine (rw aux_m%d 0);;\n' $i >> "$M/vir-arm-tools/steps/c2-router.mp"; i=$((i+1)); done
printf 'refine (rw unfold_read_u32 0);;\nrefine (rw unfold_vir_U 0);;\n' >> "$M/vir-arm-tools/steps/c2-router.mp"
: > "$M/vir-arm-tools/runs-c2-router.txt"
i=0; while [ $i -lt $W ]; do printf '   ....wf....\n....wf....\n' >> "$M/vir-arm-tools/runs-c2-router.txt"; i=$((i+1)); done
printf '   ....assertion....\n' >> "$M/vir-arm-tools/runs-c2-router.txt"
printf '=== CHILDREN 2: - wf assertion main\n=== CHILDREN 4: wf\n' >> "$M/vir-arm-tools/runs-c2-router.txt"
i=1; while [ $i -le $R ]; do printf '=== STEP 1 [ok] :: refine (x);;\n=== STEP 2 [ok] :: cd "1";;\n' > "$M/vir-arm-tools/runs-$(printf %02d $i).txt"; i=$((i+1)); done
o=$(python3 "$H/count.py" --arm metaprl "$M"); g4() { printf '%s\n' "$o" | awk -F'\t' -v c="$1" '$2==c{print $3}'; }
if [ "$(g4 C2wf)" = "$W" ] && [ "$(g4 C2cond)" = 1 ] && [ "$(g4 C3strict)" = "$U" ] && [ "$(g4 C3)" = "$((U+1))" ] \
   && [ "$(g4 C3declared)" = "$A" ] && [ "$(g4 C4)" = 1 ] && [ "$(g4 C6sessions)" = "$R" ] && [ "$(g4 C6refines)" = "$R" ] && [ "$(g4 C2genWf)" = 2 ] && [ "$(g4 C2gen)" = 3 ]; then
  say "ARM4 metaprl fixture OK"; else say "ARM4 metaprl fixture FAIL"; printf '%s\n' "$o"; fail=1; fi
o=$(python3 "$H/count.py" --arm metaprl "$F/none"); if printf '%s\n' "$o" | awk -F'\t' '$4!="EMPTY"' | grep -q .; then say "ARM5 empty metaprl FAIL"; fail=1; else say "ARM5 empty metaprl OK"; fi

# (6) the L-DEEP columns: D aux constructors declared, E used by the deep chain, 1 given used; then a mutant
D=4; E=2
mkdir -p "$F/d/VIR"
{ printf 'inductive Step where\n  | slice_fuse : Step\n'; i=0; while [ $i -lt $D ]; do printf '  | aux_d%d : Step\n' $i; i=$((i+1)); done
  printf 'theorem router_fusion_deep_steps : True := by\n'; i=0; while [ $i -lt $E ]; do printf '  refine .trans (.aux_d%d) ?_\n' $i; i=$((i+1)); done
  printf '  exact .slice_fuse aux_d3\n'; } > "$F/d/VIR/Deep.lean"
g6() { printf '%s\n' "$1" | awk -F'\t' -v c="$2" '$2==c{print $3}'; }
o=$(python3 "$H/count.py" --arm lean "$F/d")
if [ "$(g6 "$o" C3deep)" = "$E" ] && [ "$(g6 "$o" C3deepGivenUsed)" = 1 ]; then say "ARM6 deep fixture OK"; else say "ARM6 deep fixture FAIL"; printf '%s\n' "$o"; fail=1; fi
sed 's/re.search(r.\\\.. + a + r.\\b., dblk)/re.search(a, dblk)/' "$H/count.py" > "$F/mutant6.py"
if cmp -s "$H/count.py" "$F/mutant6.py"; then say "ARM7 mutant NOT PLANTED"; fail=1
else o=$(python3 "$F/mutant6.py" --arm lean "$F/d"); if [ "$(g6 "$o" C3deep)" = "$E" ]; then say "ARM7 mutant SURVIVED"; fail=1; else say "ARM7 mutant KILLED"; fi; fi

# (8) row 19: a file outside the program's declared set moves NO .scoped row (and does move the whole-tree C2)
mkdir -p "$F/s/VIR"
for f in Core Rules Router; do printf 'theorem %s_t : True := (by trivial)\n' "$f" > "$F/s/VIR/$f.lean"; done
o1=$(python3 "$H/count.py" --arm lean --program 1 "$F/s")
printf 'theorem extra : True := (by trivial)\n' > "$F/s/VIR/Extra.lean"
o2=$(python3 "$H/count.py" --arm lean --program 1 "$F/s")
s1=$(printf '%s\n' "$o1" | grep -F '.scoped'); s2=$(printf '%s\n' "$o2" | grep -F '.scoped')
if [ -n "$s1" ] && [ "$s1" = "$s2" ] && [ "$(g6 "$o1" C2.scoped)" = 3 ] && [ "$(g6 "$o2" C2)" = 4 ]; then say "ARM8 scope fixture OK"
else say "ARM8 scope fixture FAIL"; printf '%s\n---\n%s\n' "$o1" "$o2"; fail=1; fi

find "${F:?}" -delete
echo "SELFTEST rc=$fail"
exit $fail
