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

# (9) program 3 (fixed before any proof): C1coe counts ↑ · .val · Subtype.val · .property in route_acl_safe's term only
mkdir -p "$F/p3/VIR" "$F/p3/out"
printf 'theorem route_acl_safe : True := by\n  exact (by trivial)\n' > "$F/p3/VIR/Router3.lean"
printf 'theorem VIR.route_acl_safe : ∀ b, ↑b = b.val ∧ Subtype.val b = b ∧ h.property :=\nfun b => x\ntheorem VIR.other : ↑a := ↑a\n' > "$F/p3/out/terms.txt"
o=$(python3 "$H/count.py" --arm lean --program 3 "$F/p3")
if [ "$(g6 "$o" P3.C1coe)" = 4 ] && [ "$(g6 "$o" P3.C2cond)" = 1 ] && [ "$(g6 "$o" P3.C3)" = 0 ]; then say "ARM9 program-3 fixture OK"
else say "ARM9 program-3 fixture FAIL"; printf '%s\n' "$o"; fail=1; fi
o=$(python3 "$H/count.py" --arm metaprl --program 3 "$F/none"); if printf '%s\n' "$o" | awk -F'\t' '$4!="EMPTY"' | grep -q .; then say "ARM9b empty metaprl p3 FAIL"; fail=1; else say "ARM9b empty metaprl p3 OK"; fi

# (10) a FILE-FINAL proof never absorbs the next file's header (C5chain leak, fixed at row 25)
mkdir -p "$F/fb/VIR"
printf 'namespace VIR\ntheorem router2_fusion : True := by\n  trivial\nend VIR\n' > "$F/fb/VIR/A.lean"
printf '/- header -/\nimport VIR.A\nnamespace VIR.Z\ntheorem zz : True := trivial\nend VIR.Z\n' > "$F/fb/VIR/B.lean"
o=$(python3 "$H/count.py" --arm lean --program 2 "$F/fb")
if [ "$(g6 "$o" P2.C5chain)" = 1 ]; then say "ARM10 file-boundary OK"; else say "ARM10 file-boundary FAIL"; printf '%s\n' "$o" | grep C5chain; fail=1; fi

# (11) C6 is PROGRAM-SCOPED on the MetaPRL arm (mojave @[bus]): program 1's driver runs are runs-NN.txt,
# program N's are runs-pN-NN.txt; --program N must read its own files only. R1/R3 differ so a cross-read shows.
M="$F/c6"; mkdir -p "$M/vir-metaprl/theories/vir" "$M/vir-arm-tools/steps"
: > "$M/vir-metaprl/theories/vir/vir.ml"; : > "$M/vir-metaprl/theories/vir/vir3.ml"
R1=4; R3=2
i=1; while [ $i -le $R1 ]; do printf '=== STEP 1 [ok] :: refine (x);;\n' > "$M/vir-arm-tools/runs-$(printf %02d $i).txt"; i=$((i+1)); done
i=1; while [ $i -le $R3 ]; do printf '=== STEP 1 [ok] :: refine (x);;\n=== STEP 2 [ok] :: refine (y);;\n' > "$M/vir-arm-tools/runs-p3-$(printf %02d $i).txt"; i=$((i+1)); done
printf '=== STEP 1 [ok] :: refine (z);;\n' > "$M/vir-arm-tools/runs-p3-export.txt"   # not a session file
o1=$(python3 "$H/count.py" --arm metaprl "$M"); o3=$(python3 "$H/count.py" --arm metaprl --program 3 "$M")
if [ "$(g6 "$o1" C6sessions)" = "$R1" ] && [ "$(g6 "$o1" C6refines)" = "$R1" ] \
   && [ "$(g6 "$o3" C6sessions)" = "$R3" ] && [ "$(g6 "$o3" C6refines)" = "$((2*R3))" ]; then say "ARM11 C6 program-scope OK"
else say "ARM11 C6 program-scope FAIL"; printf '%s\n---\n%s\n' "$o1" "$o3" | grep C6; fail=1; fi

# (12) C2genWf ATTRIBUTION (row 31, exploratory, post-proof): a wf child of `refine (dT 0)` (intro on the conclusion)
# is the STATEMENT's well-formedness; every other wf child is the PROOF's. Counts derived from construction.
M="$F/attr"; mkdir -p "$M/vir-metaprl/theories/vir" "$M/vir-arm-tools/steps"
: > "$M/vir-metaprl/theories/vir/vir.ml"; : > "$M/vir-metaprl/theories/vir/vir3.ml"
WS=2; WP=3; f="$M/vir-arm-tools/runs-c2-router3.txt"; : > "$f"; k=1
i=0; while [ $i -lt $WS ]; do printf '=== STEP %d [ok] :: refine (dT 0);;\n=== CHILDREN %d: wf main\n' $k $k >> "$f"; k=$((k+1)); i=$((i+1)); done
i=0; while [ $i -lt $WP ]; do printf '=== STEP %d [ok] :: refine (dT 7);;\n=== CHILDREN %d: wf main\n' $k $k >> "$f"; k=$((k+1)); i=$((i+1)); done
printf '=== STEP %d [ok] :: refine (dT 0 thenT autoT);;\n=== CHILDREN %d: wf\n' $k $k >> "$f"   # not bare dT 0: proof-side
o=$(python3 "$H/count.py" --arm metaprl --program 3 "$M")
if [ "$(g6 "$o" C2genWf)" = "$((WS+WP+1))" ] && [ "$(g6 "$o" C2genWf.stmt)" = "$WS" ] && [ "$(g6 "$o" C2genWf.proof)" = "$((WP+1))" ]; then say "ARM12 wf attribution OK"
else say "ARM12 wf attribution FAIL"; printf '%s\n' "$o" | grep C2gen; fail=1; fi

# (13) MetaPRL C5 from mojave's MANIFEST (row 32; vir-arm-tools/STORED.tsv @[bus]): C5 = refine lines of the
# program's stored script, C5tok = their whitespace tokens, C5.inArchive = how many refine arguments occur, whitespace-
# normalised, as a `String "(…)"` node of the named .prla. One argument is planted ABSENT so the match can fail.
M="$F/c5"; mkdir -p "$M/vir-metaprl/theories/vir" "$M/vir-arm-tools/steps"
: > "$M/vir-metaprl/theories/vir/vir.ml"; : > "$M/vir-metaprl/theories/vir/vir3.ml"
printf 'program\tstored_script\tarchive\ttheorem\n3\tsteps/s3.mp\tvir-metaprl/theories/vir/vir3.prla\tthm\n' > "$M/vir-arm-tools/STORED.tsv"
printf 'refine (dT 0);;\nrefine (dT  0);;\nrefine (rw  foo 2);;\nrefine (absentT 1);;\nrefine (autoT);;\n' > "$M/vir-arm-tools/steps/s3.mp"
# the archive quotes a string only when it must: `String (autoT)` is stored BARE (measured in vir3.prla, p506)
printf 'P\tp1\tString "(dT 0)"\nP\tp2\tString "(rw foo 2)"\nP\tp3\tString (autoT)\n' > "$M/vir-metaprl/theories/vir/vir3.prla"
T5=$(grep '^ *refine' "$M/vir-arm-tools/steps/s3.mp" | wc -w | tr -d ' ')
o=$(python3 "$H/count.py" --arm metaprl --program 3 "$M")
if [ "$(g6 "$o" C5)" = 5 ] && [ "$(g6 "$o" C5tok)" = "$T5" ] && [ "$(g6 "$o" C5.inArchive)" = 4 ]; then say "ARM13 C5 manifest OK"
else say "ARM13 C5 manifest FAIL"; printf '%s\n' "$o" | grep C5; fail=1; fi

# (14) C5 over EVERY manifest row of a program (row 34, mojave @[bus]): a theorem's block in a shared script runs from
# the `cd` naming it to the next `cd`; a script with no such cd is whole. C5lex = LEXICAL tokens of each refine's argument
# (mojave's unit). Fixture: main script 2 refines + a shared lemma file holding lemmas a (1 refine) and b (2), and an OTHER
# lemma c (1) that the manifest does not name and must not be counted.
M="$F/c5b"; mkdir -p "$M/vir-metaprl/theories/vir" "$M/vir-arm-tools/steps"
: > "$M/vir-metaprl/theories/vir/vir.ml"; : > "$M/vir-metaprl/theories/vir/vir.prla"
printf 'program\tstored_script\tarchive\ttheorem\n1\tsteps/m.mp\tvir-metaprl/theories/vir/vir.prla\tmain\n1\tsteps/l.mp\tvir-metaprl/theories/vir/vir.prla\ta\n1\tsteps/l.mp\tvir-metaprl/theories/vir/vir.prla\tb\n' > "$M/vir-arm-tools/STORED.tsv"
printf 'cd "/vir/vir/main";;\nrefine (dT 0);;\ncd "../2";;\nrefine logicAutoT;;\ncd "/vir/vir/main/2/1";;\n' > "$M/vir-arm-tools/steps/m.mp"   # subgoal cds stay inside the block
printf 'cd "/vir/vir/a";;\nrefine (rw f 0);;\ncd "../c";;\nrefine (rw g 0);;\ncd "../b";;\nrefine (x <<y>>);;\ncd "1";;\nrefine autoT;;\ncd "..";;\nrefine (rw h 0);;\n' > "$M/vir-arm-tools/steps/l.mp"
# lexical tokens, derived by hand from the unit's definition: (dT 0)=4 · logicAutoT=1 · (rw f 0)=5 · (x <<y>>)=6 · autoT=1
o=$(python3 "$H/count.py" --arm metaprl "$M")
if [ "$(g6 "$o" C5)" = 5 ] && [ "$(g6 "$o" C5lex)" = 17 ] && [ "$(g6 "$o" C5.main)" = 2 ]; then say "ARM14 C5 lemma blocks OK"
else say "ARM14 C5 lemma blocks FAIL"; printf '%s\n' "$o" | grep C5; fail=1; fi

# (15) row 40: the COMPILER rows read a git repo AT A PINNED SHA (paris's tree moves), by layer.
# Fixture: a repo whose pinned commit has NL non-blank lines in Router/Paths.lean (layer1) and NR in
# Router/Refines.lean (layer2), with T theorems; a LATER commit adds lines that must NOT move the pinned count.
G="$F/cc"; mkdir -p "$G/Router" "$F/ccv/Compose"
git -C "$G" init -q; NL=3; NR=2; T=4
i=0; : > "$G/Router/Paths.lean"; while [ $i -lt $NL ]; do printf 'theorem p%d : True := trivial\n\n' $i >> "$G/Router/Paths.lean"; i=$((i+1)); done
i=0; : > "$G/Router/Refines.lean"; while [ $i -lt $NR ]; do printf 'def r%d := 1\n' $i >> "$G/Router/Refines.lean"; i=$((i+1)); done
printf 'theorem c0 : True := trivial\n' > "$F/ccv/Compose/A.lean"
git -C "$G" add -A; git -C "$G" -c user.name=t -c user.email=t@t commit -qm pin; PIN=$(git -C "$G" rev-parse HEAD)
printf 'theorem late : True := trivial\n' >> "$G/Router/Paths.lean"; git -C "$G" -c user.name=t -c user.email=t@t commit -qam late
o=$(python3 "$H/count.py" --arm compiler --sha "$PIN" --compose "$F/ccv" "$G" 2>&1)
TL=$(( NL + NR )); TT=$(( NL + 1 ))
if [ "$(g6 "$o" CC.layer1.C5)" = "$NL" ] && [ "$(g6 "$o" CC.layer2.C5)" = "$NR" ] && [ "$(g6 "$o" CC.spike.C5)" = "$TL" ] \
   && [ "$(g6 "$o" CC.theorems)" = "$TT" ] && [ "$(g6 "$o" CC.compose.C5)" = 1 ]; then say "ARM15 compiler rows at pinned sha OK"
else say "ARM15 compiler rows at pinned sha FAIL"; printf '%s\n' "$o" | head -12; fail=1; fi

# (16) row 45: with --compose-sha the COMPOSE rows are read at a sha too (a later file must not move them).
V2="$F/vr"; mkdir -p "$V2/compose/Compose"; git -C "$V2" init -q
printf 'theorem c0 : True := trivial\ntheorem c1 : True := trivial\n' > "$V2/compose/Compose/A.lean"
git -C "$V2" add -A; git -C "$V2" -c user.name=t -c user.email=t@t commit -qm pin; VPIN=$(git -C "$V2" rev-parse HEAD)
printf 'theorem late : True := trivial\n' > "$V2/compose/Compose/B.lean"; printf 'theorem late2 : True := trivial\n' >> "$V2/compose/Compose/A.lean"; git -C "$V2" add -A; git -C "$V2" -c user.name=t -c user.email=t@t commit -qm late
o=$(python3 "$H/count.py" --arm compiler --sha "$PIN" --compose "$V2/compose" --compose-sha "$VPIN" "$G" 2>&1)
if [ "$(g6 "$o" CC.compose.C5)" = 2 ] && [ "$(g6 "$o" CC.theorems)" = "$(( NL + 2 ))" ] && [ "$(g6 "$o" CC.compose.sha)" = "$VPIN" ]; then say "ARM16 compose rows at pinned vir sha OK"
else say "ARM16 compose rows at pinned vir sha FAIL"; printf '%s\n' "$o" | grep -E 'compose|theorems|error' | head; fail=1; fi

# (17) row 46: the AXIOM GATE over an audit log. Good log rc 0; three planted defects each rc != 0.
AG="$F/ag"; mkdir -p "$AG"
good="'control_sorry' depends on axioms: [sorryAx]
'A.t' depends on axioms: [propext, Classical.choice, Quot.sound]
'A.u' does not depend on any axioms
saltbuild EXIT=0"
printf '%s\n' "$good" > "$AG/good.log"
printf '%s\n' "$good" | sed "s/'A.t' depends on axioms: \[propext/'A.t' depends on axioms: [sorryAx, propext/" > "$AG/sorry.log"
printf '%s\n' "$good" | sed "s/^'control_sorry' depends on axioms: \[sorryAx\]/'control_sorry' depends on axioms: [propext]/" > "$AG/nocontrol.log"
printf '%s\n' "$good" | sed 's/^saltbuild EXIT=0/saltbuild EXIT=1/' > "$AG/exit1.log"
r0=0; python3 "$H/axiom_gate.py" "$AG/good.log" >/dev/null 2>&1 || r0=$?
r1=0; python3 "$H/axiom_gate.py" "$AG/sorry.log" >/dev/null 2>&1 || r1=$?
r2=0; python3 "$H/axiom_gate.py" "$AG/nocontrol.log" >/dev/null 2>&1 || r2=$?
r3=0; python3 "$H/axiom_gate.py" "$AG/exit1.log" >/dev/null 2>&1 || r3=$?
if [ $r0 -eq 0 ] && [ $r1 -ne 0 ] && [ $r2 -ne 0 ] && [ $r3 -ne 0 ] && [ -f "$H/axiom_gate.py" ]; then say "ARM17 axiom gate OK"
else say "ARM17 axiom gate FAIL (good=$r0 sorry=$r1 nocontrol=$r2 exit1=$r3)"; fail=1; fi

# (18) amend-10: the B′ extractor (leanbp) sees a planted HEq and a planted extra axiom, and a missing control.
BP="$F/bp"; mkdir -p "$BP/logs"
bpgood="'control_sorry_bp' depends on axioms: [sorryAx]
theorem VIR.BPrime.router_fusion_bp : U C b0 st = F C b0 st :=
fun C b0 st => rfl
'VIR.BPrime.router_fusion_bp' depends on axioms: [propext, Quot.sound]
saltbuild EXIT=0"
printf '%s\n' "$bpgood" > "$BP/logs/audit-bp-001.log"
o0=$(python3 "$H/count.py" --arm leanbp "$BP")
printf '%s\n' "$bpgood" | sed 's/fun C b0 st => rfl/fun C b0 st => HEq.refl ≍/; s/\[propext, Quot.sound\]/[propext, Quot.sound, Classical.em_ax]/; s/\[sorryAx\]/[propext]/' > "$BP/logs/audit-bp-002.log"
o1=$(python3 "$H/count.py" --arm leanbp "$BP")
if [ "$(g6 "$o0" BP1.C1heq)" = 0 ] && [ "$(g6 "$o0" BP1.C4)" = 0 ] && [ "$(g6 "$o0" B.control)" = 1 ] \
   && [ "$(g6 "$o1" BP1.C1heq)" = 2 ] && [ "$(g6 "$o1" BP1.C4)" = 1 ] && [ "$(g6 "$o1" B.control)" = 0 ]; then say "ARM18 B′ extractor OK"
else say "ARM18 B′ extractor FAIL"; printf '%s\n%s\n' "$o0" "$o1" | grep BP1; fail=1; fi

# (19) the per-run log rule (STATUS-vir row 65): lean/VIRB/logged-build.sh REFUSES a log name already used, so a
# second run can never overwrite the first and hide it from B.C6. A stub stands in for saltbuild; real logs untouched.
LB="$F/lb"; mkdir -p "$LB/logs"
printf '#!/bin/sh\necho "saltbuild EXIT=${STUBRC:-0}"; exit ${STUBRC:-0}\n' > "$LB/stub.sh"; chmod +x "$LB/stub.sh"
W="$H/../lean/VIRB/logged-build.sh"
q1=0; SALTBUILD="$LB/stub.sh" LOGDIR="$LB/logs" "$W" audit-bp-001 build >/dev/null 2>&1 || q1=$?
before=$(cksum < "$LB/logs/audit-bp-001.log")
q2=0; SALTBUILD="$LB/stub.sh" LOGDIR="$LB/logs" STUBRC=1 "$W" audit-bp-001 build >/dev/null 2>&1 || q2=$?
q3=0; SALTBUILD="$LB/stub.sh" LOGDIR="$LB/logs" STUBRC=1 "$W" build-x build >/dev/null 2>&1 || q3=$?
o=$(python3 "$H/count.py" --arm leanbp "$LB")
if [ $q1 -eq 0 ] && [ $q2 -eq 3 ] && [ $q3 -eq 1 ] && [ "$(cksum < "$LB/logs/audit-bp-001.log")" = "$before" ] \
   && [ "$(g6 "$o" B.C6)" = "$(ls "$LB/logs" | wc -l | tr -d ' ')" ]; then say "ARM19 per-run log rule OK"
else say "ARM19 per-run log rule FAIL (new=$q1 reuse=$q2 fail-rc=$q3 B.C6=$(g6 "$o" B.C6))"; fail=1; fi

find "${F:?}" -delete
echo "SELFTEST rc=$fail"
exit $fail
