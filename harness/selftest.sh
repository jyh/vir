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

# (20) row 64: the MetaPRL B′ extractor keeps a theorem's scope across RELATIVE cds and absolute sub-goal paths, and
# leaves it at the module cd. Expected values are derived from the fixture as it is written (idiom law 1).
BM="$F/bm/vir-metaprl/theories/vir"; mkdir -p "$BM/vir-arm-tools/steps"; : > "$BM/vir-arm-tools/COUNTS-metaprl-bprime.md"
printf 'prim p1 : x\ninteractive route_acl_safe : y\n' > "$BM/vir3.ml"
cat > "$BM/vir-arm-tools/steps/bp-vir3.mp" <<'MP'
cd "/vir/vir3/lemma_a";;
refine (autoT);;
cd "/vir/vir3/route_acl_safe";;
refine (dT 0);;
cd "3";;
refine (dT 5);;
cd "../2";;
refine (nthHypT 8);;
cd "/vir/vir3/route_acl_safe/2/1";;
refine (autoT);;
cd "/vir/vir3";;
refine (autoT);;
export ();;
MP
inthm=$(awk '/^cd "\/vir\/vir3\/route_acl_safe";;/{on=1} /^cd "\/vir\/vir3";;/{on=0} on && /^refine/{n++} END{print n+0}' "$BM/vir-arm-tools/steps/bp-vir3.mp")
n=0; : > "$BM/vir-arm-tools/runs-bp-vir3.txt"
while IFS= read -r ln; do n=$((n+1)); printf '=== STEP %d [ok] 0.00s :: %s\n' $n "$ln" >> "$BM/vir-arm-tools/runs-bp-vir3.txt"
  case $ln in refine*) printf '=== CHILDREN %d: wf main\n' $n >> "$BM/vir-arm-tools/runs-bp-vir3.txt";; esac
done < "$BM/vir-arm-tools/steps/bp-vir3.mp"
printf '=== END steps=%d ok=%d err=0 rc=0 cmoz-written=0\n' $n $n >> "$BM/vir-arm-tools/runs-bp-vir3.txt"
o=$(python3 "$H/count.py" --arm metaprlbp "$F/bm")
if [ "$(g6 "$o" BM3.refines.thm)" = "$inthm" ] && [ "$(g6 "$o" BM3.C2gen.thm)" = "$inthm" ] && [ "$(g6 "$o" BM3.replay)" = 1 ] \
   && [ "$(g6 "$o" BM3.prims)" = 1 ] && [ "$(g6 "$o" BM3.C2genWf)" = "$(grep -c '^refine' "$BM/vir-arm-tools/steps/bp-vir3.mp")" ]; then say "ARM20 MetaPRL B′ scope OK"
else say "ARM20 MetaPRL B′ scope FAIL (want $inthm)"; printf '%s\n' "$o" | grep BM3; fail=1; fi

# (21) B4 on MetaPRL: a tc rule is CLOSED only when its refine ran ok and left no children. The fixture writes one rule
# per line of $tc; a rule whose children field is non-empty must not count. Expected = rules with an empty field.
TC="$F/tc/vir-metaprl/theories/vir/vir-arm-tools"; mkdir -p "$TC/steps"; : > "$TC/COUNTS-metaprl-bprime.md"; : > "$TC/steps/tc.mp"
tc='tc_a|
tc_b|wf
tc_c|'
n=0; : > "$TC/runs-tc.txt"
while IFS='|' read -r r ch; do
  n=$((n+1)); printf '=== STEP %d [ok] 0.00s :: cd "/vir/virtc/%s";;\n' $n "$r" >> "$TC/runs-tc.txt"
  n=$((n+1)); printf '=== STEP %d [ok] 0.00s :: refine (logicAutoT);;\n=== CHILDREN %d: %s\n' $n $n "$ch" >> "$TC/runs-tc.txt"
done <<< "$tc"
want_rules=$(printf '%s\n' "$tc" | wc -l | tr -d ' '); want_closed=$(printf '%s\n' "$tc" | grep -c '|$')
o=$(python3 "$H/count.py" --arm metaprlbp "$F/tc")
if [ "$(g6 "$o" BMtc.rules)" = "$want_rules" ] && [ "$(g6 "$o" BMtc.closed)" = "$want_closed" ] && [ "$want_closed" -lt "$want_rules" ]; then say "ARM21 MetaPRL tc closed OK"
else say "ARM21 MetaPRL tc closed FAIL (want $want_closed/$want_rules)"; printf '%s\n' "$o" | grep BMtc; fail=1; fi

# (22) amend-11's Lean extractor (--arm leanp): counts DERIVED from the fixture's construction.
# N subst-statements + one theorem mentioning a DEFINED `weaken` (D1: joins the list) + K ins-only (BESIDE) + a DECOY whose
# NAME contains subst but whose statement does not + one axiom + Part.fix once in code and once in a comment.
P="$F/p"; mkdir -p "$P/VIRP" "$P/logs"; N=3; K=2
{ printf 'def weaken (x : Nat) : Nat := x\n'
  i=0; while [ $i -lt $N ]; do printf 'theorem s%d : Tm.subst e 0 v = e := rfl\n' $i; i=$((i+1)); done
  printf 'theorem w0 : weaken 0 = 0 := rfl\n'
  i=0; while [ $i -lt $K ]; do printf 'theorem i%d : (ins 0 x l).length = l.length + 1 := rfl\n' $i; i=$((i+1)); done
  printf 'theorem Decoy.subst : True := by exact (Tm.subst e 0 v).show.length = 0 |>.elim\n'
  printf 'axiom bad : False\n-- Part.fix in a comment\ndef g := Part.fix f\n'; } > "$P/VIRP/A.lean"
SL=2   # S5: SL law theorems (union/Disj/emp) + one frame theorem that mentions `own` (not a law) + one whose NAME says union
{ i=0; while [ $i -lt $SL ]; do printf 'theorem l%d (h : Frag) : union h emp = h := rfl\n' $i; i=$((i+1)); done
  printf 'theorem fr (hd : Disj hf (own s)) : True := trivial\n'
  printf 'theorem Decoy.union : True := trivial\n'; } > "$P/VIRP/Sep.lean"
want_sep_th=$((SL+2)); want_sep_laws=$SL
printf "'x' depends on axioms: [propext, sorryAx]\n" > "$P/logs/audit-001.log"
printf "'control_sorry' depends on axioms: [propext, sorryAx]\nsaltbuild EXIT=0\n" > "$P/logs/audit-control-001.log"
printf 'saltbuild EXIT=1\n' > "$P/logs/build-001.log"
want_binder=$((N+1)); want_ins=$K; want_c6=$(cat "$P"/logs/*.log | grep -c '^saltbuild EXIT=')
check22() { local o; o=$(python3 "$1" --arm leanp "$P")
  [ "$(g6 "$o" P.binder)" = "$want_binder" ] && [ "$(g6 "$o" P.binder.insOnly)" = "$want_ins" ] && [ "$(g6 "$o" P.C4vir)" = 1 ] \
  && [ "$(g6 "$o" P.sep.theorems)" = "$want_sep_th" ] && [ "$(g6 "$o" P.sep.laws)" = "$want_sep_laws" ] && [ "$(g6 "$o" P.fix)" = 1 ] && [ "$(g6 "$o" P.C4)" = 1 ] && [ "$(g6 "$o" P.control)" = 1 ] && [ "$(g6 "$o" P.C6)" = "$want_c6" ]; }
if check22 "$H/count.py"; then say "ARM22 leanp fixture OK (binder=$want_binder ins=$want_ins)"
else say "ARM22 leanp fixture FAIL"; python3 "$H/count.py" --arm leanp "$P"; fail=1; fi
sed 's/rest = block\[m.end():\] if m else block/rest = block/' "$H/count.py" > "$F/mutant22.py"
if cmp -s "$H/count.py" "$F/mutant22.py"; then say "ARM22 mutant NOT PLANTED"; fail=1
elif check22 "$F/mutant22.py"; then say "ARM22 mutant SURVIVED (a theorem NAME is counted as its statement)"; fail=1
else say "ARM22 mutant KILLED"; fi

# (23) V3 (amend-11): central definitions EDITED by one commit, from git history. A fixture repo whose base has the four
# central definitions plus a helper; the ext commit edits E of them and ADDS A new definitions beside. Want edited=E.
R3="$F/v3"; mkdir -p "$R3/virp/VIRP"; git -C "$R3" init -q; git -C "$R3" config user.email t@t; git -C "$R3" config user.name t
{ for n in Tm Step HasType den; do printf 'inductive %s where\n  | a\n' $n; done; printf 'def helper := 1\n'; } > "$R3/virp/VIRP/S.lean"
git -C "$R3" add -A; git -C "$R3" commit -qm base; B3=$(git -C "$R3" rev-parse HEAD)
E=2; A=1
sed -i.bak -e 's/^inductive Tm where/inductive Tm where\n  | ext/' -e 's/^inductive den where/inductive den where\n  | ext/' "$R3/virp/VIRP/S.lean"; rm -f -- "${R3:?}/virp/VIRP/S.lean.bak"
printf 'def letAtomNew := 2\n' >> "$R3/virp/VIRP/S.lean"
git -C "$R3" add -A; git -C "$R3" commit -qm ext; X3=$(git -C "$R3" rev-parse HEAD)
check23() { local o; o=$(python3 "$1" --arm v3 --base "$B3" --ext "$X3" "$R3")
  [ "$(g6 "$o" V3.edited)" = "$E" ] && [ "$(g6 "$o" V3.added)" = "$A" ] && [ "$(g6 "$o" V3.central.missingAtBase)" = 0 ]; }
if check23 "$H/count.py"; then say "ARM23 v3 fixture OK (edited=$E added=$A)"
else say "ARM23 v3 fixture FAIL"; python3 "$H/count.py" --arm v3 --base "$B3" --ext "$X3" "$R3"; fail=1; fi
sed 's/edited = \[n for n in V3_LEAN if n in before and n in after and before\[n\] != after\[n\]\]/edited = [n for n in after if n not in before or before[n] != after[n]]/' "$H/count.py" > "$F/mutant23.py"
if cmp -s "$H/count.py" "$F/mutant23.py"; then say "ARM23 mutant NOT PLANTED"; fail=1
elif check23 "$F/mutant23.py"; then say "ARM23 mutant SURVIVED (an addition counted as an edit)"; fail=1
else say "ARM23 mutant KILLED"; fi

# (24) layer L1 (amend-13, row 94): the l1 extractor. A fixture VIRL1/ with one theorem whose STATEMENT mentions `subst`, one
# whose PROOF alone does, one that uses the fixpoint's leastness, and three mutant logs: EXIT=1 (red), EXIT=0 (survived, NOT red)
# and one with no EXIT line (unread). Want binder=1, leastness=1, mutants=3, red=1, unread=1.
L="$F/l1"; mkdir -p "$L/VIRL1" "$L/logs"
printf 'theorem a_subst (x : Nat) : Tm.subst x = x := rfl\ntheorem b_plain (x : Nat) : x = x := by simp [Tm.subst]\ntheorem c_least : True := by have := Part.Fix.mem_iff; trivial\n' > "$L/VIRL1/A.lean"
printf 'saltbuild EXIT=1\n' > "$L/logs/mutant-001.log"; printf 'saltbuild EXIT=0\n' > "$L/logs/mutant-002.log"; printf 'no exit line\n' > "$L/logs/mutant-003.log"
check24() { local o; o=$(python3 "$1" --arm l1 "$L")
  [ "$(g6 "$o" L1.binder)" = 1 ] && [ "$(g6 "$o" L1.leastness)" = 1 ] && [ "$(g6 "$o" L1.mutants)" = 3 ] &&
  [ "$(g6 "$o" L1.mutants.red)" = 1 ] && [ "$(g6 "$o" L1.mutants.unread)" = 1 ]; }
if check24 "$H/count.py"; then say "ARM24 l1 fixture OK (binder=1 leastness=1 mutants 3/red 1/unread 1)"
else say "ARM24 l1 fixture FAIL"; python3 "$H/count.py" --arm l1 "$L"; fail=1; fi
sed "s/        elif ex\[-1\] != '0':/        else:/" "$H/count.py" > "$F/mutant24.py"
if cmp -s "$H/count.py" "$F/mutant24.py"; then say "ARM24 mutant NOT PLANTED"; fail=1
elif check24 "$F/mutant24.py"; then say "ARM24 mutant SURVIVED (a mutant that BUILT is counted red)"; fail=1
else say "ARM24 mutant KILLED"; fi

# (25) W3 on layer L1 (amend-15): central-definition CATEGORIES edited by one commit. A fixture repo whose base has every
# name amend-15 lists; the ext commit edits Atom AND Tm (one category, syntax) and the NONCOMPUTABLE den (one category,
# den: a modifier must not hide a declaration), and ADDS a def.
# Want categories=2 (syntax,den), added=1. A count of edited BLOCKS would read 3.
R5="$F/v3l1"; mkdir -p "$R5/l1/VIRL1"; git -C "$R5" init -q; git -C "$R5" config user.email t@t; git -C "$R5" config user.name t
{ for n in Ty Atom Tm Step HasTypeA HasTypeL HasType; do printf 'inductive %s where\n  | a\n' $n; done
  for n in Atom.eval head Φ; do printf 'def %s := 1\n' $n; done; printf 'theorem gap : True := trivial\nnoncomputable def den := 1\ndef helper := 1\n'; } > "$R5/l1/VIRL1/S.lean"
git -C "$R5" add -A; git -C "$R5" commit -qm base; B5=$(git -C "$R5" rev-parse HEAD)
sed -i.bak -e 's/^inductive Atom where/inductive Atom where\n  | ext/' -e 's/^inductive Tm where/inductive Tm where\n  | ext/' -e 's/^noncomputable def den := 1/noncomputable def den := 2/' "$R5/l1/VIRL1/S.lean"; rm -f -- "${R5:?}/l1/VIRL1/S.lean.bak"
printf 'def maxNew := 2\n' >> "$R5/l1/VIRL1/S.lean"
git -C "$R5" add -A; git -C "$R5" commit -qm ext; X5=$(git -C "$R5" rev-parse HEAD)
check25() { local o; o=$(python3 "$1" --arm v3l1 --base "$B5" --ext "$X5" --prefix l1/VIRL1 "$R5")
  [ "$(g6 "$o" W3.categories)" = 2 ] && [ "$(g6 "$o" W3.added)" = 1 ] && [ "$(g6 "$o" W3.central.missingAtBase)" = 0 ]; }
if check25 "$H/count.py"; then say "ARM25 v3l1 fixture OK (categories=2 added=1)"
else say "ARM25 v3l1 fixture FAIL"; python3 "$H/count.py" --arm v3l1 --base "$B5" --ext "$X5" --prefix l1/VIRL1 "$R5"; fail=1; fi
sed 's/    cats = sorted(set(cat for cat, n in edited))/    cats = [cat for cat, n in edited]/' "$H/count.py" > "$F/mutant25.py"
if cmp -s "$H/count.py" "$F/mutant25.py"; then say "ARM25 mutant NOT PLANTED"; fail=1
elif check25 "$F/mutant25.py"; then say "ARM25 mutant SURVIVED (edited BLOCKS counted as categories)"; fail=1
else say "ARM25 mutant KILLED"; fi

# (26) layer L1, the MetaPRL side (row 99; amend-14's file rule). A fixture vir-metaprl/theories/vir with one virl1_ theory
# holding ONE prim and one interactive, and itt_bar + itt_bar_bterm holding 3 prims between them. W1 is scored on virl1_*
# alone and the PARTIALITY THEORY column sits beside it. Want W1=1, PARTIALITY=3, interactive=1.
M6="$F/ml1/vir-metaprl/theories/vir"; mkdir -p "$M6"
printf 'prim foo :\n   sequent { <H> >- a }\ninteractive bar :\n   sequent { <H> >- b }\n' > "$M6/virl1_x.ml"
printf 'prim h1 : a\nprim h2 : b\n' > "$M6/itt_bar.ml"; printf 'prim_rw h3 : c <--> d\n' > "$M6/itt_bar_bterm.ml"
printf 'prim notcounted : z\n' > "$M6/other.ml"
check26() { local o; o=$(python3 "$1" --arm metaprll1 "$F/ml1")
  [ "$(g6 "$o" L1M.W1)" = 1 ] && [ "$(g6 "$o" L1M.PARTIALITY)" = 3 ] && [ "$(g6 "$o" L1M.interactive)" = 1 ]; }
if check26 "$H/count.py"; then say "ARM26 metaprll1 fixture OK (W1=1 PARTIALITY=3 interactive=1)"
else say "ARM26 metaprll1 fixture FAIL"; python3 "$H/count.py" --arm metaprll1 "$F/ml1"; fail=1; fi
sed "s/if f.startswith('virl1_') and f.endswith('.ml')/if (f.startswith('virl1_') or f.startswith('itt_bar')) and f.endswith('.ml')/" "$H/count.py" > "$F/mutant26.py"
if cmp -s "$H/count.py" "$F/mutant26.py"; then say "ARM26 mutant NOT PLANTED"; fail=1
elif check26 "$F/mutant26.py"; then say "ARM26 mutant SURVIVED (itt_bar counted in W1)"; fail=1
else say "ARM26 mutant KILLED"; fi

# (27) W8 at L2 (amend-13 W8, amend-16 Y2 draft; STATUS-vir row 104): L1 DEFINITIONS edited between the L1-closed sha and the
# L2-closed sha. Base: inductive I, noncomputable def D, def A, theorem T in l1/VIRL1/S.lean. Ext edits I, D and T, and adds a
# NEW file with def N. Want W8=2 (I and D: a theorem edit is BESIDE, a modifier must not hide D), thmEdited=1, newFiles=1.
R7="$F/w8"; mkdir -p "$R7/l1/VIRL1"; git -C "$R7" init -q; git -C "$R7" config user.email t@t; git -C "$R7" config user.name t
printf 'inductive I where\n  | a\nnoncomputable def D := 1\ndef A := 1\ntheorem T : True := trivial\n' > "$R7/l1/VIRL1/S.lean"
git -C "$R7" add -A; git -C "$R7" commit -qm base; B7=$(git -C "$R7" rev-parse HEAD)
printf 'inductive I where\n  | a\n  | b\nnoncomputable def D := 2\ndef A := 1\ntheorem T : True := by trivial\n' > "$R7/l1/VIRL1/S.lean"
printf 'def N := 1\n' > "$R7/l1/VIRL1/L2.lean"
git -C "$R7" add -A; git -C "$R7" commit -qm ext; X7=$(git -C "$R7" rev-parse HEAD)
check27() { local o; o=$(python3 "$1" --arm w8 --base "$B7" --ext "$X7" --prefix l1/VIRL1 "$R7")
  [ "$(g6 "$o" W8.defsEdited)" = 2 ] && [ "$(g6 "$o" W8.thmEdited)" = 1 ] && [ "$(g6 "$o" W8.newFiles)" = 1 ]; }
if check27 "$H/count.py"; then say "ARM27 w8 fixture OK (defsEdited=2 thmEdited=1 newFiles=1)"
else say "ARM27 w8 fixture FAIL"; python3 "$H/count.py" --arm w8 --base "$B7" --ext "$X7" --prefix l1/VIRL1 "$R7"; fail=1; fi
sed "s/        if not ISTHM.match(before\[n\]):/        if True:/" "$H/count.py" > "$F/mutant27.py"
if cmp -s "$H/count.py" "$F/mutant27.py"; then say "ARM27 mutant NOT PLANTED"; fail=1
elif check27 "$F/mutant27.py"; then say "ARM27 mutant SURVIVED (a theorem edit counted as a definition edit)"; fail=1
else say "ARM27 mutant KILLED"; fi

# (28) FINDINGS M-F6: the MetaPRL L1 soundness floor, by ANCESTRY, and the FRAMEWORK EDITS column. Fixture: a git repo
# vir-metaprl/ with commit P (pin: theories/itt/core/r.ml + theories/vir/virl1_x.ml), A (edits theories/vir only), B (edits
# theories/itt/core/r.ml), and a side branch S off P. At HEAD=B with floor A,B: floorMissing=0, frameworkEdits=1 (r.ml; the
# theories/vir edit is NOT a framework edit). With floor A,S: floorMissing=1 (S is not an ancestor).
R8="$F/ml8/vir-metaprl"; mkdir -p "$R8/theories/itt/core" "$R8/theories/vir"; git -C "$R8" init -q
git -C "$R8" config user.email t@t; git -C "$R8" config user.name t
printf 'prim r : a\n' > "$R8/theories/itt/core/r.ml"; printf 'interactive x : a\n' > "$R8/theories/vir/virl1_x.ml"
git -C "$R8" add -A; git -C "$R8" commit -qm P; P8=$(git -C "$R8" rev-parse HEAD)
git -C "$R8" checkout -q -b side; printf 'z\n' > "$R8/theories/side.txt"; git -C "$R8" add -A; git -C "$R8" commit -qm S; S8=$(git -C "$R8" rev-parse HEAD)
git -C "$R8" checkout -q -; printf 'interactive y : b\n' >> "$R8/theories/vir/virl1_x.ml"; git -C "$R8" commit -qam A; A8=$(git -C "$R8" rev-parse HEAD)
printf 'prim r : b\n' > "$R8/theories/itt/core/r.ml"; git -C "$R8" commit -qam B; B8=$(git -C "$R8" rev-parse HEAD)
check28() { local o q; o=$(VIR_L1M_PIN=$P8 VIR_L1M_FLOOR=$A8,$B8 python3 "$1" --arm metaprll1 "$F/ml8")
  q=$(VIR_L1M_PIN=$P8 VIR_L1M_FLOOR=$A8,$S8 python3 "$1" --arm metaprll1 "$F/ml8")
  [ "$(g6 "$o" L1M.floorMissing)" = 0 ] && [ "$(g6 "$o" L1M.frameworkEdits)" = 1 ] && [ "$(g6 "$q" L1M.floorMissing)" = 1 ]; }
if check28 "$H/count.py"; then say "ARM28 metaprll1 floor fixture OK (floorMissing 0 then 1, frameworkEdits=1)"
else say "ARM28 metaprll1 floor fixture FAIL"; VIR_L1M_PIN=$P8 VIR_L1M_FLOOR=$A8,$S8 python3 "$H/count.py" --arm metaprll1 "$F/ml8"; fail=1; fi
sed "s/'--', 'theories', ':!theories\/vir')/'--', 'theories')/" "$H/count.py" > "$F/mutant28.py"
if cmp -s "$H/count.py" "$F/mutant28.py"; then say "ARM28 mutant NOT PLANTED"; fail=1
elif check28 "$F/mutant28.py"; then say "ARM28 mutant SURVIVED (a theories/vir edit counted as a framework edit)"; fail=1
else say "ARM28 mutant KILLED"; fi

# (29) OCaml COMMENTS (the 14th head, scoring MetaPRL L1 at be5312958): the revived virl1_hoas_lang carries 4 `interactive`
# lines inside (* ... *) blocks, which the line regex counted (639 against check_all's 635). A commented `prim` would be read
# into W1 the same way. Fixture: virl1_c.ml with one live prim, one live interactive, a commented prim, and a NESTED comment
# holding an interactive; itt_bar_c.ml with one live prim and one commented. Want W1=1, interactive=1, PARTIALITY=1.
R9="$F/ml9/vir-metaprl/theories/vir"; mkdir -p "$R9"
printf 'prim a : x\n(* prim b : y *)\n(* outer (* inner *)\ninteractive z : w\n*)\ninteractive q : r\n' > "$R9/virl1_c.ml"
printf 'prim p : x\n(*\nprim d : y\n*)\n' > "$R9/itt_bar_c.ml"
check29() { local o; o=$(python3 "$1" --arm metaprll1 "$F/ml9")
  [ "$(g6 "$o" L1M.W1)" = 1 ] && [ "$(g6 "$o" L1M.interactive)" = 1 ] && [ "$(g6 "$o" L1M.PARTIALITY)" = 1 ]; }
if check29 "$H/count.py"; then say "ARM29 metaprll1 comment fixture OK (W1=1 interactive=1 PARTIALITY=1)"
else say "ARM29 metaprll1 comment fixture FAIL"; python3 "$H/count.py" --arm metaprll1 "$F/ml9"; fail=1; fi
sed "s/t = strip_ml_comments(read(os.path.join(root, f)))/t = read(os.path.join(root, f))/" "$H/count.py" > "$F/mutant29.py"
if cmp -s "$H/count.py" "$F/mutant29.py"; then say "ARM29 mutant NOT PLANTED"; fail=1
elif check29 "$F/mutant29.py"; then say "ARM29 mutant SURVIVED (a commented prim counted in W1)"; fail=1
else say "ARM29 mutant KILLED"; fi

# (30) W2b at L1, MetaPRL (the 14th head): a BINDER LEMMA is a rule in virl1_* whose STATEMENT applies one of amend-11's NAMED
# reflection binder operators (subst · bind · bdepth · var, as op{...}). Fixture: 5 rules; a uses subst{, d uses bdepth{,
# b uses none, c is commented out, e uses substl{ (a different operator). Want L1M.binder=2, and REVIVED=1 (hoas_lang's 1).
R10="$F/ml10/vir-metaprl/theories/vir"; mkdir -p "$R10"
printf 'interactive a :\n   sequent { <H> >- subst{%se; %sv} in BTerm }\n\ninteractive b : foo{%sx}\n(* interactive c : bind{x. %st} *)\ninteractive_rw d : bdepth{%se} <--> 0\ninteractive e : substl{%sx}\n' "'" "'" "'" "'" "'" "'" > "$R10/virl1_b.ml"
printf 'interactive h : var{0; 1} in BTerm\n' > "$R10/virl1_hoas_lang.ml"
check30() { local o; o=$(python3 "$1" --arm metaprll1 "$F/ml10")
  [ "$(g6 "$o" L1M.binder)" = 3 ] && [ "$(g6 "$o" L1M.binder.revived)" = 1 ] && [ "$(g6 "$o" L1M.binder.substOnly)" = 1 ]; }
if check30 "$H/count.py"; then say "ARM30 metaprll1 binder fixture OK (binder=3, revived=1, substOnly=1)"
else say "ARM30 metaprll1 binder fixture FAIL"; python3 "$H/count.py" --arm metaprll1 "$F/ml10"; fail=1; fi
sed 's/(subst|bind|bdepth|var)\\{/(subst|bind|bdepth|var)/' "$H/count.py" > "$F/mutant30.py"
if cmp -s "$H/count.py" "$F/mutant30.py"; then say "ARM30 mutant NOT PLANTED"; fail=1
elif check30 "$F/mutant30.py"; then say "ARM30 mutant SURVIVED (substl read as subst)"; fail=1
else say "ARM30 mutant KILLED"; fi

# (31) W1b's PIN figure, MetaPRL (the 14th head): prims READ AT THE PIN (git show, never the working tree) in the reflection
# theories (theories/itt/reflection, obsolete/ excluded) and the integer theory (itt_int_base + itt_int_ext). Fixture: pin P
# has reflection/core/x.ml (2 live prims + 1 commented), reflection/obsolete/y.ml + obsolete_flat/z.ml (1 prim each, NOT in
# reflection/MetaprlInfo's DIRS), core/itt_int_base.ml (1 prim);
# HEAD adds a prim to x.ml. Want pinReflection=2, pinInt=1.
R11="$F/ml11/vir-metaprl"; mkdir -p "$R11/theories/itt/reflection/core" "$R11/theories/itt/reflection/obsolete" "$R11/theories/itt/core" "$R11/theories/vir"
git -C "$R11" init -q; git -C "$R11" config user.email t@t; git -C "$R11" config user.name t
printf 'prim a : x\nprim b : y\n(* prim c : z *)\n' > "$R11/theories/itt/reflection/core/x.ml"
printf 'prim o : x\n' > "$R11/theories/itt/reflection/obsolete/y.ml"; printf 'prim i : x\n' > "$R11/theories/itt/core/itt_int_base.ml"
mkdir -p "$R11/theories/itt/reflection/obsolete_flat"; printf 'prim f : x\n' > "$R11/theories/itt/reflection/obsolete_flat/z.ml"
printf 'DIRS[] =\n    core\n#    obsolete\n\nVirtualTheory($(DIRS))\n' > "$R11/theories/itt/reflection/MetaprlInfo"
printf 'interactive v : x\n' > "$R11/theories/vir/virl1_v.ml"
git -C "$R11" add -A; git -C "$R11" commit -qm P; P11=$(git -C "$R11" rev-parse HEAD)
printf 'prim d : w\n' >> "$R11/theories/itt/reflection/core/x.ml"; git -C "$R11" commit -qam H
check31() { local o; o=$(VIR_L1M_PIN=$P11 VIR_L1M_FLOOR=$P11 python3 "$1" --arm metaprll1 "$F/ml11")
  [ "$(g6 "$o" L1M.pinReflection)" = 2 ] && [ "$(g6 "$o" L1M.pinInt)" = 1 ]; }
if check31 "$H/count.py"; then say "ARM31 metaprll1 pin-prims fixture OK (pinReflection=2 pinInt=1)"
else say "ARM31 metaprll1 pin-prims fixture FAIL"; VIR_L1M_PIN=$P11 VIR_L1M_FLOOR=$P11 python3 "$H/count.py" --arm metaprll1 "$F/ml11"; fail=1; fi
sed "s/if p.split('\\/')\\[3\\] in built:/if True:/" "$H/count.py" > "$F/mutant31.py"
if cmp -s "$H/count.py" "$F/mutant31.py"; then say "ARM31 mutant NOT PLANTED"; fail=1
elif check31 "$F/mutant31.py"; then say "ARM31 mutant SURVIVED (an unbuilt dir counted at the pin)"; fail=1
else say "ARM31 mutant KILLED"; fi

# (32) W6 at L1, MetaPRL (the 14th head): uses of itt_bar's fix_intro (its ONLY fixpoint rule, and it IS fixpoint induction, so
# "uses the fixpoint" and "uses leastness" are one rule there) in the PROOF scripts virl1_*.prla. Fixture: virl1_k2.prla uses it
# twice, virl1_den.prla once plus a near-miss fix_intro2, itt_bar.prla once (framework, not counted). Want fix=3, fixK2=2.
R12="$F/ml12/vir-metaprl/theories/vir"; mkdir -p "$R12"
printf 'x fix_intro y\nz fix_intro\n' > "$R12/virl1_k2.prla"; printf 'fix_intro fix_intro2\n' > "$R12/virl1_den.prla"
printf 'fix_intro\n' > "$R12/itt_bar.prla"; printf 'interactive q : r\n' > "$R12/virl1_k2.ml"
check32() { local o; o=$(python3 "$1" --arm metaprll1 "$F/ml12")
  [ "$(g6 "$o" L1M.fix)" = 3 ] && [ "$(g6 "$o" L1M.fixK2)" = 2 ]; }
if check32 "$H/count.py"; then say "ARM32 metaprll1 fix fixture OK (fix=3 fixK2=2)"
else say "ARM32 metaprll1 fix fixture FAIL"; python3 "$H/count.py" --arm metaprll1 "$F/ml12"; fail=1; fi
sed "s/FIXI_RE = re.compile(r'(?<!\\[A-Za-z0-9_])fix_intro(?!\\[A-Za-z0-9_])')/FIXI_RE = re.compile(r'fix_intro')/" "$H/count.py" > "$F/mutant32.py"
if cmp -s "$H/count.py" "$F/mutant32.py"; then say "ARM32 mutant NOT PLANTED"; fail=1
elif check32 "$F/mutant32.py"; then say "ARM32 mutant SURVIVED (fix_intro2 read as fix_intro)"; fail=1
else say "ARM32 mutant KILLED"; fi
# (33) W3 on L1, MetaPRL (STATUS-vir row 98; mojave's category declaration 2026-11-03 06:38, before any extension commit): the
# DEFINE/DECLARE items of virl1_{sig,syntax} (syntax) · {eval,step} (step) · typing · den, keyed by the defined TERM, compared at
# two shas with comments stripped. Σ-instance names (the nine prims and their _op, sig1, interp, pty, pty1) and the K programs
# (lit*, k*) are not central. Fixture: E1 edits interp (Σ), adds declare l1_max, edits k1, changes only a COMMENT in aeval; E2
# edits aeval's body. Want E1: categories 0, altCentral 1, added 1; E2: categories 1 (step).
R13="$F/ml13"; mkdir -p "$R13/theories/vir"; git -C "$R13" init -q; git -C "$R13" config user.email t@t; git -C "$R13" config user.name t
printf "define unfold_aeval : aeval{'a} <--> x\ndefine unfold_interp : interp{'p} <--> y\n" > "$R13/theories/vir/virl1_eval.ml"
printf "declare l1_add\ndeclare l1_app{'a}\n" > "$R13/theories/vir/virl1_sig.ml"
printf "define unfold_k1 : k1 <--> z\n" > "$R13/theories/vir/virl1_syntax.ml"
git -C "$R13" add -A; git -C "$R13" commit -qm B; B13=$(git -C "$R13" rev-parse HEAD)
printf "(* note *) define unfold_aeval : aeval{'a} <--> x\ndefine unfold_interp : interp{'p} <--> y2\n" > "$R13/theories/vir/virl1_eval.ml"
printf "declare l1_add\ndeclare l1_app{'a}\ndeclare l1_max\n" > "$R13/theories/vir/virl1_sig.ml"
printf "define unfold_k1 : k1 <--> z2\n" > "$R13/theories/vir/virl1_syntax.ml"
git -C "$R13" commit -qam E1; E13=$(git -C "$R13" rev-parse HEAD)
printf "(* note *) define unfold_aeval : aeval{'a} <--> x3\ndefine unfold_interp : interp{'p} <--> y2\n" > "$R13/theories/vir/virl1_eval.ml"
git -C "$R13" commit -qam E2; G13=$(git -C "$R13" rev-parse HEAD)
check33() { local o q; o=$(python3 "$1" --arm v3l1m --base "$B13" --ext "$E13" "$R13"); q=$(python3 "$1" --arm v3l1m --base "$E13" --ext "$G13" "$R13")
  [ "$(g6 "$o" W3M.categories)" = 0 ] && [ "$(g6 "$o" W3M.categories.altCentral)" = 1 ] && [ "$(g6 "$o" W3M.added)" = 1 ] && [ "$(g6 "$q" W3M.categories)" = 1 ]; }
if check33 "$H/count.py"; then say "ARM33 v3l1m fixture OK (E1: 0 / alt 1 / added 1; E2: 1)"
else say "ARM33 v3l1m fixture FAIL"; python3 "$H/count.py" --arm v3l1m --base "$B13" --ext "$E13" "$R13"; fail=1; fi
sed "s/        t = strip_ml_comments(g('show', sha + ':' + path).stdout)/        t = g('show', sha + ':' + path).stdout/" "$H/count.py" > "$F/mutant33.py"
if cmp -s "$H/count.py" "$F/mutant33.py"; then say "ARM33 mutant NOT PLANTED"; fail=1
elif check33 "$F/mutant33.py"; then say "ARM33 mutant SURVIVED (a comment-only change counted as an edit)"; fail=1
else say "ARM33 mutant KILLED"; fi

# (34) W3b, MetaPRL (amend-17 (iii)b; STATUS-vir row 115): beside the category count, the RULES (interactive/prim) edited or added
# across theories/vir/*.ml, and the stored-proof archives (.prla) changed. Fixture: base has rule r1 and r2 in virl1_x.ml and
# virl1_x.prla; ext edits r1, adds r3, leaves r2, changes virl1_x.prla, and adds a comment-only change above r2. Want
# rulesEdited=1, rulesAdded=1, prlaChanged=1.
R14="$F/ml14"; mkdir -p "$R14/theories/vir"; git -C "$R14" init -q; git -C "$R14" config user.email t@t; git -C "$R14" config user.name t
printf "interactive r1 : a\ninteractive r2 : b\n" > "$R14/theories/vir/virl1_x.ml"; printf "p1\n" > "$R14/theories/vir/virl1_x.prla"
git -C "$R14" add -A; git -C "$R14" commit -qm B; B14=$(git -C "$R14" rev-parse HEAD)
printf "interactive r1 : a2\ninteractive r2 : b\n(* note *)\ninteractive r3 : c\n" > "$R14/theories/vir/virl1_x.ml"; printf "p2\n" > "$R14/theories/vir/virl1_x.prla"
git -C "$R14" commit -qam E; E14=$(git -C "$R14" rev-parse HEAD)
check34() { local o; o=$(python3 "$1" --arm v3l1m --base "$B14" --ext "$E14" "$R14")
  [ "$(g6 "$o" W3M.rulesEdited)" = 1 ] && [ "$(g6 "$o" W3M.rulesAdded)" = 1 ] && [ "$(g6 "$o" W3M.prlaChanged)" = 1 ]; }
if check34 "$H/count.py"; then say "ARM34 v3l1m W3b fixture OK (rulesEdited=1 rulesAdded=1 prlaChanged=1)"
else say "ARM34 v3l1m W3b fixture FAIL"; python3 "$H/count.py" --arm v3l1m --base "$B14" --ext "$E14" "$R14"; fail=1; fi
sed "s/        rt = strip_ml_comments(g('show', sha + ':' + p).stdout)/        rt = g('show', sha + ':' + p).stdout/" "$H/count.py" > "$F/mutant34.py"
if cmp -s "$H/count.py" "$F/mutant34.py"; then say "ARM34 mutant NOT PLANTED"; fail=1
elif check34 "$F/mutant34.py"; then say "ARM34 mutant SURVIVED (a comment glued onto r2 read as an edit)"; fail=1
else say "ARM34 mutant KILLED"; fi

# (35) amend-16 Y3/Y4 (count.py --arm l2): the closure line is REFUSED unless the newest closure log's PROOF control reads
# typing2 > 0 (a closure that follows statements only reads it 0: l2 mutant-001), and Y4 counts the frame rule's explicit
# binder groups. Fixture A: control 0, frame 5 => Y3.control 0, Y3.frame 0 REFUSED. Fixture B: control 9, frame 3, in the
# NEWER of two logs => Y3.frame 3; binders 3 (a side condition planted). Mutant: the control check removed => A reads 5.
for x in A B; do mkdir -p "$F/l2$x/VIRL2" "$F/l2$x/logs"; done
printf 'theorem frame {P} (R : Assn) (h : Triple P e Q) : Triple P e Q := by\n  exact h\n' > "$F/l2A/VIRL2/L.lean"
printf 'theorem frame {P} (R : Assn) (hx : Disjoint R P) (h : Triple P e Q) : Triple P e Q := by\n  exact h\n' > "$F/l2B/VIRL2/L.lean"
printf 'closure control_proof_uses_typing: constants 2 · VIRL2 0 · typing2 0\nclosure VIRL2.frame: constants 9 · VIRL2 1 · typing2 5\n' > "$F/l2A/logs/closure-001.log"
printf 'closure control_proof_uses_typing: constants 2 · VIRL2 0 · typing2 0\nclosure VIRL2.frame: constants 9 · VIRL2 1 · typing2 7\n' > "$F/l2B/logs/closure-001.log"
printf 'closure control_proof_uses_typing: constants 9 · VIRL2 2 · typing2 9\nclosure VIRL2.frame: constants 9 · VIRL2 1 · typing2 3\n' > "$F/l2B/logs/closure-002.log"
check35() { local a b; a=$(python3 "$1" --arm l2 "$F/l2A"); b=$(python3 "$1" --arm l2 "$F/l2B")
  [ "$(g6 "$a" L2.Y3.control)" = 0 ] && [ "$(g6 "$a" L2.Y3.frame)" = 0 ] && [ "$(g6 "$b" L2.Y3.control)" = 1 ] &&
  [ "$(g6 "$b" L2.Y3.frame)" = 3 ] && [ "$(g6 "$a" L2.Y4.frameExplicitBinders)" = 2 ] && [ "$(g6 "$b" L2.Y4.frameExplicitBinders)" = 3 ]; }
if check35 "$H/count.py"; then say "ARM35 l2 Y3/Y4 fixture OK (A refused, B frame=3 from the newer log, binders 2 then 3)"
else say "ARM35 l2 Y3/Y4 fixture FAIL"; python3 "$H/count.py" --arm l2 "$F/l2A"; python3 "$H/count.py" --arm l2 "$F/l2B"; fail=1; fi
sed "s/        ok = 1 if ctl is not None and ctl > 0 else 0/        ok = 1/" "$H/count.py" > "$F/mutant35.py"
if cmp -s "$H/count.py" "$F/mutant35.py"; then say "ARM35 mutant NOT PLANTED"; fail=1
elif check35 "$F/mutant35.py"; then say "ARM35 mutant SURVIVED (a closure with a dead proof control was scored)"; fail=1
else say "ARM35 mutant KILLED"; fi

# (36) amend-16 Y5 (count.py --arm l2; STATUS-vir row 124): Y5.closed / Y5.open by name; Y5.fuelInStatement = fuel tokens
# (Nat · fuel · run · stepFn) in THOSE TWO statements (amend-16 Y5 is FALSIFIED if it cannot be stated without fuel);
# Y5.boundsInTyping = bound premises (< · ≤ · InRegion · lookup) inside the ⊢₂ inductives (FALSIFIED under (ii) if ⊢₂ needs
# one). Fixture C: both theorems, clean => 1 1 0 0. Fixture D: no y5_closed, y5_open's statement carries a Nat, HasType₂
# carries i < n => 0 1 1 1. Mutant: the fuel scan reads y5_closed's statement only => D reads fuel 0.
for x in C D; do mkdir -p "$F/l2$x/VIRL2" "$F/l2$x/logs"; done
printf 'inductive HasType₂ : Ctx -> Tm -> Prop where\n  | ret {G a} : HasType₂ G (.ret a)\nend\n' > "$F/l2C/VIRL2/Typing2.lean"
printf 'theorem y5_closed {e t} (h : HasType₂ [] [] e t) : TripleIF emp e (Y5Post t) := by\n  exact rt h\n\ntheorem y5_open {G D e t vs O} (h : HasType₂ G D e t) (hb : Binds G D vs O) : TripleIF (OwnAll O) e (Y5Post t) := by\n  exact rt h\n' > "$F/l2C/VIRL2/Y5.lean"
printf 'inductive HasType₂ : Ctx -> Tm -> Prop where\n  | load {G a i n} : i < n -> HasType₂ G (.ret a)\nend\n' > "$F/l2D/VIRL2/Typing2.lean"
printf 'theorem y5_open {G D e t vs O} (k : Nat) (h : HasType₂ G D e t) : TripleIF (OwnAll O) e (Y5Post t) := by\n  exact rt h\n' > "$F/l2D/VIRL2/Y5.lean"
check36() { local c d; c=$(python3 "$1" --arm l2 "$F/l2C"); d=$(python3 "$1" --arm l2 "$F/l2D")
  [ "$(g6 "$c" L2.Y5.closed)" = 1 ] && [ "$(g6 "$c" L2.Y5.open)" = 1 ] && [ "$(g6 "$c" L2.Y5.fuelInStatement)" = 0 ] &&
  [ "$(g6 "$c" L2.Y5.boundsInTyping)" = 0 ] && [ "$(g6 "$d" L2.Y5.closed)" = 0 ] && [ "$(g6 "$d" L2.Y5.open)" = 1 ] &&
  [ "$(g6 "$d" L2.Y5.fuelInStatement)" = 1 ] && [ "$(g6 "$d" L2.Y5.boundsInTyping)" = 1 ]; }
if check36 "$H/count.py"; then say "ARM36 l2 Y5 fixture OK (C: 1 1 0 0; D: 0 1 1 1)"
else say "ARM36 l2 Y5 fixture FAIL"; python3 "$H/count.py" --arm l2 "$F/l2C"; python3 "$H/count.py" --arm l2 "$F/l2D"; fail=1; fi
sed "s/for b in y5.values()),/for b in [y5.get('y5_closed', '')]),/" "$H/count.py" > "$F/mutant36.py"
if cmp -s "$H/count.py" "$F/mutant36.py"; then say "ARM36 mutant NOT PLANTED"; fail=1
elif check36 "$F/mutant36.py"; then say "ARM36 mutant SURVIVED (a fuel premise in y5_open went unread)"; fail=1
else say "ARM36 mutant KILLED"; fi

# (39) amend-19 on the Lean arm (count.py --arm ind DIR): I3 proof lines of the rule's theorems (ind_ty ind_atom ind_atoms ind_tm
# three_sorted_induction, the statement excluded) and AUXILIARY lemmas (any other theorem in Induction.lean); I6 the W3 premises
# (X1… binders); I2 theorems in the newest ind-audit log outside the standard three. Fixture I: the five, 3 proof lines in all,
# 2 X premises, a clean audit => 3 0 2 0. Fixture J: one extra lemma, an audit line with sorryAx => aux 1, I2 1.
# Mutant: aux lemmas counted from the five names' complement read as 0 => J reads aux 0.
for x in I J; do mkdir -p "$F/ind$x/VIRL1" "$F/ind$x/logs"; done
printf 'variable (X1 : P) (X2 : Q)\ntheorem ind_ty : A\n  | x => h\ntheorem ind_atom : B := by\n  exact h\ntheorem three_sorted_induction : C :=\n  h\n' > "$F/indI/VIRL1/Induction.lean"
printf "'VIRL1.ind_ty' does not depend on any axioms\n'VIRL1.three_sorted_induction' depends on axioms: [propext]\n" > "$F/indI/logs/ind-audit-001.log"
printf 'variable (X1 : P)\ntheorem helper : D := h\ntheorem ind_ty : A\n  | x => h\n' > "$F/indJ/VIRL1/Induction.lean"
printf "'VIRL1.ind_ty' depends on axioms: [propext, sorryAx]\n" > "$F/indJ/logs/ind-audit-001.log"
check39() { local i j; i=$(python3 "$1" --arm ind "$F/indI"); j=$(python3 "$1" --arm ind "$F/indJ")
  [ "$(g6 "$i" IND.I3.proofLines)" = 3 ] && [ "$(g6 "$i" IND.I3.auxLemmas)" = 0 ] && [ "$(g6 "$i" IND.I6.w3Premises)" = 2 ] &&
  [ "$(g6 "$i" IND.I2.nonStandard)" = 0 ] && [ "$(g6 "$j" IND.I3.auxLemmas)" = 1 ] && [ "$(g6 "$j" IND.I2.nonStandard)" = 1 ]; }
if check39 "$H/count.py"; then say "ARM39 ind fixture OK (I: 3 0 2 0; J: aux 1, I2 1)"
else say "ARM39 ind fixture FAIL"; python3 "$H/count.py" --arm ind "$F/indI"; python3 "$H/count.py" --arm ind "$F/indJ"; fail=1; fi
sed "s/aux = \[n for n in thm if n not in IND_NAMES\]/aux = []/" "$H/count.py" > "$F/mutant39.py"
if cmp -s "$H/count.py" "$F/mutant39.py"; then say "ARM39 mutant NOT PLANTED"; fail=1
elif check39 "$F/mutant39.py"; then say "ARM39 mutant SURVIVED (an auxiliary lemma went uncounted)"; fail=1
else say "ARM39 mutant KILLED"; fi

# (40) amend-19 on the MetaPRL arm (--arm indm): a git fixture whose counts are fixed by its construction.
# base: theories/vir/virl1_sig.ml (core_ops a_op b_op c_op; sig1 d_op, shapes {} {0;0} {0;1} {}: 3 distinct) + virl1_old.ml.
# ext: virl1_old.ml UNCHANGED but for a comment; NEW virl1_induct.ml (unpack lemmas for shapes nil and 0::0, one prim)
# + virl1_induct.prla: rule l1_op_induction (root step + 1 subgoal step + 1 EXTRA step, which is NOT the proof) and
# rule l1_induction (one step naming l1_op_induction and helper_s), helper_s (one step).
R40="$F/indm"; mkdir -p "$R40/theories/vir" "$R40/theories/itt"; git -C "$R40" init -q; git -C "$R40" config user.email t@t; git -C "$R40" config user.name t
cat > "$R40/theories/vir/virl1_sig.ml" <<'EOS'
define unfold_a_op : a_op <--> operator[(l1_a):op]
define unfold_b_op : b_op <--> operator[(l1_b{it; it}):op]
define unfold_c_op : c_op <--> operator[(l1_c{it; x. it}):op]
define unfold_d_op : d_op <--> operator[(l1_d):op]
define unfold_z_op : z_op <--> operator[(l1_z{it; x, y. it}):op]
define unfold_core_ops : core_ops <-->
   a_op :: b_op :: c_op :: nil
define unfold_sig1 : sig1 <-->
   ((nil), ((d_op :: nil), nil))
EOS
printf 'interactive old_r :\n   sequent { <H> >- \x27a }\n' > "$R40/theories/vir/virl1_old.ml"
git -C "$R40" add -A; git -C "$R40" commit -qm base; B40=$(git -C "$R40" rev-parse HEAD)
printf '(* a comment only *)\n' >> "$R40/theories/vir/virl1_old.ml"
cat > "$R40/theories/vir/virl1_induct.ml" <<'EOS'
interactive unpack_s 'd :
   sequent { <H> >- compatible_shapes{'d; nil; 'subs} } -->
   sequent { <H> >- ('subs ~ (nil)) }
interactive unpack_s00 'd :
   sequent { <H> >- compatible_shapes{'d; 0 :: 0 :: nil; 'subs} } -->
   sequent { <H> >- 'subs }
(* interactive unpack_s01 'd : sequent { <H> >- compatible_shapes{'d; 0 :: 1 :: nil; 'subs} } *)
prim new_prim : sequent { <H> >- 'a } = it
interactive helper_s : sequent { <H> >- 'a }
interactive l1_op_induction : sequent { <H> >- 'a }
interactive l1_induction : sequent { <H> >- 'a }
EOS
W_ROOT="(dT 0 thenT helper_x y)"; W_SUB="a b c"; W_EXTRA="e1 e2 e3 e4 e5 e6"; W_IND="(l1_op_induction thenT helper_s)"; W_HELP="autoT x"
{ printf '#PRL version 1.0.28 ASCII term\n'
  printf 'NSummary!rule\trule\trule Summary\nNSummary!ext_rule\text_rule\text_rule Summary\nNSummary!interactive\tinteractive\tinteractive Summary\n'
  printf 'NSummary!status_incomplete\tstatus_incomplete\tstatus_incomplete Summary\nNSummary!ext_unjustified\text_unjustified\text_unjustified Summary\n'
  printf 'NPerv!xnil\txnil\txnil Perv\nNPerv!xcons\txcons\txcons Perv\nNPerv!rule\trule9\trule Perv\n'
  printf 'O\tost\tstatus_incomplete\nT\ttst\tost\nB\tbst\ttst\nO\tou\text_unjustified\nT\ttu\tou\nB\tbu\ttu\n'
  printf 'O\ton\txnil\nT\ttn\ton\nB\tbn\ttn\nO\toc\txcons\nO\toi\tinteractive\nO\tdecoy\trule9 pdn\nP\tpdn\tString decoy\n'
  step() { printf 'P\tp%s\tString "%s"\nO\to%s\text_rule p%s\n' "$1" "$2" "$1" "$1"; }
  step sub "$W_SUB"; printf 'T\ttsub\tosub bst bu bn bn\nB\tbsub\ttsub\nT\ttls\toc bsub bn\nB\tbls\ttls\n'
  step ex "$W_EXTRA"; printf 'T\ttex\toex bst bu bn bn\nB\tbex\ttex\nT\ttlx\toc bex bn\nB\tblx\ttlx\n'
  step root "$W_ROOT"; printf 'T\ttroot\toroot bst bu bls blx\nB\tbroot\ttroot\nT\ttir\toi broot\nB\tbir\ttir\n'
  printf 'P\tpn1\tString l1_op_induction\nO\tor1\trule pn1\nT\ttr1\tor1 bir bn\n'
  step ind "$W_IND"; printf 'T\ttind\toind bst bu bn bn\nB\tbind\ttind\nT\ttii\toi bind\nB\tbii\ttii\n'
  printf 'P\tpn2\tString l1_induction\nO\tor2\trule pn2\nT\ttr2\tor2 bii bn\n'
  step help "$W_HELP"; printf 'T\tthelp\tohelp bst bu bn bn\nB\tbhelp\tthelp\nT\ttih\toi bhelp\nB\tbih\ttih\n'
  printf 'P\tpn3\tString helper_s\nO\tor3\trule pn3\nT\ttr3\tor3 bih bn\nT\ttdecoy\tdecoy bn\n'
} > "$R40/theories/vir/virl1_induct.prla"
git -C "$R40" add -A; git -C "$R40" commit -qm ext; X40=$(git -C "$R40" rev-parse HEAD)
wc_w() { printf '%s\n' "$1" | wc -w | tr -d ' '; }
E40_U=$(( $(wc_w "$W_ROOT") + $(wc_w "$W_SUB") )); E40_S=$(( $(wc_w "$W_IND") + $(wc_w "$W_HELP") )); E40_X=$(wc_w "$W_EXTRA")
check40() {
  o=$(python3 "$1" --arm indm --base "$B40" --ext "$X40" "$R40") || return 1
  v() { printf '%s\n' "$o" | awk -F'\t' -v c="$1" '$2==c{print $3}'; }
  [ "$(v INDM.I1.rulesEdited)" = 0 ] && [ "$(v INDM.I1.defsEdited)" = 0 ] && [ "$(v INDM.I1.prlaChanged)" = 0 ] \
  && [ "$(v INDM.I2.newPrims)" = 1 ] && [ "$(v INDM.I4a.arityShapes)" = 3 ] && [ "$(v INDM.I4a.unpackLemmas)" = 2 ] \
  && [ "$(v INDM.I4a.shapesCovered)" = 2 ] && [ "$(v INDM.rules)" = 3 ] \
  && [ "$(v INDM.I5.U.C5tok)" = "$E40_U" ] && [ "$(v INDM.I5.S.C5tok)" = "$E40_S" ] \
  && [ "$(v INDM.I4b.C5tok)" = "$((E40_U + E40_S))" ] && [ "$(v INDM.extras.C5tok)" = "$E40_X" ] \
  && [ "$(v INDM.I4a.unpack.U)" = 0 ] && [ "$(v INDM.I4a.unpack.notU)" = 2 ] && [ "$(v INDM.I5.U.rules)" = 1 ] && [ "$(v INDM.I5.S.rules)" = 2 ] && [ "$(v INDM.I5.neither)" = 0 ]
}
if check40 "$H/count.py"; then say "ARM40 indm fixture OK (I1 0/0/0; prim 1; shapes 3, lemmas 2; U $E40_U S $E40_S, extras $E40_X kept out)"
else say "ARM40 indm fixture FAIL"; python3 "$H/count.py" --arm indm --base "$B40" --ext "$X40" "$R40"; fail=1; fi
sed 's/xs += a\[0\] + a\[2\]; xw += a\[1\] + a\[3\]  # EXTRAS/s += a[0] + a[2]; w += a[1] + a[3]  # EXTRAS/' "$H/count.py" > "$F/mutant40.py"
if cmp -s "$H/count.py" "$F/mutant40.py"; then say "ARM40 mutant NOT PLANTED"; fail=1
elif check40 "$F/mutant40.py"; then say "ARM40 mutant SURVIVED (stale extras counted as proof)"; fail=1
else say "ARM40 mutant KILLED"; fi

# (41) the MetaPRL L2 column (--arm metaprll2): a git fixture whose counts are fixed by its construction.
# base: virl1_a.ml (rule r1) + itt_bar.ml. ext: virl1_a.ml + a comment only; NEW virl1_new.ml (an L1 addendum, beside);
# virl2_typing (ty_r) · virl2_triple (triple_frame using helper_h and naming ty_rx, a DIFFERENT rule; helper_h) ·
# virl2_tot (tot_r using ty_r: the live control) · virl2_store.ml with a COMMENTED prim (not counted) · NEW itt_bar_list.ml
# with 2 prims (framework, beside Y1).
R41="$F/l2m"; mkdir -p "$R41/theories/vir"; git -C "$R41" init -q; git -C "$R41" config user.email t@t; git -C "$R41" config user.name t
printf 'interactive r1 :\n   sequent { <H> >- \x27a }\n' > "$R41/theories/vir/virl1_a.ml"; printf 'prim old_bar : sequent { <H> >- \x27a } = it\n' > "$R41/theories/vir/itt_bar.ml"
git -C "$R41" add -A; git -C "$R41" commit -qm base; B41=$(git -C "$R41" rev-parse HEAD)
printf '(* comment *)\n' >> "$R41/theories/vir/virl1_a.ml"; printf 'interactive n1 : sequent { <H> >- \x27a }\n' > "$R41/theories/vir/virl1_new.ml"
printf 'prim p1 : sequent { <H> >- \x27a } = it\nprim_rw p2 : \x27a <--> \x27a\n' > "$R41/theories/vir/itt_bar_list.ml"
printf 'extends Itt_bar_list\nextends Virl2_store\nprim pv : sequent { <H> >- adm{Store} } = it\n' > "$R41/theories/vir/itt_bar_res.ml"
printf 'extends Itt_bar_list\nextends Virl2_store\nprim pg : sequent { <H> >- adm{list{int}} } = it\n' > "$R41/theories/vir/itt_bar_gen.ml"
printf 'extends Itt_bar_list\nprim pm : sequent { <H> >- adm{list{int}} } = it\n' > "$R41/theories/vir/itt_bar_mli.ml"
printf 'extends Itt_bar_list\nrule pm : sequent { <H> >- adm{Store} }\n' > "$R41/theories/vir/itt_bar_mli.mli"
printf 'define unfold_Store : Store <--> list{int}\n(* prim hidden : sequent { <H> >- \x27a } = it *)\ninteractive st_r : sequent { <H> >- \x27a }\ninteractive ty_rx : sequent { <H> >- \x27a }\n' > "$R41/theories/vir/virl2_store.ml"
printf 'define unfold_tcx : tcx{\x27a} <--> \x27a\ninteractive ty_r : sequent { <H> >- \x27a }\ninteractive ty_rx : sequent { <H> >- \x27a }\ninteractive ty_use : sequent { <H> >- \x27a }\n' > "$R41/theories/vir/virl2_typing.ml"
Y4N=2; printf 'interactive triple_frame :\n   [wf] sequent { <H> >- \x27a } -->\n   sequent { <H> >- \x27b } -->\n   sequent { <H> >- \x27c }\ninteractive helper_h : sequent { <H> >- \x27a }\n' > "$R41/theories/vir/virl2_triple.ml"
printf 'interactive tot_r : sequent { <H> >- tcx{\x27a} }\n' > "$R41/theories/vir/virl2_tot.ml"
prla() { # $1 file, then name=text pairs
  f=$1; shift
  { printf '#PRL version 1.0.28 ASCII term\n'
    printf 'NSummary!rule\trule\trule Summary\nNSummary!ext_rule\text_rule\text_rule Summary\nNSummary!interactive\tinteractive\tinteractive Summary\n'
    printf 'NSummary!status_incomplete\tsi\tstatus_incomplete Summary\nNSummary!ext_unjustified\teu\text_unjustified Summary\nNPerv!xnil\txnil\txnil Perv\n'
    printf 'O\tost\tsi\nT\ttst\tost\nB\tbst\ttst\nO\tou\teu\nT\ttu\tou\nB\tbu\ttu\nO\ton\txnil\nT\ttn\ton\nB\tbn\ttn\nO\toi\tinteractive\n'
    i=0; for kv in "$@"; do n=${kv%%=*}; t=${kv#*=}; i=$((i+1))
      printf 'P\tpt%d\tString "%s"\nO\tot%d\text_rule pt%d\nT\ttt%d\tot%d bst bu bn bn\nB\tbt%d\ttt%d\nT\tti%d\toi bt%d\nB\tbi%d\tti%d\n' $i "$t" $i $i $i $i $i $i $i $i $i $i
      printf 'P\tpn%d\tString %s\nO\tor%d\trule pn%d\nT\ttr%d\tor%d bi%d bn\n' $i "$n" $i $i $i $i $i; done; } > "$f"; }
prla "$R41/theories/vir/virl2_typing.prla" "ty_r=autoT" "ty_rx=autoT" "ty_use=(ty_r thenT autoT)"
prla "$R41/theories/vir/virl2_triple.prla" "triple_frame=(helper_h thenT ty_rx_note autoT)" "helper_h=autoT"
prla "$R41/theories/vir/virl2_tot.prla" "tot_r=(ty_r thenT autoT)"
prla "$R41/theories/vir/virl2_store.prla" "st_r=autoT" "ty_rx=autoT"
git -C "$R41" add -A; git -C "$R41" commit -qm ext; X41=$(git -C "$R41" rev-parse HEAD)
check41() {
  o=$(python3 "$1" --arm metaprll2 --base "$B41" --ext "$X41" "$R41") || return 1
  v() { printf '%s\n' "$o" | awk -F'\t' -v c="$1" '$2==c{print $3}'; }
  [ "$(v L2M.files)" = 4 ] && [ "$(v L2M.Y1.prims)" = 0 ] && [ "$(v L2M.Y1.frameworkPrims)" = 3 ] && [ "$(v L2M.Y1.virDependentPrims)" = 2 ] && [ "$(v L2M.Y1.primFigure)" = 2 ] \
  && [ "$(v L2M.Y2.defsEdited)" = 0 ] && [ "$(v L2M.Y2.rulesEdited)" = 0 ] && [ "$(v L2M.Y2.newL1Files)" = 1 ] \
  && [ "$(v L2M.Y3.frameClosure)" = 2 ] && [ "$(v L2M.Y3.frameTyping)" = 0 ] && [ "$(v L2M.Y3.control)" = 2 ] \
  && [ "$(v L2M.Y3.frameTypingTerms)" = 0 ] && printf '%s\n' "$o" | awk -F'\t' '$2=="L2M.Y3.frameTyping"' | grep -q MEASURED && [ "$(v L2M.Y3.termControl)" = 1 ] \
  && [ "$(v L2M.Y4.framePremises)" = "$Y4N" ] && [ "$(v L2M.rules)" = 8 ]
}
if check41 "$H/count.py"; then say "ARM41 metaprll2 fixture OK (Y1 0 / generic fw 3 (one extends Virl2 and names no VIR term) / vir-term 2 (one by its .mli), figure 2; Y2 0 0 new 1; Y3 closure 2 typing 0 control 2 terms 0/1; Y4 $Y4N)"
else say "ARM41 metaprll2 fixture FAIL"; python3 "$H/count.py" --arm metaprll2 --base "$B41" --ext "$X41" "$R41"; fail=1; fi
sed 's/return {m for m in names if m != n and re.search(r"(?<!\[A-Za-z0-9_\x27\])%s(?!\[A-Za-z0-9_\x27\])" % re.escape(m), text)}  # REFS/return {m for m in names if m != n and m in text}  # REFS/' "$H/count.py" > "$F/mutant41.py"
if cmp -s "$H/count.py" "$F/mutant41.py"; then say "ARM41 mutant NOT PLANTED"; fail=1
elif check41 "$F/mutant41.py"; then say "ARM41 mutant SURVIVED (a name read inside a longer name)"; fail=1
else say "ARM41 mutant KILLED"; fi

find "${F:?}" -delete
echo "SELFTEST rc=$fail"
exit $fail
