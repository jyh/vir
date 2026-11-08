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

# (38) amend-18 Z rows on the Lean L3 arm (count.py --arm l3): rows present by name; Z2 casts over VIRL3; Z3 `Triple` in
# Inequality.lean; Z5 step tokens (Step₂ Steps₂ stepFn₂ run₂) inside R4's block; Z6 `frame` applications and locality-lemma
# citations inside R5_frame's proof; Z7 `fix` in the terms; Z8 proof lines of R7 and R8. Fixture G is clean (Z5 0 · Z6 1/0 ·
# Z3 0); fixture H plants a run₂ in R4's FILE-FINAL block, a load_at in R5_frame and a Triple in Inequality.lean (Z5 1 · Z6 1/1 ·
# Z3 1). Mutant: Z5 reads the statement only => H reads 0.
for x in G H; do mkdir -p "$F/l3$x/VIRL3"; done
printf 'theorem R2 : den = den := by\n  rfl\n' > "$F/l3G/VIRL3/Inequality.lean"
printf 'theorem R5_frame (R : Assn) : Triple (P ∗ R) e Q :=\n  frame R (R4 h)\n\ntheorem R4 {p} : Triple P e Q := by\n  refine letOp_rule rfl (load_at _ 87 _ _ ?_) ?_\n' > "$F/l3G/VIRL3/RouterTriple.lean"
printf 'theorem R2 : den = den := by\n  have : Triple P e Q := sorry\n  rfl\n' > "$F/l3H/VIRL3/Inequality.lean"
printf 'theorem R5_frame (R : Assn) : Triple (P ∗ R) e Q :=\n  frame R (load_at R4)\n\ntheorem R4 {p} : Triple P e Q := by\n  have := run₂_steps 80 c\n  exact h' > "$F/l3H/VIRL3/RouterTriple.lean"
check38() { local g h; g=$(python3 "$1" --arm l3 "$F/l3G"); h=$(python3 "$1" --arm l3 "$F/l3H")
  [ "$(g6 "$g" L3.Z5.stepInR4)" = 0 ] && [ "$(g6 "$g" L3.Z6.frameApps)" = 1 ] && [ "$(g6 "$g" L3.Z6.localityCited)" = 0 ] &&
  [ "$(g6 "$g" L3.Z3.tripleInR2File)" = 0 ] && [ "$(g6 "$h" L3.Z5.stepInR4)" = 1 ] && [ "$(g6 "$h" L3.Z6.localityCited)" = 1 ] &&
  [ "$(g6 "$h" L3.Z3.tripleInR2File)" = 1 ]; }
if check38 "$H/count.py"; then say "ARM38 l3 Z fixture OK (G: 0 1 0 0; H: 1 1 1 1)"
else say "ARM38 l3 Z fixture FAIL"; python3 "$H/count.py" --arm l3 "$F/l3G"; python3 "$H/count.py" --arm l3 "$F/l3H"; fail=1; fi
sed "s/len(STEP_RE.findall(proof_of(thm.get('R4', ''))))/len(STEP_RE.findall(p_statement(thm.get('R4', ''))))/" "$H/count.py" > "$F/mutant38.py"
if cmp -s "$H/count.py" "$F/mutant38.py"; then say "ARM38 mutant NOT PLANTED"; fail=1
elif check38 "$F/mutant38.py"; then say "ARM38 mutant SURVIVED (a step token in R4's proof went unread)"; fail=1
else say "ARM38 mutant KILLED"; fi

# (37) the L3 transcription check (harness/transcribe_l3.py; l3/DECLARATIONS-LEAN.md): the TEXT of inputs/L3-programs.md,
# parsed and macro-expanded by the script, against the Lean arm's printed F / U / U_tx (l3/logs/transcribe-001.log).
# Real: SAME ×3, rc 0. Mutant: RD32's first load reads offset 4+o for 3+o => every term DIFF, rc 1. Skipped (said so) where the Lean log
# is absent (a checkout without the L3 Lean arm).
TL="$H/../l3/logs/transcribe-001.log"
if [ -f "$TL" ]; then
  if python3 "$H/transcribe_l3.py" "$H/../inputs/L3-programs.md" "$TL" > "$F/t37.txt" 2>&1; then say "ARM37 transcribe L3 OK (F U U_tx SAME)"
  else say "ARM37 transcribe L3 FAIL"; cat "$F/t37.txt"; fail=1; fi
  sed "s/ld(x + '0', 3 + o,/ld(x + '0', 4 + o,/" "$H/transcribe_l3.py" > "$F/mutant37.py"
  if cmp -s "$H/transcribe_l3.py" "$F/mutant37.py"; then say "ARM37 mutant NOT PLANTED"; fail=1
  elif python3 "$F/mutant37.py" "$H/../inputs/L3-programs.md" "$TL" > /dev/null 2>&1; then say "ARM37 mutant SURVIVED"; fail=1
  else say "ARM37 mutant KILLED"; fi
else say "ARM37 SKIPPED (no l3/logs/transcribe-001.log in this checkout)"; fi
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
printf 'extends Itt_bar_res\nextends Itt_bar\ndefine unfold_Store : Store <--> list{int}\n(* prim hidden : sequent { <H> >- \x27a } = it *)\ninteractive st_r : sequent { <H> >- \x27a }\ninteractive ty_rx : sequent { <H> >- \x27a }\n' > "$R41/theories/vir/virl2_store.ml"
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
  [ "$(v L2M.files)" = 4 ] && [ "$(v L2M.Y1.prims)" = 0 ] && [ "$(v L2M.Y1.frameworkPrims)" = 3 ] && [ "$(v L2M.Y1.virDependentPrims)" = 2 ] && [ "$(v L2M.Y1.primFigure)" = 2 ] && [ "$(v L2M.trustedBase.prims)" = 4 ] && [ "$(v L2M.trustedBase.files)" = 3 ] \
  && [ "$(v L2M.Y2.defsEdited)" = 0 ] && [ "$(v L2M.Y2.rulesEdited)" = 0 ] && [ "$(v L2M.Y2.newL1Files)" = 1 ] \
  && [ "$(v L2M.Y3.frameClosure)" = 2 ] && [ "$(v L2M.Y3.frameTyping)" = 0 ] && [ "$(v L2M.Y3.control)" = 2 ] \
  && [ "$(v L2M.Y3.frameTypingTerms)" = 0 ] && printf '%s\n' "$o" | awk -F'\t' '$2=="L2M.Y3.frameTyping"' | grep -q MEASURED && [ "$(v L2M.Y3.termControl)" = 1 ] \
  && [ "$(v L2M.Y4.framePremises)" = "$Y4N" ] && [ "$(v L2M.rules)" = 8 ]
}
if check41 "$H/count.py"; then say "ARM41 metaprll2 fixture OK (Y1 0 / generic fw 3 (one extends Virl2 and names no VIR term) / vir-term 2 (one by its .mli), figure 2; trusted base 4 prims in 3 files by the extends closure, one unchanged since base; Y2 0 0 new 1; Y3 closure 2 typing 0 control 2 terms 0/1; Y4 $Y4N)"
else say "ARM41 metaprll2 fixture FAIL"; python3 "$H/count.py" --arm metaprll2 --base "$B41" --ext "$X41" "$R41"; fail=1; fi
sed 's/(set(re.findall(r"\[A-Za-z0-9_\x27\]+", text)) \& plain)/{m for m in plain if m in text}/' "$H/count.py" > "$F/mutant41.py"  # the REFS2 token path: a name read inside a longer name
if cmp -s "$H/count.py" "$F/mutant41.py"; then say "ARM41 mutant NOT PLANTED"; fail=1
elif check41 "$F/mutant41.py"; then say "ARM41 mutant SURVIVED (a name read inside a longer name)"; fail=1
else say "ARM41 mutant KILLED"; fi

# ARM42 (STATUS-vir 151): grammar carving by CONTENT. On X41 no carving predicate is defined: EMPTY, never a 0 that reads
# as a pass. On X42: one define, two rules whose statement names wfs2{ (a wf rule, a hypothesis), one naming only wfs2x{ (a
# longer name, NOT counted) and one naming none.
c42() { python3 "$1" --arm metaprll2 --base "$B41" --ext "$2" "$R41" | awk -F'\t' -v c="$3" '$2==c{print $3 "\t" $4}'; }
printf 'define unfold_wfs2 : wfs2{\x27k; \x27t} <--> \x27t\ndefine unfold_wfs2x : wfs2x{\x27t} <--> \x27t\ninteractive wfs2_wf : sequent { <H> >- wfs2{\x27k; \x27t} in bool }\ninteractive cv_pres : sequent { <H>; x: wfs2{2; \x27e} >- \x27a }\ninteractive cv_long : sequent { <H> >- wfs2x{\x27t} }\ninteractive cv_none : sequent { <H> >- \x27a }\n' > "$R41/theories/vir/virl2_sem.ml"
prla "$R41/theories/vir/virl2_sem.prla" "wfs2_wf=autoT" "cv_pres=(wfs2_wf thenT autoT)" "cv_long=autoT" "cv_none=autoT"
git -C "$R41" add -A; git -C "$R41" commit -qm carve; X42=$(git -C "$R41" rev-parse HEAD)
check42() {
  case "$(c42 "$1" "$X41" L2M.Y5.carvingDefs)" in 0*EMPTY*) ;; *) return 1;; esac
  case "$(c42 "$1" "$X41" L2M.Y5.carvingRules)" in 0*EMPTY*) ;; *) return 1;; esac
  case "$(c42 "$1" "$X42" L2M.Y5.carvingDefs)" in 1*MEASURED*) ;; *) return 1;; esac
  case "$(c42 "$1" "$X42" L2M.Y5.carvingRules)" in "2	MEASURED"*cv_pres*wfs2_wf) ;; *) return 1;; esac
}
if check42 "$H/count.py"; then say "ARM42 carving fixture OK (X41 EMPTY; X42 defs 1, rules 2 (cv_long's wfs2x not read as wfs2))"
else say "ARM42 carving fixture FAIL"; c42 "$H/count.py" "$X42" L2M.Y5.carvingRules; fail=1; fi
sed 's/(?<!\[A-Za-z0-9_\x27\])(?:%s)\\{" % \x27|\x27.join(names), stm/(?:%s)" % \x27|\x27.join(names), stm/' "$H/count.py" > "$F/mutant42.py"
if cmp -s "$H/count.py" "$F/mutant42.py"; then say "ARM42 mutant NOT PLANTED"; fail=1
elif check42 "$F/mutant42.py"; then say "ARM42 mutant SURVIVED (wfs2x read as wfs2)"; fail=1
else say "ARM42 mutant KILLED"; fi

# ARM43 (STATUS-vir 155, mojave's D9): the SCOPING carving (scoped2{n; Δ; e}, the object's §4 scoping in the arm's
# placeholder encoding) on its OWN sub-line, so its cost is never read as grammar cost; a rule naming both predicates is
# in both lines and counted once more on carvingOverlap. On X42 nothing names scoped2: EMPTY. On X43: one define, a rule
# naming scoped2 alone, a rule naming scoped2 AND wfs2 (overlap 1), and one naming only scoped2x (NOT counted).
printf 'define unfold_scoped2 : scoped2{\x27n; \x27d; \x27e} <--> \x27e\ninteractive sc_wf : sequent { <H> >- scoped2{\x27n; \x27d; \x27e} in bool }\ninteractive sc_both : sequent { <H>; x: wfs2{2; \x27e}; y: scoped2{\x27n; \x27d; \x27e} >- \x27a }\ninteractive sc_long : sequent { <H> >- scoped2x{\x27t} }\n' > "$R41/theories/vir/virl2_scope.ml"
prla "$R41/theories/vir/virl2_scope.prla" "sc_wf=autoT" "sc_both=(sc_wf thenT autoT)" "sc_long=autoT"
git -C "$R41" add -A; git -C "$R41" commit -qm scope; X43=$(git -C "$R41" rev-parse HEAD)
check43() {
  case "$(c42 "$1" "$X42" L2M.Y5.scopingDefs)" in 0*EMPTY*) ;; *) return 1;; esac
  case "$(c42 "$1" "$X43" L2M.Y5.scopingDefs)" in 1*MEASURED*) ;; *) return 1;; esac
  case "$(c42 "$1" "$X43" L2M.Y5.scopingRules)" in "2	MEASURED"*sc_both*sc_wf) ;; *) return 1;; esac
  case "$(c42 "$1" "$X43" L2M.Y5.carvingRules)" in "3	MEASURED"*) ;; *) return 1;; esac
  case "$(c42 "$1" "$X43" L2M.Y5.carvingOverlap)" in "1	"*sc_both*) ;; *) return 1;; esac
}
if check43 "$H/count.py"; then say "ARM43 scoping fixture OK (X42 EMPTY; X43 defs 1, rules 2 (sc_long's scoped2x not read), grammar rules 3, overlap 1)"
else say "ARM43 scoping fixture FAIL"; c42 "$H/count.py" "$X43" L2M.Y5.scopingRules; fail=1; fi
sed 's/L2M_SCOPE = (\x27scoped2\x27, \x27scoped\x27)/L2M_SCOPE = (\x27scoped2x\x27,)/' "$H/count.py" > "$F/mutant43.py"
if cmp -s "$H/count.py" "$F/mutant43.py"; then say "ARM43 mutant NOT PLANTED"; fail=1
elif check43 "$F/mutant43.py"; then say "ARM43 mutant SURVIVED (scoping read from the wrong name)"; fail=1
else say "ARM43 mutant KILLED"; fi

# ARM44 (STATUS-vir 170, mojave's D10): the INDEX-FAULT departure (is_ifault given the let congruence, ruled (a)
# @98,653,117) on its OWN sub-line, so its cost is counted in Y5's C5 and read beside it. On X43 nothing names is_ifault:
# EMPTY. On X44: one define, a rule naming is_ifault (the regression lemma), a wf rule naming it, a rule naming only
# ifault_op (a DIFFERENT predicate, NOT counted) and one naming is_ifaultx (a longer name, NOT counted).
printf 'define unfold_is_ifault : is_ifault{\x27c} <--> \x27c\ninteractive if_let : sequent { <H> >- is_ifault{\x27c} = btrue in bool }\ninteractive if_wf : sequent { <H> >- is_ifault{\x27c} in bool }\ninteractive if_op : sequent { <H> >- ifault_op{\x27o; \x27v; \x27s} in bool }\ninteractive if_long : sequent { <H> >- is_ifaultx{\x27c} }\n' > "$R41/theories/vir/virl2_triple.ml"
prla "$R41/theories/vir/virl2_triple.prla" "if_let=autoT" "if_wf=autoT" "if_op=autoT" "if_long=autoT"
git -C "$R41" add -A; git -C "$R41" commit -qm ifault; X44=$(git -C "$R41" rev-parse HEAD)
check44() {
  case "$(c42 "$1" "$X43" L2M.Y5.ifaultDefs)" in 0*EMPTY*) ;; *) return 1;; esac
  case "$(c42 "$1" "$X44" L2M.Y5.ifaultDefs)" in 1*MEASURED*) ;; *) return 1;; esac
  case "$(c42 "$1" "$X44" L2M.Y5.ifaultRules)" in "2	MEASURED"*if_let*if_wf) ;; *) return 1;; esac
  case "$(c42 "$1" "$X44" L2M.Y5.ifaultC5tok)" in [0-9]*BESIDE*"2 of 2"*) ;; *) return 1;; esac
  case "$(c42 "$1" "$X44" L2M.Y5.scopingRules)" in "2	MEASURED"*) ;; *) return 1;; esac
}
if check44 "$H/count.py"; then say "ARM44 index-fault fixture OK (X43 EMPTY; X44 defs 1, rules 2 (if_op and is_ifaultx not read), scoping unchanged)"
else say "ARM44 index-fault fixture FAIL"; c42 "$H/count.py" "$X44" L2M.Y5.ifaultRules; fail=1; fi
sed 's/L2M_IFAULT = (\x27is_ifault\x27, \x27ifault2\x27)/L2M_IFAULT = (\x27is_ifault\x27, \x27ifault2\x27, \x27ifault_op\x27)/' "$H/count.py" > "$F/mutant44.py"
if cmp -s "$H/count.py" "$F/mutant44.py"; then say "ARM44 mutant NOT PLANTED"; fail=1
elif check44 "$F/mutant44.py"; then say "ARM44 mutant SURVIVED (ifault_op read as the departure)"; fail=1
else say "ARM44 mutant KILLED"; fi

# ARM45 (STATUS-vir 170, mojave 517d086da): D10 as committed puts the let congruence in a SUPPORT term, ifault2, and
# is_ifault is its spread; ifault2_wf (a bterm induction) is the bulk of D10's cost. A rule naming ONLY ifault2 is D10's
# cost too, so it is read on the index-fault sub-line. On X45: X44 plus one define of ifault2 and one rule naming only it.
printf 'define unfold_ifault2 : ifault2{\x27c} <--> \x27c\ninteractive if2_wf : sequent { <H> >- ifault2{\x27c} in bool }\n' > "$R41/theories/vir/virl2_ifault.ml"
prla "$R41/theories/vir/virl2_ifault.prla" "if2_wf=autoT"
git -C "$R41" add -A; git -C "$R41" commit -qm ifault2; X45=$(git -C "$R41" rev-parse HEAD)
check45() {
  case "$(c42 "$1" "$X45" L2M.Y5.ifaultDefs)" in 2*MEASURED*) ;; *) return 1;; esac
  case "$(c42 "$1" "$X45" L2M.Y5.ifaultRules)" in "3	MEASURED"*if2_wf*) ;; *) return 1;; esac
  case "$(c42 "$1" "$X45" L2M.Y5.ifaultC5tok)" in [0-9]*BESIDE*"3 of 3"*) ;; *) return 1;; esac
}
if check45 "$H/count.py"; then say "ARM45 ifault2 fixture OK (X45 defs 2, rules 3: the support term's rule read on the D10 line)"
else say "ARM45 ifault2 fixture FAIL"; c42 "$H/count.py" "$X45" L2M.Y5.ifaultRules; fail=1; fi
sed 's/L2M_IFAULT = (\x27is_ifault\x27, \x27ifault2\x27)/L2M_IFAULT = (\x27is_ifault\x27,)/' "$H/count.py" > "$F/mutant45.py"
if cmp -s "$H/count.py" "$F/mutant45.py"; then say "ARM45 mutant NOT PLANTED"; fail=1
elif check45 "$F/mutant45.py"; then say "ARM45 mutant SURVIVED (ifault2 not read as D10)"; fail=1
else say "ARM45 mutant KILLED"; fi

# ARM46 (STATUS-vir 147, amend-20 SL1-SL8 + amend-22 D1-D4): the SLang arm, built BEFORE the MetaPRL arm's SLang sha.
# Base B46: an L1 signature (lam_op in core_ops, arrow_op in sig1), amend-19's l1_induction with two recognisers in its
# premises (is_tyterm, wfs: the derived recogniser set, so the SL4 control is live) and one pre-existing rule old_r.
# X46 (clean): a generic itt_slang (SLang, slang_ind, slang_wf) and an L1 instance virl1_slang (ssig1, L1SLang,
# l1s_induction citing slang_ind and l1s_aux). X46b (dirty): itt_slang names lam_op (SL3 1); l1s_induction's proof cites
# l1s_rec, whose statement has is_tyterm (SL4 1 through the closure, none in the root); old_r edited (SL1 rules 1).
R46="$F/r46"; mkdir -p "$R46/theories/vir"; git -C "$R46" init -q; git -C "$R46" config user.email t@t; git -C "$R46" config user.name t
printf 'define unfold_lam_op : lam_op <--> operator[(l1_lam):op]\ndefine unfold_arrow_op : arrow_op <--> operator[(l1_arrow):op]\ndefine unfold_core_ops : core_ops <-->\n   lam_op :: nil\ndefine unfold_sig1 : sig1 <-->\n   arrow_op :: nil\n' > "$R46/theories/vir/virl1_sig.ml"
printf 'define unfold_is_tyterm : is_tyterm{\x27t} <--> \x27t\ninteractive l1_induction :\n   [T2] sequent { <H>; t1: L1Lang{sig1}; is_tyterm{\x27t1} = btrue in bool; wfs{\x27t1} = btrue in bool >- \x27Pt[\x27t1] }\ninteractive old_r : sequent { <H> >- \x27a }\n' > "$R46/theories/vir/virl1_induct.ml"
prla "$R46/theories/vir/virl1_induct.prla" "l1_induction=autoT" "old_r=autoT"
git -C "$R46" add -A; git -C "$R46" commit -qm base; B46=$(git -C "$R46" rev-parse HEAD)
printf 'define unfold_SLang : SLang{\x27ss; \x27s} <--> \x27ss\ninteractive slang_ind : sequent { <H> >- SLang{\x27ss; \x27s} }\ninteractive slang_wf : sequent { <H> >- SLang{\x27ss; \x27s} Type }\n' > "$R46/theories/vir/itt_slang.ml"
prla "$R46/theories/vir/itt_slang.prla" "slang_ind=(autoT thenT dT 0)" "slang_wf=autoT"
printf 'define unfold_ssig1 : ssig1 <--> lam_op\ndefine unfold_L1SLang : L1SLang{\x27s} <--> SLang{ssig1; \x27s}\ninteractive l1s_induction : sequent { <H>; t: L1SLang{\x27s} >- \x27P[\x27t] }\ninteractive l1s_aux : sequent { <H> >- \x27a }\n' > "$R46/theories/vir/virl1_slang.ml"
prla "$R46/theories/vir/virl1_slang.prla" "l1s_induction=(slang_ind thenT l1s_aux thenT autoT)" "l1s_aux=autoT"
git -C "$R46" add -A; git -C "$R46" commit -qm slang; X46=$(git -C "$R46" rev-parse HEAD)
printf 'interactive slang_bad : sequent { <H> >- lam_op in Term }\n' >> "$R46/theories/vir/itt_slang.ml"
printf 'interactive l1s_rec : sequent { <H>; is_tyterm{\x27t} = btrue in bool >- \x27a }\n' >> "$R46/theories/vir/virl1_slang.ml"
prla "$R46/theories/vir/virl1_slang.prla" "l1s_induction=(slang_ind thenT l1s_aux thenT l1s_rec)" "l1s_aux=autoT" "l1s_rec=autoT"
sed 's/^interactive old_r : sequent { <H> >- \x27a }/interactive old_r : sequent { <H> >- \x27b }/' "$R46/theories/vir/virl1_induct.ml" > "$F/oi.ml"; mv "$F/oi.ml" "$R46/theories/vir/virl1_induct.ml"
git -C "$R46" add -A; git -C "$R46" commit -qm dirty; X46b=$(git -C "$R46" rev-parse HEAD)
c46() { VIR_SLANG_ROOT=l1s_induction python3 "$1" --arm slangm --base "$B46" --ext "$2" "$R46" | awk -F'\t' -v c="$3" '$2==c{print $3 "\t" $4}'; }
check46() {
  case "$(c46 "$1" "$X46" SLM.SL1.rulesEdited)" in "0	MEASURED"*) ;; *) return 1;; esac
  case "$(c46 "$1" "$X46" SLM.SL2.newPrims)" in "0	MEASURED"*) ;; *) return 1;; esac
  case "$(c46 "$1" "$X46" SLM.stage.fw)" in "1	MEASURED"*itt_slang*) ;; *) return 1;; esac
  case "$(c46 "$1" "$X46" SLM.stage.l1)" in "1	MEASURED"*virl1_slang*) ;; *) return 1;; esac
  case "$(c46 "$1" "$X46" SLM.SL3.hits)" in "0	MEASURED"*) ;; *) return 1;; esac
  case "$(c46 "$1" "$X46" SLM.SL4.control)" in "2	MEASURED"*is_tyterm*wfs*) ;; *) return 1;; esac
  case "$(c46 "$1" "$X46" SLM.SL4.recogHits)" in "0	MEASURED"*) ;; *) return 1;; esac
  case "$(c46 "$1" "$X46" SLM.SL5.L1.C5tok)" in "6	MEASURED"*25332*) ;; *) return 1;; esac
  case "$(c46 "$1" "$X46" SLM.SL5.total.C5tok)" in "11	MEASURED"*69794*) ;; *) return 1;; esac
  case "$(c46 "$1" "$X46" SLM.SL8.fw.rules)" in "2	MEASURED"*) ;; *) return 1;; esac
  case "$(c46 "$1" "$X46b" SLM.SL1.rulesEdited)" in "1	MEASURED"*) ;; *) return 1;; esac
  case "$(c46 "$1" "$X46b" SLM.SL3.hits)" in "1	MEASURED"*lam_op*) ;; *) return 1;; esac
  case "$(c46 "$1" "$X46b" SLM.SL4.recogHits)" in "1	MEASURED"*is_tyterm*) ;; *) return 1;; esac
  case "$(c46 "$1" "$X46b" SLM.SL4.rootStatement)" in "0	BESIDE"*) ;; *) return 1;; esac
  case "$(VIR_SLANG_ROOT=nosuch python3 "$1" --arm slangm --base "$B46" --ext "$X46" "$R46" | awk -F'\t' '$2=="SLM.SL4.recogHits"{print $4}')" in EMPTY*) ;; *) return 1;; esac
  case "$(VIR_SLANG_ROOT= python3 "$1" --arm slangm --base "$B46" --ext "$X46" "$R46" | awk -F'\t' '$2=="SLM.SL4.recogHits"{print $4}')" in Q*) ;; *) return 1;; esac
}
if check46 "$H/count.py"; then say "ARM46 slangm fixture OK (X46 SL1 0, SL3 0, SL4 0 with control 2, L1 6 tok, total 11; X46b SL1 1, SL3 1 lam_op, SL4 1 through the closure; no root => Q)"
else say "ARM46 slangm fixture FAIL"; VIR_SLANG_ROOT=l1s_induction python3 "$H/count.py" --arm slangm --base "$B46" --ext "$X46b" "$R46"; fail=1; fi
sed 's/todo += list(mpl_refs(x, RT\[x\], names))  # SLM-CLOSURE/pass  # SLM-CLOSURE/' "$H/count.py" > "$F/mutant46.py"
if cmp -s "$H/count.py" "$F/mutant46.py"; then say "ARM46 mutant NOT PLANTED"; fail=1
elif check46 "$F/mutant46.py"; then say "ARM46 mutant SURVIVED (SL4 read the root alone)"; fail=1
else say "ARM46 mutant KILLED"; fi
sed 's/^SLM_RECOG_RE = .*/SLM_RECOG_RE = re.compile(r"(?!x)x")/' "$H/count.py" > "$F/mutant46b.py"
if cmp -s "$H/count.py" "$F/mutant46b.py"; then say "ARM46 mutant-b NOT PLANTED"; fail=1
elif check46 "$F/mutant46b.py"; then say "ARM46 mutant-b SURVIVED (an empty recogniser set read as SL4 HOLDS)"; fail=1
else say "ARM46 mutant-b KILLED"; fi

# ARM47 (STATUS-vir 174): SL3.binderOnly, BESIDE. At SLang act 1 (mojave 41de5e05d) SL3 read 1 on `kids`, which vir_slang uses only
# as a BOUND name; the reader is unchanged and this row says which hits are bound names only. X47 = X46 + itt_slang binding lam_op
# (`spread{'x; lam_op, r. 'r}`, the comma-list form): hits 1, binderOnly 1. X47b = X47 + `lam_op :: nil` (a TERM, and a `::` that
# must not read as a binder colon): hits 1, binderOnly 0. X46b (lam_op as a term only): binderOnly 0.
git -C "$R46" checkout -q "$X46"
printf 'define unfold_SPick : SPick{\x27x} <--> spread{\x27x; lam_op, r. \x27r}\n' >> "$R46/theories/vir/itt_slang.ml"
git -C "$R46" add -A; git -C "$R46" commit -qm x47; X47=$(git -C "$R46" rev-parse HEAD)
printf 'define unfold_SL : SL <--> lam_op :: nil\n' >> "$R46/theories/vir/itt_slang.ml"
git -C "$R46" add -A; git -C "$R46" commit -qm x47b; X47b=$(git -C "$R46" rev-parse HEAD)
check47() {
  case "$(c46 "$1" "$X47" SLM.SL3.hits)" in "1	MEASURED"*lam_op*) ;; *) return 1;; esac
  case "$(c46 "$1" "$X47" SLM.SL3.binderOnly)" in "1	BESIDE"*itt_slang:lam_op*) ;; *) return 1;; esac
  case "$(c46 "$1" "$X47b" SLM.SL3.hits)" in "1	MEASURED"*lam_op*) ;; *) return 1;; esac
  case "$(c46 "$1" "$X47b" SLM.SL3.binderOnly)" in "0	BESIDE"*) ;; *) return 1;; esac
  case "$(c46 "$1" "$X46b" SLM.SL3.binderOnly)" in "0	BESIDE"*) ;; *) return 1;; esac
  case "$(c46 "$1" "$X46" SLM.SL3.binderOnly)" in "0	BESIDE"*) ;; *) return 1;; esac
}
if check47 "$H/count.py"; then say "ARM47 SL3.binderOnly fixture OK (X47 hits 1 binderOnly 1; X47b hits 1 binderOnly 0 with ::; X46b 0)"
else say "ARM47 SL3.binderOnly fixture FAIL"; for x in "$X47" "$X47b"; do VIR_SLANG_ROOT=l1s_induction python3 "$H/count.py" --arm slangm --base "$B46" --ext "$x" "$R46" | grep -F SL3; done; fail=1; fi
sed 's/if not SLM_BINDER_RE.match(txt, mo.end()):  # SLM-BINDER/if False:  # SLM-BINDER/' "$H/count.py" > "$F/mutant47.py"
if cmp -s "$H/count.py" "$F/mutant47.py"; then say "ARM47 mutant NOT PLANTED"; fail=1
elif check47 "$F/mutant47.py"; then say "ARM47 mutant SURVIVED (every hit read as a bound name)"; fail=1
else say "ARM47 mutant KILLED"; fi
sed 's/^SLM_BINDER_RE = .*/SLM_BINDER_RE = re.compile(r"\\s*(?:\\.|:)")/' "$H/count.py" > "$F/mutant47b.py"
if cmp -s "$H/count.py" "$F/mutant47b.py"; then say "ARM47 mutant-b NOT PLANTED"; fail=1
elif check47 "$F/mutant47b.py"; then say "ARM47 mutant-b SURVIVED (a :: read as a binder colon, or the comma list missed)"; fail=1
else say "ARM47 mutant-b KILLED"; fi

# ARM48 (STATUS-vir 181): SL6 from the ARTIFACT. VIR_SLANG_SL6 names six rules in the order type-fwd, type-bwd, atom-fwd,
# atom-bwd, expr-fwd, expr-bwd. A slot counts toward SLM.SL6.directions only if its rule is an `interactive` in an L1-stage module
# with a STORED derivation (>= 1 step) AND its statement names L1SLang and the slot's recogniser (is_tyterm for type, wfs for
# atom and expression). Sort numbers are the arm's map (D-S2), so they are printed BESIDE for the hand read, never typed here.
# X48 = X46 + six such rules, all stored: 6. X48b: expr-bwd has no stored proof and atom-bwd names is_tyterm: 4 (proved 5, recog 5).
git -C "$R46" checkout -q "$X46"
printf 'interactive sl6_tf : sequent { <H>; t: L1SLang{0} >- is_tyterm{\x27t} = btrue in bool }\ninteractive sl6_tb : sequent { <H>; is_tyterm{\x27t} = btrue in bool >- \x27t in L1SLang{0} }\ninteractive sl6_af : sequent { <H>; t: L1SLang{2} >- wfs{0; \x27t} = btrue in bool }\ninteractive sl6_ab : sequent { <H>; wfs{0; \x27t} = btrue in bool >- \x27t in L1SLang{2} }\ninteractive sl6_ef : sequent { <H>; t: L1SLang{3} >- wfs{2; \x27t} = btrue in bool }\ninteractive sl6_eb : sequent { <H>; wfs{2; \x27t} = btrue in bool >- \x27t in L1SLang{3} }\n' >> "$R46/theories/vir/virl1_slang.ml"
prla "$R46/theories/vir/virl1_slang.prla" "l1s_induction=(slang_ind thenT l1s_aux thenT autoT)" "l1s_aux=autoT" "sl6_tf=autoT" "sl6_tb=autoT" "sl6_af=autoT" "sl6_ab=autoT" "sl6_ef=autoT" "sl6_eb=autoT"
git -C "$R46" add -A; git -C "$R46" commit -qm x48; X48=$(git -C "$R46" rev-parse HEAD)
sed 's/^interactive sl6_ab : sequent { <H>; wfs{0; /interactive sl6_ab : sequent { <H>; is_tyterm{/' "$R46/theories/vir/virl1_slang.ml" > "$F/s48.ml"; mv "$F/s48.ml" "$R46/theories/vir/virl1_slang.ml"
prla "$R46/theories/vir/virl1_slang.prla" "l1s_induction=(slang_ind thenT l1s_aux thenT autoT)" "l1s_aux=autoT" "sl6_tf=autoT" "sl6_tb=autoT" "sl6_af=autoT" "sl6_ab=autoT" "sl6_ef=autoT"
git -C "$R46" add -A; git -C "$R46" commit -qm x48b; X48b=$(git -C "$R46" rev-parse HEAD)
SL6N=sl6_tf,sl6_tb,sl6_af,sl6_ab,sl6_ef,sl6_eb
c48() { VIR_SLANG_SL6="$SL6N" c46 "$@"; }
check48() {
  case "$(c48 "$1" "$X48" SLM.SL6.directions)" in "6	MEASURED"*) ;; *) return 1;; esac
  case "$(c48 "$1" "$X48" SLM.SL6.proved)" in "6	MEASURED"*) ;; *) return 1;; esac
  case "$(c48 "$1" "$X48" SLM.SL6.recogMatch)" in "6	BESIDE"*"sl6_af:L1SLang{2}/wfs{0"*) ;; *) return 1;; esac
  case "$(c48 "$1" "$X48b" SLM.SL6.directions)" in "4	MEASURED"*) ;; *) return 1;; esac
  case "$(c48 "$1" "$X48b" SLM.SL6.proved)" in "5	MEASURED"*"missing:sl6_eb"*) ;; *) return 1;; esac
  case "$(c48 "$1" "$X48b" SLM.SL6.recogMatch)" in "5	BESIDE"*) ;; *) return 1;; esac
  case "$(VIR_SLANG_SL6=sl6_tf c46 "$1" "$X48" SLM.SL6.directions)" in "1	INVALID"*) ;; *) return 1;; esac
  case "$(c46 "$1" "$X48" SLM.SL6.directions)" in "0	Q"*) ;; *) return 1;; esac
}
if check48 "$H/count.py"; then say "ARM48 SL6 fixture OK (X48 6/6; X48b 4 = proved 5 with sl6_eb missing, recog 5; one name => INVALID; unset => Q)"
else say "ARM48 SL6 fixture FAIL"; for x in "$X48" "$X48b"; do VIR_SLANG_SL6="$SL6N" VIR_SLANG_ROOT=l1s_induction python3 "$H/count.py" --arm slangm --base "$B46" --ext "$x" "$R46" | grep -F SL6; done; fail=1; fi
sed 's/if R.get(n, (0,))\[0\] > 0:  # SLM-SL6-STORED/if True:  # SLM-SL6-STORED/' "$H/count.py" > "$F/mutant48.py"
if cmp -s "$H/count.py" "$F/mutant48.py"; then say "ARM48 mutant NOT PLANTED"; fail=1
elif check48 "$F/mutant48.py"; then say "ARM48 mutant SURVIVED (a statement with no stored proof read as proved)"; fail=1
else say "ARM48 mutant KILLED"; fi
sed 's/if rx and re.search(rx, stt):  # SLM-SL6-RECOG/if True:  # SLM-SL6-RECOG/' "$H/count.py" > "$F/mutant48b.py"
if cmp -s "$H/count.py" "$F/mutant48b.py"; then say "ARM48 mutant-b NOT PLANTED"; fail=1
elif check48 "$F/mutant48b.py"; then say "ARM48 mutant-b SURVIVED (the slot's recogniser never checked)"; fail=1
else say "ARM48 mutant-b KILLED"; fi

# ARM49 (STATUS-vir 182): the SL6 STAGE. mojave puts SL6 in a NEW module (vir_l1sl6) so vir_l1slang stays byte-identical. amend-20
# SL5(a) prices "the per-form rule and everything L1-specific under it"; SL6 checks that stage and is not under the rule, so its
# rules must count for SL6's slots and get their own SL8 line, NEVER enter SL5. Stage sl6 = a NEW module, neither fw nor l1, holding
# the statement of a VIR_SLANG_SL6 rule. X49 = X46 + virl1_sl6.ml/.prla with the six rules: SL6 6/6, stage.sl6 1, SL8.sl6.rules 6,
# SL5.L1.C5tok EQUAL to X46's. Without VIR_SLANG_SL6 the module is unstaged (stage.sl6 0) and SL5 is still X46's.
git -C "$R46" checkout -q "$X46"
printf 'interactive sl6_tf : sequent { <H>; t: L1SLang{0} >- is_tyterm{\x27t} = btrue in bool }\ninteractive sl6_tb : sequent { <H>; is_tyterm{\x27t} = btrue in bool >- \x27t in L1SLang{0} }\ninteractive sl6_af : sequent { <H>; t: L1SLang{2} >- wfs{0; \x27t} = btrue in bool }\ninteractive sl6_ab : sequent { <H>; wfs{0; \x27t} = btrue in bool >- \x27t in L1SLang{2} }\ninteractive sl6_ef : sequent { <H>; t: L1SLang{3} >- wfs{2; \x27t} = btrue in bool }\ninteractive sl6_eb : sequent { <H>; wfs{2; \x27t} = btrue in bool >- \x27t in L1SLang{3} }\n' > "$R46/theories/vir/virl1_sl6.ml"
prla "$R46/theories/vir/virl1_sl6.prla" "sl6_tf=(autoT thenT dT 0)" "sl6_tb=autoT" "sl6_af=autoT" "sl6_ab=autoT" "sl6_ef=autoT" "sl6_eb=autoT"
git -C "$R46" add -A; git -C "$R46" commit -qm x49; X49=$(git -C "$R46" rev-parse HEAD)
L46=$(c46 "$H/count.py" "$X46" SLM.SL5.L1.C5tok | cut -f1)
check49() {
  case "$L46" in ''|0) return 1;; esac
  case "$(c48 "$1" "$X49" SLM.SL6.directions)" in "6	MEASURED"*) ;; *) return 1;; esac
  case "$(c48 "$1" "$X49" SLM.stage.sl6)" in "1	MEASURED"*virl1_sl6*) ;; *) return 1;; esac
  case "$(c48 "$1" "$X49" SLM.SL8.sl6.rules)" in "6	MEASURED"*) ;; *) return 1;; esac
  case "$(c48 "$1" "$X49" SLM.SL5.L1.C5tok)" in "$L46	"*) ;; *) return 1;; esac
  case "$(c48 "$1" "$X49" SLM.unstaged.rules)" in "0	BESIDE"*) ;; *) return 1;; esac
  case "$(c46 "$1" "$X49" SLM.stage.sl6)" in "0	"*) ;; *) return 1;; esac
  case "$(c46 "$1" "$X49" SLM.SL5.L1.C5tok)" in "$L46	"*) ;; *) return 1;; esac
}
if check49 "$H/count.py"; then say "ARM49 SL6 stage fixture OK (X49: SL6 6/6 from a new module, stage.sl6 1, SL8.sl6 6 rules, SL5.L1 = X46's $L46; unset => unstaged)"
else say "ARM49 SL6 stage fixture FAIL"; VIR_SLANG_SL6="$SL6N" VIR_SLANG_ROOT=l1s_induction python3 "$H/count.py" --arm slangm --base "$B46" --ext "$X49" "$R46" | grep -E 'SL6|stage|SL5|SL8|unstaged'; fail=1; fi
sed "s/stmod.get(n) in ('l1', 'sl6'):  # SLM-SL6-STAGE/stmod.get(n) == 'l1':  # SLM-SL6-STAGE/" "$H/count.py" > "$F/mutant49.py"
if cmp -s "$H/count.py" "$F/mutant49.py"; then say "ARM49 mutant NOT PLANTED"; fail=1
elif check49 "$F/mutant49.py"; then say "ARM49 mutant SURVIVED (an SL6 module's rules not counted for SL6)"; fail=1
else say "ARM49 mutant KILLED"; fi
sed "s/'sl6' if mod(p) in sl6m else '-'  # SLM-SL6-STAGEMAP/'l1' if mod(p) in sl6m else '-'  # SLM-SL6-STAGEMAP/" "$H/count.py" > "$F/mutant49b.py"
if cmp -s "$H/count.py" "$F/mutant49b.py"; then say "ARM49 mutant-b NOT PLANTED"; fail=1
elif check49 "$F/mutant49b.py"; then say "ARM49 mutant-b SURVIVED (SL6's rules folded into the L1 stage and SL5)"; fail=1
else say "ARM49 mutant-b KILLED"; fi

# ARM50 (STATUS-vir 185): the MetaPRL L3 column (amend-18 Z1-Z9). A row's C5 is its IN-LAYER closure: the posted roots, every
# virl3_* rule a closure text names as a whole identifier, and every virl3_* `{| reduce |}` rule when a text invokes reduceC.
# Fixture: base = virl1/virl2 modules; ext adds virl3_prog (a `fix` only inside a comment) and virl3_typ, and touches a virl2 file
# by a COMMENT only (files 1, items 0). R8's posted root has no derivation (a RED row, never a silent 0).
R50="$F/r50"; mkdir -p "$R50/theories/vir"; git -C "$R50" init -q; git -C "$R50" config user.email t@t; git -C "$R50" config user.name t
printf 'define unfold_one : one <--> 1\n' > "$R50/theories/vir/virl1_x.ml"
printf 'define unfold_l2step : l2step{\x27a} <--> \x27a\ninteractive step2_r : sequent { <H> >- \x27a }\n' > "$R50/theories/vir/virl2_step.ml"
printf 'interactive triple_frame : sequent { <H> >- triple{\x27P; \x27e; \x27Q} }\ninteractive store_local : sequent { <H> >- \x27a }\n' > "$R50/theories/vir/virl2_triple.ml"
printf 'interactive let_rule : sequent { <H> >- \x27a }\n' > "$R50/theories/vir/virl2_rules.ml"
git -C "$R50" add -A; git -C "$R50" commit -qm base; B50=$(git -C "$R50" rev-parse HEAD)
printf '(* touched *)\n' >> "$R50/theories/vir/virl2_rules.ml"
printf 'extends Virl2_rules\n(* a fix in a comment is not a fix *)\ndefine unfold_l3_F : l3_F <--> bind{w. e_ret{\x27w}}\n' > "$R50/theories/vir/virl3_prog.ml"
printf 'extends Virl3_prog\ninteractive_rw h1 {| reduce |} : a <--> b\ninteractive_rw h2 : a <--> b\ninteractive_rw hz {| reduce |} : a <--> b\ninteractive_rw r1 : a <--> b\ninteractive_rw r7 : a <--> b\ninteractive r2 : sequent { <H> >- \x27a }\ninteractive r3 : sequent { <H> >- \x27a }\ninteractive r4 : sequent { <H> >- \x27a }\ninteractive r5 : sequent { <H> >- \x27a }\n' > "$R50/theories/vir/virl3_typ.ml"
T1="rw (reduceC thenC h2) 0"; TH1="rw (unfold_occ thenC reduceC) 0"; TH2="rw unfold_pty 0"; THZ="rw unfold_x 0"; T7="rw (sweepDnC unfold_l3_F7) 0"
T2="(let_rule thenT triple_frame thenT autoT)"; T3="(r2 thenT a b c d e f g h i j k l m n o p q r s t u v w x y z thenT autoT)"
T4="(step2_r thenT step2_r_note thenT unfold_l2step thenT autoT)"; T5="(triple_frame thenT store_local thenT autoT)"
prla "$R50/theories/vir/virl3_typ.prla" "h1=$TH1" "h2=$TH2" "hz=$THZ" "r1=$T1" "r7=$T7" "r2=$T2" "r3=$T3" "r4=$T4" "r5=$T5"
git -C "$R50" add -A; git -C "$R50" commit -qm ext; X50=$(git -C "$R50" rev-parse HEAD)
w() { printf '%s\n' "$1" | wc -w | tr -d ' '; }
# R1's closure = r1 + h2 (named) + h1 + hz (the reduce resource: r1 and h1 both invoke reduceC)
C1=$(( $(w "$T1") + $(w "$TH1") + $(w "$TH2") + $(w "$THZ") )); C3=$(( $(w "$T3") + $(w "$T2") ))
ALL=$(( $(w "$T1") + $(w "$TH1") + $(w "$TH2") + $(w "$THZ") + $(w "$T7") + $(w "$T2") + $(w "$T3") + $(w "$T4") + $(w "$T5") ))
check50() {
  o=$(VIR_L3M_ROOTS='R1=r1;R2=r2;R3=r3;R4=r4;R5=r5;R7=r7;R8=r8' python3 "$1" --arm metaprll3 --base "$B50" --ext "$X50" "$R50") || return 1
  v() { printf '%s\n' "$o" | awk -F'\t' -v c="$1" '$2==c{print $3}'; }
  [ "$(v L3M.files)" = 2 ] && [ "$(v L3M.prims)" = 0 ] && [ "$(v L3M.declares)" = 0 ] \
  && [ "$(v L3M.Z1.defsEdited)" = 0 ] && [ "$(v L3M.Z1.rulesEdited)" = 0 ] && [ "$(v L3M.Z1.filesChanged)" = 1 ] \
  && [ "$(v L3M.rules)" = 9 ] && [ "$(v L3M.rows.rooted)" = 6 ] && [ "$(v L3M.R8.missing)" = 1 ] \
  && printf '%s\n' "$o" | awk -F'\t' '$2=="L3M.R8.missing"' | grep -q RED \
  && [ "$(v L3M.R1.C5tok)" = "$C1" ] && [ "$(v L3M.R1.rootTok)" = "$(w "$T1")" ] && [ "$(v L3M.R7.C5tok)" = "$(w "$T7")" ] \
  && [ "$(v L3M.Z3.tripleCites)" = 1 ] && [ "$(v L3M.Z3.moduleCites)" = 2 ] && [ "$(v L3M.Z4.R3C5)" = "$C3" ] && [ "$(v L3M.Z5.stepInR4)" = 2 ] \
  && [ "$(v L3M.Z6.frameApps)" = 1 ] && [ "$(v L3M.Z6.localityCited)" = 1 ] && [ "$(v L3M.Z7.fixInTerms)" = 0 ] \
  && [ "$(v L3M.Z8.R7Steps)" = 1 ] && printf '%s\n' "$o" | awk -F'\t' '$2=="L3M.Z8.R8Steps"' | grep -q '^.*	Q:' \
  && [ "$(v L3M.Z9.l3C5tok)" = "$ALL" ]
}
if check50 "$H/count.py"; then say "ARM50 metaprll3 fixture OK (Z1 0/0 files 1; R1 closure $C1 tok incl. 2 by the reduce resource; Z3 1 by statement (2 by module); Z4 R3 $C3; Z5 2 (step2_r_note is not step2_r); Z6 1/1; Z7 0; Z8 R7 1 step; R8 RED; Z9 $ALL)"
else say "ARM50 metaprll3 fixture FAIL"; VIR_L3M_ROOTS='R1=r1;R2=r2;R3=r3;R4=r4;R5=r5;R7=r7;R8=r8' python3 "$H/count.py" --arm metaprll3 --base "$B50" --ext "$X50" "$R50"; fail=1; fi
sed 's/                todo += sorted(reduce_rw)/                pass/' "$H/count.py" > "$F/mutant50.py"  # the reduce resource dropped: a name closure alone
if cmp -s "$H/count.py" "$F/mutant50.py"; then say "ARM50 mutant NOT PLANTED"; fail=1
elif check50 "$F/mutant50.py"; then say "ARM50 mutant SURVIVED (the reduce-resource helpers not in a row's closure)"; fail=1
else say "ARM50 mutant KILLED"; fi
sed 's/sum(len(ident(k) \& names) for k in C\[r\])/sum(sum(text(k).count(n) for n in names) for k in C[r])/' "$H/count.py" > "$F/mutant50b.py"  # a cite read inside a longer name
if cmp -s "$H/count.py" "$F/mutant50b.py"; then say "ARM50 mutant-b NOT PLANTED"; fail=1
elif check50 "$F/mutant50b.py"; then say "ARM50 mutant-b SURVIVED (a cite read inside a longer name)"; fail=1
else say "ARM50 mutant-b KILLED"; fi

# ARM51 (STATUS-vir 187, declared 2026-11-07 by the 40th head AFTER R1, R2 and R7 exist on the arm, BEFORE R3-R6/R8): two
# corrections found at the R2 dry read. (a) Z3 "cites a triple" is read by the cited rule's STATEMENT (it mentions triple{ or
# triple_i{), never by its module: virl2_rules holds iteration and wf lemmas too (iter2_succ, retv0_wf), and the module
# reading read R2 FALSIFIED on four non-triple cites. The module reading stays BESIDE. (b) A rule declared {| intro |} is used
# by autoT/dT through the intro resource and named by nothing, so a name closure misses it: L3M.<row>.C5tokIntro is the
# closure plus every virl3_* intro rule when a closure text invokes autoT/dT (BESIDE, an upper bound; the primary is unchanged).
R51="$F/r51"; mkdir -p "$R51/theories/vir"; git -C "$R51" init -q; git -C "$R51" config user.email t@t; git -C "$R51" config user.name t
printf 'interactive tri_let : sequent { <H> >- triple_i{\x27P; \x27e; \x27Q} }\ninteractive iter_succ : sequent { <H> >- \x27a }\n' > "$R51/theories/vir/virl2_rules.ml"
printf 'interactive bt0 : sequent { <H> >- \x27a }\n' > "$R51/theories/vir/virl2_triple.ml"
git -C "$R51" add -A; git -C "$R51" commit -qm base; B51=$(git -C "$R51" rev-parse HEAD)
printf 'interactive w0 {| intro [] |} : sequent { <H> >- \x27a }\ninteractive w1 {| intro [] |} : sequent { <H> >- \x27b }\ninteractive r2 : sequent { <H> >- \x27a }\ninteractive r3 : sequent { <H> >- \x27a }\n' > "$R51/theories/vir/virl3_eq.ml"
TW0="rw unfold_a 0"; TW1="rw (unfold_b thenC unfold_c) 0"; TR2="(iter_succ thenT bt0 thenT autoT)"; TR3="(tri_let thenT iter_succ thenT w0)"
prla "$R51/theories/vir/virl3_eq.prla" "w0=$TW0" "w1=$TW1" "r2=$TR2" "r3=$TR3"
git -C "$R51" add -A; git -C "$R51" commit -qm ext; X51=$(git -C "$R51" rev-parse HEAD)
check51() {
  o=$(VIR_L3M_ROOTS='R2=r2;R3=r3' python3 "$1" --arm metaprll3 --base "$B51" --ext "$X51" "$R51") || return 1
  v() { printf '%s\n' "$o" | awk -F'\t' -v c="$1" '$2==c{print $3}'; }
  [ "$(v L3M.Z3.tripleCites)" = 0 ] && [ "$(v L3M.Z3.moduleCites)" = 2 ] \
  && [ "$(v L3M.R2.C5tok)" = "$(w "$TR2")" ] && [ "$(v L3M.R2.C5tokIntro)" = $(( $(w "$TR2") + $(w "$TW0") + $(w "$TW1") )) ] \
  && [ "$(v L3M.R3.C5tok)" = $(( $(w "$TR3") + $(w "$TW0") )) ] && [ "$(v L3M.R3.C5tokIntro)" = $(( $(w "$TR3") + $(w "$TW0") )) ]
}
if check51 "$H/count.py"; then say "ARM51 metaprll3 Z3-by-statement + intro resource OK (Z3 0 by statement, 2 by module; R2 intro closure adds w0+w1; R3 names w0, no autoT)"
else say "ARM51 metaprll3 Z3-by-statement / intro FAIL"; VIR_L3M_ROOTS='R2=r2;R3=r3' python3 "$H/count.py" --arm metaprll3 --base "$B51" --ext "$X51" "$R51"; fail=1; fi
sed 's/                todo += sorted(intro_rw)/                pass/' "$H/count.py" > "$F/mutant51.py"  # the intro resource dropped
if cmp -s "$H/count.py" "$F/mutant51.py"; then say "ARM51 mutant NOT PLANTED"; fail=1
elif check51 "$F/mutant51.py"; then say "ARM51 mutant SURVIVED (intro rules not in the intro closure)"; fail=1
else say "ARM51 mutant KILLED"; fi
sed 's/names = tri_stated/names = tri_mod/' "$H/count.py" > "$F/mutant51b.py"  # Z3 by module again
if cmp -s "$H/count.py" "$F/mutant51b.py"; then say "ARM51 mutant-b NOT PLANTED"; fail=1
elif check51 "$F/mutant51b.py"; then say "ARM51 mutant-b SURVIVED (Z3 read by module)"; fail=1
else say "ARM51 mutant-b KILLED"; fi

# ARM52 (STATUS-vir 189, the 41st head, 2026-11-08, after the MetaPRL arm's declared read of two Lean L3 files): VIR_L3M_FROZEN
# 'R7=<sha>' asserts that a row's roots were not touched after <sha>. L3M.R7.frozenSame = 1 iff each root's .ml statement and
# stored derivation at ext equal those at <sha>; L3M.R7.frozenClosureEdited (BESIDE) counts closure rules present at <sha> whose
# derivation differs. An unknown sha, or a root absent at <sha>, is a RED 0, never a silent pass.
R52="$F/r52"; mkdir -p "$R52/theories/vir"; git -C "$R52" init -q; git -C "$R52" config user.email t@t; git -C "$R52" config user.name t
printf 'interactive base0 : sequent { <H> >- \x27a }\n' > "$R52/theories/vir/virl2_rules.ml"
git -C "$R52" add -A; git -C "$R52" commit -qm base; B52=$(git -C "$R52" rev-parse HEAD)
ML52='interactive r7 : sequent { <H> >- \x27a }\ninteractive h1 : sequent { <H> >- \x27c }\ninteractive r8 : sequent { <H> >- \x27b }\n'
printf "$ML52" > "$R52/theories/vir/virl3_typ.ml"
TR7="(h1 thenT autoT)"; TH="rw unfold_a 0"; TR8="(base0 thenT autoT)"
c52() { git -C "$R52" add -A; git -C "$R52" commit -qm "$1"; git -C "$R52" rev-parse HEAD; }
prla "$R52/theories/vir/virl3_typ.prla" "r7=$TR7" "h1=$TH" "r8=$TR8"; F52=$(c52 frozen)
prla "$R52/theories/vir/virl3_typ.prla" "r7=$TR7" "h1=$TH" "r8=(base0 thenT trivialT)"; S52=$(c52 other-row-only)
prla "$R52/theories/vir/virl3_typ.prla" "r7=(h1 thenT trivialT)" "h1=$TH" "r8=$TR8"; P52=$(c52 proof-edited)
prla "$R52/theories/vir/virl3_typ.prla" "r7=$TR7" "h1=$TH" "r8=$TR8"
printf 'interactive r7 : sequent { <H> >- \x27z }\ninteractive h1 : sequent { <H> >- \x27c }\ninteractive r8 : sequent { <H> >- \x27b }\n' > "$R52/theories/vir/virl3_typ.ml"; T52=$(c52 statement-edited)
printf "$ML52" > "$R52/theories/vir/virl3_typ.ml"
prla "$R52/theories/vir/virl3_typ.prla" "r7=$TR7" "h1=rw unfold_b 0" "r8=$TR8"; H52=$(c52 helper-edited)
r52() { VIR_L3M_ROOTS='R7=r7' VIR_L3M_FROZEN="R7=$3" python3 "$1" --arm metaprll3 --base "$B52" --ext "$2" "$R52"; }
v52() { awk -F'\t' -v c="$1" '$2==c{print $3}'; }
check52() {
  o=$(r52 "$1" "$S52" "$F52") || return 1; [ "$(printf '%s\n' "$o" | v52 L3M.R7.frozenSame)" = 1 ] && [ "$(printf '%s\n' "$o" | v52 L3M.R7.frozenClosureEdited)" = 0 ] || return 1
  o=$(r52 "$1" "$P52" "$F52") || return 1; [ "$(printf '%s\n' "$o" | v52 L3M.R7.frozenSame)" = 0 ] || return 1
  o=$(r52 "$1" "$T52" "$F52") || return 1; [ "$(printf '%s\n' "$o" | v52 L3M.R7.frozenSame)" = 0 ] || return 1
  o=$(r52 "$1" "$H52" "$F52") || return 1; [ "$(printf '%s\n' "$o" | v52 L3M.R7.frozenSame)" = 1 ] && [ "$(printf '%s\n' "$o" | v52 L3M.R7.frozenClosureEdited)" = 1 ] || return 1
  o=$(r52 "$1" "$S52" "0000000000000000000000000000000000000000") || return 1; [ "$(printf '%s\n' "$o" | v52 L3M.R7.frozenSame)" = 0 ] && printf '%s\n' "$o" | awk -F'\t' '$2=="L3M.R7.frozenSame"' | grep -q RED || return 1
  o=$(r52 "$1" "$S52" "$B52") || return 1; [ "$(printf '%s\n' "$o" | v52 L3M.R7.frozenSame)" = 0 ] && printf '%s\n' "$o" | awk -F'\t' '$2=="L3M.R7.frozenSame"' | grep -q RED
}
if check52 "$H/count.py"; then say "ARM52 metaprll3 frozen rows OK (another row's edit 1/0; root proof 0; root statement 0; helper edit 1/1; unknown sha and absent root RED)"
else say "ARM52 metaprll3 frozen rows FAIL"; r52 "$H/count.py" "$P52" "$F52" | awk -F'\t' '$2 ~ /frozen/'; fail=1; fi
sed 's/if fp\[name\]\[4\] != R\[k\]\[4\]:/if False:/' "$H/count.py" > "$F/mutant52.py"  # the stored derivation not compared
if cmp -s "$H/count.py" "$F/mutant52.py"; then say "ARM52 mutant NOT PLANTED"; fail=1
elif check52 "$F/mutant52.py"; then say "ARM52 mutant SURVIVED (a root's proof edit reads frozen)"; fail=1
else say "ARM52 mutant KILLED"; fi
sed 's/if fs != items(ext, p + \x27.ml\x27).get(\x27i:\x27 + name):/if False:/' "$H/count.py" > "$F/mutant52b.py"  # the statement not compared
if cmp -s "$H/count.py" "$F/mutant52b.py"; then say "ARM52 mutant-b NOT PLANTED"; fail=1
elif check52 "$F/mutant52b.py"; then say "ARM52 mutant-b SURVIVED (a root's statement edit reads frozen)"; fail=1
else say "ARM52 mutant-b KILLED"; fi

# ARM53 (STATUS-vir 194, the 42nd head, 2026-11-08: AFTER R1/R2/R3/R7 exist on the arm and BEFORE R4 does; written after reading
# lines 1-20 of the arm's R4 plan, which says R4 reuses R3's path lemmas). amend-18 Z5 says "no step rule in its proof tree".
# At the R3 export the old reader (every name of virl2_step) read R3's closure at 66, on unfold_effop and its helpers AND on
# value encoders (unfold_capv, unfold_a_unit), while no step2_* appears in any text: those are reduce rules, fired by resource
# through the arm's own rule l3_dstep3. So: the primary counts step rules and step unfolds only; the old reading is BESIDE
# (allNames); BESIDE stepStated names the rules in the closure stated over l2step{/l2iter{/reach{, the one reading that sees a
# step taken by resource; BESIDE rootStep is the root's own text, the like of Lean's proof-text count.
R53="$F/r53"; mkdir -p "$R53/theories/vir"; git -C "$R53" init -q; git -C "$R53" config user.email t@t; git -C "$R53" config user.name t
printf 'define unfold_capv : capv{\x27p} <--> foo{\x27p}\ndefine unfold_effop : effop{\x27o} <--> bar{\x27o}\ninteractive_rw step2_ret {| reduce |} : l2step{(e_ret{\x27a}, \x27s)} <--> inr{it}\n' > "$R53/theories/vir/virl2_step.ml"
printf 'interactive rs : sequent { <H> >- reach{\x27a; \x27b} }\n' > "$R53/theories/vir/virl2_den.ml"
git -C "$R53" add -A; git -C "$R53" commit -qm base; B53=$(git -C "$R53" rev-parse HEAD)
: > "$R53/theories/vir/virl3_eq.ml"
for n in r4v r4e r4d r4h r4r r4s h1; do printf 'interactive %s : sequent { <H> >- \x27a }\n' "$n" >> "$R53/theories/vir/virl3_eq.ml"; done
printf 'interactive l3_dstep : sequent { <H> >- l2step{\x27c} = \x27d in \x27T }\n' >> "$R53/theories/vir/virl3_eq.ml"
prla "$R53/theories/vir/virl3_eq.prla" "r4v=rw unfold_capv 0" "r4e=rw unfold_effop 0" "r4d=(l3_dstep thenT idT)" "r4h=(h1 thenT idT)" "r4r=(rs thenT idT)" "r4s=rw step2_ret 0" "h1=rw unfold_effop 0" "l3_dstep=rw unfold_x 0"
git -C "$R53" add -A; git -C "$R53" commit -qm ext; X53=$(git -C "$R53" rev-parse HEAD)
r53() { VIR_L3M_ROOTS="R4=$2" python3 "$1" --arm metaprll3 --base "$B53" --ext "$X53" "$R53"; }
v53() { awk -F'\t' -v k="$1" '$2==k{print $3}'; }
e53() { # $1 count.py, $2 root, then stepInR4 allNames stepStated rootStep
  o=$(r53 "$1" "$2") || return 1
  [ "$(printf '%s\n' "$o" | v53 L3M.Z5.stepInR4)" = "$3" ] && [ "$(printf '%s\n' "$o" | v53 L3M.Z5.allNames)" = "$4" ] && [ "$(printf '%s\n' "$o" | v53 L3M.Z5.stepStated)" = "$5" ] && [ "$(printf '%s\n' "$o" | v53 L3M.Z5.rootStep)" = "$6" ]
}
check53() { e53 "$1" r4v 0 1 0 0 && e53 "$1" r4e 1 1 0 1 && e53 "$1" r4d 0 0 1 0 && e53 "$1" r4h 1 1 0 0 && e53 "$1" r4r 0 0 1 0 && e53 "$1" r4s 1 1 1 1; }
if check53 "$H/count.py"; then say "ARM53 metaprll3 Z5 reader OK (value encoder 0/1; effop unfold 1, in root 1; step by resource 0 named, 1 stated; helper 1, root 0; L2 rule over reach stated 1; step2_ named 1)"
else say "ARM53 metaprll3 Z5 reader FAIL"; r53 "$H/count.py" r4v | awk -F'\t' '$2 ~ /Z5/'; fail=1; fi
sed 's/if L3M_STEP_RULE_RE.match(n)}/if True}/' "$H/count.py" > "$F/mutant53.py"  # a value encoder reads as a step rule
if cmp -s "$H/count.py" "$F/mutant53.py"; then say "ARM53 mutant NOT PLANTED"; fail=1
elif check53 "$F/mutant53.py"; then say "ARM53 mutant SURVIVED (a value encoder reads as a step rule)"; fail=1
else say "ARM53 mutant KILLED"; fi
sed 's/(l2step|l2iter|reach)/(nostepword)/' "$H/count.py" > "$F/mutant53b.py"  # a step taken by resource is invisible
if cmp -s "$H/count.py" "$F/mutant53b.py"; then say "ARM53 mutant-b NOT PLANTED"; fail=1
elif check53 "$F/mutant53b.py"; then say "ARM53 mutant-b SURVIVED (a step taken by resource is invisible)"; fail=1
else say "ARM53 mutant-b KILLED"; fi

# ARM55 (STATUS-vir 199, the 43rd head, 2026-11-08: AFTER R4/R5 exist on the arm; no verdict moves). L3M.Z5.stepInR4 prints a count
# only, and Z5's FALSIFIED clause is read by hand on the rules it counted. BESIDE: stepNames prints the distinct step rules and
# unfolds, each with the closure rule that names it. Uses ARM53's fixture.
check55() { o=$(r53 "$1" r4h) || return 1; l=$(printf '%s\n' "$o" | awk -F'\t' '$2=="L3M.Z5.stepNames"')
  [ "$(printf '%s\n' "$l" | cut -f3)" = 1 ] && [ "$(printf '%s\n' "$l" | cut -f4 | sed 's/.*://')" = 'unfold_effop' ] && printf '%s\n' "$l" | cut -f4 | /usr/bin/grep -qF 'h1:unfold_effop' || return 1
  o=$(r53 "$1" r4v) || return 1; [ "$(printf '%s\n' "$o" | v53 L3M.Z5.stepNames)" = 0 ]; }
if check55 "$H/count.py"; then say "ARM55 metaprll3 Z5 stepNames OK (helper h1 names unfold_effop; a value encoder is not listed)"
else say "ARM55 metaprll3 Z5 stepNames FAIL"; r53 "$H/count.py" r4h | awk -F'\t' '$2 ~ /Z5/'; fail=1; fi
sed "s/'%s:%s' % (k.split(':', 1)\[1\], n)/n/" "$H/count.py" > "$F/mutant55.py"  # the site that names the rule is lost
if cmp -s "$H/count.py" "$F/mutant55.py"; then say "ARM55 mutant NOT PLANTED"; fail=1
elif check55 "$F/mutant55.py"; then say "ARM55 mutant SURVIVED (the naming site is lost)"; fail=1
else say "ARM55 mutant KILLED"; fi

# ARM54 (STATUS-vir 195, the 42nd head, 2026-11-08: BEFORE R5 exists on the arm). Z6's localityCited matches virl2_* names
# containing "local", and at 10b8ddbab no such name exists (population 0), so the row cannot fire. BESIDE: localityPop prints
# that population, and unionStated names the virl2_* rules in R5's closure stated over st_union{ (the frame's own vocabulary),
# so a locality lemma is at least visible to the hand read. localityCited and frameApps are unchanged.
R54="$F/r54"; mkdir -p "$R54/theories/vir"; git -C "$R54" init -q; git -C "$R54" config user.email t@t; git -C "$R54" config user.name t
printf 'interactive triple_frame : sequent { <H> >- triple{\x27P; \x27e; \x27Q} }\ninteractive op_safe : sequent { <H> >- st_union{\x27a; \x27b; \x27c} }\ninteractive store_local : sequent { <H> >- \x27a }\n' > "$R54/theories/vir/virl2_rules.ml"
git -C "$R54" add -A; git -C "$R54" commit -qm base; B54=$(git -C "$R54" rev-parse HEAD)
for n in r5a r5b r5c; do printf 'interactive %s : sequent { <H> >- \x27a }\n' "$n"; done > "$R54/theories/vir/virl3_tri.ml"
prla "$R54/theories/vir/virl3_tri.prla" "r5a=(triple_frame thenT idT)" "r5b=(triple_frame thenT op_safe)" "r5c=(triple_frame thenT store_local)"
git -C "$R54" add -A; git -C "$R54" commit -qm ext; X54=$(git -C "$R54" rev-parse HEAD)
r54() { VIR_L3M_ROOTS="R5=$2" python3 "$1" --arm metaprll3 --base "$B54" --ext "$X54" "$R54"; }
e54() { # $1 count.py, $2 root, then frameApps localityCited localityPop unionStated
  o=$(r54 "$1" "$2") || return 1
  [ "$(printf '%s\n' "$o" | v53 L3M.Z6.frameApps)" = "$3" ] && [ "$(printf '%s\n' "$o" | v53 L3M.Z6.localityCited)" = "$4" ] && [ "$(printf '%s\n' "$o" | v53 L3M.Z6.localityPop)" = "$5" ] && [ "$(printf '%s\n' "$o" | v53 L3M.Z6.unionStated)" = "$6" ]
}
check54() { e54 "$1" r5a 1 0 1 0 && e54 "$1" r5b 1 0 1 1 && e54 "$1" r5c 1 1 1 0; }
if check54 "$H/count.py"; then say "ARM54 metaprll3 Z6 population OK (frame only 1/0; union-stated lemma visible 1; named locality lemma cited 1; population 1)"
else say "ARM54 metaprll3 Z6 population FAIL"; r54 "$H/count.py" r5b | awk -F'\t' '$2 ~ /Z6/'; fail=1; fi
sed 's/pop = len({n for m in l2names.values() for n in m if .local. in n})/pop = 0/' "$H/count.py" > "$F/mutant54.py"  # the population not measured
if cmp -s "$H/count.py" "$F/mutant54.py"; then say "ARM54 mutant NOT PLANTED"; fail=1
elif check54 "$F/mutant54.py"; then say "ARM54 mutant SURVIVED (the population is not measured)"; fail=1
else say "ARM54 mutant KILLED"; fi
sed 's/st_union\\{/nosuchop\\{/' "$H/count.py" > "$F/mutant54b.py"  # a union-stated lemma is invisible
if cmp -s "$H/count.py" "$F/mutant54b.py"; then say "ARM54 mutant-b NOT PLANTED"; fail=1
elif check54 "$F/mutant54b.py"; then say "ARM54 mutant-b SURVIVED (a union-stated lemma is invisible)"; fail=1
else say "ARM54 mutant-b KILLED"; fi

# ARM56 (STATUS-vir row 166; l4/DECLARATIONS-LEAN.md addendum 7): `--arm l4`, C5 of a row as the in-layer PROOF CLOSURE.
# Fixture K: a depth-2 private helper under par₄_rule (a one-pass closure misses it), a shared helper `go` reached by S and V
# (counted once per side), a reference by last dotted component (Shared.go), a def reached only by V (withDefs only), one name
# of an imported layer (l3), a comment inside a counted block, and an unrelated theorem kept out. Expectations are wc -w of the blocks.
K="$F/l4K"; mkdir -p "$K/l4/VIRL4" "$K/l2/VIRL2" "$K/l3/VIRL3"
B_SP='theorem safe₄_par : True := by
  exact helper₄ trivial'
B_HP='private theorem helper₄ (h : True) : True := h'
B_PR='theorem par₄_rule : True := safe₄_par'
B_UN='theorem unrelated : True := trivial'
B_DF='def Inv₄ : Prop := True'
B_N1S='theorem N1_S : True := trivial'
B_F4S='theorem F₄_S : True := by exact (Shared.go)'
B_GO='theorem go : True := trivial'
B_N1V='theorem N1_V : Inv₄ := trivial_from_l3'
B_N4V='theorem N4_V : True := by exact go'
B_CF='theorem ce_fwd : True := trivial'
B_CB='theorem ce_bwd : True := ce_fwd'
B_FR='theorem frame : True := frame_aux'
B_FA='lemma frame_aux : True := trivial'
{ printf -- '-- a comment that is never counted\n%s\n\n%s\n\n%s\n\n%s\n\n%s\n\n%s\n\n%s  -- stripped words here\n\n%s\n\n' \
    "$B_SP" "$B_HP" "$B_PR" "$B_UN" "$B_DF" "$B_N1S" "$B_F4S" "$B_GO"
  printf '%s\n\n%s\n\n%s\n\n%s\n' "$B_N1V" "$B_N4V" "$B_CF" "$B_CB"; } > "$K/l4/VIRL4/R.lean"
printf '/- block comment -/\n%s\n\n%s\n' "$B_FR" "$B_FA" > "$K/l2/VIRL2/Logic.lean"
printf 'theorem trivial_from_l3 : True := trivial\n' > "$K/l3/VIRL3/X.lean"
E56_PAR=$(( $(wc_w "$B_PR") + $(wc_w "$B_SP") + $(wc_w "$B_HP") )); E56_FR=$(( $(wc_w "$B_FR") + $(wc_w "$B_FA") ))
E56_S=$(( $(wc_w "$B_N1S") + $(wc_w "$B_F4S") + $(wc_w "$B_GO") )); E56_V=$(( $(wc_w "$B_N1V") + $(wc_w "$B_N4V") + $(wc_w "$B_GO") ))
E56_VD=$(( E56_V + $(wc_w "$B_DF") )); E56_CE=$(( $(wc_w "$B_CF") + $(wc_w "$B_CB") )); E56_PROOT=$(wc_w "$B_PR")
check56() {
  o=$(python3 "$1" --arm l4 "$K/l4") || return 1
  v() { printf '%s\n' "$o" | awk -F'\t' -v c="$1" '$2==c{print $3}'; }
  [ "$(v L4.Q3.par.C5tok)" = "$E56_PAR" ] && [ "$(v L4.Q3.frame.C5tok)" = "$E56_FR" ] && [ "$(v L4.Q3.par.root.C5tok)" = "$E56_PROOT" ] \
  && [ "$(v L4.Q4.S.C5tok)" = "$E56_S" ] && [ "$(v L4.Q4.V.C5tok)" = "$E56_V" ] && [ "$(v L4.Q4.V.withDefs.C5tok)" = "$E56_VD" ] \
  && [ "$(v L4.Q4.V.crossRefs)" = 1 ] && [ "$(v L4.Q7.C5tok)" = "$E56_CE" ] \
  && [ "$(v L4.Q3.held)" = $([ "$E56_PAR" -le $((3 * E56_FR)) ] && echo 1 || echo 0) ] \
  && [ "$(v L4.Q4.direction)" = $([ "$E56_V" -gt "$E56_S" ] && echo 1 || echo 0) ]
}
if check56 "$H/count.py"; then say "ARM56 l4 fixture OK (Q3 par $E56_PAR vs frame $E56_FR; Q4 V $E56_V vs S $E56_S, withDefs $E56_VD; Q7 $E56_CE)"
else say "ARM56 l4 fixture FAIL"; python3 "$H/count.py" --arm l4 "$K/l4"; fail=1; fi
sed 's/changed = True  # CLOSURE-FIXPOINT$/changed = False  # CLOSURE-FIXPOINT/' "$H/count.py" > "$F/mutant56.py"
if cmp -s "$H/count.py" "$F/mutant56.py"; then say "ARM56 mutant NOT PLANTED"; fail=1
elif check56 "$F/mutant56.py"; then say "ARM56 mutant SURVIVED (a depth-2 helper went unread: the closure stopped after one pass)"; fail=1
else say "ARM56 mutant KILLED"; fi

find "${F:?}" -delete
echo "SELFTEST rc=$fail"
exit $fail
