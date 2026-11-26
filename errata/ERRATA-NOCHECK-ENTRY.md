# ERRATA — OBJECT-NOCHECK-ENTRY (the object is never edited; corrections live here)

## E1 (2026-11-25, the 90th vir head, found BEFORE the entry file; only the agnostic `s3/S3/Contain.lean` exists): the decider cannot return a bare `bool`
**What the object says.** NE-D: the decider d "returns a `bool`"; NE-C: on `true`, call e's code.
**What is true.** e's code is entered under `DriverCall L ρ₀ wm s`, which needs e's argument words at `L.env0` (`WordsAt s.mem L.env0 ρ₀`).
After d's code returns, the only machine facts are R3's `done` clause (`s3/S3/Rel3.lean:120–121`): `Returned`, `Common` (BUF, the
control block, `Rep` of the live cells), `r13 = |ws|`, and the result words at BUF. **Nothing is stated about the words at `env0`**,
which d's run uses as its environment. So with a bare `bool` the stub has no verified copy of e's arguments to call e with. Saving the
arguments before the call would put them outside every region R3 tracks, or would need a second layout for d.
**The correction, for the route.** d returns `unit + τarg` (L2's sum, lowered with a tag word): `inr a` = ACCEPT, carrying e's argument
back, and `inl ()` = REJECT. The soundness premise becomes: if d run from σ returns `inr a`, then a is the argument it was given, σ is
unchanged, and `P σ`. On ACCEPT the stub copies the argument words from BUF to `env0`, which is what Driver3's `after_done` already
does for a capability. The verified result words are the only source.
**Effect on the predictions (amend-27), declared before scoring:** NE1 reads "the decider's read-only predicate, its soundness" for the
sum-returning d. NE5's one router lemma is `dF`'s soundness for the sum form. No row's threshold changes.

## E2 (2026-11-25, the 90th head, still BEFORE the entry file): the decider returns `τarg × bool`, not `unit + τarg` (replaces E1's form; E1's reason stands)
**Why the change.** Product values lower as concatenation, so `(cap, b)` lands in BUF as `[base, len, b]`, with the argument words at
BUF[0..1]. Those are exactly the words Driver3's `after_done` already copies to `env0` (`loopTail`) before jumping to a head in
`AtHead`. The sum form puts the argument at BUF[1..2] and would need a new copy lemma. With the product, the stub is a 4-instruction
test of BUF[2] (= 1, else to the FAULT target) followed by `loopTail env0 XF H₂`, and `H₂: call base_e`. `after_done` is reused through
a copy of the layout with `ret0` re-pointed (`Lay3.Ok` mentions neither `ret0` nor `stubRet`, `s3/S3/Rel3.lean:38`).
**The soundness premise, as used:** if d run from σ returns `(a, true)`, then a is the argument it was given and `P σ`. The store
stays σ along every run (the read-only predicate, `S3.readOnly_mem` at the word level).
**Effect on amend-27:** as E1's (NE1 and NE5 read for this form). NE4's "≥ 2 of `head_call`, `after_done`, `after_exit`" is now the plan.

## E3 (2026-11-25, the 90th head, found DURING the route, at NE-R): a decider of type `cap × bool` is UNTYPEABLE in L2; the decider returns `tcap` and rejects by a deliberate index fault (replaces E2's interface)
**What is true.** L2's typing is linear in capabilities (`l2/VIRL2/Typing2.lean:54–57`). `ret a` needs `Mask.empty Δ`. The only way to end
while owning a capability is `retCap`, which returns that capability ALONE at type `tcap`. A `load` needs `Δ[n] = true` and keeps it,
so a decider that reads its argument's cells owns the capability until its end, and it can return only the capability. Measured:
`HasType₂ [tcap] [true] dF (.prod tcap tbool)` leaves the goal `Mask.empty [true]` (`k7/logs/ne-r-005.log`). The attempt is kept as
`k7/probes/RouterEntryCapBool.lean`, with `dF_sound` proved for it (`ne-r-003`), as the record.
**What stands from the route (s3, builds ne-001..ne-018).** `Contain.lean`, `ReadOnly.lean`, `bool_check`, `gate_accept`, `gate_reject`,
`compile_x86S`, `compile_entry`, `compile_entry_run` are all proved. They are proved for E2's interface (`cap × bool`, a BUF[2] test),
which no L2 program can instantiate. So **compile_entry as built has no instance**, and NE-R cannot be completed on it. That is the
finding, and it is posted as such.
**The correction.** The decider has type `tcap`. ACCEPT: `ret w` (DONE, the capability's words at BUF[0..1], which `after_done` copies
to ENV). REJECT: a `load` at index −1, which d's CHECKED lowering turns into the FAULT status. The gate is then Driver3's `loopTail`
alone (a status other than DONE goes to XF), with no BUF[2] test. Soundness: every finishing run of d returns the capability it was
given, leaves σ, and gives NC-P′ for e. NE1–NE8 are unchanged in form. NE6's count continues from ne-018 on the corrected statement,
and every build is counted.
