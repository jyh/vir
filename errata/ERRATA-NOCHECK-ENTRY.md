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
