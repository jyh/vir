# ERRATA — OBJECT-NOCHECK (the object is never edited; corrections live here)

## E1 (2026-11-25, the 90th vir head, found BEFORE the first route file): NC-P alone does not give NC-W under fork N1 (a)
**What the object says.** §2 defines `NoFault vs e σ :≡ ∀ c, Steps₂ (instL 0 vs e, σ) c → ¬ Faults c`, and fork N1 (a) derives
NC-W (no word run reaches `.fault`) from it and compile_refines' clauses by a whole-run argument.
**What is true.** `Faults c` is `¬ c.1.IsTerminal ∧ ∀ c', ¬ Step₂ c c'` (`l2/VIRL2/Step2.lean:26`), and `Tm.IsTerminal` holds of
EVERY `ret a` (`l1/VIRL1/Semantics.lean:55`), including one whose atom does not evaluate. A source run that stops at such a `ret a`
is not a fault, so NC-P does not exclude it; compile_refines' clause (1) needs `Atom.eval a = some w`, clause (3) bounds the word
run only from below, and so no clause pins what the word run does after that point. The whole-run argument has a missing case.
Closing it from typing would need L2's runtime typing (`RT`, `OwnAll`) at the start state, which compile_x86's premises do not carry.
**The correction, for the route.** The premise is **NC-P′ :≡ NC-P ∧ ∀ a σ', Steps₂ (instL 0 vs e, σ) (.ret a, σ') →
(Atom.eval a).isSome**, one definition. Every L2 `Triple` still supplies it at a state satisfying its precondition: the first
conjunct is the Triple's first, the second is read from the Triple's second (`a.eval = some v`).
**Effect on the predictions (amend-26), declared before scoring:** NC3 is scored with NC-P′ as the ONE added hypothesis. If the
route finds NC-P′'s second conjunct unnecessary, that is reported, and NC3 is then scored against NC-P as pinned. NC6 is
unchanged (the router's triple supplies both conjuncts). No other row changes.
