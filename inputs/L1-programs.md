# L1 acceptance programs K1–K5 (OBJECT-L1 §7). An INPUT: both arms receive the same bytes

Written 2026-11-02 by vir with OBJECT-L1, before either arm's first L1 file, and pinned at the same sha. Concrete syntax is
OBJECT-L1 §2's. Each arm proves: the typing; the denotation's value (`¬Dom` for K2); and a ⟶* trace to the value.

| id | what it exercises | program | type | meaning |
|---|---|---|---|---|
| K1 | fix, non-tail recursion, `let` sequencing | `let fact:int→int = ret (fix fact(n:int):int. if le(n,0) then ret 1 else let r:int = fact sub(n,1) in ret mul(n,r)) in fact 5` | int | 120 |
| K2 | divergence (partiality is REAL) | `(fix loop(x:int):int. loop x) 0` | int | ¬Dom |
| K3 | higher-order functions, a returned closure | `let twice:(int→int)→int→int = ret (λ(f:int→int). ret (λ(x:int). let y:int = f x in f y)) in let g:int→int = twice (λ(z:int). ret add(z,1)) in g 40` | int | 42 |
| K4 | pure operators, both `if` branches typed | `if and(lt(1,2), not(eq(3,4))) then ret 7 else ret 8` | int | 7 |
| K5 | currying and a TAIL CALL inside fix | `let sum:int→int→int = ret (fix sum(n:int):int→int. ret (λ(acc:int). if le(n,0) then ret acc else let k:int→int = sum sub(n,1) in k add(acc,n))) in let s:int→int = sum 10 in s 0` | int | 55 |

Notes, fixed here so that neither arm decides them:
- In K1 the inner `fact` is fix's own binder. The outer `let fact` shadows nothing at that point: it binds the value for the
  final call. An arm on de Bruijn indices translates names by scope, as usual.
- K2's `¬Dom` is the statement `¬ (⟦K2⟧).Dom` (Lean) / `¬ halts(⟦K2⟧)` (MetaPRL). Proving it needs the LEASTNESS of the
  fixpoint (fixpoint induction), not just its unfolding equation. That is the point of K2.
- In K5, `k add(acc,n)` is in tail position (the else-branch of an if that is the body of a λ). The value is 0+10+9+…+1 = 55.
