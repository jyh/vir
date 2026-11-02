import VIRP
open VIRP
-- MUTANT (must be RED): one emit charged as TWO tokens.
theorem call_tokens_bad (σ : Store) (w : List Int) (p : Int) :
    (call σ w).1.bucket p + (match (call σ w).2 with | .emit _ => if rd32 w 4 = p then 2 else 0 | .drop _ => 0)
      = σ.bucket p := by
  unfold call Fn
  split_ifs with h1 h2 h3 <;> simp_all [Store.dec]
  all_goals omega
