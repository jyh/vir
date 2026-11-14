/-
  O95 layer L5, Lean arm (STATUS 318, LV8 Deflate5, SCOPY). The chunk step's triple (scopy5_chunk) and its cost
  (scopy5_chunk_cost) put together by run_of_triple₅: at every fuel F ≥ 4·c + 13 — in particular at KSTEP = 512 less the dispatch's
  share — the run of SCOPY from an exact region with ANY contents ends returning the world ⟨p⟩, and the region holds scopyPost.
  A triple does not distinguish `ret a` from `retK a []`, so the statement admits both terminal forms; the L5 stepS reads the
  returned capability by evaluation.
-/
import VIRL5.ScopyCost5
import VIRL5.RunTriple5

namespace VIRL5
open VIRL1 VIRL2 VIRDeflate.Step

theorem scopy5_chunk_run (p : Int) (L : Nat) (g : Int → Int) (k bx n m : Int)
    (hk : g (p + cPEND) = k) (hk0 : 0 < k) (hby : g (p + cBY) = bx) (hn : g (p + cN) = n) (hm : g (p + cM) = m)
    (hbx : 0 ≤ bx) (hm0 : 0 ≤ m) (hcap : bx + min k CS ≤ n) (hL : IN + n + m + min k CS ≤ L)
    {σ : Store} (hR : RegionAt p L g σ) (hwf : Store.WF σ) {F : Nat} (hF : 4 * (min k CS).toNat + 13 ≤ F) :
    ∃ a, ((run₅ F (scopyT₅.subst 0 (.const (.cap p)), σ)).1 = .ret a ∨
          (run₅ F (scopyT₅.subst 0 (.const (.cap p)), σ)).1 = .retK a []) ∧
      a.eval = some (.const (.cap p)) ∧
      RegionAt p L (scopyPost p g k bx n m) (run₅ F (scopyT₅.subst 0 (.const (.cap p)), σ)).2 := by
  obtain ⟨v, qs, ⟨hv, hqs, hreg⟩, hcase⟩ :=
    run_of_triple₅ (scopy5_chunk p L g k bx n m hk hk0 hby hn hm hbx hm0 hcap hL)
      (scopy5_chunk_cost p L g k bx n m hk hk0 hby hn hm hbx hm0 hcap hL) hR hwf hF
  subst hv
  subst hqs
  rcases hcase with ⟨a, ha, hav, -⟩ | ⟨a, ds, ha, hav, hds⟩
  · exact ⟨a, Or.inl ha, hav, hreg⟩
  · have hl := evalL_length hds
    have hd : ds = [] := List.eq_nil_of_length_eq_zero (by simpa using hl.symm)
    subst hd
    exact ⟨a, Or.inr ha, hav, hreg⟩

end VIRL5
