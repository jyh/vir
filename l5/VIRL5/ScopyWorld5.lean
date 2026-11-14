/-
  O95 layer L5, Lean arm (STATUS 318, LV8 Deflate5, SCOPY in DEFLATE's terms). scopy5_chunk_run speaks the routines' language
  (RegionAt, absolute contents). DEFLATE's simulation speaks World (relative contents). Bridge (i) moves it across: from a World
  on a store that owns the one region and nothing else (Sole, which initStore has), the chunked SCOPY run returns ⟨p⟩ and leaves
  a World on a Sole store, its contents scopyPost read back relatively. The premises are DEFLATE's own cells (PEND, BY, N, M).
-/
import VIRL5.ScopyRun5

namespace VIRL5
open VIRL1 VIRL2 VIRDeflate.Step

/-- The contents after one chunk, relative to the base (DEFLATE's World form). -/
def scopyPostRel (p : Int) (f : Int → Int) (k bx n m : Int) : Int → Int :=
  fun i => scopyPost p (fun a => f (a - p)) k bx n m (p + i)

theorem scopy5_chunk_world (p : Int) (L : Nat) (f : Int → Int) (k bx n m : Int)
    (hk : f cPEND = k) (hk0 : 0 < k) (hby : f cBY = bx) (hn : f cN = n) (hm : f cM = m)
    (hbx : 0 ≤ bx) (hm0 : 0 ≤ m) (hcap : bx + min k CS ≤ n) (hL : IN + n + m + min k CS ≤ L)
    {σ : Store} (hw : World σ p L f) (hs : Sole σ p L) (hwf : Store.WF σ) {F : Nat} (hF : 4 * (min k CS).toNat + 13 ≤ F) :
    ∃ a, ((run₅ F (scopyT₅.subst 0 (.const (.cap p)), σ)).1 = .ret a ∨
          (run₅ F (scopyT₅.subst 0 (.const (.cap p)), σ)).1 = .retK a []) ∧
      a.eval = some (.const (.cap p)) ∧
      World (run₅ F (scopyT₅.subst 0 (.const (.cap p)), σ)).2 p L (scopyPostRel p f k bx n m) ∧
      Sole (run₅ F (scopyT₅.subst 0 (.const (.cap p)), σ)).2 p L := by
  have hR := VIRL5.World.regionAt hw hs
  obtain ⟨a, hterm, hav, hreg⟩ := scopy5_chunk_run p L (fun a => f (a - p)) k bx n m
    (by simpa using hk) hk0 (by simpa using hby) (by simpa using hn) (by simpa using hm)
    hbx hm0 hcap hL hR hwf hF
  obtain ⟨hw', hs'⟩ := VIRL5.RegionAt.world hreg
  exact ⟨a, hterm, hav, hw', hs'⟩

end VIRL5
