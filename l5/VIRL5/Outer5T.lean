/-
  O95 layer L5, Lean arm (STATUS 323, LV8-MAP Addendum 6, fork (T)): the OUTER argument with the table invariant in the run
  invariant. `Refine₅T` is Outer5's `Refine₅` with `Tab f` added to its hypotheses (READ and DECODE need it, the other cases
  ignore it). (T) holds at the initial world (`tab_init`) and every DEFLATE step keeps it (`iterS_tab`), so it holds at every
  ⟶₅ step's start, and Outer5's proofs go through with it threaded. Outer5 itself is unchanged: it sits upstream of the
  dispatch, which the frame needs.
-/
import VIRL5.TabStep5

namespace VIRL5
open VIRL1 VIRL2 VIRDeflate.Step

/-- **The one per-mode obligation, under (T).** -/
def Refine₅T : Prop :=
  ∀ (b : Array Nat) (om : Nat) (lit : Bool) (p : Int) (σ : Store) (f : Int → Int), (∀ x ∈ b, x < 256) →
    World σ p (L0 b.size om) f → Sole σ p (L0 b.size om) → Inv b om lit f → Tab f →
    ∃ j σ', stepS₅ p σ = some σ' ∧ iterS p j σ = some σ' ∧ Sole σ' p (L0 b.size om) ∧
      (f cMODE ≠ mDONE → f cMODE ≠ mREJECT → 1 ≤ j)

theorem iter_reach₅T (hr : Refine₅T) (b : Array Nat) (om : Nat) (lit : Bool) (p : Int) (hb : ∀ x ∈ b, x < 256) :
    ∀ (k : Nat) (σ : Store) (f : Int → Int), World σ p (L0 b.size om) f → Sole σ p (L0 b.size om) → Inv b om lit f →
      Tab f → Φ f < k → ∃ j σ', j ≤ k ∧ iterS₅ p j σ = some σ' ∧ (modeOf p σ' = mDONE ∨ modeOf p σ' = mREJECT) := by
  have hL : 0 < L0 b.size om := by unfold L0; omega
  intro k
  induction k with
  | zero =>
    intro σ f _ _ hi _ hk
    have := Φ_nonneg b om lit f hi
    push_cast at hk; omega
  | succ k ih =>
    intro σ f hw hs hi hT hk
    by_cases ht : f cMODE = mDONE ∨ f cMODE = mREJECT
    · exact ⟨0, σ, by omega, rfl, by rw [modeOf_world hw hL]; exact ht⟩
    · push Not at ht
      obtain ⟨j, σ1, hst, hit, hs1, hj⟩ := hr b om lit p σ f hb hw hs hi hT
      have hj1 := hj ht.1 ht.2
      obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      obtain ⟨f1, hw1, hi1, hc⟩ := defl_rest_succ b om lit p hb j' σ σ1 f hw hi ht.1 ht.2 hit
      have hT1 := iterS_tab b om lit p hb (j' + 1) σ σ1 f hw hs hi hT hit f1 hw1
      rcases hc with hlt | ht1
      · obtain ⟨j₂, σ₂, hj₂, hit₂, hm⟩ := ih σ1 f1 hw1 hs1 hi1 hT1 (by push_cast at hk ⊢; omega)
        exact ⟨j₂ + 1, σ₂, by omega, by simp [iterS₅, hst, hit₂], hm⟩
      · exact ⟨1, σ1, by omega, by simp [iterS₅, hst], by rw [modeOf_world hw1 hL]; exact ht1⟩

/-- **SAFETY over ⟶₅, from Refine₅T:** N = `Nbound` + 1, DEFLATE's own. -/
theorem safety₅_ofT (hr : Refine₅T) : SafetyStmt₅ := by
  refine ⟨fun n om => Nbound n om + 1, fun b om lit p hb => ?_⟩
  obtain ⟨j, σ', hj, hit, hm⟩ := iter_reach₅T hr b om lit p hb (Nbound b.size om + 1) (initStore b om lit p)
    (initCell b om lit) (initStore_world b om lit p) (initStore_sole b om lit p) (Inv_init b om lit) (tab_init b om lit)
    (by rw [Φ_init]; push_cast; omega)
  exact ⟨j, σ', hj, hit, hm⟩

theorem l5_reachT (hr : Refine₅T) (b : Array Nat) (om : Nat) (lit : Bool) (p : Int) (hb : ∀ x ∈ b, x < 256) :
    ∀ (k : Nat) (σ₀ σ : Store) (f₀ : Int → Int), World σ₀ p (L0 b.size om) f₀ → Sole σ₀ p (L0 b.size om) →
      Inv b om lit f₀ → Tab f₀ → iterS₅ p k σ₀ = some σ → ∃ J, iterS p J σ₀ = some σ := by
  intro k
  induction k with
  | zero =>
    intro σ₀ σ f₀ _ _ _ _ h
    simp only [iterS₅, Option.some.injEq] at h
    exact ⟨0, by simp [iterS, h]⟩
  | succ k ih =>
    intro σ₀ σ f₀ hw hs hi hT h
    obtain ⟨j, σ1, hst, hit, hs1, -⟩ := hr b om lit p σ₀ f₀ hb hw hs hi hT
    simp only [iterS₅, hst, Option.bind_some] at h
    obtain ⟨f1, hw1, hi1⟩ := reach_inv b om lit p hb j σ₀ σ1 f₀ hw hi hit
    have hT1 := iterS_tab b om lit p hb j σ₀ σ1 f₀ hw hs hi hT hit f1 hw1
    obtain ⟨J, hJ⟩ := ih σ1 σ f1 hw1 hs1 hi1 hT1 h
    exact ⟨j + J, by rw [iterS_add, hit]; simpa using hJ⟩

/-- **CORRECTNESS over ⟶₅, from Refine₅T.** -/
theorem correct₅_ofT (hr : Refine₅T) : CorrectStmt₅ := by
  intro b om lit p hb
  have reach : ∀ k σ, iterS₅ p k (initStore b om lit p) = some σ → ∃ J, iterS p J (initStore b om lit p) = some σ :=
    fun k σ h => l5_reachT hr b om lit p hb k _ σ _ (initStore_world b om lit p) (initStore_sole b om lit p)
      (Inv_init b om lit) (tab_init b om lit) h
  obtain ⟨_, hS⟩ := safety₅_ofT hr
  obtain ⟨k₅, σ₅, -, h₅, ht₅⟩ := hS b om lit p hb
  obtain ⟨J₅, hJ₅⟩ := reach k₅ σ₅ h₅
  obtain ⟨hok, herr⟩ := correct b om lit p hb
  constructor
  · intro o
    constructor
    · rintro ⟨k, σ, hit, hm, ho⟩
      obtain ⟨J, hJ⟩ := reach k σ hit
      exact (hok o).1 ⟨J, σ, hJ, hm, ho⟩
    · intro hro
      obtain ⟨k, σ', hit, hm, ho⟩ := (hok o).2 hro
      have e := term_unique b om lit p hb hJ₅ ht₅ hit (Or.inl hm)
      exact ⟨k₅, σ₅, h₅, by rw [e]; exact hm, by rw [e]; exact ho⟩
  · constructor
    · rintro ⟨k, σ, hit, hm⟩
      obtain ⟨J, hJ⟩ := reach k σ hit
      exact herr.1 ⟨J, σ, hJ, hm⟩
    · intro hre
      obtain ⟨k, σ', hit, hm⟩ := herr.2 hre
      have e := term_unique b om lit p hb hJ₅ ht₅ hit (Or.inr hm)
      exact ⟨k₅, σ₅, h₅, by rw [e]; exact hm⟩

end VIRL5
