/-
  O95 layer L5, Lean arm (STATUS 321, LV8 assembly, LV8-MAP Addendum 5): the OUTER argument, checked before the per-mode cases
  (DEFLATE's own order: `safety_of_step` before its 28 cases). From the one per-mode obligation `Refine₅` — on a world with the
  invariant that owns only its region, one ⟶₅ step is j DEFLATE steps to the same store, j ≥ 1 unless the mode is terminal —
  `SafetyStmt₅` follows with DEFLATE's own N, and `CorrectStmt₅` follows from DEFLATE's `correct`. DEFLATE's proofs are used as
  they stand: `stepSafe`, `reach_inv`, `stepS_fixed`, `iterS_fixed`, `term_unique`, `correct`, `Φ_init`, `Φ_nonneg`.
-/
import VIRL5.Assembly5
import VIRDeflate.Dynamic
import VIRDeflate.Safety

namespace VIRL5
open VIRL1 VIRL2 VIRDeflate.Step

/-- **The one per-mode obligation.** -/
def Refine₅ : Prop :=
  ∀ (b : Array Nat) (om : Nat) (lit : Bool) (p : Int) (σ : Store) (f : Int → Int), (∀ x ∈ b, x < 256) →
    World σ p (L0 b.size om) f → Sole σ p (L0 b.size om) → Inv b om lit f →
    ∃ j σ', stepS₅ p σ = some σ' ∧ iterS p j σ = some σ' ∧ Sole σ' p (L0 b.size om) ∧
      (f cMODE ≠ mDONE → f cMODE ≠ mREJECT → 1 ≤ j)

/-- A DEFLATE run from a world with the invariant keeps it; it stays put, lowers Φ, or ends at DONE or REJECT. -/
theorem defl_rest (b : Array Nat) (om : Nat) (lit : Bool) (p : Int) (hb : ∀ x ∈ b, x < 256) :
    ∀ (j : Nat) (σ σ' : Store) (f : Int → Int), World σ p (L0 b.size om) f → Inv b om lit f → iterS p j σ = some σ' →
      ∃ f', World σ' p (L0 b.size om) f' ∧ Inv b om lit f' ∧
        ((σ' = σ ∧ f' = f) ∨ Φ f' < Φ f ∨ f' cMODE = mDONE ∨ f' cMODE = mREJECT) := by
  have hL : 0 < L0 b.size om := by unfold L0; omega
  intro j
  induction j with
  | zero =>
    intro σ σ' f hw hi h
    simp only [iterS, Option.some.injEq] at h
    subst h
    exact ⟨f, hw, hi, Or.inl ⟨rfl, rfl⟩⟩
  | succ j ih =>
    intro σ σ' f hw hi h
    by_cases ht : f cMODE = mDONE ∨ f cMODE = mREJECT
    · simp only [iterS, stepS_fixed hw hL ht, Option.bind_some] at h
      have e : σ = σ' := Option.some.inj (by rw [← h, iterS_fixed hw hL ht j])
      subst e
      exact ⟨f, hw, hi, Or.inl ⟨rfl, rfl⟩⟩
    · push Not at ht
      obtain ⟨σ1, f1, hst, hw1, hi1, hlt⟩ := stepSafe b om lit p σ f hb hw hi ht.1 ht.2
      simp only [iterS, hst, Option.bind_some] at h
      obtain ⟨f', hw', hi', hc⟩ := ih σ1 σ' f1 hw1 hi1 h
      refine ⟨f', hw', hi', Or.inr ?_⟩
      rcases hlt with hlt | ht1
      · rcases hc with ⟨_, rfl⟩ | hc | hc
        · exact Or.inl hlt
        · exact Or.inl (lt_trans hc hlt)
        · exact Or.inr hc
      · have e : σ1 = σ' := Option.some.inj (by rw [← h, iterS_fixed hw1 hL ht1 j])
        subst e
        have m1 := modeOf_world hw1 hL
        have m2 := modeOf_world hw' hL
        rw [m1] at m2
        rw [← m2]
        exact Or.inr ht1

/-- From a NON-terminal world, j + 1 DEFLATE steps lower Φ or end at DONE or REJECT. -/
theorem defl_rest_succ (b : Array Nat) (om : Nat) (lit : Bool) (p : Int) (hb : ∀ x ∈ b, x < 256)
    (j : Nat) (σ σ' : Store) (f : Int → Int) (hw : World σ p (L0 b.size om) f) (hi : Inv b om lit f)
    (hd : f cMODE ≠ mDONE) (hr : f cMODE ≠ mREJECT) (h : iterS p (j + 1) σ = some σ') :
    ∃ f', World σ' p (L0 b.size om) f' ∧ Inv b om lit f' ∧ (Φ f' < Φ f ∨ f' cMODE = mDONE ∨ f' cMODE = mREJECT) := by
  have hL : 0 < L0 b.size om := by unfold L0; omega
  obtain ⟨σ1, f1, hst, hw1, hi1, hlt⟩ := stepSafe b om lit p σ f hb hw hi hd hr
  simp only [iterS, hst, Option.bind_some] at h
  obtain ⟨f', hw', hi', hc⟩ := defl_rest b om lit p hb j σ1 σ' f1 hw1 hi1 h
  refine ⟨f', hw', hi', ?_⟩
  rcases hlt with hlt | ht1
  · rcases hc with ⟨_, rfl⟩ | hc | hc
    · exact Or.inl hlt
    · exact Or.inl (lt_trans hc hlt)
    · exact Or.inr hc
  · have e : σ1 = σ' := Option.some.inj (by rw [← h, iterS_fixed hw1 hL ht1 j])
    subst e
    have m1 := modeOf_world hw1 hL
    have m2 := modeOf_world hw' hL
    rw [m1] at m2
    rw [← m2]
    exact Or.inr ht1

/-- The ⟶₅ run reaches DONE or REJECT within Φ + 1 steps (as `iter_reach`, one ⟶₅ step being ≥ 1 DEFLATE step). -/
theorem iter_reach₅ (hr : Refine₅) (b : Array Nat) (om : Nat) (lit : Bool) (p : Int) (hb : ∀ x ∈ b, x < 256) :
    ∀ (k : Nat) (σ : Store) (f : Int → Int), World σ p (L0 b.size om) f → Sole σ p (L0 b.size om) → Inv b om lit f →
      Φ f < k → ∃ j σ', j ≤ k ∧ iterS₅ p j σ = some σ' ∧ (modeOf p σ' = mDONE ∨ modeOf p σ' = mREJECT) := by
  have hL : 0 < L0 b.size om := by unfold L0; omega
  intro k
  induction k with
  | zero =>
    intro σ f _ _ hi hk
    have := Φ_nonneg b om lit f hi
    push_cast at hk; omega
  | succ k ih =>
    intro σ f hw hs hi hk
    by_cases ht : f cMODE = mDONE ∨ f cMODE = mREJECT
    · exact ⟨0, σ, by omega, rfl, by rw [modeOf_world hw hL]; exact ht⟩
    · push Not at ht
      obtain ⟨j, σ1, hst, hit, hs1, hj⟩ := hr b om lit p σ f hb hw hs hi
      have hj1 := hj ht.1 ht.2
      obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      obtain ⟨f1, hw1, hi1, hc⟩ := defl_rest_succ b om lit p hb j' σ σ1 f hw hi ht.1 ht.2 hit
      rcases hc with hlt | ht1
      · obtain ⟨j₂, σ₂, hj₂, hit₂, hm⟩ := ih σ1 f1 hw1 hs1 hi1 (by push_cast at hk ⊢; omega)
        exact ⟨j₂ + 1, σ₂, by omega, by simp [iterS₅, hst, hit₂], hm⟩
      · exact ⟨1, σ1, by omega, by simp [iterS₅, hst], by rw [modeOf_world hw1 hL]; exact ht1⟩

/-- **SAFETY over ⟶₅, from Refine₅:** N = `Nbound` + 1, DEFLATE's own. -/
theorem safety₅_of (hr : Refine₅) : SafetyStmt₅ := by
  refine ⟨fun n om => Nbound n om + 1, fun b om lit p hb => ?_⟩
  obtain ⟨j, σ', hj, hit, hm⟩ := iter_reach₅ hr b om lit p hb (Nbound b.size om + 1) (initStore b om lit p)
    (initCell b om lit) (initStore_world b om lit p) (initStore_sole b om lit p) (Inv_init b om lit)
    (by rw [Φ_init]; push_cast; omega)
  exact ⟨j, σ', hj, hit, hm⟩

/-- Every store the ⟶₅ run reaches, DEFLATE's run reaches. -/
theorem l5_reach (hr : Refine₅) (b : Array Nat) (om : Nat) (lit : Bool) (p : Int) (hb : ∀ x ∈ b, x < 256) :
    ∀ (k : Nat) (σ₀ σ : Store) (f₀ : Int → Int), World σ₀ p (L0 b.size om) f₀ → Sole σ₀ p (L0 b.size om) →
      Inv b om lit f₀ → iterS₅ p k σ₀ = some σ → ∃ J, iterS p J σ₀ = some σ := by
  intro k
  induction k with
  | zero =>
    intro σ₀ σ f₀ _ _ _ h
    simp only [iterS₅, Option.some.injEq] at h
    exact ⟨0, by simp [iterS, h]⟩
  | succ k ih =>
    intro σ₀ σ f₀ hw hs hi h
    obtain ⟨j, σ1, hst, hit, hs1, -⟩ := hr b om lit p σ₀ f₀ hb hw hs hi
    simp only [iterS₅, hst, Option.bind_some] at h
    obtain ⟨f1, hw1, hi1⟩ := reach_inv b om lit p hb j σ₀ σ1 f₀ hw hi hit
    obtain ⟨J, hJ⟩ := ih σ1 σ f1 hw1 hs1 hi1 h
    exact ⟨j + J, by rw [iterS_add, hit]; simpa using hJ⟩

/-- **CORRECTNESS over ⟶₅, from Refine₅:** the ⟶₅ run's terminal store is DEFLATE's (`term_unique`), so `correct` carries. -/
theorem correct₅_of (hr : Refine₅) : CorrectStmt₅ := by
  intro b om lit p hb
  have reach : ∀ k σ, iterS₅ p k (initStore b om lit p) = some σ → ∃ J, iterS p J (initStore b om lit p) = some σ :=
    fun k σ h => l5_reach hr b om lit p hb k _ σ _ (initStore_world b om lit p) (initStore_sole b om lit p)
      (Inv_init b om lit) h
  obtain ⟨_, hS⟩ := safety₅_of hr
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
