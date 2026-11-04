/-
  O95 layer L2, Lean arm. Y5 step 7 (STAGE-L2-LEAN): `OwnAll Ω`, the separating conjunction over p ∈ Ω of "σ owns exactly
  the region at p" (any length, any contents); its permutation and append lemmas (Ω₁ ++ Ω₂ ↔ ∗), the extraction of one
  owned region, and region-level `load` / `store` specified from `IsRegion` alone (the contents function is built from the
  fragment's own lookups, then `load_at` / `store_at` apply). Preservation (step 8) carries OwnAll Ω as its store invariant.
-/
import VIRL2.Triples

namespace VIRL2
open VIRL1

/-! ## ∗: associativity, monotonicity, the unit. -/

theorem sep_assoc {P Q R : Assn} {σ} (h : ((P ∗ Q) ∗ R) σ) : (P ∗ (Q ∗ R)) σ := by
  obtain ⟨_, σ₃, hd, rfl, ⟨σ₁, σ₂, hd₁₂, rfl, hP, hQ⟩, hR⟩ := h
  obtain ⟨hd₁₃, hd₂₃⟩ := (Store.disj_union_left _ _ _).1 hd
  exact ⟨σ₁, σ₂ ⊎ σ₃, (Store.disj_union_right _ _ _).2 ⟨hd₁₂, hd₁₃⟩, Store.union_assoc _ _ _, hP,
    σ₂, σ₃, hd₂₃, rfl, hQ, hR⟩

theorem sep_assoc' {P Q R : Assn} {σ} (h : (P ∗ (Q ∗ R)) σ) : ((P ∗ Q) ∗ R) σ := by
  obtain ⟨σ₁, _, hd, rfl, hP, σ₂, σ₃, hd₂₃, rfl, hQ, hR⟩ := h
  obtain ⟨hd₁₂, hd₁₃⟩ := (Store.disj_union_right _ _ _).1 hd
  exact ⟨σ₁ ⊎ σ₂, σ₃, (Store.disj_union_left _ _ _).2 ⟨hd₁₃, hd₂₃⟩, (Store.union_assoc _ _ _).symm,
    ⟨σ₁, σ₂, hd₁₂, rfl, hP, hQ⟩, hR⟩

theorem sep_mono {P P' Q Q' : Assn} (hP : ∀ σ, P σ → P' σ) (hQ : ∀ σ, Q σ → Q' σ) {σ} (h : (P ∗ Q) σ) :
    (P' ∗ Q') σ := by
  obtain ⟨σ₁, σ₂, hd, rfl, h₁, h₂⟩ := h; exact ⟨σ₁, σ₂, hd, rfl, hP _ h₁, hQ _ h₂⟩

theorem emp_sep_iff {R : Assn} {σ} : (Assn.emp ∗ R) σ ↔ R σ := ⟨sep_emp_inv, emp_sep⟩

/-- Exchange of the two leftmost conjuncts. -/
theorem sep_swap {P Q R : Assn} {σ} (h : (P ∗ (Q ∗ R)) σ) : (Q ∗ (P ∗ R)) σ :=
  sep_assoc (sep_mono (fun _ h => sep_comm h) (fun _ h => h) (sep_assoc' h))

/-! ## OwnAll. -/

/-- σ owns exactly the region based at p, of some length. -/
def OwnsRegion (p : Int) : Assn := fun σ => ∃ n, IsRegion p n σ

/-- `OwnAll Ω` := ∗ over p ∈ Ω of `OwnsRegion p` (the empty list is `emp`). -/
def OwnAll : List Int → Assn
  | [] => Assn.emp
  | p :: Ω => OwnsRegion p ∗ OwnAll Ω

theorem OwnAll.nil_iff {σ} : OwnAll [] σ ↔ σ = Store.empty := Iff.rfl

theorem OwnAll.append : ∀ (Ω₁ Ω₂ : List Int) σ, OwnAll (Ω₁ ++ Ω₂) σ ↔ (OwnAll Ω₁ ∗ OwnAll Ω₂) σ
  | [], Ω₂, σ => emp_sep_iff.symm
  | p :: Ω₁, Ω₂, σ => by
    show (OwnsRegion p ∗ OwnAll (Ω₁ ++ Ω₂)) σ ↔ ((OwnsRegion p ∗ OwnAll Ω₁) ∗ OwnAll Ω₂) σ
    constructor
    · intro h; exact sep_assoc' (sep_mono (fun _ h => h) (fun σ h => (OwnAll.append Ω₁ Ω₂ σ).1 h) h)
    · intro h; exact sep_mono (fun _ h => h) (fun σ h => (OwnAll.append Ω₁ Ω₂ σ).2 h) (sep_assoc h)

theorem OwnAll.perm {Ω Ω' : List Int} (h : Ω.Perm Ω') : ∀ σ, OwnAll Ω σ → OwnAll Ω' σ := by
  induction h with
  | nil => exact fun _ h => h
  | cons x _ ih => exact fun _ h => sep_mono (fun _ h => h) ih h
  | swap x y l => exact fun _ h => sep_swap h
  | trans _ _ ih₁ ih₂ => exact fun σ h => ih₂ σ (ih₁ σ h)

theorem OwnAll.perm_iff {Ω Ω' : List Int} (h : Ω.Perm Ω') (σ) : OwnAll Ω σ ↔ OwnAll Ω' σ :=
  ⟨OwnAll.perm h σ, OwnAll.perm h.symm σ⟩

/-- One owned region taken out of OwnAll. -/
theorem OwnAll.extract {Ω : List Int} {p : Int} (hp : p ∈ Ω) {σ} (h : OwnAll Ω σ) :
    (OwnsRegion p ∗ OwnAll (Ω.erase p)) σ :=
  OwnAll.perm (List.perm_cons_erase hp) σ h

/-- ... and put back. -/
theorem OwnAll.insert {Ω : List Int} {p : Int} (hp : p ∈ Ω) {σ} (h : (OwnsRegion p ∗ OwnAll (Ω.erase p)) σ) :
    OwnAll Ω σ :=
  OwnAll.perm (List.perm_cons_erase hp).symm σ h

/-! ## Region-level load and store from `IsRegion` alone. -/

/-- The contents a region fragment carries, read from its own cells. -/
def contentsOf (σ : Store) : Int → Int := fun a => (σ.H.lookup a).getD 0

theorem IsRegion.regionAt {p : Int} {n : Nat} {σ : Store} (h : IsRegion p n σ) : RegionAt p n (contentsOf σ) σ := by
  refine ⟨h.1, fun a => ?_⟩
  split_ifs with hc
  · obtain ⟨w, hw⟩ := Finmap.mem_iff.1 ((h.2 a).2 hc)
    simp [contentsOf, hw]
  · exact Finmap.lookup_eq_none.2 (fun hm => hc ((h.2 a).1 hm))

theorem load_region (p : Int) (n : Nat) (i : Int) (hi : 0 ≤ i ∧ i < n) :
    OpTriple (IsRegion p n) .load [.const (.cap p), .const (.int i)]
      (fun v σ => (∃ w, v = .const (.int w)) ∧ IsRegion p n σ) := by
  intro σ σf h hd hwf
  obtain ⟨v, σq, hop, hdq, hw, hv, hR⟩ := load_at p n (contentsOf σ) i hi σ σf h.regionAt hd hwf
  exact ⟨v, σq, hop, hdq, hw, ⟨_, hv⟩, hR.isRegion⟩

theorem store_region (p : Int) (n : Nat) (i v : Int) (hi : 0 ≤ i ∧ i < n) :
    OpTriple (IsRegion p n) .store [.const (.cap p), .const (.int i), .const (.int v)]
      (fun c σ => c = .const (.cap p) ∧ IsRegion p n σ) := by
  intro σ σf h hd hwf
  obtain ⟨c, σq, hop, hdq, hw, hc, hR⟩ := store_at p n (contentsOf σ) i v hi σ σf h.regionAt hd hwf
  exact ⟨c, σq, hop, hdq, hw, hc, hR.isRegion⟩

/-- `alloc`'s result is an owned region. -/
theorem alloc_region (n : Int) (hn : 0 < n) :
    OpTriple Assn.emp .alloc [.const (.int n)] (fun v σ => ∃ p, v = .const (.cap p) ∧ OwnsRegion p σ) :=
  op_conseq (fun _ h => h) (fun _ _ ⟨p, hv, hR⟩ => ⟨p, hv, _, hR.isRegion⟩) (alloc_axiom n hn)

end VIRL2
