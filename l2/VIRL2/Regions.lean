/-
  O95 layer L2, Lean arm. Region-level specifications used by the acceptance programs: `load` and `store` on a fragment
  owning a WHOLE region with contents f, the FRAME RULE for one operation (M2's middle `store` is derived by it), and the
  precondition rules (∃, a pure conjunct). Each is proved from the definitions in Logic/Axioms; none adds a primitive.
-/
import VIRL2.Rules

namespace VIRL2
open VIRL1

theorem regionAt_lookup_p {p n f σ σf} (h : RegionAt p n f σ) : ((σ ⊎ σf).R).lookup p = some n := by
  show (σ.R ∪ σf.R).lookup p = some n
  rw [h.1, Store.lookup_sing_union]; simp

theorem load_at (p : Int) (n : Nat) (f : Int → Int) (i : Int) (hi : 0 ≤ i ∧ i < n) :
    OpTriple (RegionAt p n f) .load [.const (.cap p), .const (.int i)]
      (fun v σ => v = .const (.int (f (p + i))) ∧ RegionAt p n f σ) := by
  intro σ σf h hd hwf
  refine ⟨.const (.int (f (p + i))), σ, ?_, hd, hwf, rfl, h⟩
  have hin : Store.InRegion (p + i) p n := by unfold Store.InRegion; omega
  have hH : (σ ⊎ σf).H.lookup (p + i) = some (f (p + i)) := by
    show (σ.H ∪ σf.H).lookup (p + i) = _
    have hl := h.2 (p + i); rw [if_pos hin] at hl
    rw [Finmap.lookup_union_left (Finmap.mem_of_lookup_eq_some hl), hl]
  simp [opStep, Store.load, regionAt_lookup_p (σf := σf) h, hi, hH]

theorem store_at (p : Int) (n : Nat) (f : Int → Int) (i v : Int) (hi : 0 ≤ i ∧ i < n) :
    OpTriple (RegionAt p n f) .store [.const (.cap p), .const (.int i), .const (.int v)]
      (fun c σ => c = .const (.cap p) ∧ RegionAt p n (Function.update f (p + i) v) σ) := by
  intro σ σf h hd hwf
  have hin : Store.InRegion (p + i) p n := by unfold Store.InRegion; omega
  have hmem : p + i ∈ σ.H := by
    have hl := h.2 (p + i); rw [if_pos hin] at hl; exact Finmap.mem_of_lookup_eq_some hl
  let σq : Store := ⟨σ.H.insert (p + i) v, σ.R⟩
  have hq : RegionAt p n (Function.update f (p + i) v) σq := by
    refine ⟨h.1, fun a => ?_⟩
    show (σ.H.insert (p + i) v).lookup a = _
    by_cases ha : a = p + i
    · subst ha; rw [Finmap.lookup_insert, if_pos hin]; simp
    · rw [Finmap.lookup_insert_of_ne _ ha, h.2 a, Function.update_of_ne ha]
  have hu : (⟨(σ ⊎ σf).H.insert (p + i) v, (σ ⊎ σf).R⟩ : Store) = σq ⊎ σf := by
    show (⟨(σ.H ∪ σf.H).insert (p + i) v, σ.R ∪ σf.R⟩ : Store) = ⟨σ.H.insert (p + i) v ∪ σf.H, σ.R ∪ σf.R⟩
    rw [Finmap.insert_union]
  refine ⟨.const (.cap p), σq, ?_, ⟨fun a ha => hd.1 a ?_, hd.2⟩, ?_, rfl, hq⟩
  · simp only [opStep, Store.store, regionAt_lookup_p (σf := σf) h, hi, and_self, if_true, Option.map_some]
    rw [hu]
  · rw [Finmap.mem_insert] at ha; rcases ha with rfl | ha
    · exact hmem
    · exact ha
  · rw [← hu]; exact wf_insert_mem (Finmap.mem_union.2 (Or.inl hmem)) hwf

theorem free_at (p : Int) (n : Nat) (f : Int → Int) :
    OpTriple (RegionAt p n f) .free [.const (.cap p)] (fun v σ => v = .const .unit ∧ σ = Store.empty) :=
  fun σ σf h => free_axiom p n σ σf h.isRegion

/-- THE FRAME RULE for one operation. -/
theorem op_frame {P : Assn} {o : Op} {vs : List Atom₂} {Q : Atom₂ → Assn} (R : Assn) (h : OpTriple P o vs Q) :
    OpTriple (P ∗ R) o vs (fun v => Q v ∗ R) := by
  intro σ σf hPR hd hwf
  obtain ⟨σp, σr, hpr, rfl, hP, hR⟩ := hPR
  have hd' : Store.Disj σp (σr ⊎ σf) := by
    rw [Store.disj_union_left] at hd
    exact (Store.disj_union_right _ _ _).2 ⟨hpr, hd.1⟩
  have hdr : Store.Disj σr σf := ((Store.disj_union_left _ _ _).1 hd).2
  rw [Store.union_assoc] at hwf ⊢
  obtain ⟨v, σq, hop, hq, hw, hQ⟩ := h σp (σr ⊎ σf) hP hd' hwf
  obtain ⟨hqr, hqf⟩ := (Store.disj_union_right _ _ _).1 hq
  refine ⟨v, σq ⊎ σr, ?_, (Store.disj_union_left _ _ _).2 ⟨hqf, hdr⟩, ?_, σq, σr, hqr, rfl, hQ, hR⟩
  · rw [Store.union_assoc]; exact hop
  · rw [Store.union_assoc]; exact hw

theorem pre_ex {α : Type} {P : α → Assn} {e : Tm₂} {Q : Atom₂ → Assn} (h : ∀ x, Triple (P x) e Q) :
    Triple (fun σ => ∃ x, P x σ) e Q := by
  rintro σ σf ⟨x, hx⟩ hd hwf; exact h x σ σf hx hd hwf

theorem pre_pure {φ : Prop} {P : Assn} {e : Tm₂} {Q : Atom₂ → Assn} (h : φ → Triple P e Q) :
    Triple (fun σ => φ ∧ P σ) e Q := by
  rintro σ σf ⟨hφ, hP⟩ hd hwf; exact h hφ σ σf hP hd hwf

end VIRL2
