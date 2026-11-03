/-
  O95 layer L2, Lean arm. OBJECT-L2 §5: the small axioms of the four operations, and the `let x ← o(a⃗) in e` rule that
  sequences one with its continuation. An operation is specified by an OP TRIPLE: from a fragment σ ⊨ P with any disjoint
  frame σ_f, the operation succeeds and leaves σq ⊎ σ_f with σq ⊨ Q v, the frame untouched and the whole store well-formed.
  Each small axiom is proved by the operation's LOCALITY on Finmap (amend-16 Y4: one locality argument per operation).
-/
import VIRL2.Logic

namespace VIRL2
open VIRL1

def OpTriple (P : Assn) (o : Op) (vs : List Atom₂) (Q : Atom₂ → Assn) : Prop :=
  ∀ σ σf, P σ → Store.Disj σ σf → Store.WF (σ ⊎ σf) →
    ∃ v σq, opStep o vs (σ ⊎ σf) = some (v, σq ⊎ σf) ∧ Store.Disj σq σf ∧ Store.WF (σq ⊎ σf) ∧ Q v σq

theorem step₂_letOp_inv {o as τ e σ c'} (h : Step₂ (Tm.letOp o as τ e, σ) c') :
    ∃ vs v σ', Atom.evalL as = some vs ∧ opStep o vs σ = some (v, σ') ∧ c' = (e.subst 0 v, σ') := by
  cases h with
  | pure h => cases h
  | op h₁ h₂ => exact ⟨_, _, _, h₁, h₂, rfl⟩

/-- The `let x:τ ← o(a⃗) in e` rule. -/
theorem letOp_rule {P : Assn} {o : Op} {as : List Atom₂} {τ : Ty₂} {e : Tm₂} {R : Atom₂ → Assn} {vs : List Atom₂}
    {Q : Atom₂ → Assn} (hvs : Atom.evalL as = some vs) (ho : OpTriple P o vs Q)
    (hk : ∀ v, Triple (Q v) (e.subst 0 v) R) : Triple P (.letOp o as τ e) R := by
  intro σ σf hP hd hwf
  obtain ⟨v, σq, hop, hdq, hwfq, hQ⟩ := ho σ σf hP hd hwf
  obtain ⟨hs, hpost⟩ := hk v σq σf hQ hdq hwfq
  refine ⟨fun c hc => ?_, fun a σ' hc => ?_⟩
  · cases hc with
    | refl => exact fun hf => hf.2 _ (.op hvs hop)
    | step h₁ h₂ =>
      obtain ⟨vs', v', σ', h₁', h₂', rfl⟩ := step₂_letOp_inv h₁
      rw [hvs] at h₁'; cases h₁'; rw [hop] at h₂'; cases h₂'
      exact hs c h₂
  · cases hc with
    | step h₁ h₂ =>
      obtain ⟨vs', v', σ', h₁', h₂', rfl⟩ := step₂_letOp_inv h₁
      rw [hvs] at h₁'; cases h₁'; rw [hop] at h₂'; cases h₂'
      exact hpost a σ' h₂

/-! ## load and store: a fragment owning the region entry R(p) = n and the one cell p + i. -/

/-- The fragment `reg p n ∗ (p + i ↦ w)`. -/
def cellFrag (p : Int) (n : Nat) (i w : Int) : Store := ⟨Finmap.singleton (p + i) w, Finmap.singleton p n⟩

theorem load_axiom (p : Int) (n : Nat) (i w : Int) (hi : 0 ≤ i ∧ i < n) :
    OpTriple (fun σ => σ = cellFrag p n i w) .load [.const (.cap p), .const (.int i)]
      (fun v σ => v = .const (.int w) ∧ σ = cellFrag p n i w) := by
  rintro σ σf rfl hd hwf
  refine ⟨.const (.int w), cellFrag p n i w, ?_, hd, hwf, rfl, rfl⟩
  have hR : (cellFrag p n i w ⊎ σf).R.lookup p = some n := by
    simp [cellFrag, Store.union, Finmap.lookup_union_left, Finmap.mem_singleton, Finmap.lookup_singleton_eq]
  have hH : (cellFrag p n i w ⊎ σf).H.lookup (p + i) = some w := by
    simp [cellFrag, Store.union, Finmap.lookup_union_left, Finmap.mem_singleton, Finmap.lookup_singleton_eq]
  simp [opStep, Store.load, hR, hi, hH]

theorem wf_insert_mem {σ : Store} {k v : Int} (hk : k ∈ σ.H) (h : σ.WF) : Store.WF ⟨σ.H.insert k v, σ.R⟩ where
  pos := h.pos
  disj := h.disj
  domH a := by
    rw [Finmap.mem_insert, ← h.domH a]
    constructor
    · rintro (rfl | ha) <;> assumption
    · exact Or.inr

theorem store_axiom (p : Int) (n : Nat) (i w v : Int) (hi : 0 ≤ i ∧ i < n) :
    OpTriple (fun σ => σ = cellFrag p n i w) .store [.const (.cap p), .const (.int i), .const (.int v)]
      (fun c σ => c = .const (.cap p) ∧ σ = cellFrag p n i v) := by
  rintro σ σf rfl hd hwf
  have hR : (cellFrag p n i w ⊎ σf).R.lookup p = some n := by
    simp [cellFrag, Store.union, Finmap.lookup_union_left, Finmap.mem_singleton, Finmap.lookup_singleton_eq]
  have hins : (cellFrag p n i w ⊎ σf).H.insert (p + i) v = (cellFrag p n i v ⊎ σf).H := by
    simp [cellFrag, Store.union, Finmap.insert_union, Finmap.insert_singleton_eq]
  have hmem : p + i ∈ (cellFrag p n i w ⊎ σf).H := by
    simp [cellFrag, Store.union, Finmap.mem_union, Finmap.mem_singleton]
  refine ⟨.const (.cap p), cellFrag p n i v, ?_, ?_, ?_, rfl, rfl⟩
  · have hR' : Finmap.lookup p (Finmap.singleton p n ∪ σf.R) = some n := by simpa [cellFrag, Store.union] using hR
    have hI : Finmap.insert (p + i) v (Finmap.singleton (p + i) w ∪ σf.H) = Finmap.singleton (p + i) v ∪ σf.H := by
      rw [Finmap.insert_union, Finmap.insert_singleton_eq]
    simp [opStep, Store.store, cellFrag, Store.union, hR', hi, hI]
  · exact ⟨fun a ha => hd.1 a (by simpa [cellFrag, Finmap.mem_singleton] using ha), hd.2⟩
  · have := wf_insert_mem (v := v) hmem hwf
    rw [hins] at this
    simpa [Store.union, cellFrag] using this

end VIRL2
