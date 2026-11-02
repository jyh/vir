/-
  O95 VIR program, Lean arm: the SEMANTIC reading of linearity (council 2026-11-02 §C point 4), built to the shared input
  inputs/vir-program-inputs.md S1–S5 (merged vir 5591d8b, before this file). S1 locations and partial fragments · S2 the
  separation algebra's laws, as THEOREMS · S3 what a token and a slice own · S4 THE FRAME THEOREM for the router's F: a
  fragment disjoint from F's footprint keeps its values. No disjointness premise names a region F does not touch, so this is
  the abstract form of the narrowed `hdisj`, a property of the meaning.
  Hand-built maps (Loc → Option Int), not a mathlib structure: under amend-12 these lemmas are VIR-side, and S5 counts them.
-/
import VIRP.Router

namespace VIRP

/-! ## S1. Locations and fragments -/
inductive Loc | wire (i : Nat) | bucket (p : Int)
  deriving DecidableEq

/-- A fragment: the locations it owns, with their contents. -/
abbrev Frag := Loc → Option Int

def emp : Frag := fun _ => none

/-- `h1 # h2`: disjoint domains. -/
def Disj (h1 h2 : Frag) : Prop := ∀ l, h1 l = none ∨ h2 l = none

/-- `h1 ⊎ h2`: the union (meaningful when disjoint; left-biased otherwise). -/
def union (h1 h2 : Frag) : Frag := fun l =>
  match h1 l with
  | some v => some v
  | none => h2 l

/-! ## S2. The algebra's laws -/
theorem union_emp (h : Frag) : union h emp = h := by
  funext l; unfold union emp; cases h l <;> rfl

theorem emp_union (h : Frag) : union emp h = h := by
  funext l; rfl

theorem union_comm {h1 h2 : Frag} (hd : Disj h1 h2) : union h1 h2 = union h2 h1 := by
  funext l; unfold union
  rcases hd l with e | e <;> rw [e] <;> cases h' : (h1 l) <;> cases h'' : (h2 l) <;> simp_all

theorem union_assoc (h1 h2 h3 : Frag) : union (union h1 h2) h3 = union h1 (union h2 h3) := by
  funext l; unfold union; cases h1 l <;> rfl

theorem disj_union (h1 h2 h3 : Frag) : Disj h1 (union h2 h3) ↔ Disj h1 h2 ∧ Disj h1 h3 := by
  constructor
  · intro hd
    refine ⟨fun l => ?_, fun l => ?_⟩ <;> rcases hd l with e | e
    · exact .inl e
    · unfold union at e; cases h : h2 l <;> simp_all
    · exact .inl e
    · unfold union at e; cases h : h2 l <;> simp_all
  · rintro ⟨a, b⟩ l
    rcases a l with e | e
    · exact .inl e
    · rcases b l with f | f
      · exact .inl f
      · exact .inr (by unfold union; rw [e, f])

/-! ## S3. What a type owns (the resource predicates) -/
/-- The store's contents at a location. -/
def Store.read (σ : Store) : Loc → Int
  | .wire i => σ.wire.getD i 0
  | .bucket p => σ.bucket p

def ownsTok (p : Int) (h : Frag) : Prop := ∀ l, h l ≠ none ↔ l = .bucket p
def ownsSlice (o n : Nat) (h : Frag) : Prop := ∀ l, h l ≠ none ↔ ∃ i, l = .wire i ∧ o ≤ i ∧ i < n

/-- F's footprint on σ: the token's one cell (sender p = read_u32(b0, 4)) and the frame's bytes wire(0..n). -/
def own (σ : Store) : Frag := fun l =>
  match l with
  | .wire i => if i < σ.wire.length then some (σ.read l) else none
  | .bucket p => if p = rd32 σ.wire 4 then some (σ.read l) else none

theorem own_split (σ : Store) :
    ownsTok (rd32 σ.wire 4) (fun l => match l with | .bucket p => own σ (.bucket p) | _ => none) ∧
    ownsSlice 0 σ.wire.length (fun l => match l with | .wire i => own σ (.wire i) | _ => none) := by
  constructor
  · intro l; cases l <;> simp [own]
  · intro l; cases l <;> simp [own]

/-! ## S4. THE FRAME THEOREM for F -/
/-- ⟦F⟧ either leaves the store alone or decrements the sender's one cell. -/
theorem F_effect {σ σ' : Store} {ℓ : Label} (h : denote F env0 σ = Part.some (σ', ℓ)) :
    σ' = σ ∨ σ' = σ.dec (rd32 σ.wire 4) := by
  rw [F_closed, Part.some_inj] at h
  split_ifs at h <;> simp_all

theorem frame_F {σ σ' : Store} {ℓ : Label} (h : denote F env0 σ = Part.some (σ', ℓ))
    (hf : Frag) (hd : Disj hf (own σ)) : ∀ l, hf l ≠ none → σ'.read l = σ.read l := by
  intro l hl
  rcases F_effect h with rfl | rfl
  · rfl
  · cases l with
    | wire i => rfl
    | bucket q =>
      have hq : q ≠ rd32 σ.wire 4 := by
        intro e; rcases hd (.bucket q) with x | x
        · exact hl x
        · simp [own, e] at x
      simp [Store.read, Store.dec, hq]

end VIRP
