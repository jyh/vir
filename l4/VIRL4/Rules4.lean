/-
  O95 layer L4, Lean arm (amend-21). The rules of the L4 logic, each PROVED from ⟶₄ through `safe₄` (Safe.lean), none an axiom.
  This file: safety is monotone in its index and in the lock table; the FRAME RULE for every L4 program (Q3's comparison point is
  L2's `frame`); then the lock rules and `par_rule`.
-/
import VIRL4.Safe

namespace VIRL4
open VIRL1 VIRL2

/-! ## Store algebra used throughout. -/

theorem disj_comm' {a b : Store} : Store.Disj a b ↔ Store.Disj b a := ⟨disj_symm, disj_symm⟩

/-- Swap the two right operands of a left-nested union. -/
theorem union_swap_mid {a b c : Store} (hbc : Store.Disj b c) : a ⊎ b ⊎ c = a ⊎ c ⊎ b := by
  rw [Store.union_assoc, union_comm_disj hbc, ← Store.union_assoc]

/-! ## Monotonicity of safety. -/

theorem safe₄_mono {I : Int → Assn} {Q : Atom₄ → Assn₄} :
    ∀ (m n : Nat) (e : Tm₄) (L : List LockSt) (σ : Store), m ≤ n → safe₄ I n e L σ Q → safe₄ I m e L σ Q
  | 0, _, _, _, _, _, _ => trivial
  | m + 1, n + 1, e, L, σ, hmn, ⟨hterm, hstep⟩ => by
    refine ⟨hterm, fun L' σS σF hx hg => ⟨(hstep L' σS σF hx hg).1, fun e' s' hs => ?_⟩⟩
    obtain ⟨σ', σS', hx', hg', hσ, hsafe⟩ := (hstep L' σS σF hx hg).2 e' s' hs
    exact ⟨σ', σS', hx', hg', hσ, safe₄_mono m n e' s'.locks σ' (by omega) hsafe⟩

theorem safe₄_ext {I : Int → Assn} {Q : Atom₄ → Assn₄} :
    ∀ (n : Nat) (e : Tm₄) (L L' : List LockSt) (σ : Store), Ext L L' → safe₄ I n e L σ Q → safe₄ I n e L' σ Q
  | 0, _, _, _, _, _, _ => trivial
  | n + 1, e, L, L', σ, hx, ⟨hterm, hstep⟩ => by
    refine ⟨fun a ha => ?_, fun L'' σS σF hx' hg => hstep L'' σS σF (hx.trans hx') hg⟩
    obtain ⟨v, hv, hQ⟩ := hterm a ha
    exact ⟨v, hv, fun L'' hx' => hQ L'' (hx.trans hx')⟩

/-! ## The frame rule. -/

/-- Separating conjunction on L4 assertions (both sides see the same lock table). -/
def sep₄ (P R : Assn₄) : Assn₄ := fun L σ => ∃ σ₁ σ₂, Store.Disj σ₁ σ₂ ∧ σ = σ₁ ⊎ σ₂ ∧ P L σ₁ ∧ R L σ₂

/-- An assertion that survives the environment's lock-table moves. -/
def Stable (R : Assn₄) : Prop := ∀ L L' σ, Ext L L' → R L σ → R L' σ

theorem store_frame_eq {σ₁ σ₂ σS σF : Store} (h2S : Store.Disj σ₂ σS) :
    σ₁ ⊎ σ₂ ⊎ σS ⊎ σF = σ₁ ⊎ σS ⊎ (σ₂ ⊎ σF) := by
  rw [union_swap_mid h2S, Store.union_assoc (σ₁ ⊎ σS)]

/-- Moving σ₂ from the thread into the frame. -/
theorem glob_frame_in {I : Int → Assn} {σ₁ σ₂ σS σF : Store} {L : List LockSt} (h12 : Store.Disj σ₁ σ₂)
    (hg : Glob I (σ₁ ⊎ σ₂) σS σF L) :
    Glob I σ₁ σS (σ₂ ⊎ σF) L ∧ Store.Disj σ₂ σF ∧ σ₁ ⊎ σ₂ ⊎ σS ⊎ σF = σ₁ ⊎ σS ⊎ (σ₂ ⊎ σF) := by
  obtain ⟨hA, hB, hC, hD⟩ := hg
  simp only [Store.disj_union_left] at hA hB
  obtain ⟨h1S, h2S⟩ := hA
  obtain ⟨⟨h1F, h2F⟩, hSF⟩ := hB
  have heq := store_frame_eq (σ₁ := σ₁) (σF := σF) h2S
  refine ⟨⟨h1S, ?_, hC, heq ▸ hD⟩, h2F, heq⟩
  simp only [Store.disj_union_left, Store.disj_union_right]
  exact ⟨⟨h12, disj_symm h2S⟩, h1F, hSF⟩

/-- Moving σ₂ back from the frame into the thread (the frame's own disjointness is carried, never re-derived). -/
theorem glob_frame_out {I : Int → Assn} {σ₁ σ₂ σS σF : Store} {L : List LockSt} (h2F : Store.Disj σ₂ σF)
    (hg : Glob I σ₁ σS (σ₂ ⊎ σF) L) :
    Store.Disj σ₁ σ₂ ∧ Glob I (σ₁ ⊎ σ₂) σS σF L ∧ σ₁ ⊎ σS ⊎ (σ₂ ⊎ σF) = σ₁ ⊎ σ₂ ⊎ σS ⊎ σF := by
  obtain ⟨h1S, hB, hC, hD⟩ := hg
  simp only [Store.disj_union_left, Store.disj_union_right] at hB
  obtain ⟨⟨h12, hS2⟩, h1F, hSF⟩ := hB
  have heq := store_frame_eq (σ₁ := σ₁) (σF := σF) (disj_symm hS2)
  refine ⟨h12, ⟨?_, ?_, hC, heq.symm ▸ hD⟩, heq.symm⟩
  · simp only [Store.disj_union_left]; exact ⟨h1S, disj_symm hS2⟩
  · simp only [Store.disj_union_left]; exact ⟨⟨h1F, h2F⟩, hSF⟩

/-- Safety under a frame σ₂ satisfying a STABLE R: the thread never touches σ₂, so R still holds of it at the end. -/
theorem safe₄_frame {I : Int → Assn} {Q : Atom₄ → Assn₄} {R : Assn₄} (hR : Stable R) :
    ∀ (n : Nat) (e : Tm₄) (L : List LockSt) (σ₁ σ₂ : Store), Store.Disj σ₁ σ₂ → R L σ₂ →
      safe₄ I n e L σ₁ Q → safe₄ I n e L (σ₁ ⊎ σ₂) (fun v => sep₄ (Q v) R)
  | 0, _, _, _, _, _, _, _ => trivial
  | n + 1, e, L, σ₁, σ₂, h12, hr, ⟨hterm, hstep⟩ => by
    refine ⟨fun a ha => ?_, fun L' σS σF hx hg => ?_⟩
    · obtain ⟨v, hv, hQ⟩ := hterm a ha
      exact ⟨v, hv, fun L'' hx' => ⟨σ₁, σ₂, h12, rfl, hQ L'' hx', hR L L'' σ₂ hx' hr⟩⟩
    · obtain ⟨hg₁, h2F, heq⟩ := glob_frame_in h12 hg
      obtain ⟨hnf, hst⟩ := hstep L' σS (σ₂ ⊎ σF) hx hg₁
      refine ⟨heq ▸ hnf, fun e' s' hs => ?_⟩
      obtain ⟨σ', σS', hx', hg', hσ, hsafe⟩ := hst e' s' (heq ▸ hs)
      obtain ⟨h'2, hg'', heq'⟩ := glob_frame_out h2F hg'
      exact ⟨σ' ⊎ σ₂, σS', hx', hg'', hσ.trans heq',
        safe₄_frame hR n e' s'.locks σ' σ₂ h'2 (hR L s'.locks σ₂ (hx.trans hx') hr) hsafe⟩

/-- THE FRAME RULE at L4, for EVERY L4 program (no side condition on e; R stable under the environment's lock moves). -/
theorem frame₄ {I : Int → Assn} {P : Assn₄} {e : Tm₄} {Q : Atom₄ → Assn₄} {R : Assn₄} (hR : Stable R)
    (h : Triple₄ I P e Q) : Triple₄ I (sep₄ P R) e (fun v => sep₄ (Q v) R) := by
  rintro n L σ ⟨σ₁, σ₂, h12, rfl, hP, hr⟩
  exact safe₄_frame hR n e L σ₁ σ₂ h12 hr (h n L σ₁ hP)

/-! ## The lock table: bases are stable, and the shared part moves with acquire / release / newlock. -/

theorem map_base_set : ∀ (L : List LockSt) (l : Nat) (st st' : LockSt), L[l]? = some st → st'.base = st.base →
    (L.set l st').map LockSt.base = L.map LockSt.base
  | [], _, _, _, h, _ => by simp at h
  | x :: L, 0, st, st', h, hb => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    simp [hb]
  | x :: L, l + 1, st, st', h, hb => by
    simp only [List.getElem?_cons_succ] at h
    simp [map_base_set L l st st' h hb]

theorem ext_set {L : List LockSt} {l : Nat} {st st' : LockSt} (h : L[l]? = some st) (hb : st'.base = st.base) :
    Ext L (L.set l st') := by
  unfold Ext; rw [map_base_set L l st st' h hb]

theorem ext_append (L : List LockSt) (x : LockSt) : Ext L (L ++ [x]) := by
  unfold Ext; rw [List.map_append]; exact List.prefix_append _ _

theorem base_of_ext {L L' : List LockSt} {l : Nat} {p : Int} (h : (L.map LockSt.base)[l]? = some p) (hx : Ext L L') :
    (L'.map LockSt.base)[l]? = some p := by
  obtain ⟨t, ht⟩ := hx
  have hl : l < (L.map LockSt.base).length := by
    by_contra hc
    rw [List.getElem?_eq_none (by omega)] at h
    simp at h
  rw [← ht, List.getElem?_append_left hl]; exact h

theorem lock_at {L : List LockSt} {l : Nat} {p : Int} (h : (L.map LockSt.base)[l]? = some p) :
    ∃ st, L[l]? = some st ∧ st.base = p := by
  rw [List.getElem?_map] at h
  cases hL : L[l]? with
  | none => simp [hL] at h
  | some st => simp [hL] at h; exact ⟨st, rfl, h⟩

theorem shared_take {I : Int → Assn} : ∀ (L : List LockSt) (l : Nat) (p : Int) (σS : Store),
    L[l]? = some (.free p) → Shared I L σS →
    ∃ σI σS', Store.Disj σI σS' ∧ σS = σI ⊎ σS' ∧ OwnsRegion p σI ∧ I p σI ∧ Shared I (L.set l (.held p)) σS'
  | [], _, _, _, h, _ => by simp at h
  | x :: L, 0, p, σS, h, hs => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    simp only [Shared, List.set_cons_zero] at hs ⊢
    exact hs
  | x :: L, l + 1, p, σS, h, hs => by
    simp only [List.getElem?_cons_succ] at h
    cases x with
    | held q =>
      simp only [Shared, List.set_cons_succ] at hs ⊢
      exact shared_take L l p σS h hs
    | free q =>
      simp only [Shared, List.set_cons_succ] at hs ⊢
      obtain ⟨σ₁, σ₂, h12, rfl, ho₁, hi₁, hs₂⟩ := hs
      obtain ⟨σI, σS', hd, rfl, ho, hi, hs'⟩ := shared_take L l p σ₂ h hs₂
      obtain ⟨h1I, h1S⟩ := (Store.disj_union_right _ _ _).1 h12
      refine ⟨σI, σ₁ ⊎ σS', (Store.disj_union_right _ _ _).2 ⟨disj_symm h1I, hd⟩, ?_, ho, hi,
        σ₁, σS', h1S, rfl, ho₁, hi₁, hs'⟩
      rw [← Store.union_assoc, union_comm_disj h1I, Store.union_assoc]

theorem shared_put {I : Int → Assn} : ∀ (L : List LockSt) (l : Nat) (p : Int) (σS σI : Store),
    L[l]? = some (.held p) → Shared I L σS → Store.Disj σI σS → OwnsRegion p σI → I p σI →
    Shared I (L.set l (.free p)) (σI ⊎ σS)
  | [], _, _, _, _, h, _, _, _, _ => by simp at h
  | x :: L, 0, p, σS, σI, h, hs, hd, ho, hi => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    simp only [Shared, List.set_cons_zero] at hs ⊢
    exact ⟨σI, σS, hd, rfl, ho, hi, hs⟩
  | x :: L, l + 1, p, σS, σI, h, hs, hd, ho, hi => by
    simp only [List.getElem?_cons_succ] at h
    cases x with
    | held q =>
      simp only [Shared, List.set_cons_succ] at hs ⊢
      exact shared_put L l p σS σI h hs hd ho hi
    | free q =>
      simp only [Shared, List.set_cons_succ] at hs ⊢
      obtain ⟨σ₁, σ₂, h12, rfl, ho₁, hi₁, hs₂⟩ := hs
      obtain ⟨hI1, hI2⟩ := (Store.disj_union_right _ _ _).1 hd
      refine ⟨σ₁, σI ⊎ σ₂, (Store.disj_union_right _ _ _).2 ⟨disj_symm hI1, h12⟩, ?_, ho₁, hi₁,
        shared_put L l p σ₂ σI h hs₂ hI2 ho hi⟩
      rw [← Store.union_assoc, union_comm_disj hI1, Store.union_assoc]

theorem shared_append {I : Int → Assn} : ∀ (L : List LockSt) (p : Int) (σS σI : Store),
    Shared I L σS → Store.Disj σI σS → OwnsRegion p σI → I p σI → Shared I (L ++ [.free p]) (σI ⊎ σS)
  | [], p, σS, σI, hs, hd, ho, hi => by
    simp only [Shared, List.nil_append] at hs ⊢
    exact ⟨σI, σS, hd, rfl, ho, hi, hs⟩
  | x :: L, p, σS, σI, hs, hd, ho, hi => by
    cases x with
    | held q =>
      simp only [Shared, List.cons_append] at hs ⊢
      exact shared_append L p σS σI hs hd ho hi
    | free q =>
      simp only [Shared, List.cons_append] at hs ⊢
      obtain ⟨σ₁, σ₂, h12, rfl, ho₁, hi₁, hs₂⟩ := hs
      obtain ⟨hI1, hI2⟩ := (Store.disj_union_right _ _ _).1 hd
      refine ⟨σ₁, σI ⊎ σ₂, (Store.disj_union_right _ _ _).2 ⟨disj_symm hI1, h12⟩, ?_, ho₁, hi₁,
        shared_append L p σ₂ σI hs₂ hI2 ho hi⟩
      rw [← Store.union_assoc, union_comm_disj hI1, Store.union_assoc]

theorem owns_mem {p : Int} {σ : Store} (h : OwnsRegion p σ) : p ∈ σ.R := by
  obtain ⟨n, hR, _⟩ := h
  rw [hR]; exact (Finmap.mem_singleton p p n).2 rfl

/-! ## The three lock rules, in safety form (each a step of ⟶₄; the triples follow by `Triple₄`'s definition). -/

theorem evalL_lockv (l : Nat) : Atom₄.evalL [lockv l] = some [lockv l] := by
  simp [Atom₄.evalL, Atom₄.eval, lockv]

theorem evalL_lockv_cap (l : Nat) (p : Int) : Atom₄.evalL [lockv l, capv p] = some [lockv l, capv p] := by
  simp [Atom₄.evalL, Atom₄.eval, lockv, capv]

theorem evalL_cap (p : Int) : Atom₄.evalL [capv p] = some [capv p] := by
  simp [Atom₄.evalL, Atom₄.eval, capv]

/-- ACQUIRE: the lock exists (its base p is known); the continuation receives the capability AND the invariant's region. A held
  lock is a WAIT, never a fault. -/
theorem safe₄_acquire {I : Int → Assn} {Q : Atom₄ → Assn₄} {n l : Nat} {p : Int} {τ : Ty₄} {e : Tm₄}
    {L : List LockSt} {σ : Store} (hl : (L.map LockSt.base)[l]? = some p)
    (hk : ∀ L' σI, Ext L L' → Store.Disj σ σI → OwnsRegion p σI → I p σI →
      safe₄ I n (e.subst 0 (capv p)) L' (σ ⊎ σI) Q) :
    safe₄ I (n + 1) (.letOp .acquire [lockv l] τ e) L σ Q := by
  rw [safe₄]
  refine ⟨fun a ha => (by cases ha), fun L' σS σF hx hg => ?_⟩
  obtain ⟨st, hst, hb⟩ := lock_at (base_of_ext hl hx)
  refine ⟨fun hf => ?_, fun e' s' hs => ?_⟩
  · cases st with
    | free q => exact hf.2.1 (e.subst 0 (capv q), ⟨σ ⊎ σS ⊎ σF, L'.set l (.held q)⟩) (Step₄.op (evalL_lockv l) (by simp [opStep₄, lockv, hst]))
    | held q => exact hf.2.2 (Waits.acq hst)
  · cases hs with
    | op hvs hop =>
      rw [evalL_lockv] at hvs
      cases hvs
      cases st with
      | held q => simp [opStep₄, lockv, hst] at hop
      | free q =>
        simp [opStep₄, lockv, hst] at hop
        obtain ⟨rfl, rfl⟩ := hop
        simp only [LockSt.base] at hb
        subst hb
        obtain ⟨hA, hB, hC, hD⟩ := hg
        obtain ⟨σI, σS', hIS, rfl, ho, hi, hsh⟩ := shared_take L' l q σS hst hC
        obtain ⟨hσI, hσS'⟩ := (Store.disj_union_right _ _ _).1 hA
        have hx' : Ext L' (L'.set l (.held q)) := ext_set hst rfl
        refine ⟨σ ⊎ σI, σS', hx', ⟨(Store.disj_union_left _ _ _).2 ⟨hσS', hIS⟩, ?_, hsh, ?_⟩, ?_,
          hk _ σI (hx.trans hx') hσI ho hi⟩
        · rw [Store.union_assoc σ σI σS']; exact hB
        · rw [Store.union_assoc σ σI σS']; exact hD
        · simp only [Store.union_assoc]

/-- RELEASE: the thread gives up a fragment σI owning lock l's region and satisfying its invariant. The lock is then necessarily
  HELD (a free lock's region is in the shared part, disjoint from σI), so the step exists. -/
theorem safe₄_release {I : Int → Assn} {Q : Atom₄ → Assn₄} {n l : Nat} {p : Int} {τ : Ty₄} {e : Tm₄}
    {L : List LockSt} {σ₀ σI : Store} (hl : (L.map LockSt.base)[l]? = some p) (hd : Store.Disj σ₀ σI)
    (ho : OwnsRegion p σI) (hi : I p σI) (hk : ∀ L', Ext L L' → safe₄ I n (e.subst 0 unitv) L' σ₀ Q) :
    safe₄ I (n + 1) (.letOp .release [lockv l, capv p] τ e) L (σ₀ ⊎ σI) Q := by
  rw [safe₄]
  refine ⟨fun a ha => (by cases ha), fun L' σS σF hx hg => ?_⟩
  obtain ⟨st, hst, hb⟩ := lock_at (base_of_ext hl hx)
  obtain ⟨hA, hB, hC, hD⟩ := hg
  have hheld : st = .held p := by
    cases st with
    | held q => simp only [LockSt.base] at hb; rw [hb]
    | free q =>
      simp only [LockSt.base] at hb
      subst hb
      obtain ⟨σJ, σS', _, rfl, hoJ, _, _⟩ := shared_take L' l q σS hst hC
      exact absurd (Finmap.mem_union.2 (Or.inl (owns_mem hoJ)))
        (hA.2 q (Finmap.mem_union.2 (Or.inr (owns_mem ho))))
  subst hheld
  refine ⟨fun hf => hf.2.1 (e.subst 0 unitv, ⟨σ₀ ⊎ σI ⊎ σS ⊎ σF, L'.set l (.free p)⟩) (Step₄.op (evalL_lockv_cap l p) (by simp [opStep₄, lockv, capv, hst])), fun e' s' hs => ?_⟩
  cases hs with
  | op hvs hop =>
    rw [evalL_lockv_cap] at hvs
    cases hvs
    simp [opStep₄, lockv, capv, hst] at hop
    obtain ⟨rfl, rfl⟩ := hop
    obtain ⟨h0S, hIS⟩ := (Store.disj_union_left _ _ _).1 hA
    have hx' : Ext L' (L'.set l (.free p)) := ext_set hst rfl
    refine ⟨σ₀, σI ⊎ σS, hx', ⟨(Store.disj_union_right _ _ _).2 ⟨hd, h0S⟩, ?_, shared_put L' l p σS σI hst hC hIS ho hi, ?_⟩,
      ?_, hk _ (hx.trans hx')⟩
    · rw [← Store.union_assoc]; exact hB
    · rw [← Store.union_assoc]; exact hD
    · simp only [Store.union_assoc]

/-- NEWLOCK: the thread gives up its region σI with the invariant; the continuation receives a lock id k whose base is p. -/
theorem safe₄_newlock {I : Int → Assn} {Q : Atom₄ → Assn₄} {n : Nat} {p : Int} {τ : Ty₄} {e : Tm₄}
    {L : List LockSt} {σ₀ σI : Store} (hd : Store.Disj σ₀ σI) (ho : OwnsRegion p σI) (hi : I p σI)
    (hk : ∀ L' k, Ext L L' → (L'.map LockSt.base)[k]? = some p → safe₄ I n (e.subst 0 (lockv k)) L' σ₀ Q) :
    safe₄ I (n + 1) (.letOp .newlock [capv p] τ e) L (σ₀ ⊎ σI) Q := by
  rw [safe₄]
  refine ⟨fun a ha => (by cases ha), fun L' σS σF hx hg => ?_⟩
  obtain ⟨hA, hB, hC, hD⟩ := hg
  refine ⟨fun hf => hf.2.1 (e.subst 0 (lockv L'.length), ⟨σ₀ ⊎ σI ⊎ σS ⊎ σF, L' ++ [.free p]⟩) (Step₄.op (evalL_cap p) (by simp [opStep₄, capv])), fun e' s' hs => ?_⟩
  cases hs with
  | op hvs hop =>
    rw [evalL_cap] at hvs
    cases hvs
    simp [opStep₄, capv] at hop
    obtain ⟨rfl, rfl⟩ := hop
    obtain ⟨h0S, hIS⟩ := (Store.disj_union_left _ _ _).1 hA
    have hx' : Ext L' (L' ++ [.free p]) := ext_append L' _
    refine ⟨σ₀, σI ⊎ σS, hx', ⟨(Store.disj_union_right _ _ _).2 ⟨hd, h0S⟩, ?_, shared_append L' p σS σI hC hIS ho hi, ?_⟩,
      ?_, hk _ _ (hx.trans hx') (by simp [LockSt.base])⟩
    · rw [← Store.union_assoc]; exact hB
    · rw [← Store.union_assoc]; exact hD
    · simp only [Store.union_assoc]

/-! ## ret, let, par. -/

theorem not_term {e : Tm₄} (h : ∀ a, e ≠ .ret a) : ¬ e.IsTerminal := by
  cases e <;> simp_all [Tm₄.IsTerminal]

theorem progress_of_not_faults {c : Config₄} (hnf : ¬ Faults₄ c) (ht : ¬ c.1.IsTerminal) :
    (∃ c', Step₄ c c') ∨ Waits c.1 c.2 := by
  by_contra h
  push_neg at h
  exact hnf ⟨ht, fun c' hs => h.1 c' hs, h.2⟩

theorem safe₄_ret {I : Int → Assn} {Q : Atom₄ → Assn₄} {a v : Atom₄} (hv : Atom₄.eval a = some v) {L : List LockSt}
    {σ : Store} (hQ : ∀ L', Ext L L' → Q v L' σ) : ∀ n, safe₄ I n (.ret a) L σ Q
  | 0 => trivial
  | n + 1 => by
    rw [safe₄]
    refine ⟨fun a' ha => ?_, fun L' σS σF _ _ => ⟨fun hf => hf.1 trivial, fun e' s' hs => by cases hs⟩⟩
    cases ha
    exact ⟨v, hv, hQ⟩

theorem safe₄_let {I : Int → Assn} {R Q₁ : Atom₄ → Assn₄} {τ : Ty₄} {e₂ : Tm₄}
    (hk : ∀ v L' σ', Q₁ v L' σ' → ∀ m, safe₄ I m (e₂.subst 0 v) L' σ' R) :
    ∀ (n : Nat) (e₁ : Tm₄) (L : List LockSt) (σ : Store), safe₄ I n e₁ L σ Q₁ → safe₄ I n (.letE τ e₁ e₂) L σ R
  | 0, _, _, _, _ => trivial
  | n + 1, e₁, L, σ, ⟨ht, hst⟩ => by
    rw [safe₄]
    refine ⟨fun a ha => (by cases ha), fun L' σS σF hx hg => ?_⟩
    obtain ⟨hnf, hsteps⟩ := hst L' σS σF hx hg
    refine ⟨fun hf => ?_, fun e' s' hs => ?_⟩
    · by_cases h1 : ∃ a, e₁ = .ret a
      · obtain ⟨a, rfl⟩ := h1
        obtain ⟨v, hv, _⟩ := ht a rfl
        exact hf.2.1 _ (Step₄.letRet hv)
      · push_neg at h1
        rcases progress_of_not_faults hnf (not_term h1) with ⟨⟨e₁', s₁'⟩, hs⟩ | hw
        · exact hf.2.1 _ (Step₄.letStep hs)
        · exact hf.2.2 (Waits.letW hw)
    · cases hs with
      | letRet hv =>
        obtain ⟨v', hv', hQ⟩ := ht _ rfl
        rw [hv] at hv'
        cases hv'
        exact ⟨σ, σS, Ext.refl _, hg, rfl, hk _ L' σ (hQ L' hx) n⟩
      | letStep h =>
        obtain ⟨σ', σS', hx', hg', hσ, hsafe⟩ := hsteps _ _ h
        exact ⟨σ', σS', hx', hg', hσ, safe₄_let hk n _ _ σ' hsafe⟩

/-- THE PARALLEL RULE, in safety form: two threads safe on disjoint fragments make their `par` safe on the union; each thread sees
  the other's fragment as part of its frame. -/
theorem safe₄_par {I : Int → Assn} {R Q₁ Q₂ : Atom₄ → Assn₄} {τ₁ τ₂ : Ty₄} {e : Tm₄}
    (hk : ∀ v₁ v₂ L' σ₁' σ₂', Store.Disj σ₁' σ₂' → Q₁ v₁ L' σ₁' → Q₂ v₂ L' σ₂' →
      ∀ m, safe₄ I m ((e.subst 0 v₂).subst 0 v₁) L' (σ₁' ⊎ σ₂') R) :
    ∀ (n : Nat) (e₁ e₂ : Tm₄) (L : List LockSt) (σ₁ σ₂ : Store), Store.Disj σ₁ σ₂ →
      safe₄ I n e₁ L σ₁ Q₁ → safe₄ I n e₂ L σ₂ Q₂ → safe₄ I n (.par τ₁ τ₂ e₁ e₂ e) L (σ₁ ⊎ σ₂) R
  | 0, _, _, _, _, _, _, _, _ => trivial
  | n + 1, e₁, e₂, L, σ₁, σ₂, h12, hs₁, hs₂ => by
    have hs₁' := hs₁
    have hs₂' := hs₂
    obtain ⟨ht₁, hst₁⟩ := hs₁
    obtain ⟨ht₂, hst₂⟩ := hs₂
    rw [safe₄]
    refine ⟨fun a ha => (by cases ha), fun L' σS σF hx hg => ?_⟩
    obtain ⟨hg₁, h2F, heq₁⟩ := glob_frame_in h12 hg
    have hg' : Glob I (σ₂ ⊎ σ₁) σS σF L' := by rw [← union_comm_disj h12]; exact hg
    obtain ⟨hg₂, h1F, heq₂⟩ := glob_frame_in (disj_symm h12) hg'
    have heq₂' : σ₁ ⊎ σ₂ ⊎ σS ⊎ σF = σ₂ ⊎ σS ⊎ (σ₁ ⊎ σF) := by rw [union_comm_disj h12]; exact heq₂
    obtain ⟨hnf₁, hsteps₁⟩ := hst₁ L' σS (σ₂ ⊎ σF) hx hg₁
    obtain ⟨hnf₂, hsteps₂⟩ := hst₂ L' σS (σ₁ ⊎ σF) hx hg₂
    rw [← heq₁] at hnf₁ hsteps₁
    rw [← heq₂'] at hnf₂ hsteps₂
    refine ⟨fun hf => ?_, fun e' s' hs => ?_⟩
    · by_cases h1 : ∃ a₁, e₁ = .ret a₁
      · obtain ⟨a₁, rfl⟩ := h1
        obtain ⟨v₁, hv₁, _⟩ := ht₁ a₁ rfl
        by_cases h2 : ∃ a₂, e₂ = .ret a₂
        · obtain ⟨a₂, rfl⟩ := h2
          obtain ⟨v₂, hv₂, _⟩ := ht₂ a₂ rfl
          exact hf.2.1 _ (Step₄.parDone hv₁ hv₂)
        · push_neg at h2
          rcases progress_of_not_faults hnf₂ (not_term h2) with ⟨⟨e₂', s₂'⟩, hs⟩ | hw
          · exact hf.2.1 _ (Step₄.parR hs)
          · exact hf.2.2 (Waits.parR hw)
      · push_neg at h1
        rcases progress_of_not_faults hnf₁ (not_term h1) with ⟨⟨e₁', s₁'⟩, hs⟩ | hw₁
        · exact hf.2.1 _ (Step₄.parL hs)
        · by_cases h2 : ∃ a₂, e₂ = .ret a₂
          · obtain ⟨a₂, rfl⟩ := h2
            exact hf.2.2 (Waits.parL hw₁)
          · push_neg at h2
            rcases progress_of_not_faults hnf₂ (not_term h2) with ⟨⟨e₂', s₂'⟩, hs⟩ | hw₂
            · exact hf.2.1 _ (Step₄.parR hs)
            · exact hf.2.2 (Waits.parBoth hw₁ hw₂)
    · cases hs with
      | parL h =>
        obtain ⟨σ₁', σS', hx', hgo, hσ, hsafe⟩ := hsteps₁ _ _ h
        obtain ⟨h12', hgn, heqn⟩ := glob_frame_out h2F hgo
        exact ⟨σ₁' ⊎ σ₂, σS', hx', hgn, hσ.trans heqn, safe₄_par hk n _ _ _ σ₁' σ₂ h12' hsafe
          (safe₄_mono n (n + 1) e₂ _ σ₂ (by omega) (safe₄_ext (n + 1) e₂ L _ σ₂ (hx.trans hx') hs₂'))⟩
      | parR h =>
        obtain ⟨σ₂', σS', hx', hgo, hσ, hsafe⟩ := hsteps₂ _ _ h
        obtain ⟨h21', hgn, heqn⟩ := glob_frame_out h1F hgo
        refine ⟨σ₁ ⊎ σ₂', σS', hx', ?_, ?_, safe₄_par hk n _ _ _ σ₁ σ₂' (disj_symm h21')
          (safe₄_mono n (n + 1) e₁ _ σ₁ (by omega) (safe₄_ext (n + 1) e₁ L _ σ₁ (hx.trans hx') hs₁')) hsafe⟩
        · rw [union_comm_disj (disj_symm h21')]; exact hgn
        · rw [hσ, heqn, union_comm_disj h21']
      | parDone hv₁ hv₂ =>
        obtain ⟨v₁', hv₁', hQ₁⟩ := ht₁ _ rfl
        obtain ⟨v₂', hv₂', hQ₂⟩ := ht₂ _ rfl
        rw [hv₁] at hv₁'
        cases hv₁'
        rw [hv₂] at hv₂'
        cases hv₂'
        exact ⟨σ₁ ⊎ σ₂, σS, Ext.refl _, hg, rfl, hk _ _ L' σ₁ σ₂ h12 (hQ₁ L' hx) (hQ₂ L' hx) n⟩

/-! ## The rules as triples. -/

theorem ret₄_rule {I : Int → Assn} {P : Assn₄} {a v : Atom₄} {Q : Atom₄ → Assn₄} (hv : Atom₄.eval a = some v)
    (hP : ∀ L σ, P L σ → ∀ L', Ext L L' → Q v L' σ) : Triple₄ I P (.ret a) Q :=
  fun n L σ hp => safe₄_ret hv (hP L σ hp) n

theorem let₄_rule {I : Int → Assn} {P : Assn₄} {τ : Ty₄} {e₁ e₂ : Tm₄} {Q₁ R : Atom₄ → Assn₄}
    (h₁ : Triple₄ I P e₁ Q₁) (h₂ : ∀ v, Triple₄ I (Q₁ v) (e₂.subst 0 v) R) : Triple₄ I P (.letE τ e₁ e₂) R :=
  fun n L σ hp => safe₄_let (fun v L' σ' hq m => h₂ v m L' σ' hq) n e₁ L σ (h₁ n L σ hp)

/-- THE PARALLEL RULE (OBJECT-L4 H1 (a), read by erratum L4-E1): {P₁} e₁ {Q₁} ∧ {P₂} e₂ {Q₂} ⇒ {P₁ ∗ P₂} par e₁ e₂ {…}, the two
  results bound in the continuation, which starts from Q₁ v₁ ∗ Q₂ v₂. -/
theorem par₄_rule {I : Int → Assn} {P₁ P₂ : Assn₄} {τ₁ τ₂ : Ty₄} {e₁ e₂ e : Tm₄} {Q₁ Q₂ R : Atom₄ → Assn₄}
    (h₁ : Triple₄ I P₁ e₁ Q₁) (h₂ : Triple₄ I P₂ e₂ Q₂)
    (hk : ∀ v₁ v₂, Triple₄ I (sep₄ (Q₁ v₁) (Q₂ v₂)) ((e.subst 0 v₂).subst 0 v₁) R) :
    Triple₄ I (sep₄ P₁ P₂) (.par τ₁ τ₂ e₁ e₂ e) R := by
  rintro n L σ ⟨σ₁, σ₂, h12, rfl, hp₁, hp₂⟩
  exact safe₄_par (fun v₁ v₂ L' σ₁' σ₂' hd hq₁ hq₂ m => hk v₁ v₂ m L' _ ⟨σ₁', σ₂', hd, rfl, hq₁, hq₂⟩)
    n e₁ e₂ L σ₁ σ₂ h12 (h₁ n L σ₁ hp₁) (h₂ n L σ₂ hp₂)

/-! ## L2's operations, lifted: an L2 `OpTriple` (OBJECT-L2 §5's small axioms) is an L4 op rule, the frame being the shared part
  and every other thread's fragment, the lock table untouched (Q1: L2's `opStep` and `OpTriple` are imported, unchanged). -/

theorem opStep₄_o2 {o : Op} {vs : List Atom₄} {ws : List Atom₂} {s : Store₄} (hws : vs.mapM lowerV = some ws) :
    opStep₄ (.o2 o) vs s = (opStep o ws s.σ).map fun (v, σ') => (raiseV v, ⟨σ', s.locks⟩) := by
  simp [opStep₄, hws]

theorem safe₄_op2 {I : Int → Assn} {Q : Atom₄ → Assn₄} {n : Nat} {o : Op} {as : List Atom₄} {τ : Ty₄} {e : Tm₄}
    {L : List LockSt} {σ : Store} {vs : List Atom₄} {ws : List Atom₂} {P : Assn} {Qo : Atom₂ → Assn}
    (hvs : Atom₄.evalL as = some vs) (hws : vs.mapM lowerV = some ws) (ho : OpTriple P o ws Qo) (hP : P σ)
    (hk : ∀ v σq, Qo v σq → safe₄ I n (e.subst 0 (raiseV v)) L σq Q) :
    safe₄ I (n + 1) (.letOp (.o2 o) as τ e) L σ Q := by
  rw [safe₄]
  refine ⟨fun a ha => (by cases ha), fun L' σS σF hx hg => ?_⟩
  obtain ⟨hA, hB, hC, hD⟩ := hg
  have hd : Store.Disj σ (σS ⊎ σF) :=
    (Store.disj_union_right _ _ _).2 ⟨hA, ((Store.disj_union_left _ _ _).1 hB).1⟩
  have hSF : Store.Disj σS σF := ((Store.disj_union_left _ _ _).1 hB).2
  have hwf : Store.WF (σ ⊎ (σS ⊎ σF)) := by rw [← Store.union_assoc]; exact hD
  obtain ⟨v, σq, hop, hdq, hwfq, hQo⟩ := ho σ (σS ⊎ σF) hP hd hwf
  have hop' : opStep o ws (σ ⊎ σS ⊎ σF) = some (v, σq ⊎ (σS ⊎ σF)) := by rw [Store.union_assoc]; exact hop
  refine ⟨fun hf => hf.2.1 (e.subst 0 (raiseV v), ⟨σq ⊎ (σS ⊎ σF), L'⟩) (Step₄.op hvs (by rw [opStep₄_o2 hws, hop']; rfl)),
    fun e' s' hs => ?_⟩
  cases hs with
  | op hvs' hop'' =>
    rw [hvs] at hvs'
    cases hvs'
    rw [opStep₄_o2 hws] at hop''
    simp only [hop', Option.map_some, Option.some.injEq, Prod.mk.injEq] at hop''
    obtain ⟨rfl, rfl⟩ := hop''
    obtain ⟨hqS, hqF⟩ := (Store.disj_union_right _ _ _).1 hdq
    refine ⟨σq, σS, Ext.refl _, ⟨hqS, (Store.disj_union_left _ _ _).2 ⟨hqF, hSF⟩, hC, ?_⟩, ?_,
      safe₄_ext n _ L L' σq hx (hk v σq hQo)⟩
    · rw [Store.union_assoc]; exact hwfq
    · simp only [Store.union_assoc]

/-- The lifted op rule as a triple. -/
theorem op2₄_rule {I : Int → Assn} {P₄ : Assn₄} {o : Op} {as : List Atom₄} {τ : Ty₄} {e : Tm₄} {R : Atom₄ → Assn₄}
    {vs : List Atom₄} {ws : List Atom₂} {P : Assn} {Qo : Atom₂ → Assn}
    (hvs : Atom₄.evalL as = some vs) (hws : vs.mapM lowerV = some ws) (ho : OpTriple P o ws Qo)
    (hP : ∀ L σ, P₄ L σ → P σ) (hk : ∀ v, ∀ L σ, P₄ L σ → Triple₄ I (fun _ σq => Qo v σq) (e.subst 0 (raiseV v)) R) :
    Triple₄ I P₄ (.letOp (.o2 o) as τ e) R := by
  intro n L σ hp
  cases n with
  | zero => trivial
  | succ n => exact safe₄_op2 hvs hws ho (hP L σ hp) (fun v σq hq => hk v L σ hp n L σq hq)

end VIRL4
