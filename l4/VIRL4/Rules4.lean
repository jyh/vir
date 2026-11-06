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

end VIRL4
