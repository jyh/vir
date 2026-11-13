/-
  O95 layer L5, Lean arm (amend-24 LV7, STATUS 317): `bitR : (int × int) →[1] (int × int)`, (pos, k): the k bits of the one lent
  byte region starting at BIT position pos, least significant first (RFC 1951's bit order), returned with the next position
  pos + k; the region handed back unchanged. Each bit is DEFLATE's arithmetic `bitAt` (Bits.lean), computed by a call of
  DEFLATE's own closed `BITc` atom through the embedding (Embed5.lean), so `bit_steps` is REUSED, not re-proved. No bit TABLE
  is read: a table read would need a premise on the table's contents (LV7's falsifying shape, D7).
  The byte index and bit offset are pos / 8 and pos % 8, by a pure k = 0 helper `div8` (sub and lt only).
  Precondition: the region, its size, 0 ≤ pos, pos + k ≤ 8 · size; NO premise on the contents (LV7).
-/
import VIRL5.Embed5
import VIRL5.RoutineTypes

namespace VIRL5
open VIRL1 VIRL2

/-- (pos, k) in; (value, pos + k) out; and (q, r) for the helper. -/
def τbit : Ty₅ := .prod t5int t5int

/-! ## `div8`: x ↦ (x / 8, x % 8), for x ≥ 0, by repeated subtraction (x = #0, self = #1) -/

def div8Body : Tm₅ :=
  .ite (.prim .lt [.var 0, .const (.int 8)])
    (.ret (.pair (.const (.int 0)) (.var 0)))
    (.letE τbit (.app (.var 1) (.prim .sub [.var 0, .const (.int 8)]))
      (.ret (.pair (.prim .add [.fst (.var 0), .const (.int 1)]) (.snd (.var 0)))))

def div8 : Atom₅ := .fix t5int 0 τbit div8Body

@[simp] theorem div8_subst (k : Nat) (v : Atom₅) : div8.subst k v = div8 := by
  simp [div8, div8Body, Atom₅.subst, Tm₅.subst, Atom₅.substL]

theorem div8_step (P : Assn) (x : Int) (a : Atom₅) (ha : a.eval = some (.const (.int x))) (h0 : 0 ≤ x)
    (hrec : 8 ≤ x → ∀ a' : Atom₅, a'.eval = some (.const (.int (x - 8))) →
      Triple₅ P (.app div8 a')
        (fun r qs σ => (r = .pair (.const (.int ((x - 8) / 8))) (.const (.int ((x - 8) % 8))) ∧ qs = []) ∧ P σ)) :
    Triple₅ P (.app div8 a)
      (fun r qs σ => (r = .pair (.const (.int (x / 8))) (.const (.int (x % 8))) ∧ qs = []) ∧ P σ) := by
  refine appFix_rule₅ rfl ha ?_
  simp [div8Body, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  by_cases hx : x < 8
  · refine ite_rule₅ (b := true) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp,
      Const.ofL1, hx]) ?_
    simp only [if_true]
    refine conseq₅ (fun σ h => ⟨⟨?_, rfl⟩, h⟩) (fun r qs σ h => h)
      (ret_rule₅ (v := .pair (.const (.int 0)) (.const (.int x))) (by simp [Atom₅.eval]))
    rw [show x / 8 = 0 by omega, show x % 8 = x by omega]
  · refine ite_rule₅ (b := false) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp,
      Const.ofL1, hx]) ?_
    simp only [Bool.false_eq_true, if_false]
    refine letE_rule₅ (hrec (by omega) _ (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp,
      Const.ofL1])) (fun _ _ _ h => h.1.2) (fun v => ?_)
    refine pre_pure₅ (fun hv => ?_)
    obtain ⟨rfl, -⟩ := hv
    simp only [Tm₅.subst, Atom₅.subst, Atom₅.substL]
    refine conseq₅ (fun σ h => ⟨⟨?_, rfl⟩, h⟩) (fun r qs σ h => h)
      (ret_rule₅ (v := .pair (.const (.int ((x - 8) / 8 + 1))) (.const (.int ((x - 8) % 8))))
        (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1]))
    rw [show (x - 8) / 8 + 1 = x / 8 by omega, show (x - 8) % 8 = x % 8 by omega]

/-- **div8's triple**, for any precondition (it touches no store). -/
theorem div8_spec (P : Assn) : ∀ (m : Nat) (x : Int) (a : Atom₅), a.eval = some (.const (.int x)) → 0 ≤ x →
    x < 8 * ((m : Int) + 1) →
    Triple₅ P (.app div8 a)
      (fun r qs σ => (r = .pair (.const (.int (x / 8))) (.const (.int (x % 8))) ∧ qs = []) ∧ P σ)
  | 0, x, a, ha, h0, hm => div8_step P x a ha h0 (fun h8 => absurd h8 (by push_cast at hm; omega))
  | m + 1, x, a, ha, h0, hm => div8_step P x a ha h0 (fun h8 a' ha' =>
      div8_spec P m (x - 8) a' ha' (by omega) (by push_cast at hm ⊢; omega))

theorem div8_typed : HasTypeA₅ [] div8 (.arr t5int 0 τbit) := by
  refine .fix (Δ₀ := [false, false]) rfl rfl mask_ff rfl ?_
  refine .ite (.prim (.cons (.var rfl rfl) (.cons .int .nil))) ?_ ?_
  · exact .ret mask_ff (.pair .int (.var rfl rfl))
  · refine .letE (Split.none (Split.none Split.nil)) (.inr rfl)
      (.app mask_ff (.var rfl rfl) (.prim (.cons (.var rfl rfl) (.cons .int .nil)))) ?_
    exact .ret mask_fff (.pair (.prim (.cons (.fst (.var rfl rfl)) (.cons .int .nil))) (.snd (.var rfl rfl)))

/-! ## `bitR` (c = #0, x = (pos, k) = #1, f = #2) -/

def bitBody : Tm₅ :=
  .ite (.prim .le [.snd (.var 1), .const (.int 0)])
    (.retK (.pair (.const (.int 0)) (.fst (.var 1))) [.var 0])
    (.letE τbit (.app div8 (.fst (.var 1)))                                                -- d #0, c #1, x #2, f #3
      (.letOp .load [.var 1, .fst (.var 0)] t5int                                          -- y #0, d #1, c #2, x #3, f #4
        (.letE t5int (.letE t5int (.app (ιA VIRDeflate.Step.BITc) (.pair (.var 0) (.snd (.var 1)))) (.ret (.var 0)))
          (.letK τbit 1                                                                    -- b #0, y #1, d #2, c #3, x #4, f #5
            (.appK (.var 5) (.pair (.prim .add [.fst (.var 4), .const (.int 1)]) (.prim .sub [.snd (.var 4), .const (.int 1)]))
              [.var 3])
            (.retK (.pair (.prim .add [.var 2, .prim .mul [.const (.int 2), .fst (.var 1)]]) (.snd (.var 1)))  -- c' #0, r #1
              [.var 0])))))

def bitR : Atom₅ := .fix τbit 1 τbit bitBody

/-- What `bitR` returns: the len bits from bit position pos of the region at p (contents f), least significant first. -/
def bitsF (f : Int → Int) (p : Int) : Int → Nat → Int
  | _, 0 => 0
  | pos, m + 1 => VIRDeflate.bitAt (f (p + pos / 8)) (pos % 8).toNat + 2 * bitsF f p (pos + 1) m

/-- **bitR's triple**: the region handed back unchanged, the result (bitsF f p pos len, pos + len); no premise on f. -/
theorem bitR_spec (p : Int) (n : Nat) (f : Int → Int) : ∀ (len : Nat) (pos k : Int),
    k = len → 0 ≤ pos → pos + len ≤ 8 * n →
    Triple₅ (RegionAt p n f) (.appK bitR (.pair (.const (.int pos)) (.const (.int k))) [.const (.cap p)])
      (fun r qs σ => r = .pair (.const (.int (bitsF f p pos len))) (.const (.int (pos + len))) ∧
        qs = [.const (.cap p)] ∧ RegionAt p n f σ)
  | 0, pos, k, hk, h0, hn => by
      subst hk
      refine appKFix_rule₅ rfl rfl rfl rfl ?_
      simp [Tm₅.substAll, bitBody, Tm₅.subst, Atom₅.subst, Atom₅.substL]
      refine ite_rule₅ (b := true) ?_ ?_
      · simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1]
      simp only [if_true]
      refine conseq₅ (fun σ h => ⟨rfl, rfl, h⟩) (fun r qs σ h => ?_)
        (retK_rule₅ (Q := fun r qs σ => r = .pair (.const (.int 0)) (.const (.int pos)) ∧ qs = [.const (.cap p)] ∧
          RegionAt p n f σ) (by simp [Atom₅.eval]) rfl)
      obtain ⟨rfl, rfl, hσ⟩ := h
      exact ⟨by simp [bitsF], rfl, hσ⟩
  | m + 1, pos, k, hk, h0, hn => by
      have hi' : (((pos % 8).toNat : Nat) : Int) = pos % 8 := Int.toNat_of_nonneg (Int.emod_nonneg _ (by norm_num))
      refine appKFix_rule₅ rfl rfl rfl rfl ?_
      simp [Tm₅.substAll, bitBody, Tm₅.subst, Atom₅.subst, Atom₅.substL]
      refine ite_rule₅ (b := false) ?_ ?_
      · simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1]
        omega
      simp only [Bool.false_eq_true, if_false]
      -- d = (pos / 8, pos % 8)
      refine letE_rule₅ (div8_spec (RegionAt p n f) n pos _ (by simp [Atom₅.eval]) h0 (by push_cast at hn; omega))
        (fun _ _ _ h => h.1.2) (fun v => ?_)
      refine pre_pure₅ (fun hv => ?_)
      obtain ⟨rfl, -⟩ := hv
      simp only [Tm₅.subst, Atom₅.subst, Atom₅.substL, ιBITc_subst]
      -- y = the byte at pos / 8
      refine letOp_rule₅ (cs := [.cap p, .int (pos / 8)]) (by simp [Atom₅.evalL, Atom₅.eval])
        (load_at p n f (pos / 8) ⟨by omega, by push_cast at hn; omega⟩) (fun w => ?_)
      show Triple₅ (fun σ => w = .const (.int (f (p + pos / 8))) ∧ RegionAt p n f σ) _ _
      refine pre_pure₅ (fun hw => ?_)
      subst hw
      simp only [Tm₅.subst, Atom₅.subst, Atom₅.substL, ιBITc_subst]
      -- b = bitAt y (pos % 8), by DEFLATE's BITc through the embedding
      have hb := embed_rule₅ (P := RegionAt p n f)
        (t := .letE tint (.app VIRDeflate.Step.BITc (.pair (.const (.int (f (p + pos / 8))))
          (.snd (.pair (.const (.int (pos / 8))) (.const (.int (pos % 8))))))) (.ret (.var 0)))
        (w := .const (.int (VIRDeflate.bitAt (f (p + pos / 8)) (pos % 8).toNat))) rfl (fun σ => by
          have h := VIRDeflate.Step.bit_steps (f (p + pos / 8)) (pos % 8).toNat (by omega)
            (.pair (.const (.int (f (p + pos / 8)))) (.snd (.pair (.const (.int (pos / 8))) (.const (.int (pos % 8))))))
            (by simp [Atom.eval, hi']) tint (.ret (.var 0)) σ
          simpa [Tm.subst, Atom.subst] using h)
      refine letE_rule₅ (Q := fun r qs σ =>
          (r = .const (.int (VIRDeflate.bitAt (f (p + pos / 8)) (pos % 8).toNat)) ∧ qs = []) ∧ RegionAt p n f σ)
        (conseq₅ (fun σ h => h) (fun r qs σ h => ⟨⟨h.1, h.2.1⟩, h.2.2⟩) hb) (fun _ _ _ h => h.1.2) (fun v => ?_)
      refine pre_pure₅ (fun hv => ?_)
      obtain ⟨rfl, -⟩ := hv
      simp only [Tm₅.subst, Atom₅.subst, Atom₅.substL]
      -- (r, c') ⇐ bitR (pos + 1, k − 1) [c]
      have ih := bitR_spec p n f m (pos + 1) (k - 1) (by push_cast at hk; omega) (by omega) (by push_cast at hn ⊢; omega)
      have ih' := pure_step_rev₅ (fun σ => Step₅.appKFix rfl rfl rfl rfl) ih
      refine letK_rule₅ (appKFix_rule₅ rfl ?_ rfl rfl ih') (fun v qs σ h => by rw [h.2.1]; rfl) (fun v qs _ => ?_)
      · simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1]
      refine pre_pure₅ (fun hv => ?_)
      subst hv
      refine pre_pure₅ (fun hq => ?_)
      subst hq
      simp [Tm₅.substAll, Tm₅.subst, Atom₅.subst, Atom₅.substL, ιA]
      refine conseq₅ (fun σ h => ⟨rfl, rfl, h⟩) (fun r qs σ h => ?_)
        (retK_rule₅ (Q := fun r qs σ => r = .pair (.const (.int (VIRDeflate.bitAt (f (p + pos / 8)) (pos % 8).toNat +
            2 * bitsF f p (pos + 1) m))) (.const (.int (pos + 1 + m))) ∧ qs = [.const (.cap p)] ∧ RegionAt p n f σ)
          (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1, Atom₅.subst, ιA]) rfl)
      obtain ⟨rfl, rfl, hσ⟩ := h
      refine ⟨?_, rfl, hσ⟩
      rw [show pos + ((m : Int) + 1) = pos + 1 + m by ring]
      rfl

theorem bitR_typed : HasTypeA₅ [] bitR (.arr τbit 1 τbit) := by
  refine .fix (Δ₀ := [false, false]) rfl rfl mask_ff rfl ?_
  refine .ite (.prim (.cons (.snd (.var rfl rfl)) (.cons .int .nil))) ?_ ?_
  · exact .retK (ns := [0]) rfl (.pair .int (.fst (.var rfl rfl))) (caps0 rfl (fun n => by rcases n with _ | _ | _ | n <;> simp))
  · refine .letE (Δ₁ := [false, false, false]) (Δ₂ := [true, false, false])
      (Split.right (Split.none (Split.none Split.nil))) (.inr rfl)
      (.app mask_fff (closedA₅ _ div8_typed) (.fst (.var rfl rfl))) ?_
    refine .load (n := 1) rfl rfl (.fst (.var rfl rfl)) ?_
    refine .letE (Δ₁ := [false, false, false, false, false]) (Δ₂ := [false, false, true, false, false])
      (Split.none (Split.none (Split.right (Split.none (Split.none Split.nil))))) (.inr rfl) ?_ ?_
    · refine .letE (Δ₁ := [false, false, false, false, false]) (Δ₂ := [false, false, false, false, false])
        (Split.none (Split.none (Split.none (Split.none (Split.none Split.nil))))) (.inr rfl)
        (.app (fun n => by rcases n with _ | _ | _ | _ | _ | n <;> simp)
          (closedA₅ _ (typeA_ι VIRDeflate.Step.BITc_typed)) (.pair (.var rfl rfl) (.snd (.var rfl rfl)))) ?_
      exact .ret (fun n => by rcases n with _ | _ | _ | _ | _ | _ | n <;> simp [t5int, t5cap]) (.var rfl rfl)
    · refine .letK (Δ₁ := [false, false, false, true, false, false]) (Δ₂ := [false, false, false, false, false, false])
        (Split.none (Split.none (Split.none (Split.left (Split.none (Split.none Split.nil)))))) rfl ?_ ?_
      · exact .appK (ns := [3]) (.var rfl rfl)
          (.pair (.prim (.cons (.fst (.var rfl rfl)) (.cons .int .nil))) (.prim (.cons (.snd (.var rfl rfl)) (.cons .int .nil))))
          ⟨by simp, by simp, fun n => by rcases n with _ | _ | _ | _ | _ | _ | _ | n <;> simp⟩
      · exact .retK (ns := [0]) rfl
          (.pair (.prim (.cons (.var rfl rfl) (.cons (.prim (.cons .int (.cons (.fst (.var rfl rfl)) .nil))) .nil)))
            (.snd (.var rfl rfl)))
          (caps0 rfl (fun n => by rcases n with _ | _ | _ | _ | _ | _ | _ | _ | _ | n <;> simp))

end VIRL5
