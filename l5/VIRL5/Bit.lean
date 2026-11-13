/-
  O95 layer L5, Lean arm (amend-24 LV7, STATUS 317; DECLARATIONS-LEAN Addendum 4): `bitR : (int × (int × int)) →[1]
  (int × (int × int))`, (by, bi, k): the k bits of the one lent byte region starting at bit bi of byte by, least significant first
  (RFC 1951's bit order), returned with the cursor k bits on; the region handed back unchanged. Each bit is DEFLATE's arithmetic
  `bitAt` (Bits.lean), computed by a call of DEFLATE's own closed `BITc` atom through the embedding (Embed5.lean), so `bit_steps` is
  REUSED, not re-proved. No bit TABLE is read: a table read would need a premise on the table's contents (LV7's falsifying shape, D7).
  The cursor is (byte, bit), as DEFLATE keeps it (cBY, cBI): no division in the code, constant work per bit. The value is stated as
  a function of pos = 8·by + bi (`bitsF`), so the division lives in the specification only.
  Precondition: the region, its size, 0 ≤ by, 0 ≤ bi ≤ 7, 8·by + bi + k ≤ 8 · size; NO premise on the contents (LV7).
  (The first form, (pos_bit, k) with a linear `div8`, is vir 5e2782a; Addendum 4 says why it was replaced.)
-/
import VIRL5.Embed5
import VIRL5.RoutineTypes

namespace VIRL5
open VIRL1 VIRL2

/-- A cursor (by, bi), and bitR's argument (by, (bi, k)) and result (value, (by′, bi′)). -/
def τcur : Ty₅ := .prod t5int t5int
def τbit : Ty₅ := .prod t5int τcur

/-- The body, under c = #0, x = (by, (bi, k)) = #1, f = #2. -/
def bitBody : Tm₅ :=
  .ite (.prim .le [.snd (.snd (.var 1)), .const (.int 0)])
    (.retK (.pair (.const (.int 0)) (.pair (.fst (.var 1)) (.fst (.snd (.var 1))))) [.var 0])
    (.letOp .load [.var 0, .fst (.var 1)] t5int                                              -- y #0, c #1, x #2, f #3
      (.letE t5int (.letE t5int (.app (ιA VIRDeflate.Step.BITc) (.pair (.var 0) (.fst (.snd (.var 2))))) (.ret (.var 0)))
        (.letE τcur                                                                          -- b #0, y #1, c #2, x #3, f #4
          (.ite (.prim .eq [.fst (.snd (.var 3)), .const (.int 7)])
            (.ret (.pair (.prim .add [.fst (.var 3), .const (.int 1)]) (.const (.int 0))))
            (.ret (.pair (.fst (.var 3)) (.prim .add [.fst (.snd (.var 3)), .const (.int 1)]))))
          (.letK τbit 1                                                                      -- nb #0, b #1, y #2, c #3, x #4, f #5
            (.appK (.var 5) (.pair (.fst (.var 0)) (.pair (.snd (.var 0)) (.prim .sub [.snd (.snd (.var 4)), .const (.int 1)])))
              [.var 3])
            (.retK (.pair (.prim .add [.var 3, .prim .mul [.const (.int 2), .fst (.var 1)]]) (.snd (.var 1)))  -- c' #0, r #1
              [.var 0])))))

def bitR : Atom₅ := .fix τbit 1 τbit bitBody

/-- What `bitR` returns: the len bits from bit position pos of the region at p (contents f), least significant first. -/
def bitsF (f : Int → Int) (p : Int) : Int → Nat → Int
  | _, 0 => 0
  | pos, m + 1 => VIRDeflate.bitAt (f (p + pos / 8)) (pos % 8).toNat + 2 * bitsF f p (pos + 1) m

/-- The cursor at bit position pos. -/
def curA (pos : Int) : Atom₅ := .pair (.const (.int (pos / 8))) (.const (.int (pos % 8)))

/-- **bitR's triple**: the region handed back unchanged, the result (bitsF f p pos len, the cursor at pos + len), where
  pos = 8·by + bi; no premise on f. -/
theorem bitR_spec (p : Int) (n : Nat) (f : Int → Int) : ∀ (len : Nat) (by_ bi k : Int),
    k = len → 0 ≤ by_ → 0 ≤ bi → bi ≤ 7 → 8 * by_ + bi + len ≤ 8 * n →
    Triple₅ (RegionAt p n f)
      (.appK bitR (.pair (.const (.int by_)) (.pair (.const (.int bi)) (.const (.int k)))) [.const (.cap p)])
      (fun r qs σ => r = .pair (.const (.int (bitsF f p (8 * by_ + bi) len))) (curA (8 * by_ + bi + len)) ∧
        qs = [.const (.cap p)] ∧ RegionAt p n f σ)
  | 0, by_, bi, k, hk, h0, hb0, hb7, hn => by
      subst hk
      refine appKFix_rule₅ rfl rfl rfl rfl ?_
      simp [Tm₅.substAll, bitBody, Tm₅.subst, Atom₅.subst, Atom₅.substL]
      refine ite_rule₅ (b := true) ?_ ?_
      · simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1]
      simp only [if_true]
      refine conseq₅ (fun σ h => ⟨rfl, rfl, h⟩) (fun r qs σ h => ?_)
        (retK_rule₅ (Q := fun r qs σ => r = .pair (.const (.int 0)) (.pair (.const (.int by_)) (.const (.int bi))) ∧
          qs = [.const (.cap p)] ∧ RegionAt p n f σ) (by simp [Atom₅.eval]) rfl)
      obtain ⟨rfl, rfl, hσ⟩ := h
      refine ⟨?_, rfl, hσ⟩
      simp only [bitsF, curA]
      rw [show (8 * by_ + bi) / 8 = by_ by omega, show (8 * by_ + bi) % 8 = bi by omega]
  | m + 1, by_, bi, k, hk, h0, hb0, hb7, hn => by
      have hi' : ((bi.toNat : Nat) : Int) = bi := Int.toNat_of_nonneg hb0
      have hq : (8 * by_ + bi) / 8 = by_ := by omega
      have hr : (8 * by_ + bi) % 8 = bi := by omega
      refine appKFix_rule₅ rfl rfl rfl rfl ?_
      simp [Tm₅.substAll, bitBody, Tm₅.subst, Atom₅.subst, Atom₅.substL]
      refine ite_rule₅ (b := false) ?_ ?_
      · simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1]
        omega
      simp only [Bool.false_eq_true, if_false]
      -- y = the byte at by
      refine letOp_rule₅ (cs := [.cap p, .int by_]) (by simp [Atom₅.evalL, Atom₅.eval])
        (load_at p n f by_ ⟨h0, by push_cast at hn; omega⟩) (fun w => ?_)
      show Triple₅ (fun σ => w = .const (.int (f (p + by_))) ∧ RegionAt p n f σ) _ _
      refine pre_pure₅ (fun hw => ?_)
      subst hw
      simp [Tm₅.subst, Atom₅.subst, Atom₅.substL, ιA]
      -- b = bitAt y bi, by DEFLATE's BITc through the embedding
      have hb := embed_rule₅ (P := RegionAt p n f)
        (t := .letE tint (.app VIRDeflate.Step.BITc (.pair (.const (.int (f (p + by_))))
          (.fst (.snd (.pair (.const (.int by_)) (.pair (.const (.int bi)) (.const (.int k)))))))) (.ret (.var 0)))
        (w := .const (.int (VIRDeflate.bitAt (f (p + by_)) bi.toNat))) rfl (fun σ => by
          have h := VIRDeflate.Step.bit_steps (f (p + by_)) bi.toNat (by omega)
            (.pair (.const (.int (f (p + by_)))) (.fst (.snd (.pair (.const (.int by_)) (.pair (.const (.int bi))
              (.const (.int k)))))))
            (by simp [Atom.eval, hi']) tint (.ret (.var 0)) σ
          simpa [Tm.subst, Atom.subst] using h)
      refine letE_rule₅ (Q := fun r qs σ =>
          (r = .const (.int (VIRDeflate.bitAt (f (p + by_)) bi.toNat)) ∧ qs = []) ∧ RegionAt p n f σ)
        (conseq₅ (fun σ h => h) (fun r qs σ h => ⟨⟨h.1, h.2.1⟩, h.2.2⟩) hb) (fun _ _ _ h => h.1.2) (fun v => ?_)
      refine pre_pure₅ (fun hv => ?_)
      obtain ⟨rfl, -⟩ := hv
      simp [Tm₅.subst, Atom₅.subst, Atom₅.substL, ιA]
      -- the next cursor (by′, bi′), one bit on
      obtain ⟨by', bi', hb0', hb7', hpos, hstep⟩ : ∃ by' bi' : Int, 0 ≤ bi' ∧ bi' ≤ 7 ∧ 8 * by' + bi' = 8 * by_ + bi + 1 ∧
          ∀ (P : Assn) (aby abi : Atom₅), aby.eval = some (.const (.int by_)) → abi.eval = some (.const (.int bi)) →
            Triple₅ P (.ite (.prim .eq [abi, .const (.int 7)])
              (.ret (.pair (.prim .add [aby, .const (.int 1)]) (.const (.int 0))))
              (.ret (.pair aby (.prim .add [abi, .const (.int 1)]))))
            (fun r qs σ => (r = .pair (.const (.int by')) (.const (.int bi')) ∧ qs = []) ∧ P σ) := by
        by_cases h7 : bi = 7
        · refine ⟨by_ + 1, 0, le_refl _, by norm_num, by omega, fun P aby abi hby hbi => ?_⟩
          refine ite_rule₅ (b := true) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp,
            Const.ofL1, hbi, h7]) ?_
          exact conseq₅ (fun σ h => ⟨⟨rfl, rfl⟩, h⟩) (fun r qs σ h => h)
            (ret_rule₅ (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1, hby, hbi]))
        · refine ⟨by_, bi + 1, by omega, by omega, by omega, fun P aby abi hby hbi => ?_⟩
          refine ite_rule₅ (b := false) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp,
            Const.ofL1, hbi, h7]) ?_
          exact conseq₅ (fun σ h => ⟨⟨rfl, rfl⟩, h⟩) (fun r qs σ h => h)
            (ret_rule₅ (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1, hby, hbi]))
      refine letE_rule₅ (hstep (RegionAt p n f) _ _ (by simp [Atom₅.eval]) (by simp [Atom₅.eval])) (fun _ _ _ h => h.1.2)
        (fun v => ?_)
      refine pre_pure₅ (fun hv => ?_)
      obtain ⟨rfl, -⟩ := hv
      simp [Tm₅.subst, Atom₅.subst, Atom₅.substL, ιA]
      -- (r, c') ⇐ bitR (by′, bi′, k − 1) [c]
      have ih := bitR_spec p n f m by' bi' (k - 1) (by push_cast at hk; omega) (by omega) hb0' hb7'
        (by push_cast at hn ⊢; omega)
      have ih' := pure_step_rev₅ (fun σ => Step₅.appKFix rfl rfl rfl rfl) ih
      refine letK_rule₅ (Q := fun r qs σ => r = .pair (.const (.int (bitsF f p (8 * by_ + bi + 1) m)))
          (curA (8 * by_ + bi + 1 + m)) ∧ qs = [.const (.cap p)] ∧ RegionAt p n f σ)
        (conseq₅ (fun σ h => h) (fun r qs σ h => by rw [hpos] at h; exact h) (appKFix_rule₅ rfl ?_ rfl rfl ih'))
        (fun v qs σ h => by rw [h.2.1]; rfl) (fun v qs _ => ?_)
      · simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1]
      refine pre_pure₅ (fun hv => ?_)
      subst hv
      refine pre_pure₅ (fun hq' => ?_)
      subst hq'
      simp [Tm₅.substAll, Tm₅.subst, Atom₅.subst, Atom₅.substL, ιA, curA]
      refine conseq₅ (fun σ h => ⟨rfl, rfl, h⟩) (fun r qs σ h => ?_)
        (retK_rule₅ (Q := fun r qs σ => r = .pair (.const (.int (VIRDeflate.bitAt (f (p + by_)) bi.toNat +
            2 * bitsF f p (8 * by_ + bi + 1) m))) (curA (8 * by_ + bi + 1 + m)) ∧ qs = [.const (.cap p)] ∧ RegionAt p n f σ)
          (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1, curA]) rfl)
      obtain ⟨rfl, rfl, hσ⟩ := h
      refine ⟨?_, rfl, hσ⟩
      simp only [bitsF, hq, hr]
      rw [show 8 * by_ + bi + ((m : Int) + 1) = 8 * by_ + bi + 1 + m by ring]
      rfl

theorem bitR_typed : HasTypeA₅ [] bitR (.arr τbit 1 τbit) := by
  refine .fix (Δ₀ := [false, false]) rfl rfl mask_ff rfl ?_
  refine .ite (.prim (.cons (.snd (.snd (.var rfl rfl))) (.cons .int .nil))) ?_ ?_
  · exact .retK (ns := [0]) rfl (.pair .int (.pair (.fst (.var rfl rfl)) (.fst (.snd (.var rfl rfl)))))
      (caps0 rfl (fun n => by rcases n with _ | _ | _ | n <;> simp))
  · refine .load (n := 0) rfl rfl (.fst (.var rfl rfl)) ?_
    -- Δ = [y, c, x, f] = [false, true, false, false]
    refine .letE (Δ₁ := [false, false, false, false]) (Δ₂ := [false, true, false, false])
      (Split.none (Split.right (Split.none (Split.none Split.nil)))) (.inr rfl) ?_ ?_
    · refine .letE (Δ₁ := [false, false, false, false]) (Δ₂ := [false, false, false, false])
        (Split.none (Split.none (Split.none (Split.none Split.nil)))) (.inr rfl)
        (.app (fun n => by rcases n with _ | _ | _ | _ | n <;> simp)
          (closedA₅ _ (typeA_ι VIRDeflate.Step.BITc_typed)) (.pair (.var rfl rfl) (.fst (.snd (.var rfl rfl))))) ?_
      exact .ret (fun n => by rcases n with _ | _ | _ | _ | _ | n <;> simp [t5int, t5cap]) (.var rfl rfl)
    -- Δ = [b, y, c, x, f] = [false, false, true, false, false]
    refine .letE (Δ₁ := [false, false, false, false, false]) (Δ₂ := [false, false, true, false, false])
      (Split.none (Split.none (Split.right (Split.none (Split.none Split.nil))))) (.inr rfl) ?_ ?_
    · refine .ite (.prim (.cons (.fst (.snd (.var rfl rfl))) (.cons .int .nil))) ?_ ?_
      · exact .ret (fun n => by rcases n with _ | _ | _ | _ | _ | n <;> simp)
          (.pair (.prim (.cons (.fst (.var rfl rfl)) (.cons .int .nil))) .int)
      · exact .ret (fun n => by rcases n with _ | _ | _ | _ | _ | n <;> simp)
          (.pair (.fst (.var rfl rfl)) (.prim (.cons (.fst (.snd (.var rfl rfl))) (.cons .int .nil))))
    -- Δ = [nb, b, y, c, x, f] = [false, false, false, true, false, false]
    refine .letK (Δ₁ := [false, false, false, true, false, false]) (Δ₂ := [false, false, false, false, false, false])
      (Split.none (Split.none (Split.none (Split.left (Split.none (Split.none Split.nil)))))) rfl ?_ ?_
    · exact .appK (ns := [3]) (.var rfl rfl)
        (.pair (.fst (.var rfl rfl)) (.pair (.snd (.var rfl rfl)) (.prim (.cons (.snd (.snd (.var rfl rfl))) (.cons .int .nil)))))
        ⟨by simp, by simp, fun n => by rcases n with _ | _ | _ | _ | _ | _ | _ | n <;> simp⟩
    · exact .retK (ns := [0]) rfl
        (.pair (.prim (.cons (.var rfl rfl) (.cons (.prim (.cons .int (.cons (.fst (.var rfl rfl)) .nil))) .nil)))
          (.snd (.var rfl rfl)))
        (caps0 rfl (fun n => by rcases n with _ | _ | _ | _ | _ | _ | _ | _ | _ | n <;> simp))

end VIRL5
