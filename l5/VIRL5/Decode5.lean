/-
  O95 layer L5, Lean arm (STATUS 320, LV8 Deflate5; LV8-MAP: DECODE → bitR, C = 1). DEFLATE's DECODE takes ONE bit per step from
  the TABLE and tests it against the flat code table TB(TGT) (Step.lean `decodeN`). The L5 mode takes the same bit from `bitR` on
  the cursor (IN + by, bi, 1), exactly as READ does (Read5.lean), and the code test stays hand-written (LV8-MAP: data-dependent,
  per bit). The three outcomes are DEFLATE's, store for store: a hit writes the cursor, sym at X+4 and MODE := RET; a miss at
  ℓ = 15 is REASON := INVCODE, MODE := REJECT with the cursor unmoved; otherwise the cursor, ℓ + 1 and v'. The by ≥ n branch is
  DEFLATE's TRUNC reject. The triples are over RegionAt; the premises are the counters' values and the bounds that keep each
  load and store inside the region, as DEFLATE's own `decode_step` takes them.
-/
import VIRL5.Read5

namespace VIRL5
open VIRL1 VIRL2 VIRDeflate.Step

/-- DECODE over ⟶₅, with the world at #0. The bit comes from `bitR` on the cursor (IN + by, bi, 1); TABLE is not read.
  The table base is tb = IN + n + om + 337 + 352·t, written in place at each load (Tm₅ has no pure let). -/
def decodeT₅ : Tm₅ :=
  .letOp .load [.var 0, .const (.int cBY)] t5int                                    -- by w
  (.letOp .load [.var 1, .const (.int cBI)] t5int                                   -- bi by w
    (.letOp .load [.var 2, .const (.int cN)] t5int                                  -- n bi by w
      (.letOp .load [.var 3, .const (.int cOUTMAX)] t5int                           -- om n bi by w
        (.letOp .load [.var 4, .const (.int cX)] t5int                              -- x om n bi by w
          (.ite (.prim .lt [.var 4, .var 2])
            (.letK τbit 1                                                           -- w1 r x om n bi by w
              (.appK bitR (.pair (.prim .add [.const (.int IN), .var 4]) (.pair (.var 3) (.const (.int 1)))) [.var 5])
              (.letOp .load [.var 0, .var 2] t5int                                  -- l w1 r x om n
                (.letOp .load [.var 1, .prim .add [.var 3, .const (.int 1)]] t5int  -- cv l w1 r x om n
                  (.letOp .load [.var 2, .prim .add [.var 4, .const (.int 2)]] t5int  -- t cv l w1 r x om n
                    (.letOp .load [.var 3, .prim .add [.var 5, .const (.int 3)]] t5int  -- rt t cv l w1 r x om n
                      (.letOp .load [.var 4, .prim .add [.prim .add [.prim .add [.prim .add [.prim .add [.prim .add
                          [.const (.int IN), .var 8], .var 7], .const (.int 337)], .prim .mul [.const (.int 352), .var 1]],
                          .const (.int 16)], .var 3]] t5int                         -- fs rt t cv l w1 r x om n
                        (.letOp .load [.var 5, .prim .add [.prim .add [.prim .add [.prim .add [.prim .add
                            [.const (.int IN), .var 9], .var 8], .const (.int 337)], .prim .mul [.const (.int 352), .var 2]],
                            .var 4]] t5int                                          -- c fs rt t cv l w1 r x om n
                          (.ite (.prim .and [.prim .le [.var 1, .prim .add [.prim .mul [.const (.int 2), .var 4], .fst (.var 7)]],
                                             .prim .lt [.prim .add [.prim .mul [.const (.int 2), .var 4], .fst (.var 7)],
                                                        .prim .add [.var 1, .var 0]]])
                            (.letOp .load [.var 6, .prim .add [.prim .add [.prim .add [.prim .add [.prim .add [.prim .add
                                [.const (.int IN), .var 10], .var 9], .const (.int 337)], .prim .mul [.const (.int 352), .var 3]],
                                .const (.int 32)], .var 5]] t5int                   -- o c fs rt t cv l w1 r x om n
                              (.letOp .load [.var 7, .prim .add [.prim .add [.prim .add [.prim .add [.prim .add [.prim .add
                                  [.prim .add [.const (.int IN), .var 11], .var 10], .const (.int 337)],
                                  .prim .mul [.const (.int 352), .var 4]], .const (.int 64)], .var 0],
                                  .prim .sub [.prim .add [.prim .mul [.const (.int 2), .var 5], .fst (.var 8)], .var 2]]] t5int
                                                                                    -- sy o c fs rt t cv l w1 r x
                                (.letOp .store [.var 8, .const (.int cBY), .prim .sub [.fst (.snd (.var 9)), .const (.int IN)]] t5cap
                                                                                    -- wa sy o c fs rt t cv l w1 r x
                                  (.letOp .store [.var 0, .const (.int cBI), .snd (.snd (.var 10))] t5cap
                                                                                    -- wb wa sy o c fs rt t cv l w1 r x
                                    (.letOp .store [.var 0, .prim .add [.var 12, .const (.int 4)], .var 2] t5cap
                                                                                    -- wc wb wa sy o c fs rt
                                      (.letOp .store [.var 0, .const (.int cMODE), .var 7] t5cap (.ret (.var 0))))))))
                            (.ite (.prim .eq [.var 5, .const (.int 15)])
                              (.letOp .store [.var 6, .const (.int cREASON), .const (.int rINVCODE)] t5cap
                                (.letOp .store [.var 0, .const (.int cMODE), .const (.int mREJECT)] t5cap (.ret (.var 0))))
                              (.letOp .store [.var 6, .const (.int cBY), .prim .sub [.fst (.snd (.var 7)), .const (.int IN)]] t5cap
                                                                                    -- wa c fs rt t cv l w1 r x
                                (.letOp .store [.var 0, .const (.int cBI), .snd (.snd (.var 8))] t5cap
                                                                                    -- wb wa c fs rt t cv l w1 r x
                                  (.letOp .store [.var 0, .var 10, .prim .add [.var 7, .const (.int 1)]] t5cap
                                                                                    -- wc wb wa c fs rt t cv l w1 r x
                                    (.letOp .store [.var 0, .prim .add [.var 11, .const (.int 1)],
                                        .prim .add [.prim .mul [.const (.int 2), .var 7], .fst (.var 10)]] t5cap
                                      (.ret (.var 0)))))))))))))))
            (.letOp .store [.var 5, .const (.int cREASON), .const (.int rTRUNC)] t5cap
              (.letOp .store [.var 0, .const (.int cMODE), .const (.int mREJECT)] t5cap (.ret (.var 0)))))))))

/-- The contents after one DECODE bit (by < n), by outcome, as DEFLATE's `decH`: v2 = 2·cv + the bit bitR returns. -/
def decPost (p : Int) (g : Int → Int) (bx bi X l rt fs c v2 sy : Int) : Int → Int :=
  if fs ≤ v2 ∧ v2 < fs + c then
    Function.update (Function.update (Function.update (Function.update g
      (p + cBY) (((8 * (IN + bx) + bi) + 1) / 8 - IN)) (p + cBI) (((8 * (IN + bx) + bi) + 1) % 8))
      (p + (X + 4)) sy) (p + cMODE) rt
  else if l = 15 then Function.update (Function.update g (p + cREASON) rINVCODE) (p + cMODE) mREJECT
  else
    Function.update (Function.update (Function.update (Function.update g
      (p + cBY) (((8 * (IN + bx) + bi) + 1) / 8 - IN)) (p + cBI) (((8 * (IN + bx) + bi) + 1) % 8))
      (p + X) (l + 1)) (p + (X + 1)) v2

set_option maxHeartbeats 4000000 in
/-- **DECODE, one bit (by < n).** The symbol cell is read only on a hit, so its bound is premised only there. -/
theorem decode5_bit (p : Int) (L : Nat) (g : Int → Int) (bx bi n om X l cv t rt tb fs c o sy : Int)
    (hby : g (p + cBY) = bx) (hbi : g (p + cBI) = bi) (hn : g (p + cN) = n) (hom : g (p + cOUTMAX) = om)
    (hX : g (p + cX) = X)
    (hbx : 0 ≤ bx) (hlt : bx < n) (hbi0 : 0 ≤ bi) (hbi7 : bi ≤ 7) (hL : IN + n ≤ L)
    (hX0 : 0 ≤ X) (hXL : X + 4 < L)
    (hl : g (p + X) = l) (hcv : g (p + (X + 1)) = cv) (ht : g (p + (X + 2)) = t) (hrt : g (p + (X + 3)) = rt)
    (htb : IN + n + om + 337 + 352 * t = tb) (ht0 : 0 ≤ tb) (htL : tb + 352 ≤ L) (hl1 : 1 ≤ l) (hl15 : l ≤ 15)
    (hfs : g (p + (tb + 16 + l)) = fs) (hc : g (p + (tb + l)) = c)
    (ho : fs ≤ 2 * cv + bitsF g p (8 * (IN + bx) + bi) 1 ∧ 2 * cv + bitsF g p (8 * (IN + bx) + bi) 1 < fs + c →
      g (p + (tb + 32 + l)) = o)
    (hsy0 : fs ≤ 2 * cv + bitsF g p (8 * (IN + bx) + bi) 1 ∧ 2 * cv + bitsF g p (8 * (IN + bx) + bi) 1 < fs + c →
      0 ≤ tb + 64 + o + (2 * cv + bitsF g p (8 * (IN + bx) + bi) 1 - fs) ∧
        tb + 64 + o + (2 * cv + bitsF g p (8 * (IN + bx) + bi) 1 - fs) < L)
    (hsy : fs ≤ 2 * cv + bitsF g p (8 * (IN + bx) + bi) 1 ∧ 2 * cv + bitsF g p (8 * (IN + bx) + bi) 1 < fs + c →
      g (p + (tb + 64 + o + (2 * cv + bitsF g p (8 * (IN + bx) + bi) 1 - fs))) = sy) :
    Triple₅ (RegionAt p L g) (decodeT₅.subst 0 (.const (.cap p)))
      (fun r qs σ => r = .const (.cap p) ∧ qs = [] ∧
        RegionAt p L (decPost p g bx bi X l rt fs c (2 * cv + bitsF g p (8 * (IN + bx) + bi) 1) sy) σ) := by
  have hIN : (IN : Int) = 2080 := rfl
  simp [decodeT₅, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  refine letOp_rule₅ (cs := [.cap p, .int (cBY)]) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1])
    (load_at p L _ (cBY) ⟨by unfold cBY; omega, by unfold cBY; omega⟩) (fun w => ?_)
  refine pre_pure₅ (fun hw => ?_)
  subst hw
  rw [hby]
  simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  refine letOp_rule₅ (cs := [.cap p, .int (cBI)]) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1])
    (load_at p L _ (cBI) ⟨by unfold cBI; omega, by unfold cBI; omega⟩) (fun w => ?_)
  refine pre_pure₅ (fun hw => ?_)
  subst hw
  rw [hbi]
  simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  refine letOp_rule₅ (cs := [.cap p, .int (cN)]) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1])
    (load_at p L _ (cN) ⟨by unfold cN; omega, by unfold cN; omega⟩) (fun w => ?_)
  refine pre_pure₅ (fun hw => ?_)
  subst hw
  rw [hn]
  simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  refine letOp_rule₅ (cs := [.cap p, .int (cOUTMAX)]) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1])
    (load_at p L _ (cOUTMAX) ⟨by unfold cOUTMAX; omega, by unfold cOUTMAX; omega⟩) (fun w => ?_)
  refine pre_pure₅ (fun hw => ?_)
  subst hw
  rw [hom]
  simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  refine letOp_rule₅ (cs := [.cap p, .int (cX)]) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1])
    (load_at p L _ (cX) ⟨by unfold cX; omega, by unfold cX; omega⟩) (fun w => ?_)
  refine pre_pure₅ (fun hw => ?_)
  subst hw
  rw [hX]
  simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  refine ite_rule₅ (b := true) ?_ ?_
  · simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1] <;> omega
  simp only [if_true]
  have ih := bitR_spec p L g 1 (IN + bx) bi 1 rfl (by rw [hIN]; omega) hbi0 hbi7 (by rw [hIN]; push_cast; omega)
  have ih' := pure_step_rev₅ (fun σ => Step₅.appKFix rfl rfl rfl rfl) ih
  refine letK_rule₅ (Q := fun r qs σ => r = .pair (.const (.int (bitsF g p (8 * (IN + bx) + bi) 1))) (curA ((8 * (IN + bx) + bi) + 1)) ∧
      qs = [.const (.cap p)] ∧ RegionAt p L g σ)
    ?h1 (fun v qs σ h => by simp [h.2.1]) (fun v qs _ => ?_)
  case h1 =>
    refine appKFix_rule₅ rfl ?_ rfl rfl ih'
    simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1]
  refine pre_pure₅ (fun hv => ?_)
  subst hv
  refine pre_pure₅ (fun hq => ?_)
  subst hq
  simp [Tm₅.substAll, Tm₅.subst, Atom₅.subst, Atom₅.substL, ιA, curA]
  generalize hB : bitsF g p (8 * (IN + bx) + bi) 1 = B at ho hsy0 hsy ⊢
  -- ℓ, v, TGT, RET from the cursor-3 at X
  refine letOp_rule₅ (cs := [.cap p, .int X]) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1])
    (load_at p L _ X ⟨by omega, by omega⟩) (fun w => ?_)
  refine pre_pure₅ (fun hw => ?_)
  subst hw
  rw [hl]
  simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  refine letOp_rule₅ (cs := [.cap p, .int (X + 1)]) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1])
    (load_at p L _ (X + 1) ⟨by omega, by omega⟩) (fun w => ?_)
  refine pre_pure₅ (fun hw => ?_)
  subst hw
  rw [hcv]
  simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  refine letOp_rule₅ (cs := [.cap p, .int (X + 2)]) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1])
    (load_at p L _ (X + 2) ⟨by omega, by omega⟩) (fun w => ?_)
  refine pre_pure₅ (fun hw => ?_)
  subst hw
  rw [ht]
  simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  refine letOp_rule₅ (cs := [.cap p, .int (X + 3)]) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1])
    (load_at p L _ (X + 3) ⟨by omega, by omega⟩) (fun w => ?_)
  refine pre_pure₅ (fun hw => ?_)
  subst hw
  rw [hrt]
  simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  -- first[ℓ] and count[ℓ] in TB(TGT)
  refine letOp_rule₅ (cs := [.cap p, .int (tb + 16 + l)]) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1] <;> omega)
    (load_at p L _ (tb + 16 + l) ⟨by omega, by omega⟩) (fun w => ?_)
  refine pre_pure₅ (fun hw => ?_)
  subst hw
  rw [hfs]
  simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  refine letOp_rule₅ (cs := [.cap p, .int (tb + l)]) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1] <;> omega)
    (load_at p L _ (tb + l) ⟨by omega, by omega⟩) (fun w => ?_)
  refine pre_pure₅ (fun hw => ?_)
  subst hw
  rw [hc]
  simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  by_cases hh : fs ≤ 2 * cv + B ∧ 2 * cv + B < fs + c
  · -- a hit: offs[ℓ], the symbol, the cursor, sym at X+4, MODE := RET
    obtain ⟨hy0, hyL⟩ := hsy0 hh
    have ho' := ho hh
    have hsy' := hsy hh
    obtain ⟨h1, h2⟩ := hh
    refine ite_rule₅ (b := true) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1, h1, h2]) ?_
    simp only [if_true]
    refine letOp_rule₅ (cs := [.cap p, .int (tb + 32 + l)]) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1] <;> omega)
      (load_at p L _ (tb + 32 + l) ⟨by omega, by omega⟩) (fun w => ?_)
    refine pre_pure₅ (fun hw => ?_)
    subst hw
    rw [ho']
    simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
    refine letOp_rule₅ (cs := [.cap p, .int (tb + 64 + o + (2 * cv + B - fs))]) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1] <;> omega)
      (load_at p L _ (tb + 64 + o + (2 * cv + B - fs)) ⟨hy0, hyL⟩) (fun w => ?_)
    refine pre_pure₅ (fun hw => ?_)
    subst hw
    rw [hsy']
    simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
    refine letOp_rule₅ (cs := [.cap p, .int (cBY), .int (((8 * (IN + bx) + bi) + 1) / 8 - IN)]) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1] <;> omega)
      (store_at p L _ (cBY) (((8 * (IN + bx) + bi) + 1) / 8 - IN) ⟨by unfold cBY; omega, by unfold cBY; omega⟩) (fun w => ?_)
    refine pre_pure₅ (fun hw => ?_)
    subst hw
    simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
    refine letOp_rule₅ (cs := [.cap p, .int (cBI), .int (((8 * (IN + bx) + bi) + 1) % 8)]) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1] <;> omega)
      (store_at p L _ (cBI) (((8 * (IN + bx) + bi) + 1) % 8) ⟨by unfold cBI; omega, by unfold cBI; omega⟩) (fun w => ?_)
    refine pre_pure₅ (fun hw => ?_)
    subst hw
    simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
    refine letOp_rule₅ (cs := [.cap p, .int (X + 4), .int sy]) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1] <;> omega)
      (store_at p L _ (X + 4) sy ⟨by omega, by omega⟩) (fun w => ?_)
    refine pre_pure₅ (fun hw => ?_)
    subst hw
    simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
    refine letOp_rule₅ (cs := [.cap p, .int (cMODE), .int rt]) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1] <;> omega)
      (store_at p L _ (cMODE) rt ⟨by unfold cMODE; omega, by unfold cMODE; omega⟩) (fun w => ?_)
    refine pre_pure₅ (fun hw => ?_)
    subst hw
    simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
    exact conseq₅ (fun σ h => ⟨rfl, rfl, by simpa [decPost, h1, h2] using h⟩) (fun r qs σ h => h)
      (ret_rule₅ (v := .const (.cap p))
        (Q := fun r qs σ => r = .const (.cap p) ∧ qs = [] ∧ RegionAt p L (decPost p g bx bi X l rt fs c (2 * cv + B) sy) σ)
        (by simp [Atom₅.eval]))
  · refine ite_rule₅ (b := false) (by
      simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1]
      intro h1; by_contra h2; exact hh ⟨h1, by omega⟩) ?_
    simp only [Bool.false_eq_true, if_false]
    by_cases hl15' : l = 15
    · -- a miss at ℓ = 15: invalid code, the cursor unmoved
      refine ite_rule₅ (b := true) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1, hl15']) ?_
      simp only [if_true]
      refine letOp_rule₅ (cs := [.cap p, .int (cREASON), .int rINVCODE]) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1] <;> omega)
        (store_at p L _ (cREASON) rINVCODE ⟨by unfold cREASON; omega, by unfold cREASON; omega⟩) (fun w => ?_)
      refine pre_pure₅ (fun hw => ?_)
      subst hw
      simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
      refine letOp_rule₅ (cs := [.cap p, .int (cMODE), .int mREJECT]) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1] <;> omega)
        (store_at p L _ (cMODE) mREJECT ⟨by unfold cMODE; omega, by unfold cMODE; omega⟩) (fun w => ?_)
      refine pre_pure₅ (fun hw => ?_)
      subst hw
      simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
      exact conseq₅ (fun σ h => ⟨rfl, rfl, by simpa [decPost, hh, hl15'] using h⟩) (fun r qs σ h => h)
        (ret_rule₅ (v := .const (.cap p))
          (Q := fun r qs σ => r = .const (.cap p) ∧ qs = [] ∧ RegionAt p L (decPost p g bx bi X l rt fs c (2 * cv + B) sy) σ)
          (by simp [Atom₅.eval]))
    · -- a miss below ℓ = 15: the cursor, ℓ + 1, v := v'
      refine ite_rule₅ (b := false) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1, hl15']) ?_
      simp only [Bool.false_eq_true, if_false]
      refine letOp_rule₅ (cs := [.cap p, .int (cBY), .int (((8 * (IN + bx) + bi) + 1) / 8 - IN)]) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1] <;> omega)
        (store_at p L _ (cBY) (((8 * (IN + bx) + bi) + 1) / 8 - IN) ⟨by unfold cBY; omega, by unfold cBY; omega⟩) (fun w => ?_)
      refine pre_pure₅ (fun hw => ?_)
      subst hw
      simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
      refine letOp_rule₅ (cs := [.cap p, .int (cBI), .int (((8 * (IN + bx) + bi) + 1) % 8)]) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1] <;> omega)
        (store_at p L _ (cBI) (((8 * (IN + bx) + bi) + 1) % 8) ⟨by unfold cBI; omega, by unfold cBI; omega⟩) (fun w => ?_)
      refine pre_pure₅ (fun hw => ?_)
      subst hw
      simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
      refine letOp_rule₅ (cs := [.cap p, .int X, .int (l + 1)]) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1] <;> omega)
        (store_at p L _ X (l + 1) ⟨by omega, by omega⟩) (fun w => ?_)
      refine pre_pure₅ (fun hw => ?_)
      subst hw
      simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
      refine letOp_rule₅ (cs := [.cap p, .int (X + 1), .int (2 * cv + B)]) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1] <;> omega)
        (store_at p L _ (X + 1) (2 * cv + B) ⟨by omega, by omega⟩) (fun w => ?_)
      refine pre_pure₅ (fun hw => ?_)
      subst hw
      simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
      exact conseq₅ (fun σ h => ⟨rfl, rfl, by simpa [decPost, hh, hl15'] using h⟩) (fun r qs σ h => h)
        (ret_rule₅ (v := .const (.cap p))
          (Q := fun r qs σ => r = .const (.cap p) ∧ qs = [] ∧ RegionAt p L (decPost p g bx bi X l rt fs c (2 * cv + B) sy) σ)
          (by simp [Atom₅.eval]))

/-- **DECODE, the input exhausted (by ≥ n):** REASON := TRUNC, MODE := REJECT, as DEFLATE's own branch. -/
theorem decode5_trunc (p : Int) (L : Nat) (g : Int → Int) (bx bi n : Int)
    (hby : g (p + cBY) = bx) (hbi : g (p + cBI) = bi) (hn : g (p + cN) = n) (hge : ¬ bx < n) (hL : 2080 ≤ L) :
    Triple₅ (RegionAt p L g) (decodeT₅.subst 0 (.const (.cap p)))
      (fun r qs σ => r = .const (.cap p) ∧ qs = [] ∧
        RegionAt p L (Function.update (Function.update g (p + cREASON) rTRUNC) (p + cMODE) mREJECT) σ) := by
  simp [decodeT₅, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  refine letOp_rule₅ (cs := [.cap p, .int (cBY)]) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1])
    (load_at p L _ (cBY) ⟨by unfold cBY; omega, by unfold cBY; omega⟩) (fun w => ?_)
  refine pre_pure₅ (fun hw => ?_)
  subst hw
  rw [hby]
  simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  refine letOp_rule₅ (cs := [.cap p, .int (cBI)]) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1])
    (load_at p L _ (cBI) ⟨by unfold cBI; omega, by unfold cBI; omega⟩) (fun w => ?_)
  refine pre_pure₅ (fun hw => ?_)
  subst hw
  rw [hbi]
  simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  refine letOp_rule₅ (cs := [.cap p, .int (cN)]) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1])
    (load_at p L _ (cN) ⟨by unfold cN; omega, by unfold cN; omega⟩) (fun w => ?_)
  refine pre_pure₅ (fun hw => ?_)
  subst hw
  rw [hn]
  simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  refine letOp_rule₅ (cs := [.cap p, .int (cOUTMAX)]) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1])
    (load_at p L _ (cOUTMAX) ⟨by unfold cOUTMAX; omega, by unfold cOUTMAX; omega⟩) (fun w => ?_)
  refine pre_pure₅ (fun hw => ?_)
  subst hw
  simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  refine letOp_rule₅ (cs := [.cap p, .int (cX)]) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1])
    (load_at p L _ (cX) ⟨by unfold cX; omega, by unfold cX; omega⟩) (fun w => ?_)
  refine pre_pure₅ (fun hw => ?_)
  subst hw
  simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  refine ite_rule₅ (b := false) ?_ ?_
  · simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1] <;> omega
  simp only [Bool.false_eq_true, if_false]
  refine letOp_rule₅ (cs := [.cap p, .int (cREASON), .int (rTRUNC)]) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1] <;> omega)
    (store_at p L _ (cREASON) (rTRUNC) ⟨by unfold cREASON; omega, by unfold cREASON; omega⟩) (fun w => ?_)
  refine pre_pure₅ (fun hw => ?_)
  subst hw
  simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  refine letOp_rule₅ (cs := [.cap p, .int (cMODE), .int (mREJECT)]) (by simp [Atom₅.eval, Atom₅.evalL, constsOf₅, pInterp, Const.toL1, L1.Prim.interp, Const.ofL1] <;> omega)
    (store_at p L _ (cMODE) (mREJECT) ⟨by unfold cMODE; omega, by unfold cMODE; omega⟩) (fun w => ?_)
  refine pre_pure₅ (fun hw => ?_)
  subst hw
  simp [ιA, Tm₅.subst, Atom₅.subst, Atom₅.substL]
  exact conseq₅ (fun σ h => ⟨rfl, rfl, h⟩) (fun r qs σ h => h)
    (ret_rule₅ (v := .const (.cap p)) (Q := fun r qs σ => r = .const (.cap p) ∧ qs = [] ∧
      RegionAt p L (Function.update (Function.update g (p + cREASON) rTRUNC) (p + cMODE) mREJECT) σ) (by simp [Atom₅.eval]))

end VIRL5
