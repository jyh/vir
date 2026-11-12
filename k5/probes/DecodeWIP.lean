/- K5-2 WIP (68th head): decode_step on the checked runner, after porter rounds k5p-020..027.
   OPEN at k5p-027: max recursion depth at the walk + heartbeat timeout (4,000,000). Needs its own treatment
   (split the walk, or raise maxRecDepth). Not imported. -/
import K5.Modes2

namespace K5
open VIRL1 VIRL2 VIRC VIRDeflate.Step

set_option maxHeartbeats 4000000 in
theorem decode_step_inR {σ : Store} {p : Int} {L : Nat} {f : Int → Int} (hw : World σ p L f)
    (bx bi n v : Nat) (om X l cv t rt b tb fs c o sy : Int) (hL : 2080 + n ≤ L)
    (hby : f cBY = bx) (hbi : f cBI = bi) (hn : f cN = n) (hom : f cOUTMAX = om) (hX : f cX = X)
    (hbyn : bx < n) (hbi7 : bi ≤ 7) (hv : f (IN + bx) = v) (hv8 : v < 256) (hb : f (BT + (8 * v + bi)) = b)
    (hX0 : 0 ≤ X) (hXL : X + 4 < L)
    (hl : f X = l) (hcv : f (X + 1) = cv) (ht : f (X + 2) = t) (hrt : f (X + 3) = rt)
    (htb : 2080 + n + om + 337 + 352 * t = tb) (ht0 : 0 ≤ tb) (htL : tb + 352 ≤ L) (hl1 : 1 ≤ l) (hl15 : l ≤ 15)
    (hfs : f (tb + 16 + l) = fs) (hc : f (tb + l) = c) (ho : f (tb + 32 + l) = o)
    (hsy0 : fs ≤ 2 * cv + b ∧ 2 * cv + b < fs + c → 0 ≤ tb + 64 + o + (2 * cv + b - fs) ∧ tb + 64 + o + (2 * cv + b - fs) < L)
    (hsy : f (tb + 64 + o + (2 * cv + b - fs)) = sy)
    (rr1 : inRange (2080 + (bx : Int)) = true)
    (rr2 : inRange (8 * (v : Int)) = true) (rr3 : inRange (8 * (v : Int) + 7) = true) (rr4 : inRange (20 + (8 * (v : Int) + 7)) = true) (rr5 : inRange (2080 + (bx : Int)) = true) (rr6 : inRange (8 * (v : Int) + (bi : Int)) = true) (rr7 : inRange (20 + (8 * (v : Int) + (bi : Int))) = true)
    (rr8 : inRange (X + 1) = true) (rr9 : inRange (2080 + (bx : Int)) = true) (rr10 : inRange (8 * (v : Int)) = true) (rr11 : inRange (8 * (v : Int) + 7) = true) (rr12 : inRange (20 + (8 * (v : Int) + 7)) = true) (rr13 : inRange (8 * (v : Int) + (7 : Int)) = true) (rr14 : inRange (20 + (8 * (v : Int) + (7 : Int))) = true) (rr15 : inRange (8 * (v : Int) + (bi : Int)) = true) (rr16 : inRange (20 + (8 * (v : Int) + (bi : Int))) = true)
    (rr17 : inRange (X + 2) = true) (rr18 : inRange (2080 + (bx : Int)) = true) (rr19 : inRange (8 * (v : Int)) = true) (rr20 : inRange (8 * (v : Int) + 7) = true) (rr21 : inRange (20 + (8 * (v : Int) + 7)) = true) (rr22 : inRange (X + 1) = true) (rr23 : inRange (8 * (v : Int) + (7 : Int)) = true) (rr24 : inRange (20 + (8 * (v : Int) + (7 : Int))) = true) (rr25 : inRange (8 * (v : Int) + (bi : Int)) = true) (rr26 : inRange (20 + (8 * (v : Int) + (bi : Int))) = true)
    (rr27 : inRange (X + 3) = true) (rr28 : inRange (2080 + (bx : Int)) = true) (rr29 : inRange (8 * (v : Int)) = true) (rr30 : inRange (8 * (v : Int) + 7) = true) (rr31 : inRange (20 + (8 * (v : Int) + 7)) = true) (rr32 : inRange (X + 1) = true) (rr33 : inRange (X + 2) = true) (rr34 : inRange (8 * (v : Int) + (7 : Int)) = true) (rr35 : inRange (20 + (8 * (v : Int) + (7 : Int))) = true) (rr36 : inRange (8 * (v : Int) + (bi : Int)) = true) (rr37 : inRange (20 + (8 * (v : Int) + (bi : Int))) = true)
    (rr38 : inRange (2080 + (n : Int)) = true) (rr39 : inRange (2080 + (n : Int) + om) = true) (rr40 : inRange (2080 + (n : Int) + om + 337) = true) (rr41 : inRange (352 * t) = true) (rr42 : inRange (2080 + (n : Int) + om + 337 + 352 * t) = true) (rr43 : inRange (2080 + (bx : Int)) = true) (rr44 : inRange (8 * (v : Int)) = true) (rr45 : inRange (8 * (v : Int) + 7) = true) (rr46 : inRange (20 + (8 * (v : Int) + 7)) = true) (rr47 : inRange (X + 1) = true) (rr48 : inRange (X + 2) = true) (rr49 : inRange (X + 3) = true) (rr50 : inRange (8 * (v : Int) + (7 : Int)) = true) (rr51 : inRange (20 + (8 * (v : Int) + (7 : Int))) = true) (rr52 : inRange (8 * (v : Int) + (bi : Int)) = true) (rr53 : inRange (20 + (8 * (v : Int) + (bi : Int))) = true)
    (rr54 : inRange (2080 + (n : Int) + om + 337 + 352 * t + 16) = true) (rr55 : inRange (2080 + (n : Int) + om + 337 + 352 * t + 16 + l) = true) (rr56 : inRange (2080 + (bx : Int)) = true) (rr57 : inRange (8 * (v : Int)) = true) (rr58 : inRange (8 * (v : Int) + 7) = true) (rr59 : inRange (20 + (8 * (v : Int) + 7)) = true) (rr60 : inRange (X + 1) = true) (rr61 : inRange (X + 2) = true) (rr62 : inRange (X + 3) = true) (rr63 : inRange (2080 + (n : Int)) = true) (rr64 : inRange (2080 + (n : Int) + om) = true) (rr65 : inRange (2080 + (n : Int) + om + 337) = true) (rr66 : inRange (352 * t) = true) (rr67 : inRange (2080 + (n : Int) + om + 337 + 352 * t) = true) (rr68 : inRange (8 * (v : Int) + (7 : Int)) = true) (rr69 : inRange (20 + (8 * (v : Int) + (7 : Int))) = true) (rr70 : inRange (8 * (v : Int) + (bi : Int)) = true) (rr71 : inRange (20 + (8 * (v : Int) + (bi : Int))) = true) (rr72 : inRange (2080 + (n : Int) + om + 337 + 352 * t + 16 + 15) = true) :
    SrcInRange (closeAt p decodeT, σ) := by
  subst htb
  simp only [cBY, cBI, cN, cOUTMAX, cX, IN, BT] at hby hbi hn hom hX hv hb
  have g1 := hw.get (i := 1) (by decide) (by omega) hby
  have g2 := hw.get (i := 2) (by decide) (by omega) hbi
  have g15 := hw.get (i := 15) (by decide) (by omega) hn
  have g16 := hw.get (i := 16) (by decide) (by omega) hom
  have g79 := hw.get (i := 2079) (by decide) (by omega) hX
  have gv := hw.get (i := 2080 + bx) (by omega) (by omega) hv
  have gb := hw.get (i := 20 + (8 * v + bi)) (by omega) (by omega) hb
  have gl := hw.get (i := X) (by omega) (by omega) hl
  have gcv := hw.get (i := X + 1) (by omega) (by omega) hcv
  have gt := hw.get (i := X + 2) (by omega) (by omega) ht
  have grt := hw.get (i := X + 3) (by omega) (by omega) hrt
  have gfs := hw.get (i := 2080 + ↑n + om + 337 + 352 * t + 16 + l) (by omega) (by omega) hfs
  have gc := hw.get (i := 2080 + ↑n + om + 337 + 352 * t + l) (by omega) (by omega) hc
  have go := hw.get (i := 2080 + ↑n + om + 337 + 352 * t + 32 + l) (by omega) (by omega) ho
  have hlt : (bx : Int) < n := by exact_mod_cast hbyn
  by_cases hh : fs ≤ 2 * cv + b ∧ 2 * cv + b < fs + c
  · obtain ⟨hy0, hyL⟩ := hsy0 hh
    have gsy := hw.get hy0 hyL hsy
    obtain ⟨h1, h2⟩ := hh
    by_cases h7 : bi = 7
    · subst h7
      simp only [Nat.cast_ofNat] at gb g2
      repeat (first | exact srcInRange_ret trivial | refine srcInRange_step ?_ ?_ ?_ <;> simp [headB, aInR, aInRL, cInR, rr54, rr55, rr56, rr57, rr58, rr59, rr60, rr61, rr62, rr63, rr64, rr65, rr66, rr67, rr68, rr69, rr70, rr71, rr72, rr38, rr39, rr40, rr41, rr42, rr43, rr44, rr45, rr46, rr47, rr48, rr49, rr50, rr51, rr52, rr53, rr27, rr28, rr29, rr30, rr31, rr32, rr33, rr34, rr35, rr36, rr37, rr17, rr18, rr19, rr20, rr21, rr22, rr23, rr24, rr25, rr26, rr8, rr9, rr10, rr11, rr12, rr13, rr14, rr15, rr16, rr2, rr3, rr4, rr5, rr6, rr7, rr1, closeAt, NT.c, NA.c, List.idxOf, List.findIdx, List.findIdx.go, Tm.subst, Atom.subst, Atom.substL, stepFn₂,
      stepFn, opStep, Store.load, Store.store, hw.reg, Atom.eval, Atom.evalL, constsOf, S₂, pInterp, L1.Prim.interp,
      Const.toL1, Const.ofL1, Const.toBool, decodeT, decodeN, cBY, cBI, cN, cOUTMAX, cX, IN, BT, cMODE, cREASON, decH, tblNext, hlt, h1, h2, g1, g2, g15, g16, g79, gv, gb, gl, gcv, gt, grt, gfs, gc, go, gsy,
        show (1 : Int) < L by omega, show (2 : Int) < L by omega, show (15 : Int) < L by omega, show (16 : Int) < L by omega,
        show (2079 : Int) < L by omega, show (0 : Int) < L by omega, show 0 < L by omega,
        show (2080 : Int) + bx < L by omega, show (0 : Int) ≤ 2080 + bx by omega,
        show (20 : Int) + (8 * v + 7) < L by omega, show (0 : Int) ≤ 20 + (8 * v + 7) by omega,
        show X < L by omega, show X + 1 < L by omega, show X + 2 < L by omega, show X + 3 < L by omega,
        show X + 4 < L by omega, show (0 : Int) ≤ X + 1 by omega, show (0 : Int) ≤ X + 2 by omega,
        show (0 : Int) ≤ X + 3 by omega, show (0 : Int) ≤ X + 4 by omega, hX0,
        show 2080 + ↑n + om + 337 + 352 * t + 16 + l < L by omega, show (0 : Int) ≤ 2080 + ↑n + om + 337 + 352 * t + 16 + l by omega,
        show 2080 + ↑n + om + 337 + 352 * t + l < L by omega, show (0 : Int) ≤ 2080 + ↑n + om + 337 + 352 * t + l by omega,
        show 2080 + ↑n + om + 337 + 352 * t + 32 + l < L by omega, show (0 : Int) ≤ 2080 + ↑n + om + 337 + 352 * t + 32 + l by omega,
        hy0, hyL])
    · have h7' : ¬ ((bi : Int) = 7) := by exact_mod_cast h7
      repeat (first | exact srcInRange_ret trivial | refine srcInRange_step ?_ ?_ ?_ <;> simp [headB, aInR, aInRL, cInR, rr54, rr55, rr56, rr57, rr58, rr59, rr60, rr61, rr62, rr63, rr64, rr65, rr66, rr67, rr68, rr69, rr70, rr71, rr72, rr38, rr39, rr40, rr41, rr42, rr43, rr44, rr45, rr46, rr47, rr48, rr49, rr50, rr51, rr52, rr53, rr27, rr28, rr29, rr30, rr31, rr32, rr33, rr34, rr35, rr36, rr37, rr17, rr18, rr19, rr20, rr21, rr22, rr23, rr24, rr25, rr26, rr8, rr9, rr10, rr11, rr12, rr13, rr14, rr15, rr16, rr2, rr3, rr4, rr5, rr6, rr7, rr1, closeAt, NT.c, NA.c, List.idxOf, List.findIdx, List.findIdx.go, Tm.subst, Atom.subst, Atom.substL, stepFn₂,
      stepFn, opStep, Store.load, Store.store, hw.reg, Atom.eval, Atom.evalL, constsOf, S₂, pInterp, L1.Prim.interp,
      Const.toL1, Const.ofL1, Const.toBool, decodeT, decodeN, cBY, cBI, cN, cOUTMAX, cX, IN, BT, cMODE, cREASON, decH, tblNext, h7', hlt, h1, h2, g1, g2, g15, g16, g79, gv, gb, gl, gcv, gt, grt, gfs, gc, go, gsy,
        show (1 : Int) < L by omega, show (2 : Int) < L by omega, show (15 : Int) < L by omega, show (16 : Int) < L by omega,
        show (2079 : Int) < L by omega, show (0 : Int) < L by omega, show 0 < L by omega,
        show (2080 : Int) + bx < L by omega, show (0 : Int) ≤ 2080 + bx by omega,
        show (20 : Int) + (8 * v + bi) < L by omega, show (0 : Int) ≤ 20 + (8 * v + bi) by omega,
        show X < L by omega, show X + 1 < L by omega, show X + 2 < L by omega, show X + 3 < L by omega,
        show X + 4 < L by omega, show (0 : Int) ≤ X + 1 by omega, show (0 : Int) ≤ X + 2 by omega,
        show (0 : Int) ≤ X + 3 by omega, show (0 : Int) ≤ X + 4 by omega, hX0,
        show 2080 + ↑n + om + 337 + 352 * t + 16 + l < L by omega, show (0 : Int) ≤ 2080 + ↑n + om + 337 + 352 * t + 16 + l by omega,
        show 2080 + ↑n + om + 337 + 352 * t + l < L by omega, show (0 : Int) ≤ 2080 + ↑n + om + 337 + 352 * t + l by omega,
        show 2080 + ↑n + om + 337 + 352 * t + 32 + l < L by omega, show (0 : Int) ≤ 2080 + ↑n + om + 337 + 352 * t + 32 + l by omega,
        hy0, hyL])
  · have hmiss : ¬ (fs ≤ 2 * cv + b) ∨ ¬ (2 * cv + b < fs + c) := by tauto
    by_cases h15 : l = 15
    · subst h15
      by_cases h7 : bi = 7
      · subst h7
        simp only [Nat.cast_ofNat] at gb g2
        rcases hmiss with hm | hm <;> by_cases ha : fs ≤ 2 * cv + b <;> (try (exfalso; omega)) <;>
        repeat (first | exact srcInRange_ret trivial | refine srcInRange_step ?_ ?_ ?_ <;> simp [headB, aInR, aInRL, cInR, rr54, rr55, rr56, rr57, rr58, rr59, rr60, rr61, rr62, rr63, rr64, rr65, rr66, rr67, rr68, rr69, rr70, rr71, rr72, rr38, rr39, rr40, rr41, rr42, rr43, rr44, rr45, rr46, rr47, rr48, rr49, rr50, rr51, rr52, rr53, rr27, rr28, rr29, rr30, rr31, rr32, rr33, rr34, rr35, rr36, rr37, rr17, rr18, rr19, rr20, rr21, rr22, rr23, rr24, rr25, rr26, rr8, rr9, rr10, rr11, rr12, rr13, rr14, rr15, rr16, rr2, rr3, rr4, rr5, rr6, rr7, rr1, ha, closeAt, NT.c, NA.c, List.idxOf, List.findIdx, List.findIdx.go, Tm.subst, Atom.subst, Atom.substL, stepFn₂,
          stepFn, opStep, Store.load, Store.store, hw.reg, Atom.eval, Atom.evalL, constsOf, S₂, pInterp, L1.Prim.interp,
          Const.toL1, Const.ofL1, Const.toBool, decodeT, decodeN, cBY, cBI, cN, cOUTMAX, cX, IN, BT, cMODE, cREASON, decH, tblNext, hh, hm, hlt, g1, g2, g15, g16, g79, gv, gb, gl, gcv, gt, grt, gfs, gc,
          show (1 : Int) < L by omega, show (2 : Int) < L by omega, show (15 : Int) < L by omega,
          show (16 : Int) < L by omega, show (2079 : Int) < L by omega, show (0 : Int) < L by omega, show 0 < L by omega,
          show (14 : Int) < L by omega, show (2080 : Int) + bx < L by omega, show (0 : Int) ≤ 2080 + bx by omega,
          show (20 : Int) + (8 * v + 7) < L by omega, show (0 : Int) ≤ 20 + (8 * v + 7) by omega,
          show X < L by omega, show X + 1 < L by omega, show X + 2 < L by omega, show X + 3 < L by omega,
          show (0 : Int) ≤ X + 1 by omega, show (0 : Int) ≤ X + 2 by omega, show (0 : Int) ≤ X + 3 by omega, hX0,
          rINVCODE, mREJECT,
          show 2080 + ↑n + om + 337 + 352 * t + 16 + 15 < L by omega,
          show (0 : Int) ≤ 2080 + ↑n + om + 337 + 352 * t + 16 + 15 by omega,
          show 2080 + ↑n + om + 337 + 352 * t + 15 < L by omega,
          show (0 : Int) ≤ 2080 + ↑n + om + 337 + 352 * t + 15 by omega])
      · have h7' : ¬ ((bi : Int) = 7) := by exact_mod_cast h7
        rcases hmiss with hm | hm <;> by_cases ha : fs ≤ 2 * cv + b <;> (try (exfalso; omega)) <;>
        repeat (first | exact srcInRange_ret trivial | refine srcInRange_step ?_ ?_ ?_ <;> simp [headB, aInR, aInRL, cInR, rr54, rr55, rr56, rr57, rr58, rr59, rr60, rr61, rr62, rr63, rr64, rr65, rr66, rr67, rr68, rr69, rr70, rr71, rr72, rr38, rr39, rr40, rr41, rr42, rr43, rr44, rr45, rr46, rr47, rr48, rr49, rr50, rr51, rr52, rr53, rr27, rr28, rr29, rr30, rr31, rr32, rr33, rr34, rr35, rr36, rr37, rr17, rr18, rr19, rr20, rr21, rr22, rr23, rr24, rr25, rr26, rr8, rr9, rr10, rr11, rr12, rr13, rr14, rr15, rr16, rr2, rr3, rr4, rr5, rr6, rr7, rr1, ha, closeAt, NT.c, NA.c, List.idxOf, List.findIdx, List.findIdx.go, Tm.subst, Atom.subst, Atom.substL, stepFn₂,
          stepFn, opStep, Store.load, Store.store, hw.reg, Atom.eval, Atom.evalL, constsOf, S₂, pInterp, L1.Prim.interp,
          Const.toL1, Const.ofL1, Const.toBool, decodeT, decodeN, cBY, cBI, cN, cOUTMAX, cX, IN, BT, cMODE, cREASON, decH, tblNext, hh, hm, hlt, g1, g2, g15, g16, g79, gv, gb, gl, gcv, gt, grt, gfs, gc, h7',
          show (1 : Int) < L by omega, show (2 : Int) < L by omega, show (15 : Int) < L by omega,
          show (16 : Int) < L by omega, show (2079 : Int) < L by omega, show (0 : Int) < L by omega, show 0 < L by omega,
          show (14 : Int) < L by omega, show (2080 : Int) + bx < L by omega, show (0 : Int) ≤ 2080 + bx by omega,
          show (20 : Int) + (8 * v + bi) < L by omega, show (0 : Int) ≤ 20 + (8 * v + bi) by omega,
          show X < L by omega, show X + 1 < L by omega, show X + 2 < L by omega, show X + 3 < L by omega,
          show (0 : Int) ≤ X + 1 by omega, show (0 : Int) ≤ X + 2 by omega, show (0 : Int) ≤ X + 3 by omega, hX0,
          rINVCODE, mREJECT,
          show 2080 + ↑n + om + 337 + 352 * t + 16 + 15 < L by omega,
          show (0 : Int) ≤ 2080 + ↑n + om + 337 + 352 * t + 16 + 15 by omega,
          show 2080 + ↑n + om + 337 + 352 * t + 15 < L by omega,
          show (0 : Int) ≤ 2080 + ↑n + om + 337 + 352 * t + 15 by omega])
    · by_cases h7 : bi = 7
      · subst h7
        simp only [Nat.cast_ofNat] at gb g2
        rcases hmiss with hm | hm <;> by_cases ha : fs ≤ 2 * cv + b <;> (try (exfalso; omega)) <;>
        repeat (first | exact srcInRange_ret trivial | refine srcInRange_step ?_ ?_ ?_ <;> simp [headB, aInR, aInRL, cInR, rr54, rr55, rr56, rr57, rr58, rr59, rr60, rr61, rr62, rr63, rr64, rr65, rr66, rr67, rr68, rr69, rr70, rr71, rr72, rr38, rr39, rr40, rr41, rr42, rr43, rr44, rr45, rr46, rr47, rr48, rr49, rr50, rr51, rr52, rr53, rr27, rr28, rr29, rr30, rr31, rr32, rr33, rr34, rr35, rr36, rr37, rr17, rr18, rr19, rr20, rr21, rr22, rr23, rr24, rr25, rr26, rr8, rr9, rr10, rr11, rr12, rr13, rr14, rr15, rr16, rr2, rr3, rr4, rr5, rr6, rr7, rr1, ha, closeAt, NT.c, NA.c, List.idxOf, List.findIdx, List.findIdx.go, Tm.subst, Atom.subst, Atom.substL, stepFn₂,
          stepFn, opStep, Store.load, Store.store, hw.reg, Atom.eval, Atom.evalL, constsOf, S₂, pInterp, L1.Prim.interp,
          Const.toL1, Const.ofL1, Const.toBool, decodeT, decodeN, cBY, cBI, cN, cOUTMAX, cX, IN, BT, cMODE, cREASON, decH, tblNext, hh, hm, hlt, g1, g2, g15, g16, g79, gv, gb, gl, gcv, gt, grt, gfs, gc, h15,
          show (1 : Int) < L by omega, show (2 : Int) < L by omega, show (15 : Int) < L by omega,
          show (16 : Int) < L by omega, show (2079 : Int) < L by omega, show (0 : Int) < L by omega, show 0 < L by omega,
          show (14 : Int) < L by omega, show (2080 : Int) + bx < L by omega, show (0 : Int) ≤ 2080 + bx by omega,
          show (20 : Int) + (8 * v + 7) < L by omega, show (0 : Int) ≤ 20 + (8 * v + 7) by omega,
          show X < L by omega, show X + 1 < L by omega, show X + 2 < L by omega, show X + 3 < L by omega,
          show (0 : Int) ≤ X + 1 by omega, show (0 : Int) ≤ X + 2 by omega, show (0 : Int) ≤ X + 3 by omega, hX0,
          rINVCODE, mREJECT,
          show 2080 + ↑n + om + 337 + 352 * t + 16 + l < L by omega,
          show (0 : Int) ≤ 2080 + ↑n + om + 337 + 352 * t + 16 + l by omega,
          show 2080 + ↑n + om + 337 + 352 * t + l < L by omega,
          show (0 : Int) ≤ 2080 + ↑n + om + 337 + 352 * t + l by omega])
      · have h7' : ¬ ((bi : Int) = 7) := by exact_mod_cast h7
        rcases hmiss with hm | hm <;> by_cases ha : fs ≤ 2 * cv + b <;> (try (exfalso; omega)) <;>
        repeat (first | exact srcInRange_ret trivial | refine srcInRange_step ?_ ?_ ?_ <;> simp [headB, aInR, aInRL, cInR, rr54, rr55, rr56, rr57, rr58, rr59, rr60, rr61, rr62, rr63, rr64, rr65, rr66, rr67, rr68, rr69, rr70, rr71, rr72, rr38, rr39, rr40, rr41, rr42, rr43, rr44, rr45, rr46, rr47, rr48, rr49, rr50, rr51, rr52, rr53, rr27, rr28, rr29, rr30, rr31, rr32, rr33, rr34, rr35, rr36, rr37, rr17, rr18, rr19, rr20, rr21, rr22, rr23, rr24, rr25, rr26, rr8, rr9, rr10, rr11, rr12, rr13, rr14, rr15, rr16, rr2, rr3, rr4, rr5, rr6, rr7, rr1, ha, closeAt, NT.c, NA.c, List.idxOf, List.findIdx, List.findIdx.go, Tm.subst, Atom.subst, Atom.substL, stepFn₂,
          stepFn, opStep, Store.load, Store.store, hw.reg, Atom.eval, Atom.evalL, constsOf, S₂, pInterp, L1.Prim.interp,
          Const.toL1, Const.ofL1, Const.toBool, decodeT, decodeN, cBY, cBI, cN, cOUTMAX, cX, IN, BT, cMODE, cREASON, decH, tblNext, hh, hm, hlt, g1, g2, g15, g16, g79, gv, gb, gl, gcv, gt, grt, gfs, gc, h15, h7',
          show (1 : Int) < L by omega, show (2 : Int) < L by omega, show (15 : Int) < L by omega,
          show (16 : Int) < L by omega, show (2079 : Int) < L by omega, show (0 : Int) < L by omega, show 0 < L by omega,
          show (14 : Int) < L by omega, show (2080 : Int) + bx < L by omega, show (0 : Int) ≤ 2080 + bx by omega,
          show (20 : Int) + (8 * v + bi) < L by omega, show (0 : Int) ≤ 20 + (8 * v + bi) by omega,
          show X < L by omega, show X + 1 < L by omega, show X + 2 < L by omega, show X + 3 < L by omega,
          show (0 : Int) ≤ X + 1 by omega, show (0 : Int) ≤ X + 2 by omega, show (0 : Int) ≤ X + 3 by omega, hX0,
          rINVCODE, mREJECT,
          show 2080 + ↑n + om + 337 + 352 * t + 16 + l < L by omega,
          show (0 : Int) ≤ 2080 + ↑n + om + 337 + 352 * t + 16 + l by omega,
          show 2080 + ↑n + om + 337 + 352 * t + l < L by omega,
          show (0 : Int) ≤ 2080 + ↑n + om + 337 + 352 * t + l by omega])


end K5
