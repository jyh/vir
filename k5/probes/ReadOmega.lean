/-
  O95, K5-2 route A, the first mode WITH arithmetic: READ's bit step (Step.lean `readbit_step`), its trace re-run on the
  checked runner. The range of each arithmetic site is a hypothesis here (r7–r10, the ones that need the caller's InvM facts)
  or derived from n < 2³² (the rest). A pilot: it prices the per-mode work.
-/
import K5.Checked

namespace K5
open VIRL1 VIRL2 VIRC VIRDeflate.Step

theorem inRange_of' {x : Int} (h1 : -2 ^ 63 ≤ x) (h2 : x < 2 ^ 63) : inRange x = true := by
  simp only [inRange, decide_eq_true_eq]; exact ⟨h1, h2⟩

set_option maxHeartbeats 1000000 in
theorem readbit_inR' {σ : Store} {p : Int} {L : Nat} {f : Int → Int} (hw : World σ p L f)
    (bx bi n v : Nat) (k acc wt rt t : Int) (hL : 2080 + n ≤ L) (hn32 : n < 2 ^ 32)
    (hby : f cBY = bx) (hbi : f cBI = bi) (hn : f cN = n) (hbyn : bx < n) (hbi7 : bi ≤ 7)
    (hv : f (IN + bx) = v) (hv8 : v < 256) (ht : f (BT + (8 * v + bi)) = t)
    (hk : f cK = k) (hacc : f cACC = acc) (hwt : f cWT = wt) (hrt : f cRET = rt)
    (r7 : inRange (t * wt) = true) (r8 : inRange (acc + t * wt) = true) (r9 : inRange (2 * wt) = true)
    (r10 : inRange (k - 1) = true) :
    SrcInRange (closeAt p readT, σ) := by
  simp only [cBY, cBI, cN, IN, BT, cK, cACC, cWT, cRET] at hby hbi hn hv ht hk hacc hwt hrt
  have h1 := hw.cell 1 (by decide) (by omega)
  have h2 := hw.cell 2 (by decide) (by omega)
  have h15 := hw.cell 15 (by decide) (by omega)
  have hiv := hw.cell (2080 + bx) (by omega) (by omega)
  have hit := hw.cell (20 + (8 * v + bi)) (by omega) (by omega)
  have hik := hw.cell 2068 (by decide) (by omega)
  have hia := hw.cell 2069 (by decide) (by omega)
  have hiw := hw.cell 2070 (by decide) (by omega)
  have hir := hw.cell 2071 (by decide) (by omega)
  rw [hby] at h1; rw [hbi] at h2; rw [hn] at h15; rw [hv] at hiv; rw [ht] at hit
  rw [hk] at hik; rw [hacc] at hia; rw [hwt] at hiw; rw [hrt] at hir
  have hlt : (bx : Int) < n := by exact_mod_cast hbyn
  have hiL : (2080 : Int) + bx < L := by omega
  have hi0 : (0 : Int) ≤ 2080 + bx := by omega
  have htL : (20 : Int) + (8 * v + bi) < L := by omega
  have ht0 : (0 : Int) ≤ 20 + (8 * v + bi) := by omega
  have hL1 : (1 : Int) < L := by omega
  have hL2 : (2 : Int) < L := by omega
  have hL15 : (15 : Int) < L := by omega
  have hL0 : (0 : Int) < L := by omega
  have hL0' : 0 < L := by omega
  have hLk : (2068 : Int) < L := by omega
  have hLa : (2069 : Int) < L := by omega
  have hLw : (2070 : Int) < L := by omega
  have hLr : (2071 : Int) < L := by omega
  by_cases h7 : bi = 7
  · subst h7
    simp only [Nat.cast_ofNat] at hit htL ht0 h2
    by_cases hk1 : k - 1 = 0 <;>
    · simp only [closeAt, readT, readN, NT.c, NA.c, List.idxOf, List.findIdx, List.findIdx.go, Tm.subst, Atom.subst,
        Atom.substL]
      repeat (first
        | exact srcInRange_ret trivial
        | refine srcInRange_step ?_ ?_ ?_ <;>
          simp (disch := omega) [inRange_eq, closeAt, readT, readN, NT.c, NA.c, List.idxOf, List.findIdx, List.findIdx.go, cBY, cBI, cN, IN, BT, cK, cACC, cWT, cRET, cMODE, cREASON, hk1, hlt, stepFn₂, stepFn, opStep, Store.load, Store.store, hw.reg, h1, h2, h15, hiv, hit, hik, hia, hiw,
            hir, Atom.eval, Atom.evalL, constsOf, S₂, pInterp, L1.Prim.interp, Const.toL1, Const.ofL1, Const.toBool,
            headB, aInR, aInRL, cInR, Tm.subst, Atom.subst, Atom.substL, hiL, hi0, htL, ht0, hL1, hL2, hL15, hL0, hL0',
            hLk, hLa, hLw, hLr, r7, r8, r9, r10])
  · have h7' : ¬ ((bi : Int) = 7) := by exact_mod_cast h7
    by_cases hk1 : k - 1 = 0 <;>
    · simp only [closeAt, readT, readN, NT.c, NA.c, List.idxOf, List.findIdx, List.findIdx.go, Tm.subst, Atom.subst,
        Atom.substL]
      repeat (first
        | exact srcInRange_ret trivial
        | refine srcInRange_step ?_ ?_ ?_ <;>
          simp (disch := omega) [inRange_eq, closeAt, readT, readN, NT.c, NA.c, List.idxOf, List.findIdx, List.findIdx.go, cBY, cBI, cN, IN, BT, cK, cACC, cWT, cRET, cMODE, cREASON, h7', hk1, hlt, stepFn₂, stepFn, opStep, Store.load, Store.store, hw.reg, h1, h2, h15, hiv, hit, hik, hia,
            hiw, hir, Atom.eval, Atom.evalL, constsOf, S₂, pInterp, L1.Prim.interp, Const.toL1, Const.ofL1, Const.toBool,
            headB, aInR, aInRL, cInR, Tm.subst, Atom.subst, Atom.substL, hiL, hi0, htL, ht0, hL1, hL2, hL15, hL0, hL0',
            hLk, hLa, hLw, hLr, r7, r8, r9, r10])

end K5
