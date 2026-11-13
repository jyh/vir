import VIRDeflate
/- MUTANT: code 17 repeats zero 4 + r times (S says 3 + r); the machine's PENDING is 3. Must be RED in lens_sim's 17 branch: S6's lengths loop copied into a sub-namespace, with `lens_sim`'s proof re-run on the copy (STAGE's mutant method). -/
namespace VIRDeflate.Step.DynRep17
open VIRL1 VIRL2

def lensLoopM (CL : Code) (total : Nat) : Nat → Array Nat → M (Array Nat)
  | 0, _ => reject "truncated"
  | fuel + 1, lens =>
    if lens.size < total then do
      let s ← decode CL
      let lens' ←
        if s ≤ 15 then pure (lens.push s)
        else if s = 16 then do
          if lens.size = 0 then reject "repeat with no first length"
          let r ← bits 2
          pure (pushN (lens.getD (lens.size - 1) 0) (3 + r) lens)
        else if s = 17 then do
          let r ← bits 3
          pure (pushN 0 (4 + r) lens)
        else do
          let r ← bits 7
          pure (pushN 0 (11 + r) lens)
      if lens'.size > total then reject "invalid bit length repeat"
      lensLoopM CL total fuel lens'
    else
      pure lens


def lnext (CL : Code) (total fuel : Nat) (lens' : Array Nat) : M (Array Nat) :=
  if lens'.size > total then (reject "invalid bit length repeat" : M Unit) >>= fun _ => lensLoopM CL total fuel lens'
  else lensLoopM CL total fuel lens'

/-- One `lensLoopM` body after the decode, as the do-notation elaborates it (the continuation in every branch). -/
def lbody (CL : Code) (total fuel : Nat) (lens : Array Nat) (s : Nat) : M (Array Nat) :=
  if s ≤ 15 then pure (lens.push s) >>= fun lens' => lnext CL total fuel lens'
  else if s = 16 then
    (if lens.size = 0 then (reject "repeat with no first length" : M Unit) >>= fun _ =>
        (bits 2 >>= fun r => pure (pushN (lens.getD (lens.size - 1) 0) (3 + r) lens) >>= fun lens' =>
          lnext CL total fuel lens')
     else bits 2 >>= fun r => pure (pushN (lens.getD (lens.size - 1) 0) (3 + r) lens) >>= fun lens' =>
          lnext CL total fuel lens')
  else if s = 17 then bits 3 >>= fun r => pure (pushN 0 (4 + r) lens) >>= fun lens' => lnext CL total fuel lens'
  else bits 7 >>= fun r => pure (pushN 0 (11 + r) lens) >>= fun lens' => lnext CL total fuel lens'

theorem lensLoopM_succ (CL : Code) (total fuel : Nat) (lens : Array Nat) :
    lensLoopM CL total (fuel + 1) lens = if lens.size < total then
      (decode CL >>= fun s => lbody CL total fuel lens s) else pure lens := rfl

/-- After a repeat's extra bits: LREP, then REP's copies, then the loop again. -/
theorem rep_tail {b : Array Nat} {om : Nat} {lit : Bool} {p : Int} (hb : ∀ x ∈ b, x < 256) (bf : Int) (hl hd : Nat)
    (htot : hl + hd ≤ 316) (cl : Array Nat) (fuel : Nat)
    (ih : ∀ lens, Sim b om p (lensLoopM (assign cl) (hl + hd) fuel lens) (LPre b om lit bf hl hd cl lens fuel)
      (LPost b om lit bf hl hd cl))
    (lens : Array Nat) (v q r : Nat) (hv15 : v ≤ 15) :
    Sim b om p (pure (pushN v (q + r) lens) >>= fun lens' => lnext (assign cl) (hl + hd) fuel lens')
      (fun f st => Rel b om lit f st ∧ f cMODE = mLREP ∧ f cACC = r ∧ (f cPEND = q ∧ f cLAST = v ∧
        f cFILL = lens.size ∧ LFrame b om bf hl hd cl lens f ∧ 8 * b.size - st.pos < fuel))
      (LPost b om lit bf hl hd cl) := by
  have hL : 2080 ≤ L0 b.size om := by unfold L0; omega
  refine Sim.bind (mid := fun lens' f st => lens' = pushN v (q + r) lens ∧ (Rel b om lit f st ∧ f cMODE = mLREP ∧
    f cACC = r ∧ (f cPEND = q ∧ f cLAST = v ∧ f cFILL = lens.size ∧ LFrame b om bf hl hd cl lens f ∧
      8 * b.size - st.pos < fuel))) (Sim.pure fun f st h => ⟨rfl, h⟩) (fun lens' => ?_)
  unfold lnext
  refine Sim.ite (fun hc => Sim.reject_bind ?_) (fun hc => Sim.reach ?_ (ih lens'))
  · rintro σ f st hw ⟨rfl, hR, hm, ha, hpd, hla, hfl, hF, hfu⟩
    rw [pushN_size] at hc
    obtain ⟨σ1, f1, hS, hw1, hm1⟩ := (lrep_next hb hw hR hm).1 (by rw [hF.1, hF.2.1, hfl, hpd, ha]; push_cast; omega)
    exact ⟨σ1, f1, Reach.step hS, hw1, hm1⟩
  · rintro σ f st hw ⟨rfl, hR, hm, ha, hpd, hla, hfl, hF, hfu⟩
    rw [pushN_size] at hc
    obtain ⟨σ1, f1, hS, hw1, hR1, h1, h2, hk1⟩ := (lrep_next hb hw hR hm).2
      (by rw [hF.1, hF.2.1, hfl, hpd, ha]; push_cast; omega)
    have hF1 := hF.keep hk1 (by omega) (fun c hc' => by unfold tbase LB0; omega)
    obtain ⟨σ2, f2, hR2, hw2, hRe2, hm2, hfl2, hc2, hk2⟩ := rep_run hb (q + r) σ1 f1 st lens.size hw1 hR1 h1
      (by rw [h2, hpd, ha]; push_cast; ring)
      (by rw [hk1 _ (by decide) (by unfold cFILL; omega) (by unfold cFILL; omega)]; exact hfl) (by omega)
    have eL : f1 cLAST = v := by rw [hk1 _ (by decide) (by unfold cLAST; omega) (by unfold cLAST; omega)]; exact hla
    have hF2 := hF1.keep hk2 (by omega) (fun c hc' => by unfold tbase LB0 at *; push_cast at hc'; omega)
    refine ⟨σ2, f2, (Reach.step hS).trans hR2, hw2, ⟨⟨hRe2, hm2, by rw [hfl2, pushN_size]; push_cast; ring⟩,
      hF2.pushN v (q + r) hv15 (by omega) (fun j hj => by rw [hc2 j hj, eL])⟩, hfu⟩

/-- A repeat code (16, 17, 18): LSYM's request, READ of the extra bits, then `rep_tail`. -/
theorem rep_req {b : Array Nat} {om : Nat} {lit : Bool} {p : Int} (hb : ∀ x ∈ b, x < 256) (bf : Int) (hl hd : Nat)
    (htot : hl + hd ≤ 316) (cl : Array Nat) (fuel : Nat)
    (ih : ∀ lens, Sim b om p (lensLoopM (assign cl) (hl + hd) fuel lens) (LPre b om lit bf hl hd cl lens fuel)
      (LPost b om lit bf hl hd cl))
    (lens : Array Nat) (hlt : lens.size < hl + hd) (s K q v : Nat) (hs16 : 16 ≤ s) (hne : s = 16 → lens.size ≠ 0)
    (hK : (if s = 16 then (2 : Int) else if s = 17 then 3 else 7) = (K : Int) + 1)
    (hq : (if s = 18 ∨ 18 < s then (11 : Int) else 3) = q)
    (hv : (s = 16 → v = lens.getD (lens.size - 1) 0) ∧ (s ≠ 16 → v = 0)) :
    Sim b om p (bits (K + 1) >>= fun r => pure (pushN v (q + r) lens) >>= fun lens' => lnext (assign cl) (hl + hd) fuel lens')
      (fun f st => Rel b om lit f st ∧ f cMODE = mLSYM ∧ f (X0 b.size om + 4) = s ∧
        (f cFILL = lens.size ∧ LFrame b om bf hl hd cl lens f ∧ 8 * b.size - st.pos < fuel))
      (LPost b om lit bf hl hd cl) := by
  have hL : 2080 ≤ L0 b.size om := by unfold L0; omega
  intro σ0 f0 st0 hw0 hpre0
  have hv15 : v ≤ 15 := by
    obtain ⟨-, -, -, -, hF, -⟩ := hpre0
    by_cases h : s = 16
    · rw [hv.1 h]; exact hF.2.2.2.2.2.2.2.2 _ (by have := hne h; omega)
    · rw [hv.2 h]; omega
  let Q : (Int → Int) → St → Prop := fun f st => f cPEND = q ∧ f cLAST = v ∧ f cFILL = lens.size ∧
    LFrame b om bf hl hd cl lens f ∧ 8 * b.size - st.pos < fuel
  refine (Sim.step (pre := fun f st => Rel b om lit f st ∧ f cMODE = mLSYM ∧ f (X0 b.size om + 4) = s ∧
    (f cFILL = lens.size ∧ LFrame b om bf hl hd cl lens f ∧ 8 * b.size - st.pos < fuel))
    (pre' := fun f st => (Rel b om lit f st ∧ f cMODE = mREAD ∧ f cK = K + 1 ∧ f cACC = 0 ∧ f cWT = 1 ∧
    f cRET = mLREP) ∧ Q f st) ?_ (Sim.bind (bits_sim' hb K mLREP Q Q (fun f st f' st' hq' hk _ hlt' _ =>
      ⟨by rw [hk _ (by decide) (by unfold cPEND L0; omega) (by unfold rdSet cPEND; omega)]; exact hq'.1,
       by rw [hk _ (by decide) (by unfold cLAST L0; omega) (by unfold rdSet cLAST; omega)]; exact hq'.2.1,
       by rw [hk _ (by decide) (by unfold cFILL L0; omega) (by unfold rdSet cFILL; omega)]; exact hq'.2.2.1,
       hq'.2.2.2.1.keep hk (by omega) (fun c hc => by unfold rdSet at hc; unfold tbase LB0; omega),
       by have := hq'.2.2.2.2; omega⟩))
      (fun r => rep_tail hb bf hl hd htot cl fuel ih lens v q r hv15))) σ0 f0 st0 hw0 hpre0
  rintro σ f st hw ⟨hR, hm, hs, hfl, hF, hfu⟩
  obtain ⟨-, -, hreq⟩ := lsym_next hb hw hR hm s lens.size hs hfl (by omega)
  obtain ⟨σ1, f1, hS, hw1, hR1, h1, h2, h3, h4, hK1, hq1, hv1, hk1⟩ := hreq (by exact_mod_cast hs16) (fun h => hne (by exact_mod_cast h))
  have hF1 := hF.keep hk1 (by omega) (fun c hc => by unfold tbase LB0; omega)
  refine ⟨σ1, f1, hS, hw1, ⟨hR1, h1, by rw [hK1]; push_cast; exact hK, h2, h3, h4⟩, by rw [hq1]; push_cast; exact hq, ?_,
    by rw [hk1 _ (by decide) (by unfold cFILL; omega) (by unfold cFILL; omega)]; exact hfl, hF1, hfu⟩
  rw [hv1]
  by_cases h : s = 16
  · rw [if_pos h, hv.1 h, show (lens.size : Int) - 1 = ((lens.size - 1 : Nat) : Int) by have := hne h; omega]
    exact hF.2.2.2.2.2.2.2.1 _ (by have := hne h; omega)
  · rw [if_neg h, hv.2 h]; rfl

/-- **S6's `lensLoopM` is simulated** (LENS … REP), from LENS with the lengths so far in the lengths area. -/
theorem lens_sim {b : Array Nat} {om : Nat} {lit : Bool} {p : Int} (hb : ∀ x ∈ b, x < 256) (bf : Int) (hl hd : Nat)
    (htot : hl + hd ≤ 316) (cl : Array Nat) :
    ∀ fuel (lens : Array Nat), Sim b om p (lensLoopM (assign cl) (hl + hd) fuel lens)
      (LPre b om lit bf hl hd cl lens fuel) (LPost b om lit bf hl hd cl) := by
  have hL : 2080 ≤ L0 b.size om := by unfold L0; omega
  intro fuel
  induction fuel with
  | zero => intro lens; rintro σ f st hw ⟨_, h⟩; omega
  | succ fuel ih =>
    intro lens
    rw [lensLoopM_succ]
    refine Sim.ite (fun hlt => ?_) (fun hge => Sim.pure (fun f st ⟨⟨hRm, hF⟩, _⟩ =>
      ⟨⟨hRm, hF⟩, by have := hF.2.2.2.2.2.2.1; omega⟩))
    refine Sim.step (pre' := fun f st => (DecReady b om lit f st 0 mLSYM ∧ TblRel b.size om f 0 cl) ∧
      (f cFILL = lens.size ∧ LFrame b om bf hl hd cl lens f ∧ 8 * b.size - st.pos < fuel + 1)) ?_ ?_
    · rintro σ f st hw ⟨⟨⟨hR, hm, hfl⟩, hF⟩, hfu⟩
      obtain ⟨σ1, f1, hS, hw1, hD, hk1⟩ := lens_req_next hb hw hR hm (by rw [hfl, hF.1, hF.2.1]; exact_mod_cast hlt)
      have hF1 := hF.keep hk1 (by omega) (fun c hc => by unfold decReqSet at hc; unfold tbase LB0 X0 at *; omega)
      exact ⟨σ1, f1, hS, hw1, ⟨hD, hF1.2.2.2.2.2.1⟩,
        by rw [hk1 _ (by decide) (by unfold cFILL; omega) (by unfold decReqSet cFILL X0; omega)]; exact hfl, hF1, hfu⟩
    refine Sim.bind (decode_Sim hb cl 0 mLSYM
      (fun f st => f cFILL = lens.size ∧ LFrame b om bf hl hd cl lens f ∧ 8 * b.size - st.pos < fuel + 1)
      (fun f st => f cFILL = lens.size ∧ LFrame b om bf hl hd cl lens f ∧ 8 * b.size - st.pos < fuel)
      (fun f st f' st' hq hk hlt' hin =>
        ⟨by rw [hk _ (by decide) (by unfold cFILL L0; omega) (by unfold decSet cFILL X0; omega)]; exact hq.1,
          hq.2.1.keep hk (by omega) (fun c hc => by unfold decSet at hc; unfold tbase LB0 X0 at *; omega),
          by have := hq.2.2; omega⟩)) (fun s => ?_)
    unfold lbody
    refine Sim.ite (fun h15 => ?_) (fun h15 => Sim.ite (fun h16 => ?_) (fun h16 => Sim.ite (fun h17 => ?_) (fun h17 => ?_)))
    · refine Sim.step (pre' := LPre b om lit bf hl hd cl (lens.push s) fuel) ?_ ?_
      · rintro σ f st hw ⟨hR, hm, hs, hfl, hF, hfu⟩
        obtain ⟨hl15, -, -⟩ := lsym_next hb hw hR hm s lens.size hs hfl (by omega)
        obtain ⟨σ1, f1, hS, hw1, hR1, h1, h2, h3, hk1⟩ := hl15 h15
        have hF1 := hF.keep hk1 (by omega) (fun c hc => by unfold tbase LB0 at *; omega)
        refine ⟨σ1, f1, hS, hw1, ⟨⟨hR1, h1, by rw [h2, Array.size_push]; push_cast; ring⟩, ?_⟩, hfu⟩
        exact hF1.pushN s 1 (by omega) (by omega) (fun j hj => by rw [show j = 0 by omega]; simpa using h3)
      refine Sim.bind (mid := fun lens' f st => lens' = lens.push s ∧ LPre b om lit bf hl hd cl (lens.push s) fuel f st)
        (Sim.pure fun f st h => ⟨rfl, h⟩) (fun lens' => ?_)
      unfold lnext
      refine Sim.ite (fun hc => Sim.reject_bind ?_) (fun hc => (ih lens').mono (fun f st ⟨e, h⟩ => e ▸ h) (fun _ _ _ h => h))
      rintro σ f st hw ⟨e, _⟩
      subst e
      simp at hc
      omega
    · refine Sim.ite (fun h0 => Sim.reject_bind ?_) (fun h0 => ?_)
      · rintro σ f st hw ⟨hR, hm, hs, hfl, hF, hfu⟩
        obtain ⟨-, hrej, -⟩ := lsym_next hb hw hR hm s lens.size hs hfl (by omega)
        obtain ⟨σ1, f1, hS, hw1, hm1⟩ := hrej h16 h0
        exact ⟨σ1, f1, Reach.step hS, hw1, hm1⟩
      · exact rep_req hb bf hl hd htot cl fuel ih lens hlt s 1 3 (lens.getD (lens.size - 1) 0) (by omega) (fun _ => h0)
          (by rw [if_pos h16]; norm_num) (by rw [if_neg (by omega)]; norm_num) ⟨fun _ => rfl, fun h => absurd h16 h⟩
    · exact rep_req hb bf hl hd htot cl fuel ih lens hlt s 2 4 0 (by omega) (fun h => absurd h h16)
        (by rw [if_neg h16, if_pos h17]; norm_num) (by rw [if_neg (by omega)]; norm_num) ⟨fun h => absurd h h16, fun _ => rfl⟩
    · exact rep_req hb bf hl hd htot cl fuel ih lens hlt s 6 11 0 (by omega) (fun h => absurd h h16)
        (by rw [if_neg h16, if_neg h17]; norm_num) (by rw [if_pos (by omega)]; norm_num) ⟨fun h => absurd h h16, fun _ => rfl⟩


end VIRDeflate.Step.DynRep17
