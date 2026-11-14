/-
  O95 compiler S3 (compiler/DECLARATIONS-S3.md, Addendum 12): the entry stub and the run-level statement. The driver calls the
  code base with r12 = env0 (ρ₀ above it), r14 = BUF, rbx = CB, `[rsp0]` its return address; the stub saves rsp to `[cb+8]`,
  pushes r12 and calls main, which is the bottom frame `Frames … []` reads. `s3_refines`: a word run from main's initial state is
  matched by a machine run, R3 at the run's end (for `done ws`: DONE at the driver, ws at BUF, its count in r13, every live cell
  related by `Rep`), or RES at a reached state whose `ResWhy` holds.
-/
import S3.Step3

namespace S3
open VIRC X86

def stubHead (C : Ctx3) : List AI := [st .rbx 8 .rsp, .op (.push .q (.reg .r12)), .callA (mainAddr C)]

theorem entryStub_eq (C : Ctx3) : entryStub (mainAddr C) = stubHead C ++ stubCont := rfl

/-- What the driver establishes before its call (S3-M), and where the pieces sit. -/
structure Entry (C : Ctx3) (p : Program) (L : Lay3) (main : WCode) (ρ₀ : List W) (wm : WMem) (s : Cpu) : Prop where
  stopped : s.stopped = false
  rip : CodeAt C p s.rip (entryStub (mainAddr C))
  stubRet : L.stubRet = s.rip + BitVec.ofNat 64 (bytes C (stubHead C))
  main : CodeAt C p (mainAddr C) (gen C (mainAddr C) main)
  r14 : s.regs.get .r14 = L.buf
  rbx : s.regs.get .rbx = L.cb
  r12 : s.regs.get .r12 = L.env0
  rsp : s.regs.get .rsp = L.rsp0
  ret : rd s.mem L.rsp0 = L.ret0
  cb16 : rd s.mem (L.cb + 16) = L.envLo
  cb24 : rd s.mem (L.cb + 24) = L.stkLo
  rep : VIRBridge.Rep wm s.mem L.live
  words : WordsAt s.mem L.env0 ρ₀
  hi : L.env0.toNat + 8 * ρ₀.length ≤ L.envTop.toNat
  stk : L.stkLo.toNat + 16 ≤ L.rsp0.toNat

/-- **entry_r3.** Three steps of the entry stub reach main as the R3 state `run main ρ₀ []`. -/
theorem entry_r3 {C : Ctx3} {p : Program} {L : Lay3} (E : StepEnv C p L) {main : WCode} {ρ₀ : List W} {wm : WMem} {s : Cpu}
    (hE : Entry C p L main ρ₀ wm s) :
    R3 C p L (.run main ρ₀ [], wm) (runP p 3 s) := by
  have hmain := hE.main
  have hL := E.ok
  have c0 : CodeAt C p s.rip (st .rbx 8 .rsp :: .op (.push .q (.reg .r12)) :: .callA (mainAddr C) :: stubCont) := by
    have := hE.rip; rw [entryStub_eq] at this; simpa [stubHead] using this
  have e1 := stepP_st hE.stopped c0
  set u1 := stepP p s with hu1
  have h1 : u1.stopped = false := by rw [e1]; exact hE.stopped
  have c1 := codeAt_next (s' := u1) (by rw [e1]) c0
  have e2 := stepP_push h1 c1
  set u2 := stepP p u1 with hu2
  have h2 : u2.stopped = false := by rw [e2]; exact h1
  have c2 := codeAt_next (s' := u2) (by rw [e2]) c1
  have e3 := stepP_callA h2 c2 (canon_gen E (rest := []) (by simpa using hmain))
  set u3 := stepP p u2 with hu3
  have hR := L.rsp0.isLt
  have hst := hL.stk_nowrap
  have hstk := hE.stk
  have n8 : (L.rsp0 - 8).toNat = L.rsp0.toNat - 8 := by simp only [BitVec.toNat_sub]; simp; omega
  have n16 : (L.rsp0 - 8 - 8).toNat = L.rsp0.toNat - 16 := by simp only [BitVec.toNat_sub]; simp; omega
  have h8w : (8 : W).toNat = 8 := rfl
  have e88 : L.rsp0 - 8 - 8 + 8 = L.rsp0 - 8 := by
    apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_add, n16, n8, h8w]; omega
  -- the three writes
  have mem1 : u1.mem = s.mem.writeSize .q (L.cb + 8) L.rsp0 := by rw [e1]; simp [hE.rbx, hE.rsp]
  have sp1 : u1.regs.get .rsp = L.rsp0 := by rw [e1]; exact hE.rsp
  have mem2 : u2.mem = u1.mem.writeSize .q (L.rsp0 - 8) L.env0 := by
    rw [e2]; simp only [sp1]; rw [show u1.regs.get .r12 = L.env0 by rw [e1]; exact hE.r12]
  have sp2 : u2.regs.get .rsp = L.rsp0 - 8 := by rw [e2]; simp [sp1]
  have rip2 : u2.rip + 5 = L.stubRet := by
    rw [hE.stubRet, e2, e1]
    simp only [nxt, stubHead, st, bytes_cons, bytes_nil, AI.size, ofNat_add64, BitVec.add_assoc, Nat.add_zero]
    all_goals rfl
  have mem3 : u3.mem = u2.mem.writeSize .q (L.rsp0 - 8 - 8) L.stubRet := by rw [e3]; simp only [sp2, rip2]
  have sp3 : u3.regs.get .rsp = L.rsp0 - 8 - 8 := by rw [e3]; simp [sp2]
  have reg3 : ∀ r, r ≠ .rsp → u3.regs.get r = s.regs.get r := by
    intro r hr; rw [e3, e2, e1]; simp [Regs.get_set_ne _ _ _ _ (Ne.symm hr)]
  have w8 : ∀ j, j < 8 → inStk L (L.rsp0 - 8 + BitVec.ofNat 64 j) := stk_word L (by omega) (by omega) hL
  have w16 : ∀ j, j < 8 → inStk L (L.rsp0 - 8 - 8 + BitVec.ofNat 64 j) := stk_word L (by omega) (by omega) hL
  have hcbN := hL.cb_nowrap
  have cbw : ∀ m, m < 4 → ∀ k, k < 8 → inCb L (L.cb + BitVec.ofNat 64 (8 * m) + BitVec.ofNat 64 k) := fun m hm => cb_word L hm
  have a1m : ∀ m, m < 4 → m ≠ 1 → VIRBridge.Apart (L.cb + 8) (L.cb + BitVec.ofNat 64 (8 * m)) := by
    intro m hm hm1
    have := slot_apart (b := L.cb) (N := 4) (by omega) (i := 1) (j := m) (by decide) hm (Ne.symm hm1)
    simpa [slot] using this
  -- every word apart from the three written ones keeps its value
  have hmem : ∀ x, VIRBridge.Apart (L.cb + 8) x → VIRBridge.Apart (L.rsp0 - 8) x → VIRBridge.Apart (L.rsp0 - 8 - 8) x →
      rd u3.mem x = rd s.mem x := by
    intro x h1 h2 h3; rw [mem3, rd_write_apart _ _ _ _ h3, mem2, rd_write_apart _ _ _ _ h2, mem1, rd_write_apart _ _ _ _ h1]
  have cb8w : ∀ k, k < 8 → inCb L (L.cb + 8 + BitVec.ofNat 64 k) := fun k hk => by
    have := cbw 1 (by decide) k hk; simpa using this
  have ap_cb_stk : ∀ x : W, (∀ j, j < 8 → inStk L (x + BitVec.ofNat 64 j)) → VIRBridge.Apart (L.cb + 8) x :=
    fun x hx => apart_of_disjoint (fun a h1 h2 => hL.stk_cb a h2 h1) cb8w hx
  have stk_x : ∀ x : W, (∀ j, j < 8 → inStk L (x + BitVec.ofNat 64 j)) → ∀ y : W,
      (∀ j, j < 8 → ¬ inStk L (y + BitVec.ofNat 64 j)) → VIRBridge.Apart x y := by
    intro x hx y hy i j hi hj e; exact hy j hj (by rw [← e]; exact hx i hi)
  have cb_m : ∀ m, m < 4 → m ≠ 1 → rd u3.mem (L.cb + BitVec.ofNat 64 (8 * m)) = rd s.mem (L.cb + BitVec.ofNat 64 (8 * m)) := by
    intro m hm hm1
    have hy : ∀ j, j < 8 → ¬ inStk L (L.cb + BitVec.ofNat 64 (8 * m) + BitVec.ofNat 64 j) := fun j hj h => hL.stk_cb _ h (cbw m hm j hj)
    exact hmem _ (a1m m hm hm1) (stk_x _ w8 _ hy) (stk_x _ w16 _ hy)
  have env_x : ∀ x : W, L.envLo.toNat ≤ x.toNat → x.toNat + 8 ≤ L.envTop.toNat → rd u3.mem x = rd s.mem x := by
    intro x h1 h2
    have hx : ∀ j, j < 8 → inEnv L (x + BitVec.ofNat 64 j) := by
      intro j hj
      have : (x + BitVec.ofNat 64 j).toNat = x.toNat + j := by
        have := L.envTop.isLt; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
      simp only [inEnv, this]; omega
    have hy : ∀ j, j < 8 → ¬ inStk L (x + BitVec.ofNat 64 j) := fun j hj h => hL.env_stk _ (hx j hj) h
    exact hmem x (apart_of_disjoint hL.env_cb hx cb8w |>.symm') (stk_x _ w8 _ hy) (stk_x _ w16 _ hy)
  have hlo0 := hL.envlo_le_env0
  show R3 C p L _ u3
  refine ⟨by rw [e3]; exact h2, by rw [show u3.rip = mainAddr C by rw [e3]]; exact hmain,
    ⟨by rw [reg3 .r14 (by decide), hE.r14], by rw [reg3 .rbx (by decide), hE.rbx], ⟨?_, ?_, ?_⟩, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [mem3, rd_write_apart _ _ _ _ (ap_cb_stk _ w16).symm', mem2, rd_write_apart _ _ _ _ (ap_cb_stk _ w8).symm', mem1]
    exact rd_write_same _ _ _
  · rw [show L.cb + 16 = L.cb + BitVec.ofNat 64 (8 * 2) from rfl, cb_m 2 (by decide) (by decide)]; exact hE.cb16
  · rw [show L.cb + 24 = L.cb + BitVec.ofNat 64 (8 * 3) from rfl, cb_m 3 (by decide) (by decide)]; exact hE.cb24
  · intro x hx
    have hy : ∀ j, j < 8 → ¬ inStk L (x + BitVec.ofNat 64 j) := fun j hj h => hL.stk_live _ h (live_word L hx j hj)
    have h := hmem x (apart_of_disjoint hL.cb_live cb8w (live_word L hx)) (stk_x _ w8 _ hy) (stk_x _ w16 _ hy)
    simp only [rd] at h; rw [h]; exact hE.rep x hx
  · rw [reg3 .r12 (by decide), hE.r12]; exact hlo0
  · rw [reg3 .r12 (by decide), hE.r12]; exact hE.hi
  · rw [reg3 .r12 (by decide), hE.r12]
    intro j hj
    have hT := L.envTop.isLt
    have he : (L.env0 + BitVec.ofNat 64 (8 * j)).toNat = L.env0.toNat + 8 * j := by
      have := hE.hi; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    have := env_x (L.env0 + BitVec.ofNat 64 (8 * j)) (by omega) (by have := hE.hi; omega)
    simp only [rd] at this; rw [this]; exact hE.words j hj
  · rw [sp3, reg3 .r12 (by decide), hE.r12]
    refine ⟨?_, ?_, ?_, by rw [n16]; omega, ?_, le_refl _⟩
    · rw [mem3]; exact rd_write_same _ _ _
    · have := codeAt_right (a := stubHead C) (b := stubCont) (by rw [← entryStub_eq]; exact hE.rip)
      rw [← hE.stubRet] at this; exact this
    · rw [e88, mem3, rd_write_apart _ _ _ _ (order_apart (by rw [n16, n8]; omega) (by omega)), mem2]
      exact rd_write_same _ _ _
    · rw [mem3, rd_write_apart _ _ _ _ (order_apart (by rw [n16]; omega) (by omega)), mem2,
        rd_write_apart _ _ _ _ (order_apart (by rw [n8]; omega) (by omega)), mem1,
        rd_write_apart _ _ _ _ (ap_cb_stk _ (stk_word L hL.stk_lo_le (le_refl _) hL))]
      exact hE.ret
  · rw [sp3, n16]; omega
  · rw [reg3 .r12 (by decide), hE.r12]; simp only [kSize]; omega

/-- **s3_refines.** For a program placed by `StepEnv` and `TblOk`, entered as the driver establishes (`Entry`): a word run from
    `run main ρ₀ []` to Wf, with `StepOk` at every reached state, is matched by a machine run that reaches R3 at Wf in at least
    as many steps (plus the stub's 3), or returns RES at a reached state whose `ResWhy` holds. -/
theorem s3_refines {C : Ctx3} {p : Program} {L : Lay3} (E : StepEnv C p L) {tbl : Table} (hT : TblOk C p tbl)
    {main : WCode} {ρ₀ : List W} {wm : WMem} {s : Cpu} (hE : Entry C p L main ρ₀ wm s) {n : Nat} {Wf : WSt × WMem}
    (hrun : WN tbl n (.run main ρ₀ [], wm) Wf)
    (hok : ∀ k W₁, WN tbl k (.run main ρ₀ [], wm) W₁ → StepOk L W₁.1) :
    ∃ m, (n + 3 ≤ m ∧ R3 C p L Wf (runP p m s)) ∨
      (∃ Wr Wr' k, WN tbl k (.run main ρ₀ [], wm) Wr ∧ stepW tbl Wr = some Wr' ∧ ResWhy L Wr.1 ∧ ResExit L (runP p m s) ∧
        Common L Wr'.2 (runP p m s)) := by
  obtain ⟨m, hm⟩ := s3_run E hT hrun (runP p 3 s) (entry_r3 E hE) hok
  refine ⟨3 + m, ?_⟩
  rcases hm with ⟨hle, hR⟩ | ⟨Wr, Wr', k, h1, h2, h3, h4, h5⟩
  · exact Or.inl ⟨by omega, by rw [runP_add]; exact hR⟩
  · exact Or.inr ⟨Wr, Wr', k, h1, h2, h3, by rw [runP_add]; exact h4, by rw [runP_add]; exact h5⟩

end S3
