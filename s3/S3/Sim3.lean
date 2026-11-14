/-
  O95 compiler S3 (compiler/DECLARATIONS-S3.md): one word step ↔ a run of the lowered code, by x86lean's step lemmas and C3's
  block and call lemmas, cited, never re-proved. Part 1: fetch-and-step for each straight-line `AI` form under `CodeAt`.
-/
import S3.Rel3
import X86.Effects

namespace S3
open VIRC X86

theorem codeAt_head {C : Ctx3} {p : Program} {pc : W} {i : AI} {l : List AI} (h : CodeAt C p pc (i :: l)) :
    p.at? pc = some (i.toInstr C pc) := by
  have := h 0 (by simp)
  simpa [addrAt, bytes_nil] using this

theorem codeAt_tail {C : Ctx3} {p : Program} {pc : W} {i : AI} {l : List AI} (h : CodeAt C p pc (i :: l)) :
    CodeAt C p (pc + BitVec.ofNat 64 (AI.size C i)) l := by
  have := codeAt_right (a := [i]) (b := l) h
  simpa [bytes_cons, bytes_nil] using this

theorem addr_base (b : GPR) (d : W) (s : Cpu) (nr : W) :
    ({ base := some b, disp := d } : Ea).addr s nr = s.regs.get b + d := by
  simp [Ea.addr, Ea.offset]

/-- The next state's `rip` after a straight-line AI at `pc`. -/
abbrev nxt (C : Ctx3) (pc : W) (i : AI) : W := pc + BitVec.ofNat 64 (AI.size C i)

/-- `ld r b d`: r := the quadword at `b + d`. -/
theorem stepP_ld {C : Ctx3} {p : Program} {s : Cpu} {r b : GPR} {d : W} {l : List AI}
    (hs : s.stopped = false) (hc : CodeAt C p s.rip (ld r b d :: l)) :
    stepP p s = { s with regs := s.regs.set r (rd s.mem (s.regs.get b + d)), rip := nxt C s.rip (ld r b d) } := by
  rw [stepP_of_at hs (codeAt_head hc)]
  simp only [ld, AI.toInstr, memAt]
  rw [step_mov_reg_mem .q r _ (live_of_not_stopped (by simp [hs])) rfl]
  simp [Ea.offset, Value.writeView, Mem.readSize, Size.bytes, rd, nxt, AI.size]

/-- `st b d r`: the quadword at `b + d` := r. -/
theorem stepP_st {C : Ctx3} {p : Program} {s : Cpu} {r b : GPR} {d : W} {l : List AI}
    (hs : s.stopped = false) (hc : CodeAt C p s.rip (st b d r :: l)) :
    stepP p s = { s with mem := s.mem.writeSize .q (s.regs.get b + d) (s.regs.get r), rip := nxt C s.rip (st b d r) } := by
  rw [stepP_of_at hs (codeAt_head hc)]
  simp only [st, AI.toInstr, memAt]
  rw [step_mov_mem_reg .q _ r (live_of_not_stopped (by simp [hs])) rfl]
  simp [Ea.offset, Cpu.getReg, nxt, AI.size]

/-- `movi r v`: r := v. -/
theorem stepP_movi {C : Ctx3} {p : Program} {s : Cpu} {r : GPR} {v : W} {l : List AI}
    (hs : s.stopped = false) (hc : CodeAt C p s.rip (movi r v :: l)) :
    stepP p s = { s with regs := s.regs.set r v, rip := nxt C s.rip (movi r v) } := by
  rw [stepP_of_at hs (codeAt_head hc)]
  simp only [movi, AI.toInstr]
  rw [step_mov_reg_imm .q r v (live_of_not_stopped (by simp [hs]))]
  simp [Value.writeView, Value.trunc_q, nxt, AI.size]

end S3
