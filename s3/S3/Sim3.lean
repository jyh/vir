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

theorem _root_.VIRBridge.Apart.symm' {a b : W} (h : VIRBridge.Apart a b) : VIRBridge.Apart b a :=
  fun i j hi hj e => h j i hj hi e.symm

/-! ## Word copies: `slice`, and every static prepend, are lists of (ld rax, st) pairs -/

theorem rd_write_same (m : Mem) (a v : W) : rd (m.writeSize .q a v) a = v := VIRBridge.readN_writeN m a v
theorem rd_write_apart (m : Mem) (a b v : W) (h : VIRBridge.Apart a b) : rd (m.writeSize .q a v) b = rd m b :=
  VIRBridge.readN_writeN_apart m a b v h

/-- n copies: word j from `[sb + f j]` to `[db + g j]` through rax. -/
def copyL (sb db : GPR) (f g : Nat → W) : Nat → List AI
  | 0 => []
  | n + 1 => copyL sb db f g n ++ [ld .rax sb (f n), st db (g n) .rax]

/-- **copy_run.** n copies run in 2n steps. Afterwards every destination word holds its source word as it was BEFORE the
    copies, provided every destination span is apart from every source span and distinct destinations are apart. Words apart
    from every destination keep their value. Only rax and rip change among the registers; the flags do not change. -/
theorem copy_run {C : Ctx3} {p : Program} (sb db : GPR) (hsb : sb ≠ .rax) (hdb : db ≠ .rax) (f g : Nat → W) :
    ∀ (n : Nat) (s : Cpu) (rest : List AI), s.stopped = false → CodeAt C p s.rip (copyL sb db f g n ++ rest) →
    (∀ i j, i < n → j < n → VIRBridge.Apart (s.regs.get db + g i) (s.regs.get sb + f j)) →
    (∀ i j, i < n → j < n → i ≠ j → VIRBridge.Apart (s.regs.get db + g i) (s.regs.get db + g j)) →
    ∃ s', runP p (2 * n) s = s' ∧ s'.stopped = false ∧ s'.rip = s.rip + BitVec.ofNat 64 (bytes C (copyL sb db f g n)) ∧
      (∀ r, r ≠ .rax → s'.regs.get r = s.regs.get r) ∧ s'.flags = s.flags ∧
      (∀ j, j < n → rd s'.mem (s.regs.get db + g j) = rd s.mem (s.regs.get sb + f j)) ∧
      (∀ a, (∀ j, j < n → VIRBridge.Apart (s.regs.get db + g j) a) → rd s'.mem a = rd s.mem a)
  | 0, s, _, hs, _, _, _ => ⟨s, rfl, hs, by simp [copyL, bytes_nil], fun _ _ => rfl, rfl, fun _ h => absurd h (by omega),
      fun _ _ => rfl⟩
  | n + 1, s, rest, hs, hc, hap, hdd => by
    obtain ⟨u, hu, hus, hur, hureg, hufl, hucp, hufr⟩ := copy_run sb db hsb hdb f g n s
      ([ld .rax sb (f n), st db (g n) .rax] ++ rest) hs (by simpa [copyL, List.append_assoc] using hc)
      (fun i j hi hj => hap i j (by omega) (by omega)) (fun i j hi hj hij => hdd i j (by omega) (by omega) hij)
    have hcu : CodeAt C p u.rip (ld .rax sb (f n) :: st db (g n) .rax :: rest) := by
      rw [hur]; have := codeAt_right (a := copyL sb db f g n) (b := [ld .rax sb (f n), st db (g n) .rax] ++ rest)
        (by simpa [copyL, List.append_assoc] using hc)
      simpa using this
    have h1 := stepP_ld hus hcu
    set u1 := stepP p u with hu1
    have hu1s : u1.stopped = false := by rw [h1]; exact hus
    have hcu1 : CodeAt C p u1.rip (st db (g n) .rax :: rest) := by rw [h1]; exact codeAt_tail hcu
    have h2 := stepP_st hu1s hcu1
    refine ⟨stepP p u1, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [show 2 * (n + 1) = 2 * n + 2 by omega, runP_add, hu]
      simp [runP, hu1]
    · rw [h2]; exact hu1s
    · rw [h2, h1]
      simp only [hur, nxt, copyL, bytes_append, bytes_cons, bytes_nil, ofNat_add64, BitVec.add_assoc, Nat.add_zero]
    · intro r hr; rw [h2, h1]; simp [Regs.get_set_ne _ _ _ _ (Ne.symm hr), hureg r hr]
    · rw [h2, h1]; exact hufl
    · intro j hj
      have hdbu : u.regs.get db = s.regs.get db := hureg db hdb
      have hsbu : u.regs.get sb = s.regs.get sb := hureg sb hsb
      rw [h2, h1]
      simp only [Regs.get_set_ne _ _ _ _ (Ne.symm hdb), Regs.get_set_same]
      rw [hdbu]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | hj
      · rw [rd_write_apart _ _ _ _ (hdd n j (by omega) (by omega) (by omega)), hucp j hj]
      · subst hj
        rw [rd_write_same, hsbu, hufr _ (fun i hi => hap i j (by omega) (by omega))]
    · intro a ha
      have hdbu : u.regs.get db = s.regs.get db := hureg db hdb
      rw [h2, h1]
      simp only [Regs.get_set_ne _ _ _ _ (Ne.symm hdb), Regs.get_set_same]
      rw [hdbu, rd_write_apart _ _ _ _ (ha n (by omega)), hufr a (fun j hj => ha j (by omega))]

end S3
