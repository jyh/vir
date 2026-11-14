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

/-! ## BUF slots, and `evalTo`'s `slice` case -/

/-- Distinct slots of a non-wrapping word region are apart. -/
theorem slot_apart {b : W} {N : Nat} (hN : b.toNat + 8 * N < 2 ^ 64) {i j : Nat} (hi : i < N) (hj : j < N) (hij : i ≠ j) :
    VIRBridge.Apart (b + slot i) (b + slot j) := by
  intro x y hx hy e
  have := congrArg BitVec.toNat e
  simp only [slot, BitVec.toNat_add, BitVec.toNat_ofNat] at this
  omega

theorem slice_eq_copyL (off t len : Nat) :
    ((List.range len).flatMap fun j => [ld .rax .r12 (slot (off + j)), st .r14 (slot (t + j)) .rax]) =
      copyL .r12 .r14 (fun j => slot (off + j)) (fun j => slot (t + j)) len := by
  induction len with
  | zero => rfl
  | succ n ih => rw [List.range_succ, List.flatMap_append, ih]; simp [copyL]

/-- **evalTo, slice.** `slice off len` at BUF slot t copies ρ's words off … off+len−1 to slots t …, in 2·len steps, given each
    destination slot apart from each source word and BUF non-wrapping. -/
theorem evalTo_slice_run {C : Ctx3} {p : Program} {s : Cpu} {rest : List AI} {ρ : List W} {off t len N : Nat}
    (hs : s.stopped = false) (hc : CodeAt C p s.rip (evalTo C t (.slice off len) ++ rest))
    (hρ : WordsAt s.mem (s.regs.get .r12) ρ) (hlen : off + len ≤ ρ.length)
    (hN : (s.regs.get .r14).toNat + 8 * N < 2 ^ 64) (htN : t + len ≤ N)
    (hap : ∀ i j, i < len → j < len → VIRBridge.Apart (s.regs.get .r14 + slot (t + i)) (s.regs.get .r12 + slot (off + j))) :
    ∃ s', runP p (2 * len) s = s' ∧ s'.stopped = false ∧
      s'.rip = s.rip + BitVec.ofNat 64 (bytes C (evalTo C t (.slice off len))) ∧
      (∀ r, r ≠ .rax → s'.regs.get r = s.regs.get r) ∧ s'.flags = s.flags ∧
      WordsAt s'.mem (s.regs.get .r14 + slot t) ((ρ.drop off).take len) ∧
      (∀ a, (∀ j, j < len → VIRBridge.Apart (s.regs.get .r14 + slot (t + j)) a) → rd s'.mem a = rd s.mem a) := by
  simp only [evalTo, slice_eq_copyL] at hc ⊢
  obtain ⟨s', h1, h2, h3, h4, h5, h6, h7⟩ := copy_run (C := C) .r12 .r14 (by decide) (by decide) _ _ len s rest hs hc hap
    (fun i j hi hj hij => slot_apart hN (by omega) (by omega) (by omega))
  refine ⟨s', h1, h2, h3, h4, h5, ?_, h7⟩
  intro j hj
  simp only [List.length_take, List.length_drop] at hj
  have := h6 j (by omega)
  simp only [rd] at this
  rw [show s.regs.get .r14 + slot t + BitVec.ofNat 64 (8 * j) = s.regs.get .r14 + slot (t + j) by
    simp only [slot, BitVec.add_assoc, ← ofNat_add64]; congr 2; omega, this]
  have hw := hρ (off + j) (by omega)
  rw [show s.regs.get .r12 + slot (off + j) = s.regs.get .r12 + BitVec.ofNat 64 (8 * (off + j)) from rfl, hw]
  simp [List.getElem_take, List.getElem_drop]

/-! ## Checked arithmetic: x86's OF is S2's range check (`chk`) -/

theorem msb_q (v : W) : Value.msb .q v = v.msb := by
  simp [Value.msb, Size.signBit, BitVec.msb_eq_getLsbD_last]

theorem addOF_q (x y : W) : Flags.addOF .q x y (x + y) = BitVec.saddOverflow x y := by
  rw [BitVec.saddOverflow_eq]; simp only [Flags.addOF, msb_q]
  cases x.msb <;> cases y.msb <;> cases (x + y).msb <;> rfl

theorem subOF_q (x y : W) : Flags.subOF .q x y (x - y) = BitVec.ssubOverflow x y := by
  rw [BitVec.ssubOverflow_eq]; simp only [Flags.subOF, msb_q]
  cases x.msb <;> cases y.msb <;> cases (x - y).msb <;> rfl

theorem inRange_iff (n : Int) : inRange n = !((n ≥ 2 ^ 63) || (n < -2 ^ 63)) := by
  unfold inRange
  by_cases h : -2 ^ 63 ≤ n ∧ n < 2 ^ 63
  · rw [decide_eq_true h]
    have h1 : ¬ (n ≥ 2 ^ 63) := by omega
    have h2 : ¬ (n < -2 ^ 63) := by omega
    simp <;> omega
  · rw [decide_eq_false h]
    by_cases h1 : n ≥ 2 ^ 63
    · simp <;> omega
    · have h2 : n < -2 ^ 63 := by omega
      simp <;> omega

/-- S2's checked add is x86's add with OF as the overflow. -/
theorem chk_add (x y : W) : chk (x.toInt + y.toInt) = if BitVec.saddOverflow x y then .ovf else .ok [x + y] := by
  unfold chk
  have hr : inRange (x.toInt + y.toInt) = !BitVec.saddOverflow x y := by rw [inRange_iff]; rfl
  rw [hr]
  cases h : BitVec.saddOverflow x y
  · simp only [Bool.not_false, if_true]
    rw [← BitVec.toInt_add_of_not_saddOverflow (by simp [h]), BitVec.ofInt_toInt]
    simp
  · rfl

theorem chk_sub (x y : W) : chk (x.toInt - y.toInt) = if BitVec.ssubOverflow x y then .ovf else .ok [x - y] := by
  unfold chk
  have hr : inRange (x.toInt - y.toInt) = !BitVec.ssubOverflow x y := by rw [inRange_iff]; rfl
  rw [hr]
  cases h : BitVec.ssubOverflow x y
  · simp only [Bool.not_false, if_true]
    rw [← BitVec.toInt_sub_of_not_ssubOverflow (by simp [h]), BitVec.ofInt_toInt]
    simp
  · rfl

/-! ## Fetch-and-step for the register arithmetic forms and the conditional branch -/

theorem add_sub_self' (x a : W) : x + (a - x) = a := by rw [BitVec.add_comm, BitVec.sub_add_cancel]

theorem live_of {s : Cpu} (hs : s.stopped = false) : Live s := live_of_not_stopped (by simp [hs])

theorem stepP_add_rr {C : Ctx3} {p : Program} {s : Cpu} {r r' : GPR} {l : List AI}
    (hs : s.stopped = false) (hc : CodeAt C p s.rip (.op (.bin .add .q (.reg r) (.reg r')) :: l)) :
    stepP p s = { s with regs := s.regs.set r (s.regs.get r + s.regs.get r'), flags := Flags.add .q (s.regs.get r) (s.regs.get r') s.flags, rip := nxt C s.rip (.op (.bin .add .q (.reg r) (.reg r'))) } := by
  rw [stepP_of_at hs (codeAt_head hc)]
  simp only [AI.toInstr]
  rw [step_add_reg_reg .q r r' (live_of hs)]
  simp [Value.writeView, Flags.addResult, Cpu.getReg, nxt, AI.size]

theorem stepP_sub_rr {C : Ctx3} {p : Program} {s : Cpu} {r r' : GPR} {l : List AI}
    (hs : s.stopped = false) (hc : CodeAt C p s.rip (.op (.bin .sub .q (.reg r) (.reg r')) :: l)) :
    stepP p s = { s with regs := s.regs.set r (s.regs.get r - s.regs.get r'), flags := Flags.sub .q (s.regs.get r) (s.regs.get r') s.flags, rip := nxt C s.rip (.op (.bin .sub .q (.reg r) (.reg r'))) } := by
  rw [stepP_of_at hs (codeAt_head hc)]
  simp only [AI.toInstr]
  rw [step_sub_reg_reg .q r r' (live_of hs)]
  simp [Value.writeView, Flags.subResult, Cpu.getReg, nxt, AI.size]

theorem stepP_cmp_rr {C : Ctx3} {p : Program} {s : Cpu} {r r' : GPR} {l : List AI}
    (hs : s.stopped = false) (hc : CodeAt C p s.rip (.op (.bin .cmp .q (.reg r) (.reg r')) :: l)) :
    stepP p s = { s with flags := Flags.sub .q (s.regs.get r) (s.regs.get r') s.flags, rip := nxt C s.rip (.op (.bin .cmp .q (.reg r) (.reg r'))) } := by
  rw [stepP_of_at hs (codeAt_head hc)]
  simp only [AI.toInstr]
  rw [step_cmp_reg_reg .q r r' (live_of hs)]
  simp [Cpu.getReg, nxt, AI.size]

theorem stepP_setcc {C : Ctx3} {p : Program} {s : Cpu} {c : Cc} {r : GPR} {l : List AI}
    (hs : s.stopped = false) (hc : CodeAt C p s.rip (.op (.setcc c (.reg r)) :: l)) :
    stepP p s = { s with regs := s.regs.set r (Value.writeView .b (s.regs.get r) (if c.eval s.flags then 1 else 0)), rip := nxt C s.rip (.op (.setcc c (.reg r))) } := by
  rw [stepP_of_at hs (codeAt_head hc)]
  simp only [AI.toInstr]
  rw [step_setcc_reg c r (live_of hs)]
  simp [nxt, AI.size]

/-- `jccA c a`: to `a` when `c` holds, else the next instruction. The target is canonical (a layout fact). -/
theorem stepP_jccA {C : Ctx3} {p : Program} {s : Cpu} {c : Cc} {a : W} {l : List AI}
    (hs : s.stopped = false) (hc : CodeAt C p s.rip (.jccA c a :: l)) (hcan : canonical a = true) :
    stepP p s = { s with rip := if c.eval s.flags then a else s.rip + 6 } := by
  rw [stepP_of_at hs (codeAt_head hc)]
  simp only [AI.toInstr]
  rw [step_jcc c _ (live_of hs) (fun _ => by
    have e : s.rip + 6#64 + (a - (s.rip + 6)) = a := by bv_omega
    rw [e]; exact hcan)]
  by_cases he : c.eval s.flags <;> simp [he, add_sub_self']

/-! ## The checked add block -/

theorem eval_o_add (x y : W) (f : Flags) : Cc.eval .o (Flags.add .q x y f) = BitVec.saddOverflow x y := by
  simp [Cc.eval, Flags.add, Flags.addResult, addOF_q]

/-- **arith_add_run.** With BUF slots t and t+1 holding x and y: on signed overflow the block reaches OVF in 4 steps with memory
    untouched; otherwise in 5 steps slot t holds `x + y`, and every word apart from slot t keeps its value. Among the registers
    only rax and rcx change. -/
theorem arith_add_run {C : Ctx3} {p : Program} {s : Cpu} {t : Nat} {x y : W} {rest : List AI}
    (hs : s.stopped = false) (hc : CodeAt C p s.rip (arithCode C t .add ++ rest)) (hcan : canonical C.ovf = true)
    (hx : rd s.mem (s.regs.get .r14 + slot t) = x) (hy : rd s.mem (s.regs.get .r14 + slot (t + 1)) = y) :
    (BitVec.saddOverflow x y = true → ∃ u, runP p 4 s = u ∧ u.stopped = false ∧ u.rip = C.ovf ∧ u.mem = s.mem ∧
        ∀ r, r ≠ .rax → r ≠ .rcx → u.regs.get r = s.regs.get r) ∧
    (BitVec.saddOverflow x y = false → ∃ u, runP p 5 s = u ∧ u.stopped = false ∧
        u.rip = s.rip + BitVec.ofNat 64 (bytes C (arithCode C t .add)) ∧
        rd u.mem (s.regs.get .r14 + slot t) = x + y ∧
        (∀ a, VIRBridge.Apart (s.regs.get .r14 + slot t) a → rd u.mem a = rd s.mem a) ∧
        ∀ r, r ≠ .rax → r ≠ .rcx → u.regs.get r = s.regs.get r) := by
  have c0 : CodeAt C p s.rip (ld .rax .r14 (slot t) :: ld .rcx .r14 (slot (t + 1)) ::
      .op (.bin .add .q (.reg .rax) (.reg .rcx)) :: .jccA .o C.ovf :: st .r14 (slot t) .rax :: rest) := by
    simpa [arithCode] using hc
  have e1 := stepP_ld hs c0
  set s1 := stepP p s
  have h1 : s1.stopped = false := by rw [e1]; exact hs
  have c1 : CodeAt C p s1.rip (ld .rcx .r14 (slot (t + 1)) ::
      .op (.bin .add .q (.reg .rax) (.reg .rcx)) :: .jccA .o C.ovf :: st .r14 (slot t) .rax :: rest) := by
    rw [e1]; exact codeAt_tail c0
  have e2 := stepP_ld h1 c1
  set s2 := stepP p s1
  have h2 : s2.stopped = false := by rw [e2]; exact h1
  have c2 : CodeAt C p s2.rip (.op (.bin .add .q (.reg .rax) (.reg .rcx)) :: .jccA .o C.ovf :: st .r14 (slot t) .rax :: rest) := by
    rw [e2]; exact codeAt_tail c1
  have e3 := stepP_add_rr h2 c2
  set s3 := stepP p s2
  have h3 : s3.stopped = false := by rw [e3]; exact h2
  have c3 : CodeAt C p s3.rip (.jccA .o C.ovf :: st .r14 (slot t) .rax :: rest) := by
    rw [e3]; exact codeAt_tail c2
  have e4 := stepP_jccA h3 c3 hcan
  set s4 := stepP p s3
  have r14_2 : s2.regs.get .r14 = s.regs.get .r14 := by rw [e2, e1]; simp
  have rax2 : s2.regs.get .rax = x := by rw [e2, e1]; simp [hx]
  have rcx2 : s2.regs.get .rcx = y := by rw [e2]; simp [e1, hy]
  have hfl : Cc.eval .o s3.flags = BitVec.saddOverflow x y := by rw [e3]; simp only [rax2, rcx2, eval_o_add]
  have run4 : runP p 4 s = s4 := rfl
  have mem3 : s3.mem = s.mem := by rw [e3, e2, e1]
  have regs3 : ∀ r, r ≠ .rax → r ≠ .rcx → s3.regs.get r = s.regs.get r := by
    intro r ha hc'; rw [e3, e2, e1]; simp [Regs.get_set_ne _ _ _ _ (Ne.symm ha), Regs.get_set_ne _ _ _ _ (Ne.symm hc')]
  constructor
  · intro hov
    refine ⟨s4, run4, by rw [e4]; exact h3, by rw [e4]; simp [hfl, hov], by rw [e4]; exact mem3, ?_⟩
    intro r ha hc'; rw [e4]; exact regs3 r ha hc'
  · intro hov
    have h4 : s4.stopped = false := by rw [e4]; exact h3
    have rip4 : s4.rip = s3.rip + 6 := by rw [e4]; simp [hfl, hov]
    have c4 : CodeAt C p s4.rip (st .r14 (slot t) .rax :: rest) := by
      rw [rip4]; have := codeAt_tail c3; simpa [AI.size] using this
    have e5 := stepP_st h4 c4
    have r14_4 : s4.regs.get .r14 = s.regs.get .r14 := by rw [e4]; exact regs3 .r14 (by decide) (by decide)
    have rax4 : s4.regs.get .rax = x + y := by rw [e4, e3]; simp [rax2, rcx2]
    refine ⟨stepP p s4, rfl, by rw [e5]; exact h4, ?_, ?_, ?_, ?_⟩
    · rw [e5, rip4, e3, e2, e1]
      simp only [nxt, arithCode, ld, st, bytes_cons, bytes_nil, AI.size, ofNat_add64, BitVec.add_assoc, Nat.add_zero]
      all_goals bv_omega
    · rw [e5, r14_4, rax4]; simp only [show s4.mem = s.mem by rw [e4]; exact mem3]; exact rd_write_same _ _ _
    · intro a ha; rw [e5, r14_4, show s4.mem = s.mem by rw [e4]; exact mem3]; exact rd_write_apart _ _ _ _ ha
    · intro r ha hc'; rw [e5]; rw [e4]; exact regs3 r ha hc'

/-! ## The checked sub block (the add block's proof, with sub's lemmas) -/

theorem eval_o_sub (x y : W) (f : Flags) : Cc.eval .o (Flags.sub .q x y f) = BitVec.ssubOverflow x y := by
  simp [Cc.eval, Flags.sub, Flags.subResult, subOF_q]

/-- **arith_sub_run.** With BUF slots t and t+1 holding x and y: on signed overflow the block reaches OVF in 4 steps with memory
    untouched; otherwise in 5 steps slot t holds `x - y`, and every word apart from slot t keeps its value. Among the registers
    only rax and rcx change. -/
theorem arith_sub_run {C : Ctx3} {p : Program} {s : Cpu} {t : Nat} {x y : W} {rest : List AI}
    (hs : s.stopped = false) (hc : CodeAt C p s.rip (arithCode C t .sub ++ rest)) (hcan : canonical C.ovf = true)
    (hx : rd s.mem (s.regs.get .r14 + slot t) = x) (hy : rd s.mem (s.regs.get .r14 + slot (t + 1)) = y) :
    (BitVec.ssubOverflow x y = true → ∃ u, runP p 4 s = u ∧ u.stopped = false ∧ u.rip = C.ovf ∧ u.mem = s.mem ∧
        ∀ r, r ≠ .rax → r ≠ .rcx → u.regs.get r = s.regs.get r) ∧
    (BitVec.ssubOverflow x y = false → ∃ u, runP p 5 s = u ∧ u.stopped = false ∧
        u.rip = s.rip + BitVec.ofNat 64 (bytes C (arithCode C t .sub)) ∧
        rd u.mem (s.regs.get .r14 + slot t) = x - y ∧
        (∀ a, VIRBridge.Apart (s.regs.get .r14 + slot t) a → rd u.mem a = rd s.mem a) ∧
        ∀ r, r ≠ .rax → r ≠ .rcx → u.regs.get r = s.regs.get r) := by
  have c0 : CodeAt C p s.rip (ld .rax .r14 (slot t) :: ld .rcx .r14 (slot (t + 1)) ::
      .op (.bin .sub .q (.reg .rax) (.reg .rcx)) :: .jccA .o C.ovf :: st .r14 (slot t) .rax :: rest) := by
    simpa [arithCode] using hc
  have e1 := stepP_ld hs c0
  set s1 := stepP p s
  have h1 : s1.stopped = false := by rw [e1]; exact hs
  have c1 : CodeAt C p s1.rip (ld .rcx .r14 (slot (t + 1)) ::
      .op (.bin .sub .q (.reg .rax) (.reg .rcx)) :: .jccA .o C.ovf :: st .r14 (slot t) .rax :: rest) := by
    rw [e1]; exact codeAt_tail c0
  have e2 := stepP_ld h1 c1
  set s2 := stepP p s1
  have h2 : s2.stopped = false := by rw [e2]; exact h1
  have c2 : CodeAt C p s2.rip (.op (.bin .sub .q (.reg .rax) (.reg .rcx)) :: .jccA .o C.ovf :: st .r14 (slot t) .rax :: rest) := by
    rw [e2]; exact codeAt_tail c1
  have e3 := stepP_sub_rr h2 c2
  set s3 := stepP p s2
  have h3 : s3.stopped = false := by rw [e3]; exact h2
  have c3 : CodeAt C p s3.rip (.jccA .o C.ovf :: st .r14 (slot t) .rax :: rest) := by
    rw [e3]; exact codeAt_tail c2
  have e4 := stepP_jccA h3 c3 hcan
  set s4 := stepP p s3
  have r14_2 : s2.regs.get .r14 = s.regs.get .r14 := by rw [e2, e1]; simp
  have rax2 : s2.regs.get .rax = x := by rw [e2, e1]; simp [hx]
  have rcx2 : s2.regs.get .rcx = y := by rw [e2]; simp [e1, hy]
  have hfl : Cc.eval .o s3.flags = BitVec.ssubOverflow x y := by rw [e3]; simp only [rax2, rcx2, eval_o_sub]
  have run4 : runP p 4 s = s4 := rfl
  have mem3 : s3.mem = s.mem := by rw [e3, e2, e1]
  have regs3 : ∀ r, r ≠ .rax → r ≠ .rcx → s3.regs.get r = s.regs.get r := by
    intro r ha hc'; rw [e3, e2, e1]; simp [Regs.get_set_ne _ _ _ _ (Ne.symm ha), Regs.get_set_ne _ _ _ _ (Ne.symm hc')]
  constructor
  · intro hov
    refine ⟨s4, run4, by rw [e4]; exact h3, by rw [e4]; simp [hfl, hov], by rw [e4]; exact mem3, ?_⟩
    intro r ha hc'; rw [e4]; exact regs3 r ha hc'
  · intro hov
    have h4 : s4.stopped = false := by rw [e4]; exact h3
    have rip4 : s4.rip = s3.rip + 6 := by rw [e4]; simp [hfl, hov]
    have c4 : CodeAt C p s4.rip (st .r14 (slot t) .rax :: rest) := by
      rw [rip4]; have := codeAt_tail c3; simpa [AI.size] using this
    have e5 := stepP_st h4 c4
    have r14_4 : s4.regs.get .r14 = s.regs.get .r14 := by rw [e4]; exact regs3 .r14 (by decide) (by decide)
    have rax4 : s4.regs.get .rax = x - y := by rw [e4, e3]; simp [rax2, rcx2]
    refine ⟨stepP p s4, rfl, by rw [e5]; exact h4, ?_, ?_, ?_, ?_⟩
    · rw [e5, rip4, e3, e2, e1]
      simp only [nxt, arithCode, ld, st, bytes_cons, bytes_nil, AI.size, ofNat_add64, BitVec.add_assoc, Nat.add_zero]
      all_goals bv_omega
    · rw [e5, r14_4, rax4]; simp only [show s4.mem = s.mem by rw [e4]; exact mem3]; exact rd_write_same _ _ _
    · intro a ha; rw [e5, r14_4, show s4.mem = s.mem by rw [e4]; exact mem3]; exact rd_write_apart _ _ _ _ ha
    · intro r ha hc'; rw [e5]; rw [e4]; exact regs3 r ha hc'

/-! ## Signed comparison: the `l`, `le`, `e` conditions after `cmp` are S2's `<`, `≤`, `=` on `toInt` (no `bv_decide`: it would
    add `Lean.ofReduceBool` to the axioms) -/

theorem toInt_bounds (x : W) : -2 ^ 63 ≤ x.toInt ∧ x.toInt < 2 ^ 63 :=
  ⟨by have := BitVec.le_toInt x; simpa using this, by have := BitVec.toInt_lt (x := x); simpa using this⟩

theorem cc_l_sub (x y : W) (f : Flags) : Cc.eval .l (Flags.sub .q x y f) = decide (x.toInt < y.toInt) := by
  obtain ⟨hx1, hx2⟩ := toInt_bounds x
  obtain ⟨hy1, hy2⟩ := toInt_bounds y
  simp only [Cc.eval, Flags.sub, Flags.fromResult, Flags.subResult, Value.trunc_q, subOF_q, msb_q, BitVec.ssubOverflow,
    BitVec.msb_eq_toInt, BitVec.toInt_sub, Int.bmod_def]
  rw [Bool.eq_iff_iff]
  simp only [bne_iff_ne, ne_eq, decide_eq_true_eq, ← Bool.decide_or, decide_eq_decide]
  split <;> omega

theorem sub_zero_iff (x y : W) : Value.isZero .q (Flags.subResult .q x y) = decide (x = y) := by
  simp only [Value.isZero, Flags.subResult, Value.trunc_q]
  by_cases h : x = y
  · subst h; simp
  · have : x - y ≠ 0 := fun e => h (by rw [← BitVec.sub_add_cancel x y, e]; simp)
    simpa [h] using this

theorem cc_e_sub (x y : W) (f : Flags) : Cc.eval .e (Flags.sub .q x y f) = decide (x = y) := by
  simp only [Cc.eval, Flags.sub, Flags.fromResult]; exact sub_zero_iff x y

theorem cc_le_sub (x y : W) (f : Flags) : Cc.eval .le (Flags.sub .q x y f) = decide (x.toInt ≤ y.toInt) := by
  have hl := cc_l_sub x y f
  simp only [Cc.eval] at hl ⊢
  have he : (Flags.sub .q x y f).zf = decide (x = y) := by simp only [Flags.sub, Flags.fromResult]; exact sub_zero_iff x y
  rw [he, hl]
  rw [Bool.eq_iff_iff]
  simp only [Bool.or_eq_true, decide_eq_true_eq]
  constructor
  · rintro (h | h)
    · subst h; omega
    · omega
  · intro h
    by_cases h' : x.toInt < y.toInt
    · exact Or.inr h'
    · exact Or.inl (BitVec.toInt_inj.mp (by omega))

/-- setcc into a zeroed register leaves exactly the condition's 0/1. -/
theorem writeView_b_zero (b : Bool) : Value.writeView .b 0 (if b then 1 else 0) = boolW b := by
  cases b <;> rfl

/-! ## The comparison blocks (lt, le, eq): one lemma, the condition's bridge as a premise -/

/-- The comparison block for condition `c`, whatever its operator. -/
def cmpBlock (t : Nat) (c : Cc) : List AI :=
  [movi .rdx 0, ld .rax .r14 (slot t), ld .rcx .r14 (slot (t + 1)), .op (.bin .cmp .q (.reg .rax) (.reg .rcx)),
   .op (.setcc c (.reg .rdx)), st .r14 (slot t) .rdx]

theorem arithCode_lt (C : Ctx3) (t : Nat) : arithCode C t .lt = cmpBlock t .l := rfl
theorem arithCode_le (C : Ctx3) (t : Nat) : arithCode C t .le = cmpBlock t .le := rfl
theorem arithCode_eq (C : Ctx3) (t : Nat) : arithCode C t .eq = cmpBlock t .e := rfl

/-- **cmp_run.** With slots t, t+1 holding x, y and `c`'s condition after `cmp x, y` equal to b, the block leaves `boolW b` at
    slot t in 6 steps; words apart from slot t keep their value; among the registers only rax, rcx and rdx change. -/
theorem cmp_run {C : Ctx3} {p : Program} {s : Cpu} {t : Nat} {c : Cc} {x y : W} {b : Bool} {rest : List AI}
    (hs : s.stopped = false) (hc : CodeAt C p s.rip (cmpBlock t c ++ rest))
    (hx : rd s.mem (s.regs.get .r14 + slot t) = x) (hy : rd s.mem (s.regs.get .r14 + slot (t + 1)) = y)
    (hb : ∀ f, Cc.eval c (Flags.sub .q x y f) = b) :
    ∃ u, runP p 6 s = u ∧ u.stopped = false ∧ u.rip = s.rip + BitVec.ofNat 64 (bytes C (cmpBlock t c)) ∧
      rd u.mem (s.regs.get .r14 + slot t) = boolW b ∧
      (∀ a, VIRBridge.Apart (s.regs.get .r14 + slot t) a → rd u.mem a = rd s.mem a) ∧
      ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → u.regs.get r = s.regs.get r := by
  have c0 : CodeAt C p s.rip (movi .rdx 0 :: ld .rax .r14 (slot t) :: ld .rcx .r14 (slot (t + 1)) ::
      .op (.bin .cmp .q (.reg .rax) (.reg .rcx)) :: .op (.setcc c (.reg .rdx)) :: st .r14 (slot t) .rdx :: rest) := by
    simpa [cmpBlock] using hc
  have e1 := stepP_movi hs c0
  set s1 := stepP p s
  have h1 : s1.stopped = false := by rw [e1]; exact hs
  have c1 : CodeAt C p s1.rip (ld .rax .r14 (slot t) :: ld .rcx .r14 (slot (t + 1)) ::
      .op (.bin .cmp .q (.reg .rax) (.reg .rcx)) :: .op (.setcc c (.reg .rdx)) :: st .r14 (slot t) .rdx :: rest) := by
    rw [e1]; exact codeAt_tail c0
  have e2 := stepP_ld h1 c1
  set s2 := stepP p s1
  have h2 : s2.stopped = false := by rw [e2]; exact h1
  have c2 : CodeAt C p s2.rip (ld .rcx .r14 (slot (t + 1)) ::
      .op (.bin .cmp .q (.reg .rax) (.reg .rcx)) :: .op (.setcc c (.reg .rdx)) :: st .r14 (slot t) .rdx :: rest) := by
    rw [e2]; exact codeAt_tail c1
  have e3 := stepP_ld h2 c2
  set s3 := stepP p s2
  have h3 : s3.stopped = false := by rw [e3]; exact h2
  have c3 : CodeAt C p s3.rip (.op (.bin .cmp .q (.reg .rax) (.reg .rcx)) :: .op (.setcc c (.reg .rdx)) ::
      st .r14 (slot t) .rdx :: rest) := by
    rw [e3]; exact codeAt_tail c2
  have e4 := stepP_cmp_rr h3 c3
  set s4 := stepP p s3
  have h4 : s4.stopped = false := by rw [e4]; exact h3
  have c4 : CodeAt C p s4.rip (.op (.setcc c (.reg .rdx)) :: st .r14 (slot t) .rdx :: rest) := by
    rw [e4]; exact codeAt_tail c3
  have e5 := stepP_setcc h4 c4
  set s5 := stepP p s4
  have h5 : s5.stopped = false := by rw [e5]; exact h4
  have c5 : CodeAt C p s5.rip (st .r14 (slot t) .rdx :: rest) := by rw [e5]; exact codeAt_tail c4
  have e6 := stepP_st h5 c5
  have mem5 : s5.mem = s.mem := by rw [e5, e4, e3, e2, e1]
  have regs5 : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → s5.regs.get r = s.regs.get r := by
    intro r ha hc' hd; rw [e5, e4, e3, e2, e1]
    simp [Regs.get_set_ne _ _ _ _ (Ne.symm ha), Regs.get_set_ne _ _ _ _ (Ne.symm hc'), Regs.get_set_ne _ _ _ _ (Ne.symm hd)]
  have r14_2 : s2.regs.get .r14 = s.regs.get .r14 := by rw [e2, e1]; simp
  have rax3 : s3.regs.get .rax = x := by rw [e3, e2]; simp [e1, hx]
  have rcx3 : s3.regs.get .rcx = y := by rw [e3]; simp [r14_2, e2, e1, hy]
  have rdx3 : s3.regs.get .rdx = 0 := by rw [e3, e2, e1]; simp
  have rdx5 : s5.regs.get .rdx = boolW b := by
    rw [e5]; simp only [Regs.get_set_same]
    rw [show s4.regs = s3.regs by rw [e4], rdx3, show s4.flags = Flags.sub .q (s3.regs.get .rax) (s3.regs.get .rcx) s3.flags by
      rw [e4], rax3, rcx3, hb]
    exact writeView_b_zero b
  have r14_5 : s5.regs.get .r14 = s.regs.get .r14 := regs5 .r14 (by decide) (by decide) (by decide)
  refine ⟨stepP p s5, rfl, by rw [e6]; exact h5, ?_, ?_, ?_, ?_⟩
  · rw [e6, e5, e4, e3, e2, e1]
    simp only [nxt, cmpBlock, movi, ld, st, bytes_cons, bytes_nil, AI.size, ofNat_add64, BitVec.add_assoc, Nat.add_zero]
  · rw [e6, r14_5, rdx5, mem5]; exact rd_write_same _ _ _
  · intro a ha; rw [e6, r14_5, mem5]; exact rd_write_apart _ _ _ _ ha
  · intro r ha hc' hd; rw [e6]; exact regs5 r ha hc' hd

end S3
