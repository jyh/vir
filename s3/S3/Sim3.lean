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
    copies, provided each destination span is apart from every LATER source span (so an overlapping move DOWN qualifies) and distinct
    destinations are apart. Words apart
    from every destination keep their value. Only rax and rip change among the registers; the flags do not change. -/
theorem copy_run {C : Ctx3} {p : Program} (sb db : GPR) (hsb : sb ≠ .rax) (hdb : db ≠ .rax) (f g : Nat → W) :
    ∀ (n : Nat) (s : Cpu) (rest : List AI), s.stopped = false → CodeAt C p s.rip (copyL sb db f g n ++ rest) →
    (∀ i j, i < j → j < n → VIRBridge.Apart (s.regs.get db + g i) (s.regs.get sb + f j)) →
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
  obtain ⟨s', h1, h2, h3, h4, h5, h6, h7⟩ := copy_run (C := C) .r12 .r14 (by decide) (by decide) _ _ len s rest hs hc (fun i j hij hj => hap i j (by omega) hj)
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

/-! ## and, or, max -/

/-- CMOVcc r, r' (SDM Vol. 2A CMOVcc) at quadword width. x86lean states no cmov equation, so this one is proved here from
    `step` (a new instruction fact, not a C3 lemma; a candidate to move upstream). -/
theorem step_cmov_rr (c : Cc) (r r' : GPR) {s : Cpu} {len : Nat} (h : Live s) :
    step ⟨.cmov c .q r (.reg r'), len⟩ s =
      { s with regs := s.regs.set r (if c.eval s.flags then s.regs.get r' else s.regs.get r), rip := s.rip + BitVec.ofNat 64 len } := by
  by_cases he : c.eval s.flags <;>
    simp [step, h, he, Cpu.stopped, Cpu.setReg, Cpu.setRip, Cpu.readOperand, Cpu.getReg, Value.writeView]

theorem stepP_cmov {C : Ctx3} {p : Program} {s : Cpu} {c : Cc} {r r' : GPR} {l : List AI}
    (hs : s.stopped = false) (hc : CodeAt C p s.rip (.op (.cmov c .q r (.reg r')) :: l)) :
    stepP p s = { s with regs := s.regs.set r (if c.eval s.flags then s.regs.get r' else s.regs.get r), rip := nxt C s.rip (.op (.cmov c .q r (.reg r'))) } := by
  rw [stepP_of_at hs (codeAt_head hc)]
  simp only [AI.toInstr]
  rw [step_cmov_rr c r r' (live_of hs)]
  simp [nxt, AI.size]

theorem stepP_and_rr {C : Ctx3} {p : Program} {s : Cpu} {r r' : GPR} {l : List AI}
    (hs : s.stopped = false) (hc : CodeAt C p s.rip (.op (.bin .and .q (.reg r) (.reg r')) :: l)) :
    ∃ f o, stepP p s = { s with regs := s.regs.set r (s.regs.get r &&& s.regs.get r'), flags := f, oracle := o, rip := nxt C s.rip (.op (.bin .and .q (.reg r) (.reg r'))) } := by
  rw [stepP_of_at hs (codeAt_head hc)]
  simp only [AI.toInstr]
  rw [step_and_reg_reg .q r r' (live_of hs)]
  refine ⟨Flags.logic .q (s.regs.get r &&& s.regs.get r') (s.oracle.bits s.oracle.cursor) s.flags,
    { s.oracle with cursor := s.oracle.cursor + 1 }, ?_⟩
  simp [Value.writeView, Cpu.getReg, nxt, AI.size]

theorem stepP_or_rr {C : Ctx3} {p : Program} {s : Cpu} {r r' : GPR} {l : List AI}
    (hs : s.stopped = false) (hc : CodeAt C p s.rip (.op (.bin .or .q (.reg r) (.reg r')) :: l)) :
    ∃ f o, stepP p s = { s with regs := s.regs.set r (s.regs.get r ||| s.regs.get r'), flags := f, oracle := o, rip := nxt C s.rip (.op (.bin .or .q (.reg r) (.reg r'))) } := by
  rw [stepP_of_at hs (codeAt_head hc)]
  simp only [AI.toInstr]
  rw [step_or_reg_reg .q r r' (live_of hs)]
  refine ⟨Flags.logic .q (s.regs.get r ||| s.regs.get r') (s.oracle.bits s.oracle.cursor) s.flags,
    { s.oracle with cursor := s.oracle.cursor + 1 }, ?_⟩
  simp [Value.writeView, Cpu.getReg, nxt, AI.size]

/-! ## A generic block: load slots t, t+1 into rax, rcx; a middle segment leaves z in rax; store rax to slot t -/

/-- What a middle segment of `k` steps must do: from any state holding x, y in rax, rcx, reach the segment's end with z in rax,
    memory unchanged, and registers other than rax, rcx unchanged. -/
def MidOK (C : Ctx3) (p : Program) (mid : List AI) (k : Nat) (x y z : W) : Prop :=
  ∀ (u : Cpu) (rest : List AI), u.stopped = false → CodeAt C p u.rip (mid ++ rest) →
    u.regs.get .rax = x → u.regs.get .rcx = y →
    ∃ v, runP p k u = v ∧ v.stopped = false ∧ v.rip = u.rip + BitVec.ofNat 64 (bytes C mid) ∧ v.mem = u.mem ∧
      v.regs.get .rax = z ∧ ∀ r, r ≠ .rax → r ≠ .rcx → v.regs.get r = u.regs.get r

theorem binBlock_run {C : Ctx3} {p : Program} {s : Cpu} {t k : Nat} {mid : List AI} {x y z : W} {rest : List AI}
    (hs : s.stopped = false)
    (hc : CodeAt C p s.rip ([ld .rax .r14 (slot t), ld .rcx .r14 (slot (t + 1))] ++ mid ++ [st .r14 (slot t) .rax] ++ rest))
    (hx : rd s.mem (s.regs.get .r14 + slot t) = x) (hy : rd s.mem (s.regs.get .r14 + slot (t + 1)) = y)
    (hm : MidOK C p mid k x y z) :
    ∃ u, runP p (2 + k + 1) s = u ∧ u.stopped = false ∧
      u.rip = s.rip + BitVec.ofNat 64 (bytes C ([ld .rax .r14 (slot t), ld .rcx .r14 (slot (t + 1))] ++ mid ++
        [st .r14 (slot t) .rax])) ∧
      rd u.mem (s.regs.get .r14 + slot t) = z ∧
      (∀ a, VIRBridge.Apart (s.regs.get .r14 + slot t) a → rd u.mem a = rd s.mem a) ∧
      ∀ r, r ≠ .rax → r ≠ .rcx → u.regs.get r = s.regs.get r := by
  have c0 : CodeAt C p s.rip (ld .rax .r14 (slot t) :: ld .rcx .r14 (slot (t + 1)) :: (mid ++ st .r14 (slot t) .rax :: rest)) := by
    simpa [List.append_assoc] using hc
  have e1 := stepP_ld hs c0
  set s1 := stepP p s
  have h1 : s1.stopped = false := by rw [e1]; exact hs
  have c1 : CodeAt C p s1.rip (ld .rcx .r14 (slot (t + 1)) :: (mid ++ st .r14 (slot t) .rax :: rest)) := by
    rw [e1]; exact codeAt_tail c0
  have e2 := stepP_ld h1 c1
  set s2 := stepP p s1
  have h2 : s2.stopped = false := by rw [e2]; exact h1
  have c2 : CodeAt C p s2.rip (mid ++ st .r14 (slot t) .rax :: rest) := by rw [e2]; exact codeAt_tail c1
  have r14_1 : s1.regs.get .r14 = s.regs.get .r14 := by rw [e1]; simp
  have rax2 : s2.regs.get .rax = x := by rw [e2, e1]; simp [hx]
  have rcx2 : s2.regs.get .rcx = y := by rw [e2]; simp [r14_1, e1, hy]
  obtain ⟨v, hv, hvs, hvr, hvm, hvax, hvreg⟩ := hm s2 (st .r14 (slot t) .rax :: rest) h2 c2 rax2 rcx2
  have cv : CodeAt C p v.rip (st .r14 (slot t) .rax :: rest) := by
    rw [hvr]; exact codeAt_right c2
  have e3 := stepP_st hvs cv
  have regs2 : ∀ r, r ≠ .rax → r ≠ .rcx → s2.regs.get r = s.regs.get r := by
    intro r ha hc'; rw [e2, e1]; simp [Regs.get_set_ne _ _ _ _ (Ne.symm ha), Regs.get_set_ne _ _ _ _ (Ne.symm hc')]
  have mem2 : s2.mem = s.mem := by rw [e2, e1]
  have r14v : v.regs.get .r14 = s.regs.get .r14 := by rw [hvreg .r14 (by decide) (by decide)]; exact regs2 .r14 (by decide) (by decide)
  refine ⟨stepP p v, ?_, by rw [e3]; exact hvs, ?_, ?_, ?_, ?_⟩
  · rw [runP_add, runP_add, show runP p 2 s = s2 from rfl, hv]; rfl
  · rw [e3, hvr, e2, e1]
    simp only [nxt, ld, st, bytes_append, bytes_cons, bytes_nil, AI.size, ofNat_add64, BitVec.add_assoc, Nat.add_zero]
  · rw [e3, r14v, hvax, hvm, mem2]; exact rd_write_same _ _ _
  · intro a ha; rw [e3, r14v, hvm, mem2]; exact rd_write_apart _ _ _ _ ha
  · intro r ha hc'; rw [e3]; rw [hvreg r ha hc']; exact regs2 r ha hc'

theorem mid_and (C : Ctx3) (p : Program) (x y : W) : MidOK C p [.op (.bin .and .q (.reg .rax) (.reg .rcx))] 1 x y (x &&& y) := by
  intro u rest hu hc hx hy
  obtain ⟨f, o, e⟩ := stepP_and_rr hu (by simpa using hc)
  refine ⟨stepP p u, rfl, by rw [e]; exact hu, by rw [e]; simp [nxt, bytes_cons, bytes_nil], by rw [e], by rw [e]; simp [hx, hy], ?_⟩
  intro r ha _; rw [e]; simp [Regs.get_set_ne _ _ _ _ (Ne.symm ha)]

theorem mid_or (C : Ctx3) (p : Program) (x y : W) : MidOK C p [.op (.bin .or .q (.reg .rax) (.reg .rcx))] 1 x y (x ||| y) := by
  intro u rest hu hc hx hy
  obtain ⟨f, o, e⟩ := stepP_or_rr hu (by simpa using hc)
  refine ⟨stepP p u, rfl, by rw [e]; exact hu, by rw [e]; simp [nxt, bytes_cons, bytes_nil], by rw [e], by rw [e]; simp [hx, hy], ?_⟩
  intro r ha _; rw [e]; simp [Regs.get_set_ne _ _ _ _ (Ne.symm ha)]

theorem mid_max (C : Ctx3) (p : Program) (x y : W) :
    MidOK C p [.op (.bin .cmp .q (.reg .rax) (.reg .rcx)), .op (.cmov .le .q .rax (.reg .rcx))] 2 x y
      (if x.toInt ≤ y.toInt then y else x) := by
  intro u rest hu hc hx hy
  have c0 : CodeAt C p u.rip (.op (.bin .cmp .q (.reg .rax) (.reg .rcx)) :: .op (.cmov .le .q .rax (.reg .rcx)) :: rest) := by
    simpa using hc
  have e1 := stepP_cmp_rr hu c0
  set u1 := stepP p u
  have h1 : u1.stopped = false := by rw [e1]; exact hu
  have c1 : CodeAt C p u1.rip (.op (.cmov .le .q .rax (.reg .rcx)) :: rest) := by rw [e1]; exact codeAt_tail c0
  have e2 := stepP_cmov h1 c1
  refine ⟨stepP p u1, rfl, by rw [e2]; exact h1, ?_, by rw [e2, e1], ?_, ?_⟩
  · rw [e2, e1]; simp only [nxt, bytes_cons, bytes_nil, ofNat_add64, BitVec.add_assoc, Nat.add_zero]
  · rw [e2]; simp only [Regs.get_set_same]
    rw [show u1.flags = Flags.sub .q (u.regs.get .rax) (u.regs.get .rcx) u.flags by rw [e1], hx, hy, cc_le_sub,
      show u1.regs = u.regs by rw [e1], hx, hy]
    by_cases h : x.toInt ≤ y.toInt <;> simp [h]
  · intro r ha _; rw [e2]; simp [Regs.get_set_ne _ _ _ _ (Ne.symm ha), show u1.regs = u.regs by rw [e1]]

/-! ## The checked multiply: x86lean's imulPair/imulOverflow at quadword width are `x * y` and `smulOverflow` -/

theorem sval_q (v : W) : Value.sval .q v = v.toInt := by
  rw [BitVec.toInt_eq_msb_cond]
  simp only [Value.sval, Value.uval, Value.trunc_q, msb_q, Size.bits]

theorem imulPair_q (x y : W) : (Value.imulPair .q x y).1 = x * y := by
  have hA : (Value.imulPair .q x y).1 = BitVec.ofInt 64 (x.toInt * y.toInt) := by
    apply BitVec.eq_of_toNat_eq
    simp only [Value.imulPair, sval_q, Size.bits, BitVec.toNat_ofNat, BitVec.toNat_ofInt]
    generalize x.toInt * y.toInt = q
    have h1 : 0 ≤ q % (2 : Int) ^ (2 * 64) := Int.emod_nonneg _ (by decide)
    have h2 : 0 ≤ q % ((2 ^ 64 : Nat) : Int) := Int.emod_nonneg _ (by decide)
    have e1 : (((q % (2 : Int) ^ (2 * 64)).toNat : Nat) : Int) = q % (2 : Int) ^ (2 * 64) := Int.toNat_of_nonneg h1
    have e2 : (((q % ((2 ^ 64 : Nat) : Int)).toNat : Nat) : Int) = q % ((2 ^ 64 : Nat) : Int) := Int.toNat_of_nonneg h2
    omega
  rw [hA, BitVec.ofInt_mul, BitVec.ofInt_toInt, BitVec.ofInt_toInt]

theorem imulOverflow_q (x y : W) : Value.imulOverflow .q x y = BitVec.smulOverflow x y := by
  simp only [Value.imulOverflow, imulPair_q, sval_q, BitVec.toInt_mul, BitVec.smulOverflow]
  generalize x.toInt * y.toInt = q
  rw [Bool.eq_iff_iff]
  simp only [bne_iff_ne, ne_eq, Bool.or_eq_true, decide_eq_true_eq, Int.bmod_def]
  split <;> omega

theorem chk_mul (x y : W) : chk (x.toInt * y.toInt) = if BitVec.smulOverflow x y then .ovf else .ok [x * y] := by
  unfold chk
  have hr : inRange (x.toInt * y.toInt) = !BitVec.smulOverflow x y := by rw [inRange_iff]; rfl
  rw [hr]
  cases h : BitVec.smulOverflow x y
  · simp only [Bool.not_false, if_true]
    rw [← BitVec.toInt_mul_of_not_smulOverflow (by simp [h]), BitVec.ofInt_toInt]
    simp
  · rfl

theorem stepP_imul {C : Ctx3} {p : Program} {s : Cpu} {l : List AI}
    (hs : s.stopped = false) (hc : CodeAt C p s.rip (.op (.imulr .q .rax (.reg .rcx) none) :: l)) :
    stepP p s = { s with regs := s.regs.set .rax (s.regs.get .rax * s.regs.get .rcx), flags := Flags.mulFlags (BitVec.smulOverflow (s.regs.get .rax) (s.regs.get .rcx)) (s.oracle.bits s.oracle.cursor) (s.oracle.bits (s.oracle.cursor + 1)) (s.oracle.bits (s.oracle.cursor + 2)) (s.oracle.bits (s.oracle.cursor + 3)) s.flags, oracle := { s.oracle with cursor := s.oracle.cursor + 4 }, rip := nxt C s.rip (.op (.imulr .q .rax (.reg .rcx) none)) } := by
  rw [stepP_of_at hs (codeAt_head hc)]
  simp only [AI.toInstr]
  rw [step_imulr .q .rax (.reg .rcx) none (live_of hs) rfl rfl]
  simp [Value.writeView, Cpu.getReg, Cpu.readOperand, imulPair_q, imulOverflow_q, nxt, AI.size]

/-! ## The checked multiply block (the add block's proof, with imul's step) -/

/-- **arith_mul_run.** With BUF slots t and t+1 holding x and y: on signed overflow the block reaches OVF in 4 steps with memory
    untouched; otherwise in 5 steps slot t holds `x * y`, and every word apart from slot t keeps its value. Among the registers
    only rax and rcx change. -/
theorem arith_mul_run {C : Ctx3} {p : Program} {s : Cpu} {t : Nat} {x y : W} {rest : List AI}
    (hs : s.stopped = false) (hc : CodeAt C p s.rip (arithCode C t .mul ++ rest)) (hcan : canonical C.ovf = true)
    (hx : rd s.mem (s.regs.get .r14 + slot t) = x) (hy : rd s.mem (s.regs.get .r14 + slot (t + 1)) = y) :
    (BitVec.smulOverflow x y = true → ∃ u, runP p 4 s = u ∧ u.stopped = false ∧ u.rip = C.ovf ∧ u.mem = s.mem ∧
        ∀ r, r ≠ .rax → r ≠ .rcx → u.regs.get r = s.regs.get r) ∧
    (BitVec.smulOverflow x y = false → ∃ u, runP p 5 s = u ∧ u.stopped = false ∧
        u.rip = s.rip + BitVec.ofNat 64 (bytes C (arithCode C t .mul)) ∧
        rd u.mem (s.regs.get .r14 + slot t) = x * y ∧
        (∀ a, VIRBridge.Apart (s.regs.get .r14 + slot t) a → rd u.mem a = rd s.mem a) ∧
        ∀ r, r ≠ .rax → r ≠ .rcx → u.regs.get r = s.regs.get r) := by
  have c0 : CodeAt C p s.rip (ld .rax .r14 (slot t) :: ld .rcx .r14 (slot (t + 1)) ::
      .op (.imulr .q .rax (.reg .rcx) none) :: .jccA .o C.ovf :: st .r14 (slot t) .rax :: rest) := by
    simpa [arithCode] using hc
  have e1 := stepP_ld hs c0
  set s1 := stepP p s
  have h1 : s1.stopped = false := by rw [e1]; exact hs
  have c1 : CodeAt C p s1.rip (ld .rcx .r14 (slot (t + 1)) ::
      .op (.imulr .q .rax (.reg .rcx) none) :: .jccA .o C.ovf :: st .r14 (slot t) .rax :: rest) := by
    rw [e1]; exact codeAt_tail c0
  have e2 := stepP_ld h1 c1
  set s2 := stepP p s1
  have h2 : s2.stopped = false := by rw [e2]; exact h1
  have c2 : CodeAt C p s2.rip (.op (.imulr .q .rax (.reg .rcx) none) :: .jccA .o C.ovf :: st .r14 (slot t) .rax :: rest) := by
    rw [e2]; exact codeAt_tail c1
  have e3 := stepP_imul h2 c2
  set s3 := stepP p s2
  have h3 : s3.stopped = false := by rw [e3]; exact h2
  have c3 : CodeAt C p s3.rip (.jccA .o C.ovf :: st .r14 (slot t) .rax :: rest) := by
    rw [e3]; exact codeAt_tail c2
  have e4 := stepP_jccA h3 c3 hcan
  set s4 := stepP p s3
  have r14_2 : s2.regs.get .r14 = s.regs.get .r14 := by rw [e2, e1]; simp
  have rax2 : s2.regs.get .rax = x := by rw [e2, e1]; simp [hx]
  have rcx2 : s2.regs.get .rcx = y := by rw [e2]; simp [e1, hy]
  have hfl : Cc.eval .o s3.flags = BitVec.smulOverflow x y := by rw [e3]; simp [Cc.eval, Flags.mulFlags, rax2, rcx2]
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
    have rax4 : s4.regs.get .rax = x * y := by rw [e4, e3]; simp [rax2, rcx2]
    refine ⟨stepP p s4, rfl, by rw [e5]; exact h4, ?_, ?_, ?_, ?_⟩
    · rw [e5, rip4, e3, e2, e1]
      simp only [nxt, arithCode, ld, st, bytes_cons, bytes_nil, AI.size, ofNat_add64, BitVec.add_assoc, Nat.add_zero]
      all_goals bv_omega
    · rw [e5, r14_4, rax4]; simp only [show s4.mem = s.mem by rw [e4]; exact mem3]; exact rd_write_same _ _ _
    · intro a ha; rw [e5, r14_4, show s4.mem = s.mem by rw [e4]; exact mem3]; exact rd_write_apart _ _ _ _ ha
    · intro r ha hc'; rw [e5]; rw [e4]; exact regs3 r ha hc'

/-! ## Every operator: `AOp.apply` against its block -/

/-- **arith_run.** With slots t, t+1 holding x, y: if `op.apply x y` overflows, the block reaches OVF with memory unchanged; if it
    yields `[z]`, the block ends at its last byte with z at slot t and every word apart from slot t unchanged. Registers other than
    rax, rcx, rdx are unchanged in both cases. -/
theorem arith_run {C : Ctx3} {p : Program} {s : Cpu} {t : Nat} {x y : W} {rest : List AI} (op : AOp)
    (hs : s.stopped = false) (hc : CodeAt C p s.rip (arithCode C t op ++ rest)) (hcan : canonical C.ovf = true)
    (hx : rd s.mem (s.regs.get .r14 + slot t) = x) (hy : rd s.mem (s.regs.get .r14 + slot (t + 1)) = y) :
    (op.apply x y = .ovf → ∃ n u, runP p n s = u ∧ u.stopped = false ∧ u.rip = C.ovf ∧ u.mem = s.mem ∧
        ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → u.regs.get r = s.regs.get r) ∧
    (∀ z, op.apply x y = .ok [z] → ∃ n u, runP p n s = u ∧ u.stopped = false ∧
        u.rip = s.rip + BitVec.ofNat 64 (bytes C (arithCode C t op)) ∧ rd u.mem (s.regs.get .r14 + slot t) = z ∧
        (∀ a, VIRBridge.Apart (s.regs.get .r14 + slot t) a → rd u.mem a = rd s.mem a) ∧
        ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → u.regs.get r = s.regs.get r) := by
  cases op with
  | add =>
    obtain ⟨hov, hok⟩ := arith_add_run hs hc hcan hx hy
    simp only [AOp.apply, chk_add]
    refine ⟨fun h => ?_, fun z h => ?_⟩
    · split at h
      · obtain ⟨u, h1, h2, h3, h4, h5⟩ := hov (by assumption)
        exact ⟨4, u, h1, h2, h3, h4, fun r a b _ => h5 r a b⟩
      · cases h
    · split at h
      · cases h
      · cases h
        obtain ⟨u, h1, h2, h3, h4, h5, h6⟩ := hok (Bool.eq_false_iff.mpr (by assumption))
        exact ⟨5, u, h1, h2, h3, h4, h5, fun r a b _ => h6 r a b⟩
  | sub =>
    obtain ⟨hov, hok⟩ := arith_sub_run hs hc hcan hx hy
    simp only [AOp.apply, chk_sub]
    refine ⟨fun h => ?_, fun z h => ?_⟩
    · split at h
      · obtain ⟨u, h1, h2, h3, h4, h5⟩ := hov (by assumption)
        exact ⟨4, u, h1, h2, h3, h4, fun r a b _ => h5 r a b⟩
      · cases h
    · split at h
      · cases h
      · cases h
        obtain ⟨u, h1, h2, h3, h4, h5, h6⟩ := hok (Bool.eq_false_iff.mpr (by assumption))
        exact ⟨5, u, h1, h2, h3, h4, h5, fun r a b _ => h6 r a b⟩
  | mul =>
    obtain ⟨hov, hok⟩ := arith_mul_run hs hc hcan hx hy
    simp only [AOp.apply, chk_mul]
    refine ⟨fun h => ?_, fun z h => ?_⟩
    · split at h
      · obtain ⟨u, h1, h2, h3, h4, h5⟩ := hov (by assumption)
        exact ⟨4, u, h1, h2, h3, h4, fun r a b _ => h5 r a b⟩
      · cases h
    · split at h
      · cases h
      · cases h
        obtain ⟨u, h1, h2, h3, h4, h5, h6⟩ := hok (Bool.eq_false_iff.mpr (by assumption))
        exact ⟨5, u, h1, h2, h3, h4, h5, fun r a b _ => h6 r a b⟩
  | lt =>
    refine ⟨fun h => by simp [AOp.apply] at h, fun z h => ?_⟩
    simp only [AOp.apply, WRes.ok.injEq, List.cons.injEq, and_true] at h
    obtain ⟨u, h1, h2, h3, h4, h5, h6⟩ := cmp_run (b := decide (x.toInt < y.toInt)) hs (by simpa [arithCode_lt] using hc) hx hy
      (fun f => cc_l_sub x y f)
    exact ⟨6, u, h1, h2, by rw [h3, arithCode_lt], by rw [h4, h], h5, h6⟩
  | le =>
    refine ⟨fun h => by simp [AOp.apply] at h, fun z h => ?_⟩
    simp only [AOp.apply, WRes.ok.injEq, List.cons.injEq, and_true] at h
    obtain ⟨u, h1, h2, h3, h4, h5, h6⟩ := cmp_run (b := decide (x.toInt ≤ y.toInt)) hs (by simpa [arithCode_le] using hc) hx hy
      (fun f => cc_le_sub x y f)
    exact ⟨6, u, h1, h2, by rw [h3, arithCode_le], by rw [h4, h], h5, h6⟩
  | eq =>
    refine ⟨fun h => by simp [AOp.apply] at h, fun z h => ?_⟩
    simp only [AOp.apply, WRes.ok.injEq, List.cons.injEq, and_true] at h
    obtain ⟨u, h1, h2, h3, h4, h5, h6⟩ := cmp_run (b := decide (x = y)) hs (by simpa [arithCode_eq] using hc) hx hy
      (fun f => cc_e_sub x y f)
    exact ⟨6, u, h1, h2, by rw [h3, arithCode_eq], by rw [h4, h], h5, h6⟩
  | max =>
    refine ⟨fun h => by simp [AOp.apply] at h, fun z h => ?_⟩
    simp only [AOp.apply, WRes.ok.injEq, List.cons.injEq, and_true] at h
    obtain ⟨u, h1, h2, h3, h4, h5, h6⟩ := binBlock_run (k := 2) hs (by simpa [arithCode, List.append_assoc] using hc) hx hy
      (mid_max C p x y)
    exact ⟨2 + 2 + 1, u, h1, h2, by rw [h3]; rfl, by rw [h4, h], h5, fun r a b _ => h6 r a b⟩
  | band =>
    refine ⟨fun h => by simp [AOp.apply] at h, fun z h => ?_⟩
    simp only [AOp.apply, WRes.ok.injEq, List.cons.injEq, and_true] at h
    obtain ⟨u, h1, h2, h3, h4, h5, h6⟩ := binBlock_run (k := 1) hs (by simpa [arithCode, List.append_assoc] using hc) hx hy
      (mid_and C p x y)
    exact ⟨2 + 1 + 1, u, h1, h2, by rw [h3]; rfl, by rw [h4, h], h5, fun r a b _ => h6 r a b⟩
  | bor =>
    refine ⟨fun h => by simp [AOp.apply] at h, fun z h => ?_⟩
    simp only [AOp.apply, WRes.ok.injEq, List.cons.injEq, and_true] at h
    obtain ⟨u, h1, h2, h3, h4, h5, h6⟩ := binBlock_run (k := 1) hs (by simpa [arithCode, List.append_assoc] using hc) hx hy
      (mid_or C p x y)
    exact ⟨2 + 1 + 1, u, h1, h2, by rw [h3]; rfl, by rw [h4, h], h5, fun r a b _ => h6 r a b⟩

/-! ## Immediates and padding -/

/-- n immediate stores: word j := `v j` at `[db + g j]`, through rax. -/
def immL (db : GPR) (v g : Nat → W) : Nat → List AI
  | 0 => []
  | n + 1 => immL db v g n ++ [movi .rax (v n), st db (g n) .rax]

theorem imm_run {C : Ctx3} {p : Program} (db : GPR) (hdb : db ≠ .rax) (v g : Nat → W) :
    ∀ (n : Nat) (s : Cpu) (rest : List AI), s.stopped = false → CodeAt C p s.rip (immL db v g n ++ rest) →
    (∀ i j, i < n → j < n → i ≠ j → VIRBridge.Apart (s.regs.get db + g i) (s.regs.get db + g j)) →
    ∃ s', runP p (2 * n) s = s' ∧ s'.stopped = false ∧ s'.rip = s.rip + BitVec.ofNat 64 (bytes C (immL db v g n)) ∧
      (∀ r, r ≠ .rax → s'.regs.get r = s.regs.get r) ∧
      (∀ j, j < n → rd s'.mem (s.regs.get db + g j) = v j) ∧
      (∀ a, (∀ j, j < n → VIRBridge.Apart (s.regs.get db + g j) a) → rd s'.mem a = rd s.mem a)
  | 0, s, _, hs, _, _ => ⟨s, rfl, hs, by simp [immL, bytes_nil], fun _ _ => rfl, fun _ h => absurd h (by omega), fun _ _ => rfl⟩
  | n + 1, s, rest, hs, hc, hdd => by
    obtain ⟨u, hu, hus, hur, hureg, hucp, hufr⟩ := imm_run db hdb v g n s ([movi .rax (v n), st db (g n) .rax] ++ rest) hs
      (by simpa [immL, List.append_assoc] using hc) (fun i j hi hj hij => hdd i j (by omega) (by omega) hij)
    have hcu : CodeAt C p u.rip (movi .rax (v n) :: st db (g n) .rax :: rest) := by
      rw [hur]; have := codeAt_right (a := immL db v g n) (b := [movi .rax (v n), st db (g n) .rax] ++ rest)
        (by simpa [immL, List.append_assoc] using hc)
      simpa using this
    have h1 := stepP_movi hus hcu
    set u1 := stepP p u with hu1
    have hu1s : u1.stopped = false := by rw [h1]; exact hus
    have hcu1 : CodeAt C p u1.rip (st db (g n) .rax :: rest) := by rw [h1]; exact codeAt_tail hcu
    have h2 := stepP_st hu1s hcu1
    have hdbu : u.regs.get db = s.regs.get db := hureg db hdb
    refine ⟨stepP p u1, ?_, by rw [h2]; exact hu1s, ?_, ?_, ?_, ?_⟩
    · rw [show 2 * (n + 1) = 2 * n + 2 by omega, runP_add, hu]
      simp [runP, hu1]
    · rw [h2, h1]
      simp only [hur, nxt, immL, bytes_append, bytes_cons, bytes_nil, ofNat_add64, BitVec.add_assoc, Nat.add_zero]
    · intro r hr; rw [h2, h1]; simp [Regs.get_set_ne _ _ _ _ (Ne.symm hr), hureg r hr]
    · intro j hj
      rw [h2, h1]
      simp only [Regs.get_set_ne _ _ _ _ (Ne.symm hdb), Regs.get_set_same]
      rw [hdbu]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | hj
      · rw [rd_write_apart _ _ _ _ (hdd n j (by omega) (by omega) (by omega)), hucp j hj]
      · subst hj; exact rd_write_same _ _ _
    · intro a ha
      rw [h2, h1]
      simp only [Regs.get_set_ne _ _ _ _ (Ne.symm hdb), Regs.get_set_same]
      rw [hdbu, rd_write_apart _ _ _ _ (ha n (by omega)), hufr a (fun j hj => ha j (by omega))]

/-- n stores of rax: word j := rax at `[db + g j]` (tag's padding, rax = 0). -/
def stL (db : GPR) (g : Nat → W) : Nat → List AI
  | 0 => []
  | n + 1 => stL db g n ++ [st db (g n) .rax]

theorem st_run {C : Ctx3} {p : Program} (db : GPR) (g : Nat → W) :
    ∀ (n : Nat) (s : Cpu) (rest : List AI), s.stopped = false → CodeAt C p s.rip (stL db g n ++ rest) →
    (∀ i j, i < n → j < n → i ≠ j → VIRBridge.Apart (s.regs.get db + g i) (s.regs.get db + g j)) →
    ∃ s', runP p n s = s' ∧ s'.stopped = false ∧ s'.rip = s.rip + BitVec.ofNat 64 (bytes C (stL db g n)) ∧
      s'.regs = s.regs ∧
      (∀ j, j < n → rd s'.mem (s.regs.get db + g j) = s.regs.get .rax) ∧
      (∀ a, (∀ j, j < n → VIRBridge.Apart (s.regs.get db + g j) a) → rd s'.mem a = rd s.mem a)
  | 0, s, _, hs, _, _ => ⟨s, rfl, hs, by simp [stL, bytes_nil], rfl, fun _ h => absurd h (by omega), fun _ _ => rfl⟩
  | n + 1, s, rest, hs, hc, hdd => by
    obtain ⟨u, hu, hus, hur, hureg, hucp, hufr⟩ := st_run db g n s ([st db (g n) .rax] ++ rest) hs
      (by simpa [stL, List.append_assoc] using hc) (fun i j hi hj hij => hdd i j (by omega) (by omega) hij)
    have hcu : CodeAt C p u.rip (st db (g n) .rax :: rest) := by
      rw [hur]; have := codeAt_right (a := stL db g n) (b := [st db (g n) .rax] ++ rest)
        (by simpa [stL, List.append_assoc] using hc)
      simpa using this
    have h1 := stepP_st hus hcu
    refine ⟨stepP p u, ?_, by rw [h1]; exact hus, ?_, by rw [h1]; exact hureg, ?_, ?_⟩
    · rw [show n + 1 = n + 1 from rfl, runP_add, hu]; rfl
    · rw [h1]; simp only [hur, nxt, stL, bytes_append, bytes_cons, bytes_nil, ofNat_add64, BitVec.add_assoc, Nat.add_zero]
    · intro j hj
      rw [h1, hureg]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | hj
      · rw [rd_write_apart _ _ _ _ (hdd n j (by omega) (by omega) (by omega)), hucp j hj]
      · subst hj; exact rd_write_same _ _ _
    · intro a ha
      rw [h1, hureg, rd_write_apart _ _ _ _ (ha n (by omega)), hufr a (fun j hj => ha j (by omega))]

/-! ## evalTo's pieces as the generic run lists -/

theorem wid_le_need : ∀ o : WOpd, wid o ≤ need o
  | .slice _ _ => le_refl _
  | .imm _ => le_refl _
  | .arith _ _ _ => by simp [wid, need]
  | .bnot a => by simp [wid, need]
  | .cat a b => by have := wid_le_need b; simp [wid, need]; omega
  | .take n a => by have := wid_le_need a; simp [wid, need]; omega
  | .drop n a => by have := wid_le_need a; simp [wid, need]; omega
  | .tag _ pad a => by simp [wid, need]

theorem moves_eq_copyL (s d : Nat) : ∀ n, moves s d n = copyL .r14 .r14 (fun j => slot (s + j)) (fun j => slot (d + j)) n
  | 0 => rfl
  | n + 1 => by simp only [moves, copyL, moves_eq_copyL s d n]

theorem imm_eq_immL (t : Nat) (ws : List W) :
    evalTo C t (.imm ws) = immL .r14 (fun j => ws.getD j 0) (fun j => slot (t + j)) ws.length := by
  simp only [evalTo]
  generalize ws.length = n
  induction n with
  | zero => rfl
  | succ n ih => rw [List.range_succ, List.flatMap_append, ih]; simp [immL]

theorem pad_eq_stL (k pad : Nat) :
    ((List.range pad).flatMap fun j => [st .r14 (slot (k + j)) .rax]) = stL .r14 (fun j => slot (k + j)) pad := by
  induction pad with
  | zero => rfl
  | succ n ih => rw [List.range_succ, List.flatMap_append, ih]; simp [stL]

/-- A word list at BUF slot t, read slot by slot. -/
theorem wordsAt_slot {m : Mem} {B : W} {t : Nat} {ws : List W} :
    WordsAt m (B + slot t) ws ↔ ∀ j (h : j < ws.length), rd m (B + slot (t + j)) = ws[j] := by
  have e : ∀ j, B + slot t + BitVec.ofNat 64 (8 * j) = B + slot (t + j) := by
    intro j; simp only [slot, BitVec.add_assoc, ← ofNat_add64]; congr 2; omega
  constructor
  · intro h j hj; have := h j hj; rw [e] at this; exact this
  · intro h j hj; rw [e]; exact h j hj

/-! ## evalTo against evalW -/

/-- What operand evaluation at BUF slot t needs: ρ in ENV at r12, BUF non-wrapping over N slots, ENV words apart from slots t…N−1. -/
def EvalPre (s : Cpu) (t N : Nat) (ρ : List W) : Prop :=
  WordsAt s.mem (s.regs.get .r12) ρ ∧ (s.regs.get .r14).toNat + 8 * N < 2 ^ 64 ∧
  ∀ i j, t ≤ i → i < N → j < ρ.length → VIRBridge.Apart (s.regs.get .r14 + slot i) (s.regs.get .r12 + slot j)

/-- Words apart from BUF slots t…N−1 keep their value; registers other than rax, rcx, rdx keep theirs. -/
def Frame (s u : Cpu) (t N : Nat) : Prop :=
  (∀ a, (∀ i, t ≤ i → i < N → VIRBridge.Apart (s.regs.get .r14 + slot i) a) → rd u.mem a = rd s.mem a) ∧
  ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → u.regs.get r = s.regs.get r

def EvalPost (C : Ctx3) (p : Program) (s : Cpu) (t : Nat) (o : WOpd) (ρ : List W) (N : Nat) : Prop :=
  match evalW ρ o with
  | .ok ws => ∃ n u, runP p n s = u ∧ u.stopped = false ∧ u.rip = s.rip + BitVec.ofNat 64 (bytes C (evalTo C t o)) ∧
      WordsAt u.mem (s.regs.get .r14 + slot t) ws ∧ Frame s u t N
  | .ovf => ∃ n u, runP p n s = u ∧ u.stopped = false ∧ u.rip = C.ovf ∧ Frame s u t N
  | .bad => True

theorem frame_trans {s u v : Cpu} {t t' N : Nat} (htt : t ≤ t') (h1 : Frame s u t N) (h2 : Frame u v t' N) : Frame s v t N := by
  have hB : u.regs.get .r14 = s.regs.get .r14 := h1.2 .r14 (by decide) (by decide) (by decide)
  refine ⟨fun a ha => ?_, fun r a b c => by rw [h2.2 r a b c, h1.2 r a b c]⟩
  rw [h2.1 a (fun i hi hi' => by rw [hB]; exact ha i (by omega) hi'), h1.1 a ha]

theorem pre_mono {s u : Cpu} {t t' N : Nat} {ρ : List W} (htt : t ≤ t') (hf : Frame s u t N) (hp : EvalPre s t N ρ) :
    EvalPre u t' N ρ := by
  obtain ⟨hw, hN, hap⟩ := hp
  have hB : u.regs.get .r14 = s.regs.get .r14 := hf.2 .r14 (by decide) (by decide) (by decide)
  have hE : u.regs.get .r12 = s.regs.get .r12 := hf.2 .r12 (by decide) (by decide) (by decide)
  refine ⟨fun j hj => ?_, by rw [hB]; exact hN, fun i j hi hi' hj => by rw [hB, hE]; exact hap i j (by omega) hi' hj⟩
  rw [hE]
  have := hf.1 (s.regs.get .r12 + BitVec.ofNat 64 (8 * j)) (fun i hi hi' => hap i j hi hi' hj)
  simp only [rd] at this; rw [this]; exact hw j hj

theorem frame_refl (s : Cpu) (t N : Nat) : Frame s s t N := ⟨fun _ _ => rfl, fun _ _ _ _ => rfl⟩

theorem frame_weaken {s u : Cpu} {t t' N : Nat} (htt : t ≤ t') (h : Frame s u t' N) : Frame s u t N :=
  ⟨fun a ha => h.1 a (fun i hi hi' => ha i (by omega) hi'), h.2⟩

/-- bnot's tail: from slot t holding x, `1 − x` at slot t in 4 steps; words apart from slot t kept; regs but rax, rcx kept. -/
theorem bnot_tail_run {C : Ctx3} {p : Program} {s : Cpu} {t : Nat} {x : W} {rest : List AI}
    (hs : s.stopped = false)
    (hc : CodeAt C p s.rip ([movi .rax 1, ld .rcx .r14 (slot t), .op (.bin .sub .q (.reg .rax) (.reg .rcx)), st .r14 (slot t) .rax] ++ rest))
    (hx : rd s.mem (s.regs.get .r14 + slot t) = x) :
    ∃ u, runP p 4 s = u ∧ u.stopped = false ∧
      u.rip = s.rip + BitVec.ofNat 64 (bytes C [movi .rax 1, ld .rcx .r14 (slot t), .op (.bin .sub .q (.reg .rax) (.reg .rcx)), st .r14 (slot t) .rax]) ∧
      rd u.mem (s.regs.get .r14 + slot t) = 1 - x ∧
      (∀ a, VIRBridge.Apart (s.regs.get .r14 + slot t) a → rd u.mem a = rd s.mem a) ∧
      ∀ r, r ≠ .rax → r ≠ .rcx → u.regs.get r = s.regs.get r := by
  have c0 : CodeAt C p s.rip (movi .rax 1 :: ld .rcx .r14 (slot t) :: .op (.bin .sub .q (.reg .rax) (.reg .rcx)) ::
      st .r14 (slot t) .rax :: rest) := by simpa using hc
  have e1 := stepP_movi hs c0
  set s1 := stepP p s
  have h1 : s1.stopped = false := by rw [e1]; exact hs
  have c1 : CodeAt C p s1.rip (ld .rcx .r14 (slot t) :: .op (.bin .sub .q (.reg .rax) (.reg .rcx)) :: st .r14 (slot t) .rax :: rest) := by
    rw [e1]; exact codeAt_tail c0
  have e2 := stepP_ld h1 c1
  set s2 := stepP p s1
  have h2 : s2.stopped = false := by rw [e2]; exact h1
  have c2 : CodeAt C p s2.rip (.op (.bin .sub .q (.reg .rax) (.reg .rcx)) :: st .r14 (slot t) .rax :: rest) := by
    rw [e2]; exact codeAt_tail c1
  have e3 := stepP_sub_rr h2 c2
  set s3 := stepP p s2
  have h3 : s3.stopped = false := by rw [e3]; exact h2
  have c3 : CodeAt C p s3.rip (st .r14 (slot t) .rax :: rest) := by rw [e3]; exact codeAt_tail c2
  have e4 := stepP_st h3 c3
  have mem3 : s3.mem = s.mem := by rw [e3, e2, e1]
  have regs3 : ∀ r, r ≠ .rax → r ≠ .rcx → s3.regs.get r = s.regs.get r := by
    intro r ha hc'; rw [e3, e2, e1]; simp [Regs.get_set_ne _ _ _ _ (Ne.symm ha), Regs.get_set_ne _ _ _ _ (Ne.symm hc')]
  have r14_3 : s3.regs.get .r14 = s.regs.get .r14 := regs3 .r14 (by decide) (by decide)
  have rax3 : s3.regs.get .rax = 1 - x := by rw [e3, e2, e1]; simp [hx]
  refine ⟨stepP p s3, rfl, by rw [e4]; exact h3, ?_, ?_, ?_, ?_⟩
  · rw [e4, e3, e2, e1]
    simp only [nxt, movi, ld, st, bytes_cons, bytes_nil, AI.size, ofNat_add64, BitVec.add_assoc, Nat.add_zero]
  · rw [e4, r14_3, rax3, mem3]; exact rd_write_same _ _ _
  · intro a ha; rw [e4, r14_3, mem3]; exact rd_write_apart _ _ _ _ ha
  · intro r ha hc'; rw [e4]; exact regs3 r ha hc'

/-- tag's head: tag word at slot t, then rax := 0, in 3 steps. -/
theorem tag_head_run {C : Ctx3} {p : Program} {s : Cpu} {t : Nat} {tg : W} {rest : List AI}
    (hs : s.stopped = false) (hc : CodeAt C p s.rip ([movi .rax tg, st .r14 (slot t) .rax, movi .rax 0] ++ rest)) :
    ∃ u, runP p 3 s = u ∧ u.stopped = false ∧
      u.rip = s.rip + BitVec.ofNat 64 (bytes C [movi .rax tg, st .r14 (slot t) .rax, movi .rax 0]) ∧
      rd u.mem (s.regs.get .r14 + slot t) = tg ∧ u.regs.get .rax = 0 ∧
      (∀ a, VIRBridge.Apart (s.regs.get .r14 + slot t) a → rd u.mem a = rd s.mem a) ∧
      ∀ r, r ≠ .rax → u.regs.get r = s.regs.get r := by
  have c0 : CodeAt C p s.rip (movi .rax tg :: st .r14 (slot t) .rax :: movi .rax 0 :: rest) := by simpa using hc
  have e1 := stepP_movi hs c0
  set s1 := stepP p s
  have h1 : s1.stopped = false := by rw [e1]; exact hs
  have c1 : CodeAt C p s1.rip (st .r14 (slot t) .rax :: movi .rax 0 :: rest) := by rw [e1]; exact codeAt_tail c0
  have e2 := stepP_st h1 c1
  set s2 := stepP p s1
  have h2 : s2.stopped = false := by rw [e2]; exact h1
  have c2 : CodeAt C p s2.rip (movi .rax 0 :: rest) := by rw [e2]; exact codeAt_tail c1
  have e3 := stepP_movi h2 c2
  have r14_1 : s1.regs.get .r14 = s.regs.get .r14 := by rw [e1]; simp
  refine ⟨stepP p s2, rfl, by rw [e3]; exact h2, ?_, ?_, by rw [e3]; simp, ?_, ?_⟩
  · rw [e3, e2, e1]
    simp only [nxt, movi, st, bytes_cons, bytes_nil, AI.size, ofNat_add64, BitVec.add_assoc, Nat.add_zero]
  · rw [e3, e2, r14_1]; simp only [e1, Regs.get_set_same]; exact rd_write_same _ _ _
  · intro a ha; rw [e3, e2, r14_1]; simp only [e1]; exact rd_write_apart _ _ _ _ ha
  · intro r hr; rw [e3, e2, e1]; simp [Regs.get_set_ne _ _ _ _ (Ne.symm hr)]

/-- **evalTo_run.** Operand evaluation simulates `evalW`: an `ok ws` leaves ws at BUF slots t…; an overflow reaches OVF; both
    within the frame. -/
theorem evalTo_run {C : Ctx3} {p : Program} (hcan : canonical C.ovf = true) :
    ∀ (o : WOpd) (t : Nat) (s : Cpu) (rest : List AI) (ρ : List W) (N : Nat), s.stopped = false →
    CodeAt C p s.rip (evalTo C t o ++ rest) → t + need o ≤ N → EvalPre s t N ρ → EvalPost C p s t o ρ N
  | .slice off len, t, s, rest, ρ, N, hs, hc, htN, ⟨hw, hN, hap⟩ => by
    simp only [EvalPost, evalW]
    have htN' : t + len ≤ N := by simpa [need] using htN
    by_cases hlen : off + len ≤ ρ.length
    · simp only [hlen, if_true]
      obtain ⟨u, h1, h2, h3, h4, _, h6, h7⟩ := evalTo_slice_run hs hc hw hlen hN htN'
        (fun i j hi hj => hap (t + i) (off + j) (by omega) (by omega) (by omega))
      exact ⟨2 * len, u, h1, h2, h3, h6, fun a ha => h7 a (fun j hj => ha (t + j) (by omega) (by omega)),
        fun r a _ _ => h4 r a⟩
    · simp only [hlen, if_false]
  | .imm ws, t, s, rest, ρ, N, hs, hc, htN, ⟨hw, hN, hap⟩ => by
    simp only [EvalPost, evalW]
    rw [imm_eq_immL] at hc ⊢
    obtain ⟨u, h1, h2, h3, h4, h5, h6⟩ := imm_run (C := C) .r14 (by decide) _ _ ws.length s rest hs hc
      (fun i j hi hj hij => slot_apart hN (by simp [need] at htN; omega) (by simp [need] at htN; omega) (by omega))
    refine ⟨2 * ws.length, u, h1, h2, h3, wordsAt_slot.mpr (fun j hj => by rw [h5 j hj]; simp [List.getD, List.getElem?_eq_getElem hj]),
      fun a ha => h6 a (fun j hj => ha (t + j) (by omega) (by simp [need] at htN; omega)), fun r a _ _ => h4 r a⟩
  | .take n a, t, s, rest, ρ, N, hs, hc, htN, hpre => by
    have IH := evalTo_run hcan a t s rest ρ N hs (by simpa [evalTo] using hc) (by simpa [need] using htN) hpre
    simp only [EvalPost, evalW] at IH ⊢
    cases ha : evalW ρ a with
    | bad => simp [WRes.bind]
    | ovf => simp only [ha, WRes.bind] at IH ⊢; exact IH
    | ok xs =>
      simp only [ha, WRes.bind] at IH ⊢
      obtain ⟨k, u, h1, h2, h3, h4, h5⟩ := IH
      refine ⟨k, u, h1, h2, by simpa [evalTo] using h3, fun j hj => ?_, h5⟩
      simp only [List.length_take] at hj
      rw [h4 j (by omega)]; simp [List.getElem_take]
  | .arith op a b, t, s, rest, ρ, N, hs, hc, htN, hpre => by
    have hc' : CodeAt C p s.rip (evalTo C t a ++ (evalTo C (t + 1) b ++ (arithCode C t op ++ rest))) := by
      simpa [evalTo, List.append_assoc] using hc
    have hneed : t + need a ≤ N ∧ t + 1 + need b ≤ N ∧ t + 2 ≤ N := by simp [need] at htN; omega
    have IHa := evalTo_run hcan a t s _ ρ N hs hc' hneed.1 hpre
    simp only [EvalPost, evalW] at IHa ⊢
    cases ha : evalW ρ a with
    | bad => simp [WRes.bind]
    | ovf =>
      simp only [ha, WRes.bind] at IHa ⊢; exact IHa
    | ok xs =>
      simp only [ha, WRes.bind] at IHa ⊢
      obtain ⟨n1, u1, hr1, hs1, hrip1, hw1, hf1⟩ := IHa
      have hc1 : CodeAt C p u1.rip (evalTo C (t + 1) b ++ (arithCode C t op ++ rest)) := by
        rw [hrip1]; exact codeAt_right hc'
      have IHb := evalTo_run hcan b (t + 1) u1 _ ρ N hs1 hc1 hneed.2.1 (pre_mono (by omega) hf1 hpre)
      simp only [EvalPost] at IHb
      cases hb : evalW ρ b with
      | bad => simp [WRes.bind]
      | ovf =>
        simp only [hb, WRes.bind] at IHb ⊢
        obtain ⟨n2, u2, hr2, hs2, hrip2, hf2⟩ := IHb
        exact ⟨n1 + n2, u2, by rw [runP_add, hr1, hr2], hs2, hrip2, frame_trans (t' := t + 1) (by omega) hf1 hf2⟩
      | ok ys =>
        simp only [hb, WRes.bind] at IHb ⊢
        obtain ⟨n2, u2, hr2, hs2, hrip2, hw2, hf2⟩ := IHb
        have hB1 : u1.regs.get .r14 = s.regs.get .r14 := hf1.2 .r14 (by decide) (by decide) (by decide)
        have hB2 : u2.regs.get .r14 = s.regs.get .r14 := by rw [hf2.2 .r14 (by decide) (by decide) (by decide), hB1]
        have hN := hpre.2.1
        match xs, ys, hw1, hw2 with
        | [x], [y], hw1, hw2 =>
          simp only
          have hx : rd u2.mem (u2.regs.get .r14 + slot t) = x := by
            rw [hB2, hf2.1 _ (fun i hi hi' => by rw [hB1]; exact slot_apart hN hi' (by omega) (by omega))]
            have := (wordsAt_slot.mp hw1) 0 (by simp); simpa using this
          have hy : rd u2.mem (u2.regs.get .r14 + slot (t + 1)) = y := by
            rw [hB2, ← hB1]; have := (wordsAt_slot.mp hw2) 0 (by simp); simpa using this
          have hc2 : CodeAt C p u2.rip (arithCode C t op ++ rest) := by rw [hrip2]; exact codeAt_right hc1
          obtain ⟨hov, hok⟩ := arith_run op hs2 hc2 hcan hx hy
          cases happ : op.apply x y with
          | bad => trivial
          | ovf =>
            obtain ⟨n3, u3, hr3, hs3, hrip3, hm3, hreg3⟩ := hov happ
            refine ⟨n1 + n2 + n3, u3, by rw [runP_add, runP_add, hr1, hr2, hr3], hs3, hrip3, ?_⟩
            exact frame_trans (t' := t + 1) (by omega) hf1 (frame_trans (t' := t + 1) (le_refl _) hf2 ⟨fun a _ => by rw [hm3], hreg3⟩)
          | ok zs =>
            match zs, happ with
            | [z], happ =>
              obtain ⟨n3, u3, hr3, hs3, hrip3, hz3, hfr3, hreg3⟩ := hok z happ
              refine ⟨n1 + n2 + n3, u3, by rw [runP_add, runP_add, hr1, hr2, hr3], hs3, ?_, ?_, ?_⟩
              · rw [hrip3, hrip2, hrip1]
                simp only [evalTo, bytes_append, ofNat_add64, BitVec.add_assoc]
              · exact wordsAt_slot.mpr (fun j hj => by
                  simp only [List.length_singleton] at hj
                  have : j = 0 := by omega
                  subst this; rw [← hB2]; simpa using hz3)
              · refine frame_trans (t' := t) (le_refl _) hf1 (frame_trans (t' := t) (le_refl _) (frame_weaken (by omega) hf2) ⟨fun a ha => hfr3 a ?_, hreg3⟩)
                exact ha t (by omega) (by omega)
            | [], happ => cases op <;> simp [AOp.apply, chk] at happ <;> split at happ <;> cases happ
            | _ :: _ :: _, happ => cases op <;> simp [AOp.apply, chk] at happ <;> split at happ <;> cases happ
        | [], _, _, _ => simp
        | _ :: _ :: _, _, _, _ => simp
        | [_], [], _, _ => simp
        | [_], _ :: _ :: _, _, _ => simp
  | .bnot a, t, s, rest, ρ, N, hs, hc, htN, hpre => by
    have hc' : CodeAt C p s.rip (evalTo C t a ++ ([movi .rax 1, ld .rcx .r14 (slot t),
        .op (.bin .sub .q (.reg .rax) (.reg .rcx)), st .r14 (slot t) .rax] ++ rest)) := by
      simpa [evalTo, List.append_assoc] using hc
    have hneed : t + need a ≤ N ∧ t + 1 ≤ N := by simp [need] at htN; omega
    have IH := evalTo_run hcan a t s _ ρ N hs hc' hneed.1 hpre
    simp only [EvalPost, evalW] at IH ⊢
    cases ha : evalW ρ a with
    | bad => simp [WRes.bind]
    | ovf => simp only [ha, WRes.bind] at IH ⊢; exact IH
    | ok xs =>
      simp only [ha, WRes.bind] at IH ⊢
      obtain ⟨n1, u1, hr1, hs1, hrip1, hw1, hf1⟩ := IH
      match xs, hw1 with
      | [x], hw1 =>
        simp only
        have hB1 : u1.regs.get .r14 = s.regs.get .r14 := hf1.2 .r14 (by decide) (by decide) (by decide)
        have hx : rd u1.mem (u1.regs.get .r14 + slot t) = x := by
          rw [hB1]; have := (wordsAt_slot.mp hw1) 0 (by simp); simpa using this
        obtain ⟨u2, hr2, hs2, hrip2, hz2, hfr2, hreg2⟩ := bnot_tail_run hs1 (by rw [hrip1]; exact codeAt_right hc') hx
        refine ⟨n1 + 4, u2, by rw [runP_add, hr1, hr2], hs2, ?_, ?_, ?_⟩
        · rw [hrip2, hrip1]; simp only [evalTo, bytes_append, ofNat_add64, BitVec.add_assoc]
        · exact wordsAt_slot.mpr (fun j hj => by
            simp only [List.length_singleton] at hj
            have : j = 0 := by omega
            subst this; rw [← hB1]; simpa using hz2)
        · refine frame_trans (t' := t) (le_refl _) hf1 ⟨fun a ha => hfr2 a (ha t (le_refl _) (by omega)), ?_⟩
          intro r h1 h2 _; exact hreg2 r h1 h2
      | [], _ => simp
      | _ :: _ :: _, _ => simp
  | .cat a b, t, s, rest, ρ, N, hs, hc, htN, hpre => by
    have hc' : CodeAt C p s.rip (evalTo C t a ++ (evalTo C (t + wid a) b ++ rest)) := by
      simpa [evalTo, List.append_assoc] using hc
    have hwa := wid_le_need a
    have hneed : t + need a ≤ N ∧ t + wid a + need b ≤ N := by simp [need] at htN; omega
    have IHa := evalTo_run hcan a t s _ ρ N hs hc' hneed.1 hpre
    simp only [EvalPost, evalW] at IHa ⊢
    cases ha : evalW ρ a with
    | bad => simp [WRes.bind]
    | ovf => simp only [ha, WRes.bind] at IHa ⊢; exact IHa
    | ok xs =>
      simp only [ha, WRes.bind] at IHa ⊢
      obtain ⟨n1, u1, hr1, hs1, hrip1, hw1, hf1⟩ := IHa
      have hlen : xs.length = wid a := evalW_length a ρ xs ha
      have hc1 : CodeAt C p u1.rip (evalTo C (t + wid a) b ++ rest) := by rw [hrip1]; exact codeAt_right hc'
      have IHb := evalTo_run hcan b (t + wid a) u1 rest ρ N hs1 hc1 hneed.2 (pre_mono (by omega) hf1 hpre)
      simp only [EvalPost] at IHb
      have hB1 : u1.regs.get .r14 = s.regs.get .r14 := hf1.2 .r14 (by decide) (by decide) (by decide)
      cases hb : evalW ρ b with
      | bad => simp [WRes.bind]
      | ovf =>
        simp only [hb, WRes.bind] at IHb ⊢
        obtain ⟨n2, u2, hr2, hs2, hrip2, hf2⟩ := IHb
        exact ⟨n1 + n2, u2, by rw [runP_add, hr1, hr2], hs2, hrip2, frame_trans (t' := t + wid a) (by omega) hf1 hf2⟩
      | ok ys =>
        simp only [hb, WRes.bind] at IHb ⊢
        obtain ⟨n2, u2, hr2, hs2, hrip2, hw2, hf2⟩ := IHb
        have hN := hpre.2.1
        refine ⟨n1 + n2, u2, by rw [runP_add, hr1, hr2], hs2, ?_, ?_, frame_trans (t' := t + wid a) (by omega) hf1 hf2⟩
        · rw [hrip2, hrip1]; simp only [evalTo, bytes_append, ofNat_add64, BitVec.add_assoc]
        · refine wordsAt_slot.mpr (fun j hj => ?_)
          simp only [List.length_append] at hj
          by_cases hjx : j < xs.length
          · rw [List.getElem_append_left hjx]
            rw [hf2.1 _ (fun i hi hi' => by rw [hB1]; exact slot_apart hN hi' (by omega) (by omega))]
            exact (wordsAt_slot.mp hw1) j hjx
          · rw [List.getElem_append_right (by omega)]
            have := (wordsAt_slot.mp hw2) (j - xs.length) (by omega)
            rw [hB1, show t + wid a + (j - xs.length) = t + j by omega] at this
            exact this
  | .drop n a, t, s, rest, ρ, N, hs, hc, htN, hpre => by
    have hc' : CodeAt C p s.rip (evalTo C t a ++ (moves (t + n) t (wid a - n) ++ rest)) := by
      simpa [evalTo, List.append_assoc] using hc
    have hwa := wid_le_need a
    have hneed : t + need a ≤ N := by simpa [need] using htN
    have IH := evalTo_run hcan a t s _ ρ N hs hc' hneed hpre
    simp only [EvalPost, evalW] at IH ⊢
    cases ha : evalW ρ a with
    | bad => simp [WRes.bind]
    | ovf => simp only [ha, WRes.bind] at IH ⊢; exact IH
    | ok xs =>
      simp only [ha, WRes.bind] at IH ⊢
      obtain ⟨n1, u1, hr1, hs1, hrip1, hw1, hf1⟩ := IH
      have hlen : xs.length = wid a := evalW_length a ρ xs ha
      have hB1 : u1.regs.get .r14 = s.regs.get .r14 := hf1.2 .r14 (by decide) (by decide) (by decide)
      have hN : (u1.regs.get .r14).toNat + 8 * N < 2 ^ 64 := by rw [hB1]; exact hpre.2.1
      have hc1 : CodeAt C p u1.rip (copyL .r14 .r14 (fun j => slot (t + n + j)) (fun j => slot (t + j)) (wid a - n) ++ rest) := by
        rw [hrip1, ← moves_eq_copyL]; exact codeAt_right hc'
      obtain ⟨u2, hr2, hs2, hrip2, hreg2, _, hcp2, hfr2⟩ := copy_run (C := C) .r14 .r14 (by decide) (by decide) _ _ (wid a - n)
        u1 rest hs1 hc1 (fun i j hij hj => slot_apart hN (by omega) (by omega) (by omega))
        (fun i j hi hj hij => slot_apart hN (by omega) (by omega) (by omega))
      refine ⟨n1 + 2 * (wid a - n), u2, by rw [runP_add, hr1, hr2], hs2, ?_, ?_, ?_⟩
      · rw [hrip2, hrip1, ← moves_eq_copyL]; simp only [evalTo, bytes_append, ofNat_add64, BitVec.add_assoc]
      · refine wordsAt_slot.mpr (fun j hj => ?_)
        simp only [List.length_drop] at hj
        rw [← hB1, hcp2 j (by omega), List.getElem_drop]
        have := (wordsAt_slot.mp hw1) (n + j) (by omega)
        rw [← hB1, show t + (n + j) = t + n + j by omega] at this
        exact this
      · refine frame_trans (t' := t) (le_refl _) hf1 ⟨fun a ha => hfr2 a (fun j hj => ha (t + j) (by omega) (by omega)), ?_⟩
        intro r h1 _ _; exact hreg2 r h1
  | .tag tg pad a, t, s, rest, ρ, N, hs, hc, htN, hpre => by
    have hc' : CodeAt C p s.rip (evalTo C (t + 1) a ++ ([movi .rax tg, st .r14 (slot t) .rax, movi .rax 0] ++
        (stL .r14 (fun j => slot (t + 1 + wid a + j)) pad ++ rest))) := by
      have := hc; simp only [evalTo, pad_eq_stL, List.append_assoc] at this; simpa [List.append_assoc] using this
    have hwa := wid_le_need a
    have hneed : t + 1 + need a ≤ N ∧ t + 1 + wid a + pad ≤ N := by simp [need] at htN; omega
    have IH := evalTo_run hcan a (t + 1) s _ ρ N hs hc' hneed.1 (pre_mono (by omega) (frame_refl s t N) hpre)
    simp only [EvalPost, evalW] at IH ⊢
    cases ha : evalW ρ a with
    | bad => simp [WRes.bind]
    | ovf =>
      simp only [ha, WRes.bind] at IH ⊢
      obtain ⟨n1, u1, hr1, hs1, hrip1, hf1⟩ := IH
      exact ⟨n1, u1, hr1, hs1, hrip1, frame_weaken (by omega) hf1⟩
    | ok xs =>
      simp only [ha, WRes.bind] at IH ⊢
      obtain ⟨n1, u1, hr1, hs1, hrip1, hw1, hf1⟩ := IH
      have hlen : xs.length = wid a := evalW_length a ρ xs ha
      have hB1 : u1.regs.get .r14 = s.regs.get .r14 := hf1.2 .r14 (by decide) (by decide) (by decide)
      have hN := hpre.2.1
      have hc1 : CodeAt C p u1.rip ([movi .rax tg, st .r14 (slot t) .rax, movi .rax 0] ++
          (stL .r14 (fun j => slot (t + 1 + wid a + j)) pad ++ rest)) := by rw [hrip1]; exact codeAt_right hc'
      obtain ⟨u2, hr2, hs2, hrip2, htg2, hrax2, hfr2, hreg2⟩ := tag_head_run hs1 hc1
      have hB2 : u2.regs.get .r14 = s.regs.get .r14 := by rw [hreg2 .r14 (by decide), hB1]
      have hc2 : CodeAt C p u2.rip (stL .r14 (fun j => slot (t + 1 + wid a + j)) pad ++ rest) := by
        rw [hrip2]; exact codeAt_right hc1
      obtain ⟨u3, hr3, hs3, hrip3, hreg3, hst3, hfr3⟩ := st_run (C := C) .r14 _ pad u2 rest hs2 hc2
        (fun i j hi hj hij => by rw [hB2]; exact slot_apart hN (by omega) (by omega) (by omega))
      refine ⟨n1 + 3 + pad, u3, by rw [runP_add, runP_add, hr1, hr2, hr3], hs3, ?_, ?_, ?_⟩
      · rw [hrip3, hrip2, hrip1]
        simp only [evalTo, pad_eq_stL, bytes_append, ofNat_add64, BitVec.add_assoc]
      · refine wordsAt_slot.mpr (fun j hj => ?_)
        simp only [List.length_cons, List.length_append, List.length_replicate] at hj
        have hpadfr : ∀ i, i ≠ t + 1 + wid a + 0 → True := fun _ _ => trivial
        rcases j with _ | j
        · simp only [List.getElem_cons_zero, Nat.add_zero]
          rw [hfr3 _ (fun k hk => by rw [hB2]; exact slot_apart hN (by omega) (by omega) (by omega)), ← hB1]
          exact htg2
        · simp only [List.cons_append, List.getElem_cons_succ]
          by_cases hjx : j < xs.length
          · rw [List.getElem_append_left hjx]
            rw [hfr3 _ (fun k hk => by rw [hB2]; exact slot_apart hN (by omega) (by omega) (by omega)),
              hfr2 _ (by rw [hB1]; exact slot_apart hN (by omega) (by omega) (by omega))]
            have := (wordsAt_slot.mp hw1) j hjx
            rw [show t + 1 + j = t + (j + 1) by omega] at this
            exact this
          · rw [List.getElem_append_right (by omega), List.getElem_replicate]
            have := hst3 (j - xs.length) (by omega)
            rw [hB2, show t + 1 + wid a + (j - xs.length) = t + (j + 1) by omega, hrax2] at this
            exact this
      · refine frame_trans (t' := t) (le_refl _) (frame_weaken (by omega) hf1) ⟨fun a ha => ?_, ?_⟩
        · rw [hfr3 a (fun k hk => by rw [hB2, ← hB1]; exact ha _ (by omega) (by omega)),
            hfr2 a (ha t (le_refl _) (by omega))]
        · intro r h1 _ _; rw [show u3.regs = u2.regs from hreg3]; exact hreg2 r h1

/-! ## From the layout premise (byte-disjoint regions) to word-level `Apart` -/

theorem apart_of_disjoint {P Q : W → Prop} (hd : ∀ a, P a → ¬ Q a) {a b : W}
    (ha : ∀ i, i < 8 → P (a + BitVec.ofNat 64 i)) (hb : ∀ j, j < 8 → Q (b + BitVec.ofNat 64 j)) : VIRBridge.Apart a b :=
  fun i j hi hj e => hd _ (ha i hi) (by rw [e]; exact hb j hj)

/-- Every byte of BUF slot i (i < bufN) is in BUF. -/
theorem buf_word (L : Lay3) {i : Nat} (hi : i < L.bufN) : ∀ k, k < 8 → inBuf L (L.buf + slot i + BitVec.ofNat 64 k) := by
  intro k hk
  refine ⟨8 * i + k, by omega, ?_⟩
  simp only [slot, BitVec.add_assoc, ← ofNat_add64]

/-- Every byte of ENV word j of a list of n words at e (inside ENV) is in ENV. -/
theorem env_word (L : Lay3) {e : W} {n j : Nat} (hlo : L.envLo.toNat ≤ e.toNat) (hhi : e.toNat + 8 * n ≤ L.envTop.toNat)
    (hj : j < n) : ∀ k, k < 8 → inEnv L (e + slot j + BitVec.ofNat 64 k) := by
  intro k hk
  have hT := L.envTop.isLt
  have : (e + slot j + BitVec.ofNat 64 k).toNat = e.toNat + 8 * j + k := by
    simp only [slot, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  simp only [inEnv, this]; omega

/-- Every byte of the cell at a live address is a live byte. -/
theorem live_word (L : Lay3) {c : W} (hc : L.live c) : ∀ k, k < 8 → inLive L (c + BitVec.ofNat 64 k) :=
  fun k hk => ⟨c, hc, k, hk, rfl⟩

/-- Every byte of CB word m (m < 4) is in CB. -/
theorem cb_word (L : Lay3) {m : Nat} (hm : m < 4) : ∀ k, k < 8 → inCb L (L.cb + BitVec.ofNat 64 (8 * m) + BitVec.ofNat 64 k) := by
  intro k hk
  refine ⟨8 * m + k, by omega, ?_⟩
  simp only [BitVec.add_assoc, ← ofNat_add64]

/-- A BUF slot is apart from an ENV word. -/
theorem buf_env_apart {L : Lay3} (hL : L.Ok) {i : Nat} (hi : i < L.bufN) {e : W} {n j : Nat}
    (hlo : L.envLo.toNat ≤ e.toNat) (hhi : e.toNat + 8 * n ≤ L.envTop.toNat) (hj : j < n) :
    VIRBridge.Apart (L.buf + slot i) (e + slot j) :=
  apart_of_disjoint (fun a h1 h2 => hL.env_buf a h2 h1) (buf_word L hi) (env_word L hlo hhi hj)

theorem buf_live_apart {L : Lay3} (hL : L.Ok) {i : Nat} (hi : i < L.bufN) {c : W} (hc : L.live c) :
    VIRBridge.Apart (L.buf + slot i) c :=
  apart_of_disjoint hL.buf_live (buf_word L hi) (live_word L hc)

theorem buf_cb_apart {L : Lay3} (hL : L.Ok) {i : Nat} (hi : i < L.bufN) {m : Nat} (hm : m < 4) :
    VIRBridge.Apart (L.buf + slot i) (L.cb + BitVec.ofNat 64 (8 * m)) :=
  apart_of_disjoint hL.buf_cb (buf_word L hi) (cb_word L hm)

/-! ## The stack frames survive any change confined to BUF -/

/-- The frames from rsp end at the driver's slot: `rsp + 16·(|k|+1) = rsp0`, in Nat (no wrap). -/
theorem frames_bound {C : Ctx3} {p : Program} {L : Lay3} {m : Mem} :
    ∀ (k : List (WCode × List W)) (rsp lo : W), Frames C p L m rsp lo k → rsp.toNat + 16 * (k.length + 1) = L.rsp0.toNat
  | [], rsp, lo, h => by simpa using h.2.2.2.1
  | (c, ρ) :: k, rsp, lo, h => by
    obtain ⟨q, a, _, _, _, _, _, _, hb, _, hf⟩ := h
    have ih := frames_bound k (rsp + 16) a hf
    have hR := L.rsp0.isLt
    have : (rsp + 16).toNat = rsp.toNat + 16 := by simp only [BitVec.toNat_add]; simp; omega
    simp only [List.length_cons]; omega

theorem stk_word (L : Lay3) {x : W} (hlo : L.stkLo.toNat ≤ x.toNat) (hhi : x.toNat ≤ L.rsp0.toNat) (hL : L.Ok) :
    ∀ k, k < 8 → inStk L (x + BitVec.ofNat 64 k) := by
  intro k hk
  have := hL.stk_nowrap
  have e : (x + BitVec.ofNat 64 k).toNat = x.toNat + k := by simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  simp only [inStk, e]; omega

theorem buf_stk_apart {L : Lay3} (hL : L.Ok) {i : Nat} (hi : i < L.bufN) {x : W} (hlo : L.stkLo.toNat ≤ x.toNat)
    (hhi : x.toNat ≤ L.rsp0.toNat) : VIRBridge.Apart (L.buf + slot i) x :=
  apart_of_disjoint (fun a h1 h2 => hL.stk_buf a h2 h1) (buf_word L hi) (by
    intro j hj; exact stk_word L hlo hhi hL j hj)

/-- Two memories agreeing on every word apart from BUF. -/
def AgreeBuf (L : Lay3) (m m' : Mem) : Prop :=
  ∀ a, (∀ i, i < L.bufN → VIRBridge.Apart (L.buf + slot i) a) → rd m' a = rd m a

theorem wordsAt_agree {L : Lay3} (hL : L.Ok) {m m' : Mem} (hag : AgreeBuf L m m') {e : W} {ρ : List W}
    (hlo : L.envLo.toNat ≤ e.toNat) (hhi : e.toNat + 8 * ρ.length ≤ L.envTop.toNat) (hw : WordsAt m e ρ) : WordsAt m' e ρ := by
  intro j hj
  have := hag (e + slot j) (fun i hi => buf_env_apart hL hi hlo hhi hj)
  simp only [rd, slot] at this; rw [this]; exact hw j hj

theorem frames_agree {C : Ctx3} {p : Program} {L : Lay3} (hL : L.Ok) {m m' : Mem} (hag : AgreeBuf L m m') :
    ∀ (k : List (WCode × List W)) (rsp lo : W), L.envLo.toNat ≤ lo.toNat → L.stkLo.toNat ≤ rsp.toNat →
      Frames C p L m rsp lo k → Frames C p L m' rsp lo k
  | [], rsp, lo, hel, hsl, ⟨h1, h2, h3, h4, h5, h6⟩ => by
    have hR := L.rsp0.isLt
    have hst := hL.stk_nowrap
    have e8 : (rsp + 8).toNat = rsp.toNat + 8 := by simp only [BitVec.toNat_add]; simp; omega
    refine ⟨?_, h2, ?_, h4, ?_, h6⟩
    · rw [hag rsp (fun i hi => buf_stk_apart hL hi hsl (by omega))]; exact h1
    · rw [hag (rsp + 8) (fun i hi => buf_stk_apart hL hi (by omega) (by omega))]; exact h3
    · rw [hag L.rsp0 (fun i hi => buf_stk_apart hL hi (by omega) (le_refl _))]; exact h5
  | (c, ρ) :: k, rsp, lo, hel, hsl, ⟨q, a, h1, h2, h3, h4, h5, h6, h7, h9, h8⟩ => by
    have hR := L.rsp0.isLt
    have e8 : (rsp + 8).toNat = rsp.toNat + 8 := by simp only [BitVec.toNat_add]; simp; omega
    have e16 : (rsp + 16).toNat = rsp.toNat + 16 := by simp only [BitVec.toNat_add]; simp; omega
    refine ⟨q, a, ?_, ?_, h3, h4, h5, wordsAt_agree hL hag (by omega) h5 h6, h7, h9,
      frames_agree hL hag k (rsp + 16) a (by omega) (by omega) h8⟩
    · rw [hag rsp (fun i hi => buf_stk_apart hL hi hsl (by omega))]; exact h1
    · rw [hag (rsp + 8) (fun i hi => buf_stk_apart hL hi (by omega) (by omega))]; exact h2

/-! ## R3 is kept by a change confined to BUF and scratch registers; cmp with an immediate; ret; the exits -/

theorem cb_off (L : Lay3) (m : Nat) : L.cb + BitVec.ofNat 64 (8 * m) = L.cb + BitVec.ofNat 64 (8 * m) := rfl

/-- **r3_of_buf.** A machine state that differs from an R3 state only in BUF words and in rax, rcx, rdx (and the flags, rip and
    oracle) is an R3 state at the same ρ and continuations, for any code it is placed at. -/
theorem r3_of_buf {C : Ctx3} {p : Program} {L : Lay3} (hL : L.Ok) {c c' : WCode} {ρ : List W} {k : List (WCode × List W)}
    {wm : WMem} {s u : Cpu} (hR : R3 C p L (.run c ρ k, wm) s) (hm : AgreeBuf L s.mem u.mem)
    (hreg : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → u.regs.get r = s.regs.get r) (hus : u.stopped = false)
    (hcu : CodeAt C p u.rip (gen C u.rip c')) : R3 C p L (.run c' ρ k, wm) u := by
  obtain ⟨_, _, ⟨hB, hX, ⟨hc1, hc2, hc3⟩, hRep⟩, hlo, hhi, hw, hfr, hsl, hocc⟩ := hR
  have g12 := hreg .r12 (by decide) (by decide) (by decide)
  have gsp := hreg .rsp (by decide) (by decide) (by decide)
  refine ⟨hus, hcu, ⟨by rw [hreg .r14 (by decide) (by decide) (by decide), hB],
    by rw [hreg .rbx (by decide) (by decide) (by decide), hX], ⟨?_, ?_, ?_⟩, ?_⟩, by rw [g12]; exact hlo,
    by rw [g12]; exact hhi, by rw [g12]; exact wordsAt_agree hL hm hlo hhi hw,
    by rw [g12, gsp]; exact frames_agree hL hm k _ _ hlo hsl hfr, by rw [gsp]; exact hsl, by rw [g12]; exact hocc⟩
  · rw [hm (L.cb + 8) (fun i hi => buf_cb_apart hL hi (m := 1) (by decide))]; exact hc1
  · rw [hm (L.cb + 16) (fun i hi => buf_cb_apart hL hi (m := 2) (by decide))]; exact hc2
  · rw [hm (L.cb + 24) (fun i hi => buf_cb_apart hL hi (m := 3) (by decide))]; exact hc3
  · intro a ha
    have := hm a (fun i hi => buf_live_apart hL hi ha)
    simp only [rd] at this; rw [this]; exact hRep a ha

theorem stepP_cmp_ri {C : Ctx3} {p : Program} {s : Cpu} {r : GPR} {v : W} {l : List AI}
    (hs : s.stopped = false) (hc : CodeAt C p s.rip (.op (.bin .cmp .q (.reg r) (.imm v)) :: l)) :
    stepP p s = { s with flags := Flags.sub .q (s.regs.get r) v s.flags, rip := nxt C s.rip (.op (.bin .cmp .q (.reg r) (.imm v))) } := by
  rw [stepP_of_at hs (codeAt_head hc)]
  simp only [AI.toInstr]
  rw [step_cmp_reg_imm .q r v (live_of hs)]
  simp [Cpu.getReg, nxt, AI.size]

theorem stepP_ret {C : Ctx3} {p : Program} {s : Cpu} {l : List AI}
    (hs : s.stopped = false) (hc : CodeAt C p s.rip (.op .ret :: l)) (hcan : canonical (rd s.mem (s.regs.get .rsp)) = true) :
    stepP p s = { s with regs := s.regs.set .rsp (s.regs.get .rsp + 8), rip := rd s.mem (s.regs.get .rsp) } := by
  rw [stepP_of_at hs (codeAt_head hc)]
  simp only [AI.toInstr]
  rw [step_ret_taken (live_of hs) (by simpa [Cpu.readMem, Mem.readSize, Size.bytes, rd] using hcan)]
  simp [Cpu.setReg, Cpu.readMem, Mem.readSize, Size.bytes, rd, Value.writeView]

/-- **exit_run.** From an exit's first instruction (FAULT, OVF or RES) with the control block in place, the driver's slot holding its
    return address, and the word memory represented: 4 steps return to the driver with STATUS = `code`, and `Common` still holds. -/
theorem exit_run {C : Ctx3} {p : Program} {L : Lay3} (hL : L.Ok) {code : W} {wm : WMem} {s : Cpu} {rest : List AI}
    (hs : s.stopped = false) (hc : CodeAt C p s.rip (exitCode code ++ rest)) (hcom : Common L wm s)
    (hret : rd s.mem L.rsp0 = L.ret0) (hcan : canonical L.ret0 = true) :
    ∃ u, runP p 4 s = u ∧ Returned L code u ∧ Common L wm u := by
  obtain ⟨hB, hX, ⟨hc1, hc2, hc3⟩, hRep⟩ := hcom
  have c0 : CodeAt C p s.rip (movi .rax code :: st .rbx 0 .rax :: ld .rsp .rbx 8 :: .op .ret :: rest) := by
    simpa [exitCode] using hc
  have e1 := stepP_movi hs c0
  set s1 := stepP p s
  have h1 : s1.stopped = false := by rw [e1]; exact hs
  have c1 : CodeAt C p s1.rip (st .rbx 0 .rax :: ld .rsp .rbx 8 :: .op .ret :: rest) := by rw [e1]; exact codeAt_tail c0
  have e2 := stepP_st h1 c1
  set s2 := stepP p s1
  have h2 : s2.stopped = false := by rw [e2]; exact h1
  have c2 : CodeAt C p s2.rip (ld .rsp .rbx 8 :: .op .ret :: rest) := by rw [e2]; exact codeAt_tail c1
  have e3 := stepP_ld h2 c2
  set s3 := stepP p s2
  have h3 : s3.stopped = false := by rw [e3]; exact h2
  have c3 : CodeAt C p s3.rip (.op .ret :: rest) := by rw [e3]; exact codeAt_tail c2
  have hcbN := hL.cb_nowrap
  have a01 : VIRBridge.Apart L.cb (L.cb + 8) := by
    have := slot_apart (b := L.cb) (N := 4) (by omega) (i := 0) (j := 1) (by decide) (by decide) (by decide)
    simpa [slot] using this
  have a02 : VIRBridge.Apart L.cb (L.cb + 16) := by
    have := slot_apart (b := L.cb) (N := 4) (by omega) (i := 0) (j := 2) (by decide) (by decide) (by decide)
    simpa [slot] using this
  have a03 : VIRBridge.Apart L.cb (L.cb + 24) := by
    have := slot_apart (b := L.cb) (N := 4) (by omega) (i := 0) (j := 3) (by decide) (by decide) (by decide)
    simpa [slot] using this
  have cbw0 : ∀ k, k < 8 → inCb L (L.cb + BitVec.ofNat 64 k) := fun k hk => ⟨k, by omega, rfl⟩
  have hR0 := L.rsp0.isLt
  have hst := hL.stk_nowrap
  have a0s : VIRBridge.Apart L.cb L.rsp0 := apart_of_disjoint (fun a h1 h2 => hL.stk_cb a h2 h1) cbw0 (by
    intro j hj
    have e : (L.rsp0 + BitVec.ofNat 64 j).toNat = L.rsp0.toNat + j := by simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    simp only [inStk, e]; constructor
    · have := hL.stk_lo_le; omega
    · omega)
  have mem2 : s2.mem = s.mem.writeSize .q L.cb code := by rw [e2, e1]; simp [hX]
  have rsp3 : s3.regs.get .rsp = L.rsp0 := by
    rw [e3, e2]; simp [e1, hX]
    exact (rd_write_apart _ _ _ _ a01).trans hc1
  have e4 := stepP_ret h3 c3 (by rw [rsp3, show s3.mem = s2.mem by rw [e3], mem2, rd_write_apart _ _ _ _ a0s, hret]; exact hcan)
  refine ⟨stepP p s3, rfl, ⟨by rw [e4]; exact h3, ?_, ?_, ?_⟩, ⟨?_, ?_, ⟨?_, ?_, ?_⟩, ?_⟩⟩
  · rw [e4, rsp3, show s3.mem = s2.mem by rw [e3], mem2, rd_write_apart _ _ _ _ a0s, hret]
  · rw [e4]; simp [rsp3]
  · rw [e4, show s3.mem = s2.mem by rw [e3], mem2]; exact rd_write_same _ _ _
  · rw [e4, e3, e2, e1]; simp [hB]
  · rw [e4, e3, e2, e1]; simp [hX]
  · rw [e4, show s3.mem = s2.mem by rw [e3], mem2, rd_write_apart _ _ _ _ a01]; exact hc1
  · rw [e4, show s3.mem = s2.mem by rw [e3], mem2, rd_write_apart _ _ _ _ a02]; exact hc2
  · rw [e4, show s3.mem = s2.mem by rw [e3], mem2, rd_write_apart _ _ _ _ a03]; exact hc3
  · intro a ha
    rw [e4, show s3.mem = s2.mem by rw [e3], mem2]
    have := rd_write_apart s.mem L.cb a code (apart_of_disjoint hL.cb_live cbw0 (live_word L ha))
    simp only [rd] at this; rw [this]; exact hRep a ha

/-! ## One word step: `ite` -/

theorem common_of_buf {L : Lay3} (hL : L.Ok) {wm : WMem} {s u : Cpu} (hc : Common L wm s) (hm : AgreeBuf L s.mem u.mem)
    (hreg : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → u.regs.get r = s.regs.get r) : Common L wm u := by
  obtain ⟨hB, hX, ⟨hc1, hc2, hc3⟩, hRep⟩ := hc
  refine ⟨by rw [hreg .r14 (by decide) (by decide) (by decide), hB], by rw [hreg .rbx (by decide) (by decide) (by decide), hX],
    ⟨?_, ?_, ?_⟩, ?_⟩
  · rw [hm (L.cb + 8) (fun i hi => buf_cb_apart hL hi (m := 1) (by decide))]; exact hc1
  · rw [hm (L.cb + 16) (fun i hi => buf_cb_apart hL hi (m := 2) (by decide))]; exact hc2
  · rw [hm (L.cb + 24) (fun i hi => buf_cb_apart hL hi (m := 3) (by decide))]; exact hc3
  · intro a ha
    have := hm a (fun i hi => buf_live_apart hL hi ha)
    simp only [rd] at this; rw [this]; exact hRep a ha

theorem frames_ret0 {C : Ctx3} {p : Program} {L : Lay3} {m : Mem} :
    ∀ (k : List (WCode × List W)) (rsp lo : W), Frames C p L m rsp lo k → rd m L.rsp0 = L.ret0
  | [], _, _, h => h.2.2.2.2.1
  | (_, _) :: k, rsp, _, ⟨_, a, _, _, _, _, _, _, _, _, hf⟩ => frames_ret0 k (rsp + 16) a hf

/-- A Frame from slot 0 over all of BUF, from a state whose r14 is BUF's base, is an AgreeBuf. -/
theorem agree_of_frame {L : Lay3} {s u : Cpu} (hB : s.regs.get .r14 = L.buf) (hf : Frame s u 0 L.bufN) : AgreeBuf L s.mem u.mem :=
  fun a ha => hf.1 a (fun i _ hi => by rw [hB]; exact ha i hi)

theorem agree_trans {L : Lay3} {m1 m2 m3 : Mem} (h1 : AgreeBuf L m1 m2) (h2 : AgreeBuf L m2 m3) : AgreeBuf L m1 m3 :=
  fun a ha => by rw [h2 a ha, h1 a ha]

/-- The machine facts every word step starts from: canonical code addresses and driver return, the exits in place. -/
structure StepEnv (C : Ctx3) (p : Program) (L : Lay3) : Prop where
  ok : L.Ok
  canon : ∀ a i, p.at? a = some i → canonical a = true
  ret_canon : canonical L.ret0 = true
  fault : CodeAt C p C.fault (exitCode stFault)
  ovf : CodeAt C p C.ovf (exitCode stOvf)
  res : CodeAt C p C.res (exitCode stRes)

theorem canon_of_codeAt {C : Ctx3} {p : Program} {L : Lay3} (E : StepEnv C p L) {a : W} {i : AI} {l : List AI}
    (h : CodeAt C p a (i :: l)) : canonical a = true := E.canon a _ (codeAt_head h)

/-- An overflow reached at OVF from a state related to an R3 run state by a BUF-confined change ends at the driver as R3 `ovf`. -/
theorem ovf_exit {C : Ctx3} {p : Program} {L : Lay3} (E : StepEnv C p L) {c : WCode} {ρ : List W} {k : List (WCode × List W)}
    {wm : WMem} {s u : Cpu} (hR : R3 C p L (.run c ρ k, wm) s) (hm : AgreeBuf L s.mem u.mem)
    (hreg : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → u.regs.get r = s.regs.get r) (hus : u.stopped = false) (hrip : u.rip = C.ovf) :
    ∃ v, runP p 4 u = v ∧ R3 C p L (.ovf, wm) v := by
  obtain ⟨_, _, hcom, hlo, _, _, hfr, hsl, _⟩ := hR
  have hret : rd u.mem L.rsp0 = L.ret0 := by
    have hR0 := frames_ret0 k _ _ hfr
    rw [hm L.rsp0 (fun i hi => buf_stk_apart E.ok hi (E.ok.stk_lo_le) (le_refl _))]; exact hR0
  obtain ⟨v, hv, hret', hcom'⟩ := exit_run (rest := []) E.ok hus (by rw [hrip]; simpa using E.ovf) (common_of_buf E.ok hcom hm hreg)
    hret E.ret_canon
  exact ⟨v, hv, hret', hcom'⟩

/-- The `.e`/`.ne` conditions after `cmp r, imm`. -/
theorem cc_ne_sub (x y : W) (f : Flags) : Cc.eval .ne (Flags.sub .q x y f) = !decide (x = y) := by
  have := cc_e_sub x y f; simp only [Cc.eval] at this ⊢; rw [this]

/-- **sim_ite.** A word step of `ite o c₁ c₂` is simulated: c₁ or c₂ is reached as an R3 run state, an overflow as R3 `ovf`. -/
theorem sim_ite {C : Ctx3} {p : Program} {L : Lay3} (E : StepEnv C p L) {tbl : Table} {o : WOpd} {c₁ c₂ : WCode}
    {ρ : List W} {k : List (WCode × List W)} {wm : WMem} {s : Cpu} (hR : R3 C p L (.run (.ite o c₁ c₂) ρ k, wm) s)
    (hneed : need o ≤ L.bufN) {W' : WSt × WMem} (hstep : stepW tbl (.run (.ite o c₁ c₂) ρ k, wm) = some W') :
    ∃ n, 0 < n ∧ R3 C p L W' (runP p n s) := by
  have hR0 := hR
  obtain ⟨hs, hcode, hcom, hlo, hhi, hw, hfr, hsl, hocc⟩ := hR
  have hB : s.regs.get .r14 = L.buf := hcom.1
  have hL := E.ok
  set pre : List AI := evalTo C 0 o ++ [ld .rax .r14 (slot 0), .op (.bin .cmp .q (.reg .rax) (.imm 1))] with hpre_def
  set p₁ := s.rip + BitVec.ofNat 64 (bytes C pre + 6) with hp₁
  set g₁ := gen C p₁ c₁ with hg₁
  set l₂ := p₁ + BitVec.ofNat 64 (bytes C g₁) with hl₂
  set mid : List AI := [.op (.bin .cmp .q (.reg .rax) (.imm 0)), .jccA .ne C.fault] with hmid
  set g₂ := gen C (l₂ + BitVec.ofNat 64 (bytes C mid)) c₂ with hg₂
  have hc : CodeAt C p s.rip (pre ++ ([.jccA .ne l₂] ++ (g₁ ++ (mid ++ g₂)))) := by
    have h0 := hcode; simp only [gen] at h0; simp only [List.append_assoc] at h0
    rw [hpre_def, List.append_assoc]; exact h0
  have hcE : CodeAt C p s.rip (evalTo C 0 o ++ ([ld .rax .r14 (slot 0), .op (.bin .cmp .q (.reg .rax) (.imm 1))] ++
      ([.jccA .ne l₂] ++ (g₁ ++ (mid ++ g₂))))) := by
    have := hc; rw [hpre_def, List.append_assoc] at this; exact this
  have hcJ : CodeAt C p (s.rip + BitVec.ofNat 64 (bytes C pre)) (.jccA .ne l₂ :: (g₁ ++ (mid ++ g₂))) := codeAt_right hc
  have hcG1 : CodeAt C p p₁ (g₁ ++ (mid ++ g₂)) := by
    have := codeAt_right hcJ (a := [.jccA .ne l₂])
    simp only [bytes_cons, bytes_nil, AI.size, Nat.add_zero, BitVec.add_assoc, ← ofNat_add64, List.append_eq, List.singleton_append] at this
    exact this
  have hcM : CodeAt C p l₂ (mid ++ g₂) := codeAt_right hcG1
  have hcG2 : CodeAt C p (l₂ + BitVec.ofNat 64 (bytes C mid)) g₂ := codeAt_right hcM
  have hpre : EvalPre s 0 L.bufN ρ := ⟨hw, by rw [hB]; exact hL.buf_nowrap,
    fun i j _ hi hj => by rw [hB]; exact buf_env_apart hL hi hlo hhi hj⟩
  have hpost := evalTo_run (C := C) (p := p) (canon_of_codeAt E E.ovf) o 0 s _ ρ L.bufN hs hcE (by omega) hpre
  simp only [EvalPost] at hpost
  simp only [stepW] at hstep
  cases ho : evalW ρ o with
  | bad => rw [ho] at hstep; cases hstep
  | ovf =>
    rw [ho] at hstep hpost; cases hstep
    obtain ⟨n1, u1, hr1, hs1, hrip1, hf1⟩ := hpost
    obtain ⟨v, hv, hRv⟩ := ovf_exit E hR0 (agree_of_frame hB hf1) hf1.2 hs1 hrip1
    exact ⟨n1 + 4, by omega, by rw [runP_add, hr1, hv]; exact hRv⟩
  | ok ws =>
    rw [ho] at hstep hpost
    obtain ⟨n1, u1, hr1, hs1, hrip1, hw1, hf1⟩ := hpost
    match ws, hstep, hw1 with
    | [b], hstep, hw1 =>
      simp only at hstep
      have hB1 : u1.regs.get .r14 = L.buf := by rw [hf1.2 .r14 (by decide) (by decide) (by decide), hB]
      have hbv : rd u1.mem (u1.regs.get .r14 + slot 0) = b := by
        rw [hB1, ← hB]; have := (wordsAt_slot.mp hw1) 0 (by simp); simpa using this
      have c1 : CodeAt C p u1.rip (ld .rax .r14 (slot 0) :: .op (.bin .cmp .q (.reg .rax) (.imm 1)) ::
          ([.jccA .ne l₂] ++ (g₁ ++ (mid ++ g₂)))) := by
        rw [hrip1]; have := codeAt_right hcE; simpa only [List.cons_append, List.singleton_append, List.nil_append] using this
      have e2 := stepP_ld hs1 c1
      set u2 := stepP p u1 with hu2
      have h2 : u2.stopped = false := by rw [e2]; exact hs1
      have c2 : CodeAt C p u2.rip (.op (.bin .cmp .q (.reg .rax) (.imm 1)) :: ([.jccA .ne l₂] ++ (g₁ ++ (mid ++ g₂)))) := by
        rw [e2]; exact codeAt_tail c1
      have e3 := stepP_cmp_ri h2 c2
      set u3 := stepP p u2 with hu3
      have h3 : u3.stopped = false := by rw [e3]; exact h2
      have rip3 : u3.rip = s.rip + BitVec.ofNat 64 (bytes C pre) := by
        rw [e3, e2, hrip1, hpre_def]
        simp only [nxt, ld, bytes_append, bytes_cons, bytes_nil, AI.size, ofNat_add64, BitVec.add_assoc, Nat.add_zero]
      have c3 : CodeAt C p u3.rip (.jccA .ne l₂ :: (g₁ ++ (mid ++ g₂))) := by rw [rip3]; exact hcJ
      have rax2 : u2.regs.get .rax = b := by rw [e2]; simpa using hbv
      have fl3 : Cc.eval .ne u3.flags = !decide (b = 1) := by rw [e3]; simp only [rax2]; exact cc_ne_sub b 1 _
      have e4 := stepP_jccA h3 c3 (canon_of_codeAt E (l := mid.tail ++ g₂) (by simpa [hmid] using hcM))
      set u4 := stepP p u3 with hu4
      have h4 : u4.stopped = false := by rw [e4]; exact h3
      have mem4 : u4.mem = u1.mem := by rw [e4, e3, e2]
      have reg4 : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → u4.regs.get r = s.regs.get r := by
        intro r ha hc' hd; rw [e4, e3, e2]; simp only [Regs.get_set_ne _ _ _ _ (Ne.symm ha)]; exact hf1.2 r ha hc' hd
      have ag1 : AgreeBuf L s.mem u1.mem := agree_of_frame hB hf1
      by_cases hb1 : b = 1
      · rw [if_pos hb1, Option.some.injEq] at hstep; subst hstep
        have rip4 : u4.rip = p₁ := by
          rw [e4]; simp only [fl3, hb1, decide_true, Bool.not_true, Bool.false_eq_true, if_false, rip3, hp₁, ofNat_add64,
            BitVec.add_assoc]; rfl
        refine ⟨n1 + 3, by omega, ?_⟩
        rw [runP_add, hr1]
        show R3 C p L _ u4
        exact r3_of_buf hL hR0 (by rw [mem4]; exact ag1) reg4 h4 (by rw [rip4]; exact codeAt_left hcG1)
      · by_cases hb0 : b = 0
        · rw [if_neg hb1, if_pos hb0, Option.some.injEq] at hstep; subst hstep
          have hne3 : Cc.eval .ne u3.flags = true := by
            rw [fl3]; simp only [Bool.not_eq_true', decide_eq_false_iff_not]; exact hb1
          have rip4 : u4.rip = l₂ := by rw [e4]; simp only [hne3, if_true]
          have c4 : CodeAt C p u4.rip (.op (.bin .cmp .q (.reg .rax) (.imm 0)) :: .jccA .ne C.fault :: g₂) := by
            rw [rip4]; simpa [hmid] using hcM
          have e5 := stepP_cmp_ri h4 c4
          set u5 := stepP p u4 with hu5
          have h5 : u5.stopped = false := by rw [e5]; exact h4
          have c5 : CodeAt C p u5.rip (.jccA .ne C.fault :: g₂) := by rw [e5]; exact codeAt_tail c4
          have rax4 : u4.regs.get .rax = b := by rw [e4, e3]; exact rax2
          have fl5 : Cc.eval .ne u5.flags = !decide (b = 0) := by rw [e5]; simp only [rax4]; exact cc_ne_sub b 0 _
          have e6 := stepP_jccA h5 c5 (canon_of_codeAt E E.fault)
          have rip6 : (stepP p u5).rip = l₂ + BitVec.ofNat 64 (bytes C mid) := by
            have hne5 : Cc.eval .ne u5.flags = false := by
              rw [fl5]; simp only [Bool.not_eq_false', decide_eq_true_eq]; exact hb0
            rw [e6]; simp only [hne5, Bool.false_eq_true, if_false]
            rw [e5, rip4, hmid]
            simp only [nxt, bytes_cons, bytes_nil, AI.size, ofNat_add64, BitVec.add_assoc, Nat.add_zero]
            all_goals rfl
          refine ⟨n1 + 5, by omega, ?_⟩
          rw [runP_add, hr1]
          show R3 C p L _ (stepP p u5)
          refine r3_of_buf hL hR0 (by rw [e6, e5, mem4]; exact ag1) ?_ (by rw [e6]; exact h5) (by rw [rip6]; exact hcG2)
          intro r ha hc' hd; rw [e6, e5]; exact reg4 r ha hc' hd
        · rw [if_neg hb1, if_neg hb0] at hstep; cases hstep
    | [], hstep, _ => simp at hstep
    | _ :: _ :: _, hstep, _ => simp at hstep

/-! ## The ENV room check -/

theorem stepP_mov_rr {C : Ctx3} {p : Program} {s : Cpu} {r r' : GPR} {l : List AI}
    (hs : s.stopped = false) (hc : CodeAt C p s.rip (.op (.mov .q (.reg r) (.reg r')) :: l)) :
    stepP p s = { s with regs := s.regs.set r (s.regs.get r'), rip := nxt C s.rip (.op (.mov .q (.reg r) (.reg r'))) } := by
  rw [stepP_of_at hs (codeAt_head hc)]
  simp only [AI.toInstr]
  rw [step_mov_reg_reg .q r r' (live_of hs)]
  simp [Value.writeView, Cpu.getReg, nxt, AI.size]

/-- **envRoom_run.** The ENV room check for n words: in 5 steps it reaches RES exactly when `r12 − envLo < 8n` (bytes), and
    otherwise falls through; memory unchanged, registers other than rax, rcx unchanged. -/
theorem envRoom_run {C : Ctx3} {p : Program} {s : Cpu} {n : Nat} {lo : W} {rest : List AI}
    (hs : s.stopped = false) (hc : CodeAt C p s.rip (envRoom C n ++ rest)) (hcb : rd s.mem (s.regs.get .rbx + 16) = lo)
    (hge : lo.toNat ≤ (s.regs.get .r12).toNat) (h8n : 8 * n < 2 ^ 64) (hcan : canonical C.res = true) :
    ∃ u, runP p 5 s = u ∧ u.stopped = false ∧ u.mem = s.mem ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → u.regs.get r = s.regs.get r) ∧
      u.rip = (if (s.regs.get .r12).toNat - lo.toNat < 8 * n then C.res else s.rip + BitVec.ofNat 64 (bytes C (envRoom C n))) := by
  have c0 : CodeAt C p s.rip (ld .rcx .rbx 16 :: .op (.mov .q (.reg .rax) (.reg .r12)) :: .op (.bin .sub .q (.reg .rax) (.reg .rcx)) ::
      .op (.bin .cmp .q (.reg .rax) (.imm (slot n))) :: .jccA .b C.res :: rest) := by simpa [envRoom] using hc
  have e1 := stepP_ld hs c0
  set s1 := stepP p s
  have h1 : s1.stopped = false := by rw [e1]; exact hs
  have c1 : CodeAt C p s1.rip (.op (.mov .q (.reg .rax) (.reg .r12)) :: .op (.bin .sub .q (.reg .rax) (.reg .rcx)) ::
      .op (.bin .cmp .q (.reg .rax) (.imm (slot n))) :: .jccA .b C.res :: rest) := by rw [e1]; exact codeAt_tail c0
  have e2 := stepP_mov_rr h1 c1
  set s2 := stepP p s1
  have h2 : s2.stopped = false := by rw [e2]; exact h1
  have c2 : CodeAt C p s2.rip (.op (.bin .sub .q (.reg .rax) (.reg .rcx)) ::
      .op (.bin .cmp .q (.reg .rax) (.imm (slot n))) :: .jccA .b C.res :: rest) := by rw [e2]; exact codeAt_tail c1
  have e3 := stepP_sub_rr h2 c2
  set s3 := stepP p s2
  have h3 : s3.stopped = false := by rw [e3]; exact h2
  have c3 : CodeAt C p s3.rip (.op (.bin .cmp .q (.reg .rax) (.imm (slot n))) :: .jccA .b C.res :: rest) := by
    rw [e3]; exact codeAt_tail c2
  have e4 := stepP_cmp_ri h3 c3
  set s4 := stepP p s3
  have h4 : s4.stopped = false := by rw [e4]; exact h3
  have c4 : CodeAt C p s4.rip (.jccA .b C.res :: rest) := by rw [e4]; exact codeAt_tail c3
  have e5 := stepP_jccA h4 c4 hcan
  have rax3 : s3.regs.get .rax = s.regs.get .r12 - lo := by
    have hcb' : rd s.mem (s.regs.get .rbx + 16) = lo := hcb
    rw [e3, e2, e1]; simp only [Regs.get_set_same, Regs.get_set_ne _ _ _ _ (show GPR.rax ≠ GPR.rcx by decide),
      Regs.get_set_ne _ _ _ _ (show GPR.rcx ≠ GPR.r12 by decide), Regs.get_set_ne _ _ _ _ (show GPR.rcx ≠ GPR.rbx by decide)]
    rw [hcb']
  have hb : Cc.eval .b s4.flags = decide ((s.regs.get .r12).toNat - lo.toNat < 8 * n) := by
    rw [e4, rax3, cc_b_of_sub]
    simp only [Value.uval, Value.trunc_q, slot, BitVec.toNat_sub, BitVec.toNat_ofNat]
    congr 1; apply propext
    have := (s.regs.get .r12).isLt
    constructor <;> intro h <;> omega
  refine ⟨stepP p s4, rfl, by rw [e5]; exact h4, by rw [e5, e4, e3, e2, e1], ?_, ?_⟩
  · intro r ha hc'; rw [e5, e4, e3, e2, e1]
    simp [Regs.get_set_ne _ _ _ _ (Ne.symm ha), Regs.get_set_ne _ _ _ _ (Ne.symm hc')]
  · rw [e5, hb]
    by_cases hlt : (s.regs.get .r12).toNat - lo.toNat < 8 * n
    · simp [hlt]
    · simp only [hlt, decide_false, Bool.false_eq_true, if_false]
      rw [e4, e3, e2, e1]
      simp only [nxt, envRoom, ld, bytes_cons, bytes_nil, AI.size, ofNat_add64, BitVec.add_assoc, Nat.add_zero]
      all_goals rfl

/-! ## The static prepend: room check, `lea r12`, then BUF → ENV copies -/

theorem stepP_lea_dec {C : Ctx3} {p : Program} {s : Cpu} {n : Nat} {l : List AI}
    (hs : s.stopped = false) (hc : CodeAt C p s.rip (.op (.lea .q .r12 { base := some .r12, disp := -(slot n) }) :: l)) :
    stepP p s = { s with regs := s.regs.set .r12 (s.regs.get .r12 - slot n), rip := nxt C s.rip (.op (.lea .q .r12 { base := some .r12, disp := -(slot n) })) } := by
  rw [stepP_of_at hs (codeAt_head hc)]
  simp only [AI.toInstr]
  rw [step_lea .q .r12 _ (live_of hs) rfl]
  simp [Value.writeView, Ea.offset, nxt, AI.size, BitVec.sub_eq_add_neg]

theorem prep_eq_copyL (sb n : Nat) :
    ((List.range n).flatMap fun j => [ld .rax .r14 (slot (sb + j)), st .r12 (slot j) .rax]) =
      copyL .r14 .r12 (fun j => slot (sb + j)) (fun j => slot j) n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.range_succ, List.flatMap_append, ih]; simp [copyL]

/-- **prependBuf_run, success.** When `r12 − envLo ≥ 8n`: in 6 + 2n steps r12 drops by 8n and ENV words 0…n−1 at the new r12 hold
    BUF slots sb… as they were; words apart from those n keep their value; registers other than rax, rcx, r12 are unchanged. -/
theorem prependBuf_ok {C : Ctx3} {p : Program} {s : Cpu} {sb n : Nat} {lo : W} {rest : List AI}
    (hs : s.stopped = false) (hc : CodeAt C p s.rip (prependBuf C sb n ++ rest)) (hcb : rd s.mem (s.regs.get .rbx + 16) = lo)
    (hge : lo.toNat + 8 * n ≤ (s.regs.get .r12).toNat) (hcan : canonical C.res = true)
    (hap : ∀ i j, i < n → j < n → VIRBridge.Apart (s.regs.get .r12 - slot n + slot i) (s.regs.get .r14 + slot (sb + j))) :
    ∃ u, runP p (5 + 1 + 2 * n) s = u ∧ u.stopped = false ∧ u.rip = s.rip + BitVec.ofNat 64 (bytes C (prependBuf C sb n)) ∧
      u.regs.get .r12 = s.regs.get .r12 - slot n ∧
      (∀ j, j < n → rd u.mem (s.regs.get .r12 - slot n + slot j) = rd s.mem (s.regs.get .r14 + slot (sb + j))) ∧
      (∀ a, (∀ j, j < n → VIRBridge.Apart (s.regs.get .r12 - slot n + slot j) a) → rd u.mem a = rd s.mem a) ∧
      ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .r12 → u.regs.get r = s.regs.get r := by
  have hR := (s.regs.get .r12).isLt
  have h8n : 8 * n < 2 ^ 64 := by omega
  have hc' : CodeAt C p s.rip (envRoom C n ++ (.op (.lea .q .r12 { base := some .r12, disp := -(slot n) }) ::
      (copyL .r14 .r12 (fun j => slot (sb + j)) (fun j => slot j) n ++ rest))) := by
    have := hc; simp only [prependBuf, prep_eq_copyL, List.append_assoc] at this; simpa using this
  obtain ⟨u1, hr1, hs1, hm1, hreg1, hrip1⟩ := envRoom_run hs hc' hcb (by omega) h8n hcan
  have hnot : ¬ ((s.regs.get .r12).toNat - lo.toNat < 8 * n) := by omega
  rw [if_neg hnot] at hrip1
  have c1 : CodeAt C p u1.rip (.op (.lea .q .r12 { base := some .r12, disp := -(slot n) }) ::
      (copyL .r14 .r12 (fun j => slot (sb + j)) (fun j => slot j) n ++ rest)) := by rw [hrip1]; exact codeAt_right hc'
  have e2 := stepP_lea_dec hs1 c1
  set u2 := stepP p u1 with hu2
  have h2 : u2.stopped = false := by rw [e2]; exact hs1
  have c2 : CodeAt C p u2.rip (copyL .r14 .r12 (fun j => slot (sb + j)) (fun j => slot j) n ++ rest) := by
    rw [e2]; exact codeAt_tail c1
  have r12_1 : u1.regs.get .r12 = s.regs.get .r12 := hreg1 .r12 (by decide) (by decide)
  have r14_1 : u1.regs.get .r14 = s.regs.get .r14 := hreg1 .r14 (by decide) (by decide)
  have r12_2 : u2.regs.get .r12 = s.regs.get .r12 - slot n := by rw [e2]; simp [r12_1]
  have r14_2 : u2.regs.get .r14 = s.regs.get .r14 := by rw [e2]; simp [r14_1]
  have hE : (s.regs.get .r12 - slot n).toNat = (s.regs.get .r12).toNat - 8 * n := by
    simp only [slot, BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  obtain ⟨u3, hr3, hs3, hrip3, hreg3, _, hcp3, hfr3⟩ := copy_run (C := C) .r14 .r12 (by decide) (by decide) _ _ n u2 rest h2 c2
    (fun i j _ hj => by rw [r12_2, r14_2]; exact hap i j (by omega) hj)
    (fun i j hi hj hij => by rw [r12_2]; exact slot_apart (by omega) hi hj hij)
  refine ⟨u3, ?_, hs3, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show 5 + 1 + 2 * n = 5 + (1 + 2 * n) by omega, runP_add, hr1, runP_add, show runP p 1 u1 = u2 from rfl, hr3]
  · rw [hrip3, e2, hrip1]
    simp only [prependBuf, prep_eq_copyL, nxt, bytes_append, bytes_cons, bytes_nil, ofNat_add64, BitVec.add_assoc, Nat.add_zero]
  · rw [hreg3 .r12 (by decide), r12_2]
  · intro j hj
    rw [← r12_2, hcp3 j hj, r14_2, e2, hm1]
  · intro a ha
    rw [hfr3 a (fun j hj => by rw [r12_2]; exact ha j hj), e2, hm1]
  · intro r ha hc' h12
    rw [hreg3 r ha, e2]; simp only [Regs.get_set_ne _ _ _ _ (Ne.symm h12)]; exact hreg1 r ha hc'

/-! ## R3 after a prepend: memory changed in BUF and in the n new ENV words below the old r12 -/

/-- Two 8-byte words in order, the first ending at or before the second starts, are apart. -/
theorem order_apart {x y : W} (hxy : x.toNat + 8 ≤ y.toNat) (hy : y.toNat + 8 ≤ 2 ^ 64) : VIRBridge.Apart x y := by
  intro i j hi hj e
  have := congrArg BitVec.toNat e
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at this
  omega

/-- Memory agreement on the words a frame chain reads: stack words, and ENV words at or above `lo`. -/
def AgreeOn (L : Lay3) (lo : W) (m m' : Mem) : Prop :=
  (∀ x, L.stkLo.toNat ≤ x.toNat → x.toNat ≤ L.rsp0.toNat → rd m' x = rd m x) ∧
  (∀ x, lo.toNat ≤ x.toNat → x.toNat + 8 ≤ L.envTop.toNat → rd m' x = rd m x)

theorem wordsAt_on {L : Lay3} {lo : W} {m m' : Mem} (hag : AgreeOn L lo m m') {e : W} {ρ : List W}
    (hlo : lo.toNat ≤ e.toNat) (hhi : e.toNat + 8 * ρ.length ≤ L.envTop.toNat) (hw : WordsAt m e ρ) : WordsAt m' e ρ := by
  intro j hj
  have hT := L.envTop.isLt
  have he : (e + BitVec.ofNat 64 (8 * j)).toNat = e.toNat + 8 * j := by simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have := hag.2 (e + BitVec.ofNat 64 (8 * j)) (by omega) (by omega)
  simp only [rd] at this; rw [this]; exact hw j hj

theorem frames_lo_mono {C : Ctx3} {p : Program} {L : Lay3} {m : Mem} :
    ∀ (k : List (WCode × List W)) (rsp lo lo' : W), lo'.toNat ≤ lo.toNat → Frames C p L m rsp lo k → Frames C p L m rsp lo' k
  | [], _, _, _, hle, ⟨h1, h2, h3, h4, h5, h6⟩ => ⟨h1, h2, h3, h4, h5, by omega⟩
  | (_, _) :: _, _, _, _, hle, ⟨q, a, h1, h2, h3, h4, h5, h6, h7, h9, h8⟩ => ⟨q, a, h1, h2, h3, by omega, h5, h6, h7, h9, h8⟩

theorem frames_on {C : Ctx3} {p : Program} {L : Lay3} (hL : L.Ok) {lo0 : W} {m m' : Mem} (hag : AgreeOn L lo0 m m') :
    ∀ (k : List (WCode × List W)) (rsp lo : W), lo0.toNat ≤ lo.toNat → L.stkLo.toNat ≤ rsp.toNat →
      Frames C p L m rsp lo k → Frames C p L m' rsp lo k
  | [], rsp, lo, hel, hsl, ⟨h1, h2, h3, h4, h5, h6⟩ => by
    have hR := L.rsp0.isLt
    have e8 : (rsp + 8).toNat = rsp.toNat + 8 := by simp only [BitVec.toNat_add]; simp; omega
    refine ⟨?_, h2, ?_, h4, ?_, h6⟩
    · rw [hag.1 rsp hsl (by omega)]; exact h1
    · rw [hag.1 (rsp + 8) (by omega) (by omega)]; exact h3
    · rw [hag.1 L.rsp0 hL.stk_lo_le (le_refl _)]; exact h5
  | (c, ρ) :: k, rsp, lo, hel, hsl, ⟨q, a, h1, h2, h3, h4, h5, h6, h7, h9, h8⟩ => by
    have hR := L.rsp0.isLt
    have e8 : (rsp + 8).toNat = rsp.toNat + 8 := by simp only [BitVec.toNat_add]; simp; omega
    have e16 : (rsp + 16).toNat = rsp.toNat + 16 := by simp only [BitVec.toNat_add]; simp; omega
    refine ⟨q, a, ?_, ?_, h3, h4, h5, wordsAt_on hag (by omega) h5 h6, h7, h9,
      frames_on hL hag k (rsp + 16) a (by omega) (by omega) h8⟩
    · rw [hag.1 rsp hsl (by omega)]; exact h1
    · rw [hag.1 (rsp + 8) (by omega) (by omega)]; exact h2

/-- **r3_of_prepend.** After a prepend of the n words `ws` (r12 lowered by 8n, the new ENV words holding ws, every other word apart
    from BUF and from those n words unchanged, registers but rax, rcx, rdx, r12 unchanged), R3 holds at `ws ++ ρ`. -/
theorem r3_of_prepend {C : Ctx3} {p : Program} {L : Lay3} (hL : L.Ok) {c c' : WCode} {ρ ws : List W}
    {k : List (WCode × List W)} {wm : WMem} {s u : Cpu} (hR : R3 C p L (.run c ρ k, wm) s)
    (hroom : L.envLo.toNat + 8 * ws.length ≤ (s.regs.get .r12).toNat)
    (hr12 : u.regs.get .r12 = s.regs.get .r12 - slot ws.length)
    (hnew : ∀ j (h : j < ws.length), rd u.mem (s.regs.get .r12 - slot ws.length + slot j) = ws[j])
    (hm : ∀ a, (∀ i, i < L.bufN → VIRBridge.Apart (L.buf + slot i) a) →
      (∀ j, j < ws.length → VIRBridge.Apart (s.regs.get .r12 - slot ws.length + slot j) a) → rd u.mem a = rd s.mem a)
    (hreg : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .r12 → u.regs.get r = s.regs.get r) (hus : u.stopped = false)
    (hcu : CodeAt C p u.rip (gen C u.rip c')) : R3 C p L (.run c' (ws ++ ρ) k, wm) u := by
  obtain ⟨_, _, ⟨hB, hX, ⟨hc1, hc2, hc3⟩, hRep⟩, hlo, hhi, hw, hfr, hsl, hle0, hocc⟩ := hR
  set e := s.regs.get .r12 with he_def
  set n := ws.length with hn_def
  have hT := L.envTop.isLt
  have hE' : (e - slot n).toNat = e.toNat - 8 * n := by simp only [slot, BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have hEj : ∀ j, j < n → (e - slot n + slot j).toNat = e.toNat - 8 * n + 8 * j := by
    intro j hj; simp only [slot, BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  -- a word that lies in ENV at or above e is apart from the new words
  have new_apart_hi : ∀ x, e.toNat ≤ x.toNat → x.toNat + 8 ≤ L.envTop.toNat → ∀ j, j < n →
      VIRBridge.Apart (e - slot n + slot j) x := fun x h1 h2 j hj => order_apart (by rw [hEj j hj]; omega) (by omega)
  -- the new words lie in ENV
  have new_env : ∀ j, j < n → ∀ q, q < 8 → inEnv L (e - slot n + slot j + BitVec.ofNat 64 q) := by
    intro j hj q hq
    have : (e - slot n + slot j + BitVec.ofNat 64 q).toNat = e.toNat - 8 * n + 8 * j + q := by
      simp only [slot, BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
    simp only [inEnv, this]; omega
  have g12 : u.regs.get .r12 = e - slot n := hr12
  have gsp := hreg .rsp (by decide) (by decide) (by decide) (by decide)
  have cb_new : ∀ m, m < 4 → ∀ j, j < n → VIRBridge.Apart (e - slot n + slot j) (L.cb + BitVec.ofNat 64 (8 * m)) :=
    fun m hm j hj => apart_of_disjoint hL.env_cb (new_env j hj) (cb_word L hm)
  have agOn : AgreeOn L e s.mem u.mem := by
    refine ⟨fun x h1 h2 => hm x (fun i hi => buf_stk_apart hL hi h1 h2) (fun j hj =>
      apart_of_disjoint hL.env_stk (new_env j hj) (stk_word L h1 h2 hL)), fun x h1 h2 => hm x ?_ (fun j hj => new_apart_hi x h1 h2 j hj)⟩
    intro i hi
    refine apart_of_disjoint (fun a h3 h4 => hL.env_buf a h4 h3) (buf_word L hi) ?_
    intro q hq
    have : (x + BitVec.ofNat 64 q).toNat = x.toNat + q := by simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    simp only [inEnv, this]; omega
  refine ⟨hus, hcu, ⟨by rw [hreg .r14 (by decide) (by decide) (by decide) (by decide), hB],
    by rw [hreg .rbx (by decide) (by decide) (by decide) (by decide), hX], ⟨?_, ?_, ?_⟩, ?_⟩, ?_, ?_, ?_, ?_, by rw [gsp]; exact hsl, ?_⟩
  · rw [hm (L.cb + 8) (fun i hi => buf_cb_apart hL hi (m := 1) (by decide)) (fun j hj => cb_new 1 (by decide) j hj)]; exact hc1
  · rw [hm (L.cb + 16) (fun i hi => buf_cb_apart hL hi (m := 2) (by decide)) (fun j hj => cb_new 2 (by decide) j hj)]; exact hc2
  · rw [hm (L.cb + 24) (fun i hi => buf_cb_apart hL hi (m := 3) (by decide)) (fun j hj => cb_new 3 (by decide) j hj)]; exact hc3
  · intro a ha
    have := hm a (fun i hi => buf_live_apart hL hi ha) (fun j hj => apart_of_disjoint hL.env_live (new_env j hj) (live_word L ha))
    simp only [rd] at this; rw [this]; exact hRep a ha
  · rw [g12, hE']; omega
  · rw [g12, hE', List.length_append]; omega
  · rw [g12]
    intro j hj
    rw [show e - slot n + BitVec.ofNat 64 (8 * j) = e - slot n + slot j from rfl]
    by_cases hjn : j < n
    · rw [List.getElem_append_left hjn]; exact hnew j hjn
    · rw [List.getElem_append_right (by omega)]
      simp only [List.length_append] at hj
      have hx : e - slot n + slot j = e + slot (j - n) := by
        apply BitVec.eq_of_toNat_eq
        simp only [slot, BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
      rw [hx]
      have hxe : (e + slot (j - n)).toNat = e.toNat + 8 * (j - n) := by
        simp only [slot, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
      have hjr : j - n < ρ.length := by omega
      have hb1 : e.toNat ≤ (e + slot (j - n)).toNat := by rw [hxe]; omega
      have hb2 : (e + slot (j - n)).toNat + 8 ≤ L.envTop.toNat := by rw [hxe]; omega
      have := agOn.2 (e + slot (j - n)) hb1 hb2
      simp only [rd] at this; rw [this]
      exact hw (j - n) hjr
  · rw [g12, gsp]
    exact frames_lo_mono k _ e _ (by rw [hE']; omega) (frames_on hL agOn k _ e (le_refl _) hsl hfr)
  · rw [g12, hE', List.length_append]
    constructor <;> omega

/-! ## The RES side -/

/-- Addendum 6's condition: the word state with n more words outgrows ENV's declared size. -/
def EnvOver (L : Lay3) (ρ : List W) (k : List (WCode × List W)) (n : Nat) : Prop :=
  L.env0.toNat - L.envLo.toNat < 8 * (ρ.length + kSize k + n)

/-- **prependBuf_res.** When `r12 − envLo < 8n` the prepend reaches RES in 5 steps with memory unchanged. -/
theorem prependBuf_res {C : Ctx3} {p : Program} {s : Cpu} {sb n : Nat} {lo : W} {rest : List AI}
    (hs : s.stopped = false) (hc : CodeAt C p s.rip (prependBuf C sb n ++ rest)) (hcb : rd s.mem (s.regs.get .rbx + 16) = lo)
    (hge : lo.toNat ≤ (s.regs.get .r12).toNat) (hlt : (s.regs.get .r12).toNat - lo.toNat < 8 * n) (h8n : 8 * n < 2 ^ 64)
    (hcan : canonical C.res = true) :
    ∃ u, runP p 5 s = u ∧ u.stopped = false ∧ u.rip = C.res ∧ u.mem = s.mem ∧
      ∀ r, r ≠ .rax → r ≠ .rcx → u.regs.get r = s.regs.get r := by
  have hc' : CodeAt C p s.rip (envRoom C n ++ ((.op (.lea .q .r12 { base := some .r12, disp := -(slot n) }) ::
      (List.range n).flatMap fun j => [ld .rax .r14 (slot (sb + j)), st .r12 (slot j) .rax]) ++ rest)) := by
    have := hc; simp only [prependBuf, List.append_assoc] at this; simpa using this
  obtain ⟨u, hr, hus, hm, hreg, hrip⟩ := envRoom_run hs hc' hcb hge h8n hcan
  rw [if_pos hlt] at hrip
  exact ⟨u, hr, hus, hrip, hm, hreg⟩

/-- **res_exit.** RES reached from a state related to an R3 run state by a BUF-confined change, with the ENV check failed for n
    words, returns to the driver as `ResExit`, and the word state then satisfies `EnvOver` (Addendum 6). -/
theorem res_exit {C : Ctx3} {p : Program} {L : Lay3} (E : StepEnv C p L) {c : WCode} {ρ : List W} {k : List (WCode × List W)}
    {wm : WMem} {s u : Cpu} {n : Nat} (hR : R3 C p L (.run c ρ k, wm) s) (hm : AgreeBuf L s.mem u.mem)
    (hreg : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → u.regs.get r = s.regs.get r) (hus : u.stopped = false) (hrip : u.rip = C.res)
    (hlt : (s.regs.get .r12).toNat - L.envLo.toNat < 8 * n) :
    ∃ v, runP p 4 u = v ∧ ResExit L v ∧ Common L wm v ∧ EnvOver L ρ k n := by
  obtain ⟨_, _, hcom, hlo, _, _, hfr, hsl, hle0, hocc⟩ := hR
  have hret : rd u.mem L.rsp0 = L.ret0 := by
    rw [hm L.rsp0 (fun i hi => buf_stk_apart E.ok hi (E.ok.stk_lo_le) (le_refl _))]; exact frames_ret0 k _ _ hfr
  obtain ⟨v, hv, hret', hcom'⟩ := exit_run (rest := []) E.ok hus (by rw [hrip]; simpa using E.res) (common_of_buf E.ok hcom hm hreg)
    hret E.ret_canon
  refine ⟨v, hv, hret', hcom', ?_⟩
  simp only [EnvOver]; omega

/-! ## One word step: `case` -/

/-- **case_arm.** From a state reached from an R3 run state by a BUF-confined change, at a prepend of `ws'` (BUF slots 1… holding
    it) followed by the arm's code: the run reaches the arm as an R3 state at `ws' ++ ρ`, or RES with `EnvOver` for those words. -/
theorem case_arm {C : Ctx3} {p : Program} {L : Lay3} (E : StepEnv C p L) {c c' : WCode} {ρ ws' : List W}
    {k : List (WCode × List W)} {wm : WMem} {s u : Cpu} (hR : R3 C p L (.run c ρ k, wm) s)
    (hus : u.stopped = false)
    (hc : CodeAt C p u.rip (prependBuf C 1 ws'.length ++ gen C (u.rip + BitVec.ofNat 64 (bytes C (prependBuf C 1 ws'.length))) c'))
    (hm : AgreeBuf L s.mem u.mem) (hreg : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → u.regs.get r = s.regs.get r)
    (hws : ∀ j (h : j < ws'.length), rd u.mem (L.buf + slot (1 + j)) = ws'[j]) (hbuf : 1 + ws'.length ≤ L.bufN) :
    ∃ n, (R3 C p L (.run c' (ws' ++ ρ) k, wm) (runP p n u)) ∨
      (ResExit L (runP p n u) ∧ Common L wm (runP p n u) ∧ EnvOver L ρ k ws'.length) := by
  have hR0 := hR
  obtain ⟨_, _, ⟨hB, hX, ⟨hc1, hc2, hc3⟩, hRep⟩, hlo, hhi, hw, hfr, hsl, hle0, hocc⟩ := hR
  have hL := E.ok
  have uX : u.regs.get .rbx = L.cb := by rw [hreg .rbx (by decide) (by decide) (by decide), hX]
  have uB : u.regs.get .r14 = L.buf := by rw [hreg .r14 (by decide) (by decide) (by decide), hB]
  have u12 : u.regs.get .r12 = s.regs.get .r12 := hreg .r12 (by decide) (by decide) (by decide)
  have hcb : rd u.mem (u.regs.get .rbx + 16) = L.envLo := by
    rw [uX, hm (L.cb + 16) (fun i hi => buf_cb_apart hL hi (m := 2) (by decide))]; exact hc2
  have hT := L.envTop.isLt
  have hm8 : 8 * ws'.length < 2 ^ 64 := by have := hL.buf_nowrap; omega
  by_cases hlt : (s.regs.get .r12).toNat - L.envLo.toNat < 8 * ws'.length
  · obtain ⟨v, hv, hvs, hvrip, hvm, hvreg⟩ := prependBuf_res hus hc hcb (by rw [u12]; exact hlo) (by rw [u12]; exact hlt) hm8
      (canon_of_codeAt E E.res)
    obtain ⟨x, hx, hres, hcom, hover⟩ := res_exit E hR0 (fun a ha => by rw [hvm]; exact hm a ha)
      (fun r h1 h2 h3 => by rw [hvreg r h1 h2]; exact hreg r h1 h2 h3) hvs hvrip hlt
    exact ⟨5 + 4, Or.inr (by rw [runP_add, hv, hx]; exact ⟨hres, hcom, hover⟩)⟩
  · have hroom : L.envLo.toNat + 8 * ws'.length ≤ (u.regs.get .r12).toNat := by rw [u12]; omega
    have hE' : (u.regs.get .r12 - slot ws'.length).toNat = (u.regs.get .r12).toNat - 8 * ws'.length := by
      simp only [slot, BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
    have new_env : ∀ i, i < ws'.length → ∀ q, q < 8 → inEnv L (u.regs.get .r12 - slot ws'.length + slot i + BitVec.ofNat 64 q) := by
      intro i hi q hq
      have : (u.regs.get .r12 - slot ws'.length + slot i + BitVec.ofNat 64 q).toNat = (u.regs.get .r12).toNat - 8 * ws'.length + 8 * i + q := by
        simp only [slot, BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
      simp only [inEnv, this]; rw [u12] at this ⊢; omega
    have hap : ∀ i j, i < ws'.length → j < ws'.length →
        VIRBridge.Apart (u.regs.get .r12 - slot ws'.length + slot i) (u.regs.get .r14 + slot (1 + j)) := by
      intro i j hi hj; rw [uB]
      exact apart_of_disjoint hL.env_buf (new_env i hi) (buf_word L (by omega))
    obtain ⟨v, hv, hvs, hvrip, hv12, hvcp, hvfr, hvreg⟩ := prependBuf_ok hus hc hcb hroom (canon_of_codeAt E E.res) hap
    refine ⟨5 + 1 + 2 * ws'.length, Or.inl ?_⟩
    rw [hv]
    refine r3_of_prepend hL hR0 (by rw [← u12]; exact hroom) (by rw [hv12, u12]) ?_ ?_ ?_ hvs ?_
    · intro j hj; rw [← u12, hvcp j hj, uB]; exact hws j hj
    · intro a ha hb'
      rw [hvfr a (fun j hj => by rw [u12]; exact hb' j hj)]; exact hm a ha
    · intro r h1 h2 h3 h4; rw [hvreg r h1 h2 h4]; exact hreg r h1 h2 h3
    · rw [hvrip]; exact codeAt_right hc

/-- **sim_case.** A word step of `case o n₁ n₂ c₁ c₂` is simulated: the taken arm is reached as an R3 run state; an overflow returns
    as R3 `ovf`; RES only with `EnvOver` for at most `wid o` words. -/
theorem sim_case {C : Ctx3} {p : Program} {L : Lay3} (E : StepEnv C p L) {tbl : Table} {o : WOpd} {n₁ n₂ : Nat} {c₁ c₂ : WCode}
    {ρ : List W} {k : List (WCode × List W)} {wm : WMem} {s : Cpu} (hR : R3 C p L (.run (.case o n₁ n₂ c₁ c₂) ρ k, wm) s)
    (hneed : need o ≤ L.bufN) {W' : WSt × WMem} (hstep : stepW tbl (.run (.case o n₁ n₂ c₁ c₂) ρ k, wm) = some W') :
    ∃ n, 0 < n ∧ (R3 C p L W' (runP p n s) ∨
      (ResExit L (runP p n s) ∧ Common L wm (runP p n s) ∧ ∃ m, m ≤ wid o ∧ EnvOver L ρ k m)) := by
  have hR0 := hR
  obtain ⟨hs, hcode, hcom, hlo, hhi, hw, hfr, hsl, hocc⟩ := hR
  have hB : s.regs.get .r14 = L.buf := hcom.1
  have hL := E.ok
  set w := wid o - 1 with hw_def
  set pre : List AI := evalTo C 0 o ++ [ld .rax .r14 (slot 0), .op (.bin .cmp .q (.reg .rax) (.imm 0))] with hpre_def
  set pb₁ := prependBuf C 1 (min n₁ w) with hpb₁
  set p₁ := s.rip + BitVec.ofNat 64 (bytes C pre + 6 + bytes C pb₁) with hp₁
  set g₁ := gen C p₁ c₁ with hg₁
  set l₂ := p₁ + BitVec.ofNat 64 (bytes C g₁) with hl₂
  set mid : List AI := [.op (.bin .cmp .q (.reg .rax) (.imm 1)), .jccA .ne C.fault] ++ prependBuf C 1 (min n₂ w) with hmid
  set g₂ := gen C (l₂ + BitVec.ofNat 64 (bytes C mid)) c₂ with hg₂
  have hc : CodeAt C p s.rip (pre ++ ([.jccA .ne l₂] ++ (pb₁ ++ (g₁ ++ (mid ++ g₂))))) := by
    have h0 := hcode; simp only [gen] at h0; simp only [List.append_assoc] at h0
    rw [hpre_def, List.append_assoc]; exact h0
  have hcE : CodeAt C p s.rip (evalTo C 0 o ++ ([ld .rax .r14 (slot 0), .op (.bin .cmp .q (.reg .rax) (.imm 0))] ++
      ([.jccA .ne l₂] ++ (pb₁ ++ (g₁ ++ (mid ++ g₂)))))) := by
    have := hc; rw [hpre_def, List.append_assoc] at this; exact this
  have hcJ : CodeAt C p (s.rip + BitVec.ofNat 64 (bytes C pre)) (.jccA .ne l₂ :: (pb₁ ++ (g₁ ++ (mid ++ g₂)))) := codeAt_right hc
  have hcP1 : CodeAt C p (s.rip + BitVec.ofNat 64 (bytes C pre + 6)) (pb₁ ++ (g₁ ++ (mid ++ g₂))) := by
    have := codeAt_right hcJ (a := [.jccA .ne l₂])
    simp only [bytes_cons, bytes_nil, AI.size, Nat.add_zero, BitVec.add_assoc, ← ofNat_add64, List.append_eq, List.singleton_append] at this
    exact this
  have hcM : CodeAt C p l₂ (mid ++ g₂) := by
    have h1 := codeAt_right (codeAt_right hcP1 (a := pb₁)) (a := g₁)
    simp only [BitVec.add_assoc, ← ofNat_add64] at h1
    rw [hl₂, hp₁, BitVec.add_assoc, ← ofNat_add64]; exact h1
  have hpre : EvalPre s 0 L.bufN ρ := ⟨hw, by rw [hB]; exact hL.buf_nowrap,
    fun i j _ hi hj => by rw [hB]; exact buf_env_apart hL hi hlo hhi hj⟩
  have hpost := evalTo_run (C := C) (p := p) (canon_of_codeAt E E.ovf) o 0 s _ ρ L.bufN hs hcE (by omega) hpre
  simp only [EvalPost] at hpost
  simp only [stepW] at hstep
  have hwn := wid_le_need o
  cases ho : evalW ρ o with
  | bad => rw [ho] at hstep; cases hstep
  | ovf =>
    rw [ho] at hstep hpost; cases hstep
    obtain ⟨n1, u1, hr1, hs1, hrip1, hf1⟩ := hpost
    obtain ⟨v, hv, hRv⟩ := ovf_exit E hR0 (agree_of_frame hB hf1) hf1.2 hs1 hrip1
    exact ⟨n1 + 4, by omega, Or.inl (by rw [runP_add, hr1, hv]; exact hRv)⟩
  | ok tws =>
    rw [ho] at hstep hpost
    obtain ⟨n1, u1, hr1, hs1, hrip1, hw1, hf1⟩ := hpost
    have hlen : tws.length = wid o := evalW_length o ρ tws ho
    match tws, hstep, hw1, hlen with
    | t :: ws, hstep, hw1, hlen =>
      simp only at hstep
      have hlen' : ws.length + 1 = wid o := by simpa using hlen
      have hwsl : ws.length = w := by omega
      have hB1 : u1.regs.get .r14 = L.buf := by rw [hf1.2 .r14 (by decide) (by decide) (by decide), hB]
      have hslots : ∀ j (h : j < ws.length), rd u1.mem (L.buf + slot (1 + j)) = ws[j] := by
        intro j hj; rw [← hB]; have := (wordsAt_slot.mp hw1) (1 + j) (by simp; omega)
        simpa [Nat.add_comm] using this
      have htv : rd u1.mem (u1.regs.get .r14 + slot 0) = t := by
        rw [hB1, ← hB]; have := (wordsAt_slot.mp hw1) 0 (by simp); simpa using this
      have c1 : CodeAt C p u1.rip (ld .rax .r14 (slot 0) :: .op (.bin .cmp .q (.reg .rax) (.imm 0)) ::
          ([.jccA .ne l₂] ++ (pb₁ ++ (g₁ ++ (mid ++ g₂))))) := by
        rw [hrip1]; have := codeAt_right hcE; simpa only [List.cons_append, List.singleton_append, List.nil_append] using this
      have e2 := stepP_ld hs1 c1
      set u2 := stepP p u1 with hu2
      have h2 : u2.stopped = false := by rw [e2]; exact hs1
      have c2 : CodeAt C p u2.rip (.op (.bin .cmp .q (.reg .rax) (.imm 0)) :: ([.jccA .ne l₂] ++ (pb₁ ++ (g₁ ++ (mid ++ g₂))))) := by
        rw [e2]; exact codeAt_tail c1
      have e3 := stepP_cmp_ri h2 c2
      set u3 := stepP p u2 with hu3
      have h3 : u3.stopped = false := by rw [e3]; exact h2
      have rip3 : u3.rip = s.rip + BitVec.ofNat 64 (bytes C pre) := by
        rw [e3, e2, hrip1, hpre_def]
        simp only [nxt, ld, bytes_append, bytes_cons, bytes_nil, AI.size, ofNat_add64, BitVec.add_assoc, Nat.add_zero]
      have c3 : CodeAt C p u3.rip (.jccA .ne l₂ :: (pb₁ ++ (g₁ ++ (mid ++ g₂)))) := by rw [rip3]; exact hcJ
      have rax2 : u2.regs.get .rax = t := by rw [e2]; simpa using htv
      have fl3 : Cc.eval .ne u3.flags = !decide (t = 0) := by rw [e3]; simp only [rax2]; exact cc_ne_sub t 0 _
      have e4 := stepP_jccA h3 c3 (canon_of_codeAt E (l := mid.tail ++ g₂) (by simpa [hmid] using hcM))
      set u4 := stepP p u3 with hu4
      have h4 : u4.stopped = false := by rw [e4]; exact h3
      have mem4 : u4.mem = u1.mem := by rw [e4, e3, e2]
      have reg4 : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → u4.regs.get r = s.regs.get r := by
        intro r ha hc' hd; rw [e4, e3, e2]; simp only [Regs.get_set_ne _ _ _ _ (Ne.symm ha)]; exact hf1.2 r ha hc' hd
      have ag1 : AgreeBuf L s.mem u1.mem := agree_of_frame hB hf1
      by_cases ht0 : t = 0
      · rw [if_pos ht0, Option.some.injEq] at hstep; subst hstep
        have rip4 : u4.rip = s.rip + BitVec.ofNat 64 (bytes C pre + 6) := by
          rw [e4]; simp only [fl3, ht0, decide_true, Bool.not_true, Bool.false_eq_true, if_false, rip3, ofNat_add64,
            BitVec.add_assoc]; rfl
        have hm1 : (ws.take n₁).length = min n₁ w := by simp [hwsl]
        have harm : CodeAt C p u4.rip (prependBuf C 1 (ws.take n₁).length ++
            gen C (u4.rip + BitVec.ofNat 64 (bytes C (prependBuf C 1 (ws.take n₁).length))) c₁) := by
          rw [hm1, rip4, ← hpb₁]
          have h2' : CodeAt C p (s.rip + BitVec.ofNat 64 (bytes C pre + 6)) (pb₁ ++ g₁) := codeAt_left (by
            simpa only [List.append_assoc] using hcP1)
          have hp : s.rip + BitVec.ofNat 64 (bytes C pre + 6) + BitVec.ofNat 64 (bytes C pb₁) = p₁ := by
            rw [hp₁, BitVec.add_assoc, ← ofNat_add64]
          rw [hp]; exact h2'
        obtain ⟨n2, hres⟩ := case_arm E hR0 h4 harm (by rw [mem4]; exact ag1) reg4
          (fun j hj => by rw [mem4]; simp only [List.length_take] at hj; rw [List.getElem_take]; exact hslots j (by omega))
          (by simp only [List.length_take]; have := Nat.min_le_right n₁ ws.length; omega)
        refine ⟨n1 + 3 + n2, by omega, ?_⟩
        rw [runP_add, runP_add, hr1, show runP p 3 u1 = u4 from rfl]
        rcases hres with h | ⟨h1', h2', h3'⟩
        · exact Or.inl h
        · exact Or.inr ⟨h1', h2', _, by simp only [List.length_take]; omega, h3'⟩
      · by_cases ht1 : t = 1
        · rw [if_neg ht0, if_pos ht1, Option.some.injEq] at hstep; subst hstep
          have hne3 : Cc.eval .ne u3.flags = true := by
            rw [fl3]; simp only [Bool.not_eq_true', decide_eq_false_iff_not]; exact ht0
          have rip4 : u4.rip = l₂ := by rw [e4]; simp only [hne3, if_true]
          have c4 : CodeAt C p u4.rip (.op (.bin .cmp .q (.reg .rax) (.imm 1)) :: .jccA .ne C.fault ::
              (prependBuf C 1 (min n₂ w) ++ g₂)) := by rw [rip4]; simpa [hmid] using hcM
          have e5 := stepP_cmp_ri h4 c4
          set u5 := stepP p u4 with hu5
          have h5 : u5.stopped = false := by rw [e5]; exact h4
          have c5 : CodeAt C p u5.rip (.jccA .ne C.fault :: (prependBuf C 1 (min n₂ w) ++ g₂)) := by rw [e5]; exact codeAt_tail c4
          have rax4 : u4.regs.get .rax = t := by rw [e4, e3]; exact rax2
          have fl5 : Cc.eval .ne u5.flags = !decide (t = 1) := by rw [e5]; simp only [rax4]; exact cc_ne_sub t 1 _
          have e6 := stepP_jccA h5 c5 (canon_of_codeAt E E.fault)
          set u6 := stepP p u5 with hu6
          have h6 : u6.stopped = false := by rw [e6]; exact h5
          have hne5 : Cc.eval .ne u5.flags = false := by
            rw [fl5]; simp only [Bool.not_eq_false', decide_eq_true_eq]; exact ht1
          have rip6 : u6.rip = l₂ + BitVec.ofNat 64 (bytes C [.op (.bin .cmp .q (.reg .rax) (.imm 1)), .jccA .ne C.fault]) := by
            rw [e6]; simp only [hne5, Bool.false_eq_true, if_false]
            rw [e5, rip4]
            simp only [nxt, bytes_cons, bytes_nil, AI.size, ofNat_add64, BitVec.add_assoc, Nat.add_zero]
            all_goals rfl
          have hm2 : (ws.take n₂).length = min n₂ w := by simp [hwsl]
          have harm : CodeAt C p u6.rip (prependBuf C 1 (ws.take n₂).length ++
              gen C (u6.rip + BitVec.ofNat 64 (bytes C (prependBuf C 1 (ws.take n₂).length))) c₂) := by
            rw [hm2, rip6]
            have h3' : CodeAt C p (l₂ + BitVec.ofNat 64 (bytes C [.op (.bin .cmp .q (.reg .rax) (.imm 1)), .jccA .ne C.fault]))
                (prependBuf C 1 (min n₂ w) ++ g₂) :=
              codeAt_right (a := [.op (.bin .cmp .q (.reg .rax) (.imm 1)), .jccA .ne C.fault]) (b := prependBuf C 1 (min n₂ w) ++ g₂)
                (by simpa only [hmid, List.append_assoc] using hcM)
            have hq : l₂ + BitVec.ofNat 64 (bytes C [.op (.bin .cmp .q (.reg .rax) (.imm 1)), .jccA .ne C.fault]) +
                BitVec.ofNat 64 (bytes C (prependBuf C 1 (min n₂ w))) = l₂ + BitVec.ofNat 64 (bytes C mid) := by
              rw [hmid, bytes_append, ofNat_add64, BitVec.add_assoc]
            rw [hq]; exact h3'
          have mem6 : u6.mem = u1.mem := by rw [e6, e5, mem4]
          obtain ⟨n2, hres⟩ := case_arm E hR0 h6 harm (by rw [mem6]; exact ag1)
            (fun r ha hc' hd => by rw [e6, e5]; exact reg4 r ha hc' hd)
            (fun j hj => by rw [mem6]; simp only [List.length_take] at hj; rw [List.getElem_take]; exact hslots j (by omega))
            (by simp only [List.length_take]; have := Nat.min_le_right n₂ ws.length; omega)
          refine ⟨n1 + 5 + n2, by omega, ?_⟩
          rw [runP_add, runP_add, hr1, show runP p 5 u1 = u6 from rfl]
          rcases hres with h | ⟨h1', h2', h3'⟩
          · exact Or.inl h
          · exact Or.inr ⟨h1', h2', _, by simp only [List.length_take]; omega, h3'⟩
        · rw [if_neg ht0, if_neg ht1] at hstep; cases hstep
    | [], hstep, _, _ => simp at hstep

end S3
