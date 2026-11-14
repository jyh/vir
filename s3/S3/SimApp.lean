/-
  O95 compiler S3 (compiler/DECLARATIONS-S3.md, Addendum 11): the word step `app f x`, a tail call. f is evaluated first into BUF
  at slot `need x`, x into BUF 0…, the label into rdx, r12 to the activation base `[rsp + 8]`; the dispatch chain reaches the
  label's entry, which prepends x's words (and the label for a fix) and jumps to the body: an R3 run state at the body with ρ' and
  the same continuations, or RES with the successor outgrowing ENV. A separate module; Sim3, SimRet, SimLet are not edited.
-/
import S3.SimLet

namespace S3
open VIRC X86

/-- The table's placement in a program (discharged from `lower3` where `s3_refines` is composed). -/
structure TblOk (C : Ctx3) (p : Program) (tbl : Table) : Prop where
  len : tbl.length = C.tblLen
  len64 : C.tblLen < 2 ^ 64
  body : ∀ i fx b, tbl[i]? = some (fx, b) → C.fix i = fx ∧ CodeAt C p (C.body i) (gen C (C.body i) b)

/-- An entry's code after its compare and branch. -/
def entryTail (C : Ctx3) (wx i : Nat) : List AI :=
  let n := if C.fix i then wx + 1 else wx
  envRoom C n ++ [.op (.lea .q .r12 { base := some .r12, disp := -(slot n) })] ++
    (List.range wx).flatMap (fun j => [ld .rax .r14 (slot j), st .r12 (slot j) .rax]) ++
    (if C.fix i then [st .r12 (slot wx) .rdx] else []) ++ [.jmpA (C.body i)]

theorem dispatchEntry_eq (C : Ctx3) (wx i : Nat) (nx : W) :
    dispatchEntry C wx i nx = [.op (.bin .cmp .q (.reg .rdx) (.imm (BitVec.ofNat 64 i))), .jccA .ne nx] ++ entryTail C wx i := by
  simp only [dispatchEntry, entryTail, List.append_assoc]

theorem dispatch_ne_nil (C : Ctx3) (wx : Nat) (pc : W) : ∀ fuel i, dispatch C wx pc fuel i ≠ []
  | 0, _ => by simp [dispatch]
  | _ + 1, _ => by simp [dispatch, dispatchEntry]

theorem range_copy_eq (n : Nat) :
    ((List.range n).flatMap fun j => [ld .rax .r14 (slot j), st .r12 (slot j) .rax]) =
      copyL .r14 .r12 (fun j => slot j) (fun j => slot j) n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.range_succ, List.flatMap_append, ih]; simp [copyL]

/-- **dispatch_run.** From the chain's entry i with the label `l` in rdx and `l.toNat = i + d` within the fuel: the run reaches
    entry `l.toNat`'s tail; registers and memory unchanged. -/
theorem dispatch_run {C : Ctx3} {p : Program} {L : Lay3} (E : StepEnv C p L) {wx : Nat} {l : W} :
    ∀ d fuel i (v : Cpu), l.toNat = i + d → d < fuel → v.stopped = false →
      CodeAt C p v.rip (dispatch C wx v.rip fuel i) → v.regs.get .rdx = l →
      ∃ m u rest, runP p m v = u ∧ u.stopped = false ∧ u.regs = v.regs ∧ u.mem = v.mem ∧
        CodeAt C p u.rip (entryTail C wx l.toNat ++ rest) := by
  intro d
  induction d with
  | zero =>
    intro fuel i v hl hd hs hc hrdx
    obtain ⟨fuel', rfl⟩ : ∃ f', fuel = f' + 1 := ⟨fuel - 1, by omega⟩
    set nx := v.rip + BitVec.ofNat 64 (bytes C (dispatchEntry C wx i 0)) with hnx
    have hc' : CodeAt C p v.rip (.op (.bin .cmp .q (.reg .rdx) (.imm (BitVec.ofNat 64 i))) :: .jccA .ne nx ::
        (entryTail C wx i ++ dispatch C wx nx fuel' (i + 1))) := by
      have := hc; simp only [dispatch] at this; rw [dispatchEntry_eq] at this
      simpa only [List.append_assoc, List.cons_append, List.nil_append] using this
    have hcN : CodeAt C p nx (dispatch C wx nx fuel' (i + 1)) := by
      have := codeAt_right (a := dispatchEntry C wx i nx) (by
        have := hc; simp only [dispatch] at this; exact this)
      rw [bytes_dispatchEntry] at this; exact this
    have e1 := stepP_cmp_ri hs hc'
    set v1 := stepP p v with hv1
    have h1 : v1.stopped = false := by rw [e1]; exact hs
    have c1 := codeAt_next (s' := v1) (by rw [e1]) hc'
    obtain ⟨i0, l0, hil⟩ := List.exists_cons_of_ne_nil (dispatch_ne_nil C wx nx fuel' (i + 1))
    have e2 := stepP_jccA h1 c1 (canon_of_codeAt E (by rw [hil] at hcN; exact hcN))
    have heq : l = BitVec.ofNat 64 i := by
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (by have := l.isLt; omega)]; omega
    have hne : Cc.eval .ne v1.flags = false := by
      rw [e1, hrdx, cc_ne_sub]; simp [heq]
    refine ⟨2, stepP p v1, dispatch C wx nx fuel' (i + 1), rfl, by rw [e2]; exact h1, by rw [e2, e1], by rw [e2, e1], ?_⟩
    rw [e2]; simp only [hne, Bool.false_eq_true, if_false]
    rw [show l.toNat = i by omega]
    exact codeAt_jcc_fall c1
  | succ d ih =>
    intro fuel i v hl hd hs hc hrdx
    obtain ⟨fuel', rfl⟩ : ∃ f', fuel = f' + 1 := ⟨fuel - 1, by omega⟩
    set nx := v.rip + BitVec.ofNat 64 (bytes C (dispatchEntry C wx i 0)) with hnx
    have hc' : CodeAt C p v.rip (.op (.bin .cmp .q (.reg .rdx) (.imm (BitVec.ofNat 64 i))) :: .jccA .ne nx ::
        (entryTail C wx i ++ dispatch C wx nx fuel' (i + 1))) := by
      have := hc; simp only [dispatch] at this; rw [dispatchEntry_eq] at this
      simpa only [List.append_assoc, List.cons_append, List.nil_append] using this
    have hcN : CodeAt C p nx (dispatch C wx nx fuel' (i + 1)) := by
      have := codeAt_right (a := dispatchEntry C wx i nx) (by
        have := hc; simp only [dispatch] at this; exact this)
      rw [bytes_dispatchEntry] at this; exact this
    have e1 := stepP_cmp_ri hs hc'
    set v1 := stepP p v with hv1
    have h1 : v1.stopped = false := by rw [e1]; exact hs
    have c1 := codeAt_next (s' := v1) (by rw [e1]) hc'
    obtain ⟨i0, l0, hil⟩ := List.exists_cons_of_ne_nil (dispatch_ne_nil C wx nx fuel' (i + 1))
    have e2 := stepP_jccA h1 c1 (canon_of_codeAt E (by rw [hil] at hcN; exact hcN))
    have hneq : l ≠ BitVec.ofNat 64 i := by
      intro h; have := congrArg BitVec.toNat h; simp only [BitVec.toNat_ofNat] at this
      rw [Nat.mod_eq_of_lt (by have := l.isLt; omega)] at this; omega
    have hne : Cc.eval .ne v1.flags = true := by
      rw [e1, hrdx, cc_ne_sub]; simp [hneq]
    set v2 := stepP p v1 with hv2
    have rip2 : v2.rip = nx := by rw [e2]; simp only [hne, if_true]
    obtain ⟨m, u, rest, hr, hus, hureg, humem, huc⟩ := ih fuel' (i + 1) v2 (by omega) (by omega) (by rw [e2]; exact h1)
      (by rw [rip2]; exact hcN) (by rw [e2, e1]; exact hrdx)
    refine ⟨2 + m, u, rest, by rw [runP_add]; exact hr, hus, by rw [hureg, e2, e1], by rw [humem, e2, e1], huc⟩

/-- **entry_run.** An entry's tail: RES in 5 steps when `r12 − lo < 8n` (memory and every register but rax, rcx unchanged);
    otherwise r12 drops by 8n, ENV words 0…wx−1 at the new r12 hold BUF slots 0…, word wx holds rdx for a fix, every other word
    keeps its value, and the run is at the body. -/
theorem entry_run {C : Ctx3} {p : Program} {s : Cpu} {wx i : Nat} {lo : W} {rest : List AI}
    (hs : s.stopped = false) (hc : CodeAt C p s.rip (entryTail C wx i ++ rest)) (hcb : rd s.mem (s.regs.get .rbx + 16) = lo)
    (hge : lo.toNat ≤ (s.regs.get .r12).toNat) (h8 : 8 * (wx + 1) < 2 ^ 64) (hcan : canonical C.res = true)
    (hcb' : canonical (C.body i) = true) :
    let n := if C.fix i then wx + 1 else wx
    ((s.regs.get .r12).toNat - lo.toNat < 8 * n → ∃ u, runP p 5 s = u ∧ u.stopped = false ∧ u.rip = C.res ∧ u.mem = s.mem ∧
        ∀ r, r ≠ .rax → r ≠ .rcx → u.regs.get r = s.regs.get r) ∧
    (¬ (s.regs.get .r12).toNat - lo.toNat < 8 * n →
      (∀ a b, a < wx → b < wx → VIRBridge.Apart (s.regs.get .r12 - slot n + slot a) (s.regs.get .r14 + slot b)) →
      ∃ m u, runP p m s = u ∧ u.stopped = false ∧ u.rip = C.body i ∧
        u.regs.get .r12 = s.regs.get .r12 - slot n ∧
        (∀ j, j < wx → rd u.mem (s.regs.get .r12 - slot n + slot j) = rd s.mem (s.regs.get .r14 + slot j)) ∧
        (C.fix i = true → rd u.mem (s.regs.get .r12 - slot n + slot wx) = s.regs.get .rdx) ∧
        (∀ a, (∀ j, j < n → VIRBridge.Apart (s.regs.get .r12 - slot n + slot j) a) → rd u.mem a = rd s.mem a) ∧
        ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .r12 → u.regs.get r = s.regs.get r) := by
  intro n
  have hn1 : n ≤ wx + 1 := by simp only [n]; split <;> omega
  have hwn : wx ≤ n := by simp only [n]; split <;> omega
  have h8n : 8 * n < 2 ^ 64 := by omega
  have hc' : CodeAt C p s.rip (envRoom C n ++ (.op (.lea .q .r12 { base := some .r12, disp := -(slot n) }) ::
      (copyL .r14 .r12 (fun j => slot j) (fun j => slot j) wx ++
        ((if C.fix i then [st .r12 (slot wx) .rdx] else []) ++ (.jmpA (C.body i) :: rest))))) := by
    have := hc; simp only [entryTail, range_copy_eq, List.append_assoc] at this; simpa using this
  obtain ⟨u1, hr1, hs1, hm1, hreg1, hrip1⟩ := envRoom_run hs hc' hcb hge h8n hcan
  constructor
  · intro hlt; rw [if_pos hlt] at hrip1; exact ⟨u1, hr1, hs1, hrip1, hm1, hreg1⟩
  · intro hlt hap
    rw [if_neg hlt] at hrip1
    have hR := (s.regs.get .r12).isLt
    have c1 : CodeAt C p u1.rip (.op (.lea .q .r12 { base := some .r12, disp := -(slot n) }) ::
        (copyL .r14 .r12 (fun j => slot j) (fun j => slot j) wx ++
          ((if C.fix i then [st .r12 (slot wx) .rdx] else []) ++ (.jmpA (C.body i) :: rest)))) := by
      rw [hrip1]; exact codeAt_right hc'
    have e2 := stepP_lea_dec hs1 c1
    set u2 := stepP p u1 with hu2
    have h2 : u2.stopped = false := by rw [e2]; exact hs1
    have c2 : CodeAt C p u2.rip (copyL .r14 .r12 (fun j => slot j) (fun j => slot j) wx ++
        ((if C.fix i then [st .r12 (slot wx) .rdx] else []) ++ (.jmpA (C.body i) :: rest))) := by
      rw [e2]; exact codeAt_tail c1
    have r12_1 : u1.regs.get .r12 = s.regs.get .r12 := hreg1 .r12 (by decide) (by decide)
    have r14_1 : u1.regs.get .r14 = s.regs.get .r14 := hreg1 .r14 (by decide) (by decide)
    have r12_2 : u2.regs.get .r12 = s.regs.get .r12 - slot n := by rw [e2]; simp [r12_1]
    have r14_2 : u2.regs.get .r14 = s.regs.get .r14 := by rw [e2]; simp [r14_1]
    have hE : (s.regs.get .r12 - slot n).toNat = (s.regs.get .r12).toNat - 8 * n := by
      simp only [slot, BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
    have hEE : ∀ a b, a < n → b < n → a ≠ b →
        VIRBridge.Apart (s.regs.get .r12 - slot n + slot a) (s.regs.get .r12 - slot n + slot b) :=
      fun a b ha hb hab => slot_apart (by omega) ha hb hab
    obtain ⟨u3, hr3, hs3, hrip3, hreg3, _, hcp3, hfr3⟩ := copy_run (C := C) .r14 .r12 (by decide) (by decide) _ _ wx u2 _ h2 c2
      (fun a b _ hb => by rw [r12_2, r14_2]; exact hap a b (by omega) hb)
      (fun a b ha hb hab => by rw [r12_2]; exact hEE a b (by omega) (by omega) hab)
    have rdx3 : u3.regs.get .rdx = s.regs.get .rdx := by
      rw [hreg3 .rdx (by decide), e2]; simp only [Regs.get_set_ne _ _ _ _ (show GPR.r12 ≠ GPR.rdx by decide)]
      exact hreg1 .rdx (by decide) (by decide)
    have r12_3 : u3.regs.get .r12 = s.regs.get .r12 - slot n := by rw [hreg3 .r12 (by decide), r12_2]
    have c3 : CodeAt C p u3.rip ((if C.fix i then [st .r12 (slot wx) .rdx] else []) ++ (.jmpA (C.body i) :: rest)) := by
      rw [hrip3]; exact codeAt_right c2
    have m2 : u2.mem = s.mem := by rw [e2, hm1]
    have reg2 : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .r12 → u2.regs.get r = s.regs.get r := by
      intro r ha hc' h12; rw [e2]; simp only [Regs.get_set_ne _ _ _ _ (Ne.symm h12)]; exact hreg1 r ha hc'
    cases hfx : C.fix i with
    | false =>
      simp only [hfx, List.nil_append] at c3
      have e4 := stepP_jmpA hs3 c3 hcb'
      refine ⟨5 + 1 + 2 * wx + 1, stepP p u3, ?_, by rw [e4]; exact hs3, by rw [e4], by rw [e4]; exact r12_3, ?_,
        fun h => absurd h (by simp), ?_, ?_⟩
      · rw [show 5 + 1 + 2 * wx + 1 = 5 + (1 + (2 * wx + 1)) by omega, runP_add, hr1, runP_add, show runP p 1 u1 = u2 from rfl,
          runP_add, hr3]; rfl
      · intro j hj; rw [e4]; simp only; rw [← r12_2, hcp3 j hj, r14_2, m2]
      · intro a ha; rw [e4]; simp only
        rw [hfr3 a (fun j hj => by rw [r12_2]; exact ha j (by omega)), m2]
      · intro r ha hc' h12; rw [e4]; simp only; rw [hreg3 r ha]; exact reg2 r ha hc' h12
    | true =>
      simp only [hfx, List.singleton_append] at c3
      have hnw : n = wx + 1 := by simp only [n, hfx, if_true]
      have e4 := stepP_st hs3 c3
      set u4 := stepP p u3 with hu4
      have h4 : u4.stopped = false := by rw [e4]; exact hs3
      have c4 := codeAt_next (s' := u4) (by rw [e4]) c3
      have e5 := stepP_jmpA h4 c4 hcb'
      have mem4 : u4.mem = u3.mem.writeSize .q (s.regs.get .r12 - slot n + slot wx) (s.regs.get .rdx) := by
        rw [e4]; simp only [r12_3, rdx3]
      have aw : ∀ j, j < wx → VIRBridge.Apart (s.regs.get .r12 - slot n + slot wx) (s.regs.get .r12 - slot n + slot j) :=
        fun j hj => hEE wx j (by omega) (by omega) (by omega)
      refine ⟨5 + 1 + 2 * wx + 2, stepP p u4, ?_, by rw [e5]; exact h4, by rw [e5], ?_, ?_, ?_, ?_, ?_⟩
      · rw [show 5 + 1 + 2 * wx + 2 = 5 + (1 + (2 * wx + 2)) by omega, runP_add, hr1, runP_add, show runP p 1 u1 = u2 from rfl,
          runP_add, hr3]; rfl
      · rw [e5]; simp only; rw [e4]; exact r12_3
      · intro j hj; rw [e5]; simp only; rw [mem4, rd_write_apart _ _ _ _ (aw j hj), ← r12_2, hcp3 j hj, r14_2, m2]
      · intro _; rw [e5]; simp only; rw [mem4]; exact rd_write_same _ _ _
      · intro a ha; rw [e5]; simp only; rw [mem4, rd_write_apart _ _ _ _ (ha wx (by omega))]
        rw [hfr3 a (fun j hj => by rw [r12_2]; exact ha j (by omega)), m2]
      · intro r ha hc' h12; rw [e5]; simp only; rw [e4]; simp only; rw [hreg3 r ha]; exact reg2 r ha hc' h12

/-- The activation base a frame chain records at `[rsp + 8]`: in ENV's bounds, at or above `lo`, its occupancy bounded. -/
theorem frames_base {C : Ctx3} {p : Program} {L : Lay3} (hL : L.Ok) {m : Mem} :
    ∀ (k : List (WCode × List W)) (rsp lo : W), Frames C p L m rsp lo k →
      lo.toNat ≤ (rd m (rsp + 8)).toNat ∧ (rd m (rsp + 8)).toNat ≤ L.envTop.toNat ∧
      (rd m (rsp + 8)).toNat ≤ L.env0.toNat ∧ L.env0.toNat - (rd m (rsp + 8)).toNat ≤ 8 * kSize k
  | [], _, _, ⟨_, _, h3, _, _, h6⟩ => by rw [h3]; have := hL.env0_le_top; simp only [kSize]; omega
  | (_, ρ) :: k, _, _, ⟨_, a, _, h2, _, h4, h5, _, _, h9, _⟩ => by rw [h2]; simp only [kSize]; omega

/-- Frames at `rsp` hold for any `lo'` at or below the recorded activation base. -/
theorem frames_relo {C : Ctx3} {p : Program} {L : Lay3} {m : Mem} :
    ∀ (k : List (WCode × List W)) (rsp lo lo' : W), Frames C p L m rsp lo k → lo'.toNat ≤ (rd m (rsp + 8)).toNat →
      Frames C p L m rsp lo' k
  | [], _, _, _, ⟨h1, h2, h3, h4, h5, _⟩, hle => ⟨h1, h2, h3, h4, h5, by rw [h3] at hle; exact hle⟩
  | (_, _) :: _, _, _, _, ⟨q, a, h1, h2, h3, _, h5, h6, h7, h9, h8⟩, hle => ⟨q, a, h1, h2, h3, by rw [h2] at hle; exact hle, h5, h6, h7, h9, h8⟩

/-- A BUF-confined frame from slot t over N ≤ |BUF| slots is an AgreeBuf. -/
theorem agree_of_frame' {L : Lay3} {s u : Cpu} {t N : Nat} (hB : s.regs.get .r14 = L.buf) (hN : N ≤ L.bufN)
    (hf : Frame s u t N) : AgreeBuf L s.mem u.mem :=
  fun a ha => hf.1 a (fun i _ hi => by rw [hB]; exact ha i (by omega))

/-- **sim_app.** A word step of `app f x` (f's evaluation not BAD, Addendum 11) is simulated: the body as an R3 run state at
    x's words (and the label for a fix) with the same continuations, an overflow as R3 `ovf`, or RES with the successor outgrowing
    ENV. -/
theorem sim_app {C : Ctx3} {p : Program} {L : Lay3} (E : StepEnv C p L) {tbl : Table} (hT : TblOk C p tbl) {f x : WOpd}
    {ρ : List W} {k : List (WCode × List W)} {wm : WMem} {s : Cpu} (hR : R3 C p L (.run (.app f x) ρ k, wm) s)
    (hneed : need x + need f ≤ L.bufN) (hnb : evalW ρ f ≠ .bad)
    {W' : WSt × WMem} (hstep : stepW tbl (.run (.app f x) ρ k, wm) = some W') :
    ∃ n, 0 < n ∧ (R3 C p L W' (runP p n s) ∨ (ResExit L (runP p n s) ∧ Common L W'.2 (runP p n s) ∧ RetOver L W'.1)) := by
  have hR0 := hR
  obtain ⟨hs, hcode, hcom, hlo, hhi, hw, hfr, hsl, hocc⟩ := hR
  have hcom0 := hcom
  have hB : s.regs.get .r14 = L.buf := hcom.1
  have hX : s.regs.get .rbx = L.cb := hcom.2.1
  obtain ⟨_, _, ⟨hc1, hc2, hc3⟩, hRep⟩ := hcom
  have hL := E.ok
  set pre : List AI := evalTo C (need x) f ++ evalTo C 0 x ++ [ld .rdx .r14 (slot (need x)), ld .r12 .rsp 8] with hpre
  have hc : CodeAt C p s.rip (evalTo C (need x) f ++ (evalTo C 0 x ++ ([ld .rdx .r14 (slot (need x)), ld .r12 .rsp 8] ++
      dispatch C (wid x) (s.rip + BitVec.ofNat 64 (bytes C pre)) C.tblLen 0))) := by
    have h0 := hcode; simp only [gen] at h0; simpa only [hpre, List.append_assoc] using h0
  have hpreF : EvalPre s (need x) L.bufN ρ := ⟨hw, by rw [hB]; exact hL.buf_nowrap,
    fun i j _ hi hj => by rw [hB]; exact buf_env_apart hL hi hlo hhi hj⟩
  have hpostF := evalTo_run (C := C) (p := p) (canon_of_codeAt E E.ovf) f (need x) s _ ρ L.bufN hs hc (by omega) hpreF
  simp only [EvalPost] at hpostF
  simp only [stepW] at hstep
  cases hof : evalW ρ f with
  | bad => exact absurd hof hnb
  | ovf =>
    rw [hof] at hstep hpostF; cases hstep
    obtain ⟨n1, u1, hr1, hs1, hrip1, hf1⟩ := hpostF
    obtain ⟨v, hv, hRv⟩ := ovf_exit E hR0 (agree_of_frame' hB (le_refl _) hf1) hf1.2 hs1 hrip1
    exact ⟨n1 + 4, by omega, Or.inl (by rw [runP_add, hr1, hv]; exact hRv)⟩
  | ok fs =>
    rw [hof] at hstep hpostF
    obtain ⟨n1, u1, hr1, hs1, hrip1, hwf1, hf1⟩ := hpostF
    have ag1 : AgreeBuf L s.mem u1.mem := agree_of_frame' hB (le_refl _) hf1
    have hB1 : u1.regs.get .r14 = L.buf := by rw [hf1.2 .r14 (by decide) (by decide) (by decide), hB]
    have r12_1 : u1.regs.get .r12 = s.regs.get .r12 := hf1.2 .r12 (by decide) (by decide) (by decide)
    have hcX : CodeAt C p u1.rip (evalTo C 0 x ++ ([ld .rdx .r14 (slot (need x)), ld .r12 .rsp 8] ++
        dispatch C (wid x) (s.rip + BitVec.ofNat 64 (bytes C pre)) C.tblLen 0)) := by rw [hrip1]; exact codeAt_right hc
    have hpreX : EvalPre u1 0 (need x) ρ := ⟨by rw [r12_1]; exact wordsAt_agree hL ag1 hlo hhi hw,
      by rw [hB1]; have := hL.buf_nowrap; omega,
      fun i j _ hi hj => by rw [hB1, r12_1]; exact buf_env_apart hL (by omega) hlo hhi hj⟩
    have hpostX := evalTo_run (C := C) (p := p) (canon_of_codeAt E E.ovf) x 0 u1 _ ρ (need x) hs1 hcX (by omega) hpreX
    simp only [EvalPost] at hpostX
    cases hox : evalW ρ x with
    | bad => rw [hox] at hstep; rcases fs with _ | ⟨a, _ | ⟨b, t⟩⟩ <;> simp at hstep
    | ovf =>
      rw [hox] at hpostX hstep
      have hW' : W' = (.ovf, wm) := by
        rcases fs with _ | ⟨a, _ | ⟨b, t⟩⟩ <;> simp at hstep <;> exact hstep.symm
      subst hW'
      obtain ⟨n2, u2, hr2, hs2, hrip2, hf2⟩ := hpostX
      have ag2 : AgreeBuf L s.mem u2.mem := agree_trans ag1 (agree_of_frame' hB1 (by omega) hf2)
      obtain ⟨v, hv, hRv⟩ := ovf_exit E hR0 ag2 (fun r ha hc' hd => by rw [hf2.2 r ha hc' hd]; exact hf1.2 r ha hc' hd) hs2 hrip2
      exact ⟨n1 + n2 + 4, by omega, Or.inl (by rw [runP_add, runP_add, hr1, hr2, hv]; exact hRv)⟩
    | ok ws =>
      rw [hox] at hpostX hstep
      obtain ⟨n2, u2, hr2, hs2, hrip2, hwx2, hf2⟩ := hpostX
      match fs, hstep, hwf1 with
      | [], hstep, _ => simp at hstep
      | _ :: _ :: _, hstep, _ => simp at hstep
      | [l], hstep, hwf1 =>
      try simp only at hstep
      cases htb : tbl[l.toNat]? with
      | none => rw [htb] at hstep; simp at hstep
      | some e =>
      obtain ⟨fx, b⟩ := e
      obtain ⟨hfix, hcb⟩ := hT.body _ _ _ htb
      have hltT : l.toNat < C.tblLen := by rw [← hT.len]; exact (List.getElem?_eq_some_iff.mp htb).1
      have hlen : ws.length = wid x := evalW_length x ρ ws hox
      have hwxN : wid x ≤ need x := wid_le_need x
      have ag2 : AgreeBuf L s.mem u2.mem := agree_trans ag1 (agree_of_frame' hB1 (by omega) hf2)
      have hB2 : u2.regs.get .r14 = L.buf := by rw [hf2.2 .r14 (by decide) (by decide) (by decide), hB1]
      have reg2 : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → u2.regs.get r = s.regs.get r := fun r ha hc' hd => by
        rw [hf2.2 r ha hc' hd]; exact hf1.2 r ha hc' hd
      -- the label survives x's code: slot need x is outside x's frame
      have hnf : 1 ≤ need f := by
        have h1 := wid_le_need f; have h2 := evalW_length f ρ [l] hof; simp only [List.length_singleton] at h2; omega
      have hl2 : rd u2.mem (L.buf + slot (need x)) = l := by
        have h1 := (wordsAt_slot.mp hwf1) 0 (by simp); rw [hB] at h1
        simp only [Nat.add_zero, List.getElem_cons_zero] at h1
        rw [hf2.1 _ (fun i _ hi => by
          rw [hB1]; exact slot_apart (b := L.buf) (N := L.bufN) hL.buf_nowrap (by omega) (by omega) (by omega))]
        rw [← hB1, hB1]; exact h1
      have c2 : CodeAt C p u2.rip (ld .rdx .r14 (slot (need x)) :: ld .r12 .rsp 8 ::
          dispatch C (wid x) (s.rip + BitVec.ofNat 64 (bytes C pre)) C.tblLen 0) := by
        rw [hrip2]; simpa using codeAt_right hcX
      have e3 := stepP_ld hs2 c2
      set u3 := stepP p u2 with hu3
      have h3 : u3.stopped = false := by rw [e3]; exact hs2
      have c3 := codeAt_next (s' := u3) (by rw [e3]) c2
      have e4 := stepP_ld h3 c3
      set u4 := stepP p u3 with hu4
      have h4 : u4.stopped = false := by rw [e4]; exact h3
      have rip4 : u4.rip = s.rip + BitVec.ofNat 64 (bytes C pre) := by
        rw [e4, e3, hrip2, hrip1, hpre]
        simp only [nxt, ld, bytes_append, bytes_cons, bytes_nil, AI.size, ofNat_add64, BitVec.add_assoc, Nat.add_zero]
      have c4 : CodeAt C p u4.rip (dispatch C (wid x) u4.rip C.tblLen 0) := by
        have h := codeAt_next (s' := u4) (by rw [e4]) c3; rw [← rip4] at h; exact h
      have sp4 : u4.regs.get .rsp = s.regs.get .rsp := by
        rw [e4]; simp only [Regs.get_set_ne _ _ _ _ (show GPR.r12 ≠ GPR.rsp by decide)]
        rw [e3]; simp only [Regs.get_set_ne _ _ _ _ (show GPR.rdx ≠ GPR.rsp by decide)]
        exact reg2 .rsp (by decide) (by decide) (by decide)
      have mem4 : u4.mem = u2.mem := by rw [e4, e3]
      have rdx4 : u4.regs.get .rdx = l := by
        rw [e4]; simp only [Regs.get_set_ne _ _ _ _ (show GPR.r12 ≠ GPR.rdx by decide)]
        rw [e3]; simp only [Regs.get_set_same]; rw [hB2]; exact hl2
      have r14_4 : u4.regs.get .r14 = L.buf := by
        rw [e4]; simp only [Regs.get_set_ne _ _ _ _ (show GPR.r12 ≠ GPR.r14 by decide)]
        rw [e3]; simp only [Regs.get_set_ne _ _ _ _ (show GPR.rdx ≠ GPR.r14 by decide)]; exact hB2
      have reg4 : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .r12 → u4.regs.get r = s.regs.get r := by
        intro r ha hc' hd h12
        rw [e4]; simp only [Regs.get_set_ne _ _ _ _ (Ne.symm h12)]
        rw [e3]; simp only [Regs.get_set_ne _ _ _ _ (Ne.symm hd)]; exact reg2 r ha hc' hd
      have hR := L.rsp0.isLt
      have hst := hL.stk_nowrap
      have hfb := frames_bound k _ _ hfr
      have fb := frames_base hL k _ _ hfr
      have m_sp8 : rd u2.mem (s.regs.get .rsp + 8) = rd s.mem (s.regs.get .rsp + 8) := by
        have e8 : (s.regs.get .rsp + 8).toNat = (s.regs.get .rsp).toNat + 8 := by simp only [BitVec.toNat_add]; simp; omega
        exact ag2 _ (fun i hi => buf_stk_apart hL hi (by omega) (by omega))
      have r12_4 : u4.regs.get .r12 = rd s.mem (s.regs.get .rsp + 8) := by
        rw [e4]; simp only [Regs.get_set_same]
        rw [e3]; simp only [Regs.get_set_ne _ _ _ _ (show GPR.rdx ≠ GPR.rsp by decide)]
        rw [reg2 .rsp (by decide) (by decide) (by decide)]; exact m_sp8
      set base := rd s.mem (s.regs.get .rsp + 8) with hbase
      -- the activation's frame state, placed at the body: an R3 state at (b, [], k)
      set s5 : Cpu := { u4 with rip := C.body l.toNat } with hs5
      have hR5 : R3 C p L (.run b [] k, wm) s5 := by
        refine ⟨h4, hcb, ⟨r14_4, by rw [reg4 .rbx (by decide) (by decide) (by decide) (by decide), hX], ⟨?_, ?_, ?_⟩, ?_⟩,
          ?_, ?_, ?_, ?_, ?_, ?_⟩
        · show rd u4.mem _ = _; rw [mem4, ag2 (L.cb + 8) (fun i hi => buf_cb_apart hL hi (m := 1) (by decide))]; exact hc1
        · show rd u4.mem _ = _; rw [mem4, ag2 (L.cb + 16) (fun i hi => buf_cb_apart hL hi (m := 2) (by decide))]; exact hc2
        · show rd u4.mem _ = _; rw [mem4, ag2 (L.cb + 24) (fun i hi => buf_cb_apart hL hi (m := 3) (by decide))]; exact hc3
        · intro a ha
          show u4.mem.readN a 8 = _
          rw [mem4]
          have := ag2 a (fun i hi => buf_live_apart hL hi ha)
          simp only [rd] at this; rw [this]; exact hRep a ha
        · show L.envLo.toNat ≤ (u4.regs.get .r12).toNat; rw [r12_4]; omega
        · show (u4.regs.get .r12).toNat + _ ≤ _; rw [r12_4]; simp only [List.length_nil]; omega
        · intro j hj; exact absurd hj (by simp)
        · show Frames C p L u4.mem (u4.regs.get .rsp) (u4.regs.get .r12) k
          rw [sp4, r12_4, mem4]
          exact frames_relo k _ _ base (frames_agree hL ag2 k _ _ hlo hsl hfr) (le_of_eq (by rw [m_sp8]))
        · show L.stkLo.toNat ≤ (u4.regs.get .rsp).toNat; rw [sp4]; exact hsl
        · show (u4.regs.get .r12).toNat ≤ _ ∧ _; rw [r12_4]; simp only [List.length_nil, Nat.zero_add]
          exact ⟨fb.2.2.1, fb.2.2.2⟩
      -- the dispatch chain, then the label's entry
      obtain ⟨m3, u5, rest, hr5, hs5', hreg5, hm5, hc5⟩ :=
        dispatch_run E (wx := wid x) (l := l) l.toNat C.tblLen 0 u4 (by omega) hltT h4 c4 rdx4
      have hbody : canonical (C.body l.toNat) = true := canon_gen E (rest := []) (by simpa using hcb)
      have hcb5 : rd u5.mem (u5.regs.get .rbx + 16) = L.envLo := by
        rw [hm5, hreg5, reg4 .rbx (by decide) (by decide) (by decide) (by decide), hX, mem4,
          ag2 (L.cb + 16) (fun i hi => buf_cb_apart hL hi (m := 2) (by decide))]; exact hc2
      have hbuf := hL.buf_nowrap
      have h8 : 8 * (wid x + 1) < 2 ^ 64 := by omega
      obtain ⟨hRES, hGO⟩ := entry_run (wx := wid x) (i := l.toNat) hs5' hc5 hcb5
        (by rw [hreg5, r12_4]; omega) h8 (canon_of_codeAt E E.res) hbody
      rw [hreg5, r12_4] at hRES hGO
      set ρ' : List W := ws ++ (if fx then [l] else []) with hρ'
      have hW : W' = (.run b ρ' k, wm) := by
        rw [htb] at hstep; cases fx <;> simp at hstep <;> subst hstep <;> simp [hρ']
      have hn : (if C.fix l.toNat then wid x + 1 else wid x) = ρ'.length := by
        rw [hfix, hρ', List.length_append, hlen]; cases fx <;> simp
      subst hW
      rw [hn] at hRES hGO
      by_cases hlt : base.toNat - L.envLo.toNat < 8 * ρ'.length
      · obtain ⟨u6, hr6, hs6, hrip6, hm6, hreg6⟩ := hRES hlt
        obtain ⟨v, hv, hres, hcomv, hover⟩ := res_exit (n := ρ'.length) E hR5 (u := u6)
          (fun a _ => by rw [hm6, hm5]) (fun r ha hc' _ => by rw [hreg6 r ha hc']) hs6 hrip6
          (by show (u4.regs.get .r12).toNat - _ < _; rw [r12_4]; exact hlt)
        refine ⟨n1 + n2 + 2 + m3 + 5 + 4, by omega, Or.inr ⟨?_, ?_, ?_⟩⟩
        · rw [runP_add, runP_add, runP_add, runP_add, runP_add, hr1, hr2]
          show ResExit L (runP p 4 (runP p 5 (runP p m3 u4))); rw [hr5, hr6, hv]; exact hres
        · rw [runP_add, runP_add, runP_add, runP_add, runP_add, hr1, hr2]
          show Common L wm (runP p 4 (runP p 5 (runP p m3 u4))); rw [hr5, hr6, hv]; exact hcomv
        · simp only [RetOver, EnvOver, List.length_nil, Nat.zero_add] at hover ⊢; omega
      · have hBt := base.isLt
        have hE : (base - slot ρ'.length).toNat = base.toNat - 8 * ρ'.length := by
          simp only [slot, BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
        have hlenρ : ρ'.length ≤ wid x + 1 := by rw [hρ', List.length_append, hlen]; split <;> simp
        have hap : ∀ a c, a < wid x → c < wid x →
            VIRBridge.Apart (base - slot ρ'.length + slot a) (u4.regs.get .r14 + slot c) := by
          intro a c ha hc'
          rw [r14_4]
          exact (buf_env_apart hL (by omega : c < L.bufN) (n := ρ'.length) (by rw [hE]; omega) (by rw [hE]; omega)
            (by rw [hρ', List.length_append, hlen]; omega)).symm'
        obtain ⟨m4, u6, hr6, hs6, hrip6, h12_6, hcp6, hfix6, hoth6, hreg6⟩ := hGO hlt hap
        have hR6 := r3_of_prepend (ws := ρ') (c' := b) hL hR5
          (by show _ ≤ (u4.regs.get .r12).toNat; rw [r12_4]; omega)
          (by show u6.regs.get .r12 = u4.regs.get .r12 - _; rw [r12_4]; exact h12_6)
          (by
            intro j hj
            show rd u6.mem (u4.regs.get .r12 - _ + _) = _
            rw [r12_4]
            by_cases hjw : j < wid x
            · have hρj : ρ'[j] = ws[j]'(by rw [hlen]; exact hjw) := by
                simp only [hρ']; rw [List.getElem_append_left (by rw [hlen]; exact hjw)]
              rw [hcp6 j hjw, hρj, r14_4, hm5, mem4]
              have := (wordsAt_slot.mp hwx2) j (by rw [hlen]; exact hjw); rw [hB1] at this; simpa using this
            · have hjx : j = wid x := by omega
              have hfxt : fx = true := by
                cases fx with
                | true => rfl
                | false => simp [hρ', hlen] at hj; omega
              subst hjx
              rw [hfix6 (by rw [hfix, hfxt]), rdx4]
              simp only [hρ', hfxt, if_true]
              rw [List.getElem_append_right (by rw [hlen]; try omega)]; try simp [hlen])
          (fun a _ hna => by
            show rd u6.mem a = rd u4.mem a
            rw [hoth6 a (fun j hj => by have := hna j hj; rw [show s5.regs.get .r12 = base from r12_4] at this; exact this), hm5])
          (fun r ha hc' hd h12 => by show u6.regs.get r = u4.regs.get r; exact hreg6 r ha hc' h12)
          hs6 (by rw [hrip6]; exact hcb)
        rw [List.append_nil] at hR6
        refine ⟨n1 + n2 + 2 + m3 + m4, by omega, Or.inl ?_⟩
        rw [runP_add, runP_add, runP_add, runP_add, hr1, hr2]
        show R3 C p L _ (runP p m4 (runP p m3 u4)); rw [hr5, hr6]; exact hR6

end S3
