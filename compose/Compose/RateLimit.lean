/-
  STATUS-vir row 53 (O95). RATE LIMITING AT THE MACHINE, ACROSS TWO CALLS: paris's `Router.MultiCall.two_calls`
  (spike 7241997) composed with vir's spec lemma `VIR.Compose.MultiCall.two_ok_same_sender` (compose/MultiCall.lean).
  If the repaired code stops at emit_slice (0x1043) on BOTH calls, and both frames name the same sender, then that
  sender held at least two tokens at the start, and the bucket cell call 2 leaves in memory reads two fewer.
  Every premise is `two_calls`'s, so the X-F1 region premises (FINDINGS.md) ride with it; nothing new is assumed.
-/
import Router.MultiCall
import Compose.MultiCall
import Compose.Safety

namespace VIR.Compose.RateLimit
open X86 Router Router.Refines Router.MultiCall

/-- Whatever the frame, an `Exit` at emit_slice of `F b σ` means F's four guards held (K3, for a general `b`). -/
theorem guards_of_emit (acl : VIR.Principal → VIR.TopicId → Bool) (b : VIR.Deep.Val) (σ : VIR.State)
    {s t : Cpu} {P : UInt32} (hE : Exit s t P (VIR.Deep.den acl (VIR.Deep.F b (.state σ)))) (he : t.rip = 0x1043) :
    24 ≤ b.len ∧ ((b.rd 0).toP = VIR.MAGIC ∧ acl (b.rd 4).toP (b.rd 8).toP = true ∧ 0 < σ (b.rd 4).toP) := by
  rw [VIR.Deep.F_exit] at hE
  simp only [VIR.Deep.Val.st] at hE
  by_cases h1 : 24 ≤ b.len
  · by_cases h2 : (b.rd 0).toP = VIR.MAGIC ∧ acl (b.rd 4).toP (b.rd 8).toP = true ∧ 0 < σ (b.rd 4).toP
    · exact ⟨h1, h2⟩
    · rw [if_pos h1, if_neg h2] at hE
      simp only [Exit, he] at hE
      obtain ⟨hr, _⟩ := hE
      rcases hr with hr | hr <;> exact absurd hr (by decide)
  · rw [if_neg h1] at hE
    simp only [Exit, he] at hE
    exact absurd hE.1 (by decide)

/-- The guards give the OK denotation exactly. -/
theorem den_of_guards (acl : VIR.Principal → VIR.TopicId → Bool) (b : VIR.Deep.Val) (σ : VIR.State)
    (g : 24 ≤ b.len ∧ ((b.rd 0).toP = VIR.MAGIC ∧ acl (b.rd 4).toP (b.rd 8).toP = true ∧ 0 < σ (b.rd 4).toP)) :
    VIR.Deep.den acl (VIR.Deep.F b (.state σ)) = .ret (.state (VIR.decTokens σ (b.rd 4).toP)) (b.adv 24) := by
  rw [VIR.Deep.F_exit]
  simp only [VIR.Deep.Val.st]
  rw [if_pos g.1, if_pos g.2]

/-- ⭐ TWO EMITS, ONE SENDER ⇒ TWO TOKENS. Premises: exactly `two_calls`'s (call 1's and, under ∀ s2, the caller's and
    call 2's), plus a fuel at which each run is observed stopped at 0x1043 and the two senders equal. Conclusion: the
    sender held ≥ 2 tokens in call 1's start memory, and call 2's end memory carries a token state that reads two fewer
    for that sender (StRel at the same bucket base). -/
theorem two_emits_same_sender (acl : VIR.Principal → VIR.TopicId → Bool) (s1 : Cpu)
    (buf1 : ByteArray) (off1 len1 : Nat) (σ : VIR.State) (buf2 : ByteArray) (off2 len2 : Nat)
    (h : Live s1) (hrip : s1.rip = 0x1000)
    (hlen : len1 = (s1.regs.get .rsi).toNat)
    (hbuf : BufRel buf1 off1 len1 s1.mem (s1.regs.get .rdi))
    (hacl : AclRel acl s1.mem)
    (hst : StRel σ s1.mem (s1.regs.get .rdx))
    (htopic : 24 ≤ len1 → ((VIR.Deep.Val.slice buf1 off1 len1).rd 8).toP.toNat < 64)
    (hdisj : ∀ i, i < len1 → ¬ Region (Refines.cell (s1.regs.get .rdx) ((VIR.Deep.Val.slice buf1 off1 len1).rd 4).toP) 4
      (s1.regs.get .rdi + BitVec.ofNat 64 i))
    (hacw : ∀ p t : UInt32, t.toNat < 64 →
      ¬ Region (Refines.cell (s1.regs.get .rdx) ((VIR.Deep.Val.slice buf1 off1 len1).rd 4).toP) 4 (aclAddr p t))
    (m1 : Nat) (hm1 : (runP repaired m1 s1).stopped = true) (he1 : (runP repaired m1 s1).rip = 0x1043)
    (s2 : Cpu) (hc : Caller (s1.regs.get .rdx) (runP repaired m1 s1) s2 buf2 off2 len2)
    (hbk2 : ∀ p : UInt32, ∀ k, k < 4 → ¬ Region (s2.regs.get .rdi) len2 (Refines.cell (s1.regs.get .rdx) p + BitVec.ofNat 64 k))
    (hac2 : ∀ p t : UInt32, t.toNat < 64 → ¬ Region (s2.regs.get .rdi) len2 (aclAddr p t))
    (htopic2 : 24 ≤ len2 → ((VIR.Deep.Val.slice buf2 off2 len2).rd 8).toP.toNat < 64)
    (hdisj2 : ∀ i, i < len2 → ¬ Region (Refines.cell (s1.regs.get .rdx) ((VIR.Deep.Val.slice buf2 off2 len2).rd 4).toP) 4
      (s2.regs.get .rdi + BitVec.ofNat 64 i))
    (m2 : Nat) (hm2 : (runP repaired m2 s2).stopped = true) (he2 : (runP repaired m2 s2).rip = 0x1043)
    (hsame : ((VIR.Deep.Val.slice buf2 off2 len2).rd 4).toP = ((VIR.Deep.Val.slice buf1 off1 len1).rd 4).toP) :
    let P := ((VIR.Deep.Val.slice buf1 off1 len1).rd 4).toP
    2 ≤ σ P ∧ ∃ σ2 : VIR.State, StRel σ2 (runP repaired m2 s2).mem (s2.regs.get .rdx) ∧ σ2 P = σ P - 2 := by
  intro P
  obtain ⟨n1, hs1, hx1, hk⟩ := two_calls acl s1 buf1 off1 len1 σ buf2 off2 len2 h hrip hlen hbuf hacl hst htopic hdisj hacw
  have hu1 := VIR.Compose.runP_stopped_unique repaired s1 m1 n1 hm1 hs1
  rw [hu1] at hc he1
  -- call 1 stopped at emit: its denotation is the OK one, so call 2 starts from the decremented state
  have hd1 := den_of_guards acl _ σ (guards_of_emit acl _ σ hx1 he1)
  obtain ⟨n2, hs2, hx2⟩ := hk s2 hc hbk2 hac2 htopic2 hdisj2
  rw [hd1] at hx2
  simp only [nextState] at hx2
  have hu2 := VIR.Compose.runP_stopped_unique repaired s2 m2 n2 hm2 hs2
  rw [← hu2] at hx2
  have hd2 := den_of_guards acl _ _ (guards_of_emit acl _ _ hx2 he2)
  -- vir's spec lemma: rate limiting composes
  obtain ⟨h2, hσ2⟩ := VIR.Compose.MultiCall.two_ok_same_sender acl _ _ σ _ _ _ _ hd1 hd2 hsame
  refine ⟨h2, _, ?_, hσ2⟩
  rw [hd2] at hx2
  exact hx2.2.2.2.2.2.1

/-! ## NON-VACUITY: on paris's witness layout (Router.MultiCall: 5 tokens for sender 0, the ACL bit set, the same
packet in both buffers) BOTH calls stop at emit_slice, so every premise of `two_emits_same_sender` is met. -/
set_option maxRecDepth 200000 in
theorem w_guards1 : 24 ≤ (VIR.Deep.Val.slice (bytesOf pkt) 0 24).len ∧
    (((VIR.Deep.Val.slice (bytesOf pkt) 0 24).rd 0).toP = VIR.MAGIC ∧
      wAcl ((VIR.Deep.Val.slice (bytesOf pkt) 0 24).rd 4).toP ((VIR.Deep.Val.slice (bytesOf pkt) 0 24).rd 8).toP = true ∧
      0 < wσ ((VIR.Deep.Val.slice (bytesOf pkt) 0 24).rd 4).toP) := by decide

set_option maxRecDepth 200000 in
theorem w_guards2 : 24 ≤ (VIR.Deep.Val.slice (bytesOf pkt) 0 24).len ∧
    (((VIR.Deep.Val.slice (bytesOf pkt) 0 24).rd 0).toP = VIR.MAGIC ∧
      wAcl ((VIR.Deep.Val.slice (bytesOf pkt) 0 24).rd 4).toP ((VIR.Deep.Val.slice (bytesOf pkt) 0 24).rd 8).toP = true ∧
      0 < (VIR.decTokens wσ ((VIR.Deep.Val.slice (bytesOf pkt) 0 24).rd 4).toP) ((VIR.Deep.Val.slice (bytesOf pkt) 0 24).rd 4).toP) := by
  decide

/-- ⭐ BOTH CALLS EMIT on one concrete state and caller: the premises of `two_emits_same_sender` are satisfiable. -/
theorem two_emits_witness :
    ∃ n1, (runP repaired n1 w1).stopped = true ∧ (runP repaired n1 w1).rip = 0x1043 ∧
      ∃ n2, (runP repaired n2 (enter (runP repaired n1 w1))).stopped = true ∧
        (runP repaired n2 (enter (runP repaired n1 w1))).rip = 0x1043 := by
  have hr : w1.regs.get .rdi = B1 ∧ w1.regs.get .rsi = 24 ∧ w1.regs.get .rdx = RDX := by decide
  obtain ⟨n1, hs1, hx1, hk⟩ := two_calls wAcl w1 (bytesOf pkt) 0 24 wσ (bytesOf pkt) 0 24
    rfl rfl (by rw [hr.2.1]; rfl) (by rw [hr.1]; exact w_buf _ _ w_mem_b1) (fun _ _ _ => rfl)
    (fun p => by rw [hr.2.2]; rfl) (fun _ => w_topic)
    (by rw [w_sender, hr.2.2, hr.1]; exact fun i hi => w_buf_cell 0 B1 (Or.inl rfl) i hi)
    (by rw [w_sender, hr.2.2]; exact fun p t ht => w_acl_cell p t 0 ht)
  have hd1 := den_of_guards wAcl _ wσ w_guards1
  have hx1' := hx1
  rw [hd1] at hx1'
  refine ⟨n1, hs1, hx1'.1, ?_⟩
  have he : ∀ t : Cpu, (enter t).mem = t.mem ∧ (enter t).regs.get .rdi = B2 ∧ (enter t).regs.get .rsi = 24 ∧
      (enter t).regs.get .rdx = RDX ∧ (enter t).rip = 0x1000 ∧ (enter t).ms = none := by
    intro t; simp [enter, Cpu.setReg, Value.writeView, Regs.get_set_ne]
  obtain ⟨m2, d2, l2, x2, r2, ms2⟩ := he (runP repaired n1 w1)
  have hc : Caller (w1.regs.get .rdx) (runP repaired n1 w1) (enter (runP repaired n1 w1)) (bytesOf pkt) 0 24 := by
    refine ⟨ms2, r2, by rw [x2, hr.2.2], by rw [l2]; rfl, ?_, ?_⟩
    · rw [d2]
      apply w_buf
      intro i hi
      rw [m2, read_outside_cell hx1 _ (by rw [w_sender, hr.2.2]; exact w_buf_cell 0 B2 (Or.inr rfl) i hi)]
      exact w_mem_b2 i hi
    · rw [m2]; exact agreeOutside_rfl _ _
  obtain ⟨n2, hs2, hx2⟩ := hk _ hc
    (by rw [d2, hr.2.2]; exact fun p k hk => w_cell_buf p B2 (Or.inr rfl) k hk)
    (by rw [d2]; exact fun p t ht => w_acl_buf p t ht)
    (fun _ => w_topic)
    (by rw [w_sender, hr.2.2, d2]; exact fun i hi => w_buf_cell 0 B2 (Or.inr rfl) i hi)
  rw [hd1] at hx2
  simp only [nextState] at hx2
  rw [den_of_guards wAcl _ _ w_guards2] at hx2
  exact ⟨n2, hs2, hx2.1⟩

end VIR.Compose.RateLimit
