/-
  STATUS-vir row 42 (O95), RESTATED AT DELIVERY: program 3's `route_acl_safe` is over F2 (program 2), which is NOT
  lowered (paris @[bus]). The shape that CAN be read on x86 is K3's on program 1's F: whenever the repaired code
  stops at emit_slice (0x1043), AT ANY FUEL, the guards F names held — magic, the ACL bit, a token, len ≥ 24.
  It needs "a stopped run is unique" (x86lean's `runP_stopped` + `runP_add`), so the 0x1043 the reader observes is the
  same stop `repaired_refines` speaks of.
-/
import Router.Refines

namespace VIR.Compose
open X86 Router Router.Refines

/-- Two stopped runs from one state are the same state: a finished routine stays finished. -/
theorem runP_stopped_unique (p : Program) (s : Cpu) (m n : Nat)
    (hm : (runP p m s).stopped = true) (hn : (runP p n s).stopped = true) : runP p m s = runP p n s := by
  rcases Nat.le_total m n with h | h
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [runP_add, runP_stopped p k _ hm]
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [runP_add, runP_stopped p k _ hn]

/-- K3 AT THE MACHINE (program 1): if the repaired code stops at emit_slice at any fuel `m`, then the frame was
    long enough, the magic matched, the sender's ACL bit for the topic was set, and the sender held a token. -/
theorem emit_implies_guards (acl : VIR.Principal → VIR.TopicId → Bool) (s : Cpu)
    (buf : ByteArray) (off len : Nat) (σ : VIR.State)
    (h : Live s) (hrip : s.rip = 0x1000)
    (hlen : len = (s.regs.get .rsi).toNat)
    (hbuf : BufRel buf off len s.mem (s.regs.get .rdi))
    (hacl : AclRel acl s.mem)
    (hst : StRel σ s.mem (s.regs.get .rdx))
    (htopic : 24 ≤ len → ((VIR.Deep.Val.slice buf off len).rd 8).toP.toNat < 64)
    (hdisj : ∀ i, i < len → ¬ Region (cell (s.regs.get .rdx) ((VIR.Deep.Val.slice buf off len).rd 4).toP) 4
      (s.regs.get .rdi + BitVec.ofNat 64 i))
    (m : Nat) (hm : (runP repaired m s).stopped = true) (hemit : (runP repaired m s).rip = 0x1043) :
    let b := VIR.Deep.Val.slice buf off len
    24 ≤ len ∧ (b.rd 0).toP = VIR.MAGIC ∧ acl (b.rd 4).toP (b.rd 8).toP = true ∧ 0 < σ (b.rd 4).toP := by
  intro b
  obtain ⟨n, hn, hE⟩ := repaired_refines acl s buf off len σ h hrip hlen hbuf hacl hst htopic hdisj
  rw [← runP_stopped_unique repaired s m n hm hn] at hE
  rw [VIR.Deep.F_exit] at hE
  simp only [VIR.Deep.Val.len, VIR.Deep.Val.st] at hE
  by_cases h1 : 24 ≤ len
  · by_cases h2 : (b.rd 0).toP = VIR.MAGIC ∧ acl (b.rd 4).toP (b.rd 8).toP = true ∧ 0 < σ (b.rd 4).toP
    · exact ⟨h1, h2⟩
    · simp only [h1, if_true, b] at hE h2
      rw [if_neg h2] at hE
      simp only [Exit, hemit] at hE
      obtain ⟨hr, _⟩ := hE
      rcases hr with hr | hr <;> exact absurd hr (by decide)
  · simp only [h1, if_false, Exit, hemit] at hE
    exact absurd hE.1 (by decide)

end VIR.Compose
