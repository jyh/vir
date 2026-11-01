/-
  STATUS-vir row 55 (O95). THE CALLER RELATION, SHOWN NON-TRIVIAL (paris's item 4): paris's `two_calls_witness` caller
  `enter` leaves memory UNCHANGED between the calls. Here the caller WRITES a fresh packet into buffer 2 — magic,
  sender 1, topic 0 — before re-entering, discharging `Caller`'s frame from the write itself. Sender 1's ACL bit is
  clear on the witness layout, so call 2 is predicted to DROP (unauthOrRate) with memory unchanged; the theorem says so.
-/
import Router.MultiCall
import Compose.RateLimit

namespace VIR.Compose.CallerWrite
open X86 Router Router.Refines Router.MultiCall VIR.Compose.RateLimit

/-- `putBytes` writes only inside `[a, a + length)`. -/
theorem putBytes_frame : ∀ (l : List (BitVec 8)) (m : Mem) (a : BitVec 64),
    AgreeOutside (Region a l.length) m (putBytes m a l)
  | [], m, a => agreeOutside_rfl _ _
  | b :: bs, m, a => by
      intro x hx
      have hx' : ¬ Region (a + 1) bs.length x := by
        rintro ⟨j, hj, rfl⟩
        exact hx ⟨j + 1, by simp; omega, by bv_omega⟩
      have hne : x ≠ a := fun h => hx ⟨0, by simp, by rw [h]; simp⟩
      simp only [putBytes]
      rw [← putBytes_frame bs (m.write a b) (a + 1) x hx', Mem.read_write_ne _ _ _ _ hne]

/-- …and reads back what it wrote, when the run does not wrap. -/
theorem putBytes_read : ∀ (l : List (BitVec 8)) (m : Mem) (a : BitVec 64), l.length < 2 ^ 64 →
    ∀ i, i < l.length → (putBytes m a l).read (a + BitVec.ofNat 64 i) = l.getD i 0
  | [], _, _, _, i, hi => by simp at hi
  | b :: bs, m, a, hl, 0, _ => by
      simp only [putBytes, List.getD_cons_zero]
      have hn : ¬ Region (a + 1) bs.length (a + BitVec.ofNat 64 0) := by
        rintro ⟨j, hj, he⟩
        simp only [List.length_cons] at hl
        bv_omega
      rw [← putBytes_frame bs (m.write a b) (a + 1) _ hn]
      simp
  | b :: bs, m, a, hl, i + 1, hi => by
      simp only [putBytes, List.getD_cons_succ]
      simp only [List.length_cons] at hl hi
      rw [show a + BitVec.ofNat 64 (i + 1) = a + 1 + BitVec.ofNat 64 i by bv_omega]
      exact putBytes_read bs (m.write a b) (a + 1) (by omega) i (by omega)

/-- The caller's packet: magic, sender 1, topic 0, 12 payload bytes. -/
def pkt2 : List (BitVec 8) := [0x31, 0x47, 0x53, 0x4D, 0x01, 0, 0, 0] ++ List.replicate 16 0

/-- The caller: write `pkt2` into buffer 2, then re-enter exactly as `enter` does. -/
def enterW (t : Cpu) : Cpu := enter { t with mem := putBytes t.mem B2 pkt2 }

set_option maxRecDepth 100000 in
theorem w_buf2 (m : Mem) (base : BitVec 64) (hm : ∀ i, i < 24 → m.read (base + BitVec.ofNat 64 i) = pkt2.getD i 0) :
    BufRel (bytesOf pkt2) 0 24 m base := by
  intro i hi
  rw [hm i hi]
  revert i; decide

theorem w_topic2 : ((VIR.Deep.Val.slice (bytesOf pkt2) 0 24).rd 8).toP.toNat < 64 := by decide
theorem w_sender2 : ((VIR.Deep.Val.slice (bytesOf pkt2) 0 24).rd 4).toP = 1 := by decide

set_option maxRecDepth 200000 in
/-- Sender 1 has no ACL bit for topic 0 on the witness layout, so F drops call 2 (whatever the token state). -/
theorem w_drop2 (σ : VIR.State) :
    VIR.Deep.den wAcl (VIR.Deep.F (.slice (bytesOf pkt2) 0 24) (.state σ)) = .drop .unauthOrRate := by
  rw [VIR.Deep.F_exit]
  have hacl : wAcl ((VIR.Deep.Val.slice (bytesOf pkt2) 0 24).rd 4).toP
      ((VIR.Deep.Val.slice (bytesOf pkt2) 0 24).rd 8).toP = false := by decide
  have hlen : 24 ≤ (VIR.Deep.Val.slice (bytesOf pkt2) 0 24).len := by decide
  rw [if_pos hlen, if_neg (by rw [hacl]; simp)]

/-- ⭐ A CALLER THAT WRITES: call 1 as in paris's witness (it EMITS), then the caller writes a fresh packet from
    sender 1 into buffer 2; every premise of `two_calls` for call 2 is discharged on the WRITTEN memory, and call 2
    stops at a drop label (0x1041 or 0x1042) with memory unchanged. -/
theorem caller_write_witness :
    ∃ n1, (runP repaired n1 w1).stopped = true ∧ (runP repaired n1 w1).rip = 0x1043 ∧
      ∃ n2, (runP repaired n2 (enterW (runP repaired n1 w1))).stopped = true ∧
        ((runP repaired n2 (enterW (runP repaired n1 w1))).rip = 0x1041 ∨
          (runP repaired n2 (enterW (runP repaired n1 w1))).rip = 0x1042) ∧
        (runP repaired n2 (enterW (runP repaired n1 w1))).mem = (enterW (runP repaired n1 w1)).mem := by
  have hr : w1.regs.get .rdi = B1 ∧ w1.regs.get .rsi = 24 ∧ w1.regs.get .rdx = RDX := by decide
  obtain ⟨n1, hs1, hx1, hk⟩ := two_calls wAcl w1 (bytesOf pkt) 0 24 wσ (bytesOf pkt2) 0 24
    rfl rfl (by rw [hr.2.1]; rfl) (by rw [hr.1]; exact w_buf _ _ w_mem_b1) (fun _ _ _ => rfl)
    (fun p => by rw [hr.2.2]; rfl) (fun _ => w_topic)
    (by rw [w_sender, hr.2.2, hr.1]; exact fun i hi => w_buf_cell 0 B1 (Or.inl rfl) i hi)
    (by rw [w_sender, hr.2.2]; exact fun p t ht => w_acl_cell p t 0 ht)
  have hx1' := hx1
  rw [den_of_guards wAcl _ wσ w_guards1] at hx1'
  refine ⟨n1, hs1, hx1'.1, ?_⟩
  have he : ∀ t : Cpu, (enterW t).mem = putBytes t.mem B2 pkt2 ∧ (enterW t).regs.get .rdi = B2 ∧
      (enterW t).regs.get .rsi = 24 ∧ (enterW t).regs.get .rdx = RDX ∧ (enterW t).rip = 0x1000 ∧ (enterW t).ms = none := by
    intro t; simp [enterW, enter, Cpu.setReg, Value.writeView, Regs.get_set_ne]
  obtain ⟨m2, d2, l2, x2, r2, ms2⟩ := he (runP repaired n1 w1)
  have hc : Caller (w1.regs.get .rdx) (runP repaired n1 w1) (enterW (runP repaired n1 w1)) (bytesOf pkt2) 0 24 := by
    refine ⟨ms2, r2, by rw [x2, hr.2.2], by rw [l2]; rfl, ?_, ?_⟩
    · rw [d2]
      apply w_buf2
      intro i hi
      rw [m2]
      exact putBytes_read pkt2 _ B2 (by decide) i (by simpa [pkt2] using hi)
    · rw [m2, d2]
      exact putBytes_frame pkt2 _ B2
  obtain ⟨n2, hs2, hx2⟩ := hk _ hc
    (by rw [d2, hr.2.2]; exact fun p k hk => w_cell_buf p B2 (Or.inr rfl) k hk)
    (by rw [d2]; exact fun p t ht => w_acl_buf p t ht)
    (fun _ => w_topic2)
    (by rw [w_sender2, hr.2.2, d2]; exact fun i hi => w_buf_cell 1 B2 (Or.inr rfl) i hi)
  rw [w_drop2] at hx2
  exact ⟨n2, hs2, hx2.1, hx2.2⟩

end VIR.Compose.CallerWrite
