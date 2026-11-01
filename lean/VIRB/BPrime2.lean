/-
  B′, the Lean mirror (PREDICTIONS-amend-10). Program 2 (inputs/program2-inputs.md, J1–J5).
  `take` and the bad-payload code join the uninterpreted part, as the MetaPRL arm's vir2.ml adds `take` and
  `err_bad_payload` as prims. C4vir for program 2 is therefore 10 on both arms.
-/
import VIRB.BPrime

namespace VIR.BPrime

/-- The program-2 carrier: program 1's 8 fields plus `take` (J1, a CPS operator) and the bad-payload code. -/
structure Carrier2 extends Carrier where
  take : {α : Type} → VSlice → Int → (VSlice → α) → α
  errBadPayload : VErr

variable (C : Carrier2)

/-! ## J2 -/
def parse_header2 (b0 : VSlice) (k : VSlice → Int → Int → Int → Int → Out C.toCarrier) : Out C.toCarrier :=
  vguard (decide (vlen b0 ≥ 24))
    (read_u32 C.toCarrier b0 0 fun magic =>
      vguard (magic == MAGIC)
        (read_u32 C.toCarrier b0 4 fun sender => read_u32 C.toCarrier b0 8 fun topic =>
          read_u32 C.toCarrier b0 12 fun off => read_u32 C.toCarrier b0 16 fun n =>
          advance b0 12 fun s => k s sender topic off n)
        (vdrop C.toCarrier C.errUnauth))
    (vdrop C.toCarrier C.errTruncated)

def emit_payload2 (s : VSlice) (off n : Int) (st : C.State) : Out C.toCarrier :=
  vguard (decide (24 ≤ off) && decide (off + n ≤ vlen s + 12))
    (advance s (off - 12) fun p => C.take p n fun q => vreturn C.toCarrier (st, q))
    (vdrop C.toCarrier C.errBadPayload)

/-! ## J3, J4 -/
def U2 (b0 : VSlice) (st : C.State) : Out C.toCarrier :=
  parse_header2 C b0 fun s1 sender topic off n =>
    check_rate_limit C.toCarrier st sender fun st2 =>
      verify_acl C.toCarrier sender topic (emit_payload2 C s1 off n st2)

def F2 (b0 : VSlice) (st : C.State) : Out C.toCarrier :=
  vguard (decide (vlen b0 ≥ 24))
    (read_u32 C.toCarrier b0 0 fun magic => read_u32 C.toCarrier b0 4 fun sender =>
      read_u32 C.toCarrier b0 8 fun topic => read_u32 C.toCarrier b0 12 fun off =>
      read_u32 C.toCarrier b0 16 fun n =>
      vguard ((magic == MAGIC) && (C.can_access sender topic && C.has_tokens st sender))
        (let_lin (C.dec_tokens st sender) fun st2 =>
          vguard (decide (24 ≤ off) && decide (off + n ≤ vlen b0))
            (advance b0 off fun p => C.take p n fun q => vreturn C.toCarrier (st2, q))
            (vdrop C.toCarrier C.errBadPayload))
        (vdrop C.toCarrier C.errUnauth))
    (vdrop C.toCarrier C.errTruncated)

/-! ## The AUX rule program 2 adds (E8), counted by C3: the I1 slice law read under the advance binder. On Int it
    needs no enclosing guard (amend-7 R1's finding, on the B′ carrier). -/
theorem aux_advance_guard_vlen {α : Type} (b : VSlice) (i x : Int) (c : Bool) (e : VSlice → α) (d : α) :
    advance b i (fun s => vguard (c && decide (x ≤ vlen s + i)) (e s) d)
      = advance b i (fun s => vguard (c && decide (x ≤ vlen b)) (e s) d) := by
  have h : vlen (b.1, b.2 + i) + i = vlen b := by simp only [vlen]; omega
  simp only [advance, h]

/-! ## J5, the SCORED chain: program 1's rewrite steps, then two arithmetic steps on Int (no enclosing guard needed) -/
theorem router2_fusion_bp (b0 : VSlice) (st : C.State) : U2 C b0 st = F2 C b0 st := by
  unfold U2 F2 parse_header2 check_rate_limit verify_acl emit_payload2
  congr 1; congr 1; funext magic
  rw [aux_read_past_guard]; congr 1; funext sender
  rw [aux_read_past_guard]; congr 1; funext topic
  rw [aux_read_past_guard]; congr 1; funext off
  rw [aux_read_past_guard]; congr 1; funext n
  simp only [beta_lin]
  simp only [aux_advance_past_guard]
  rw [aux_guard_swap (C.has_tokens st sender) (C.can_access sender topic)]
  rw [guard_merge (C.can_access sender topic) (C.has_tokens st sender),
      guard_merge (magic == MAGIC) (C.can_access sender topic && C.has_tokens st sender)]
  congr 1
  rw [aux_advance_guard_vlen, aux_advance_past_guard]
  congr 1
  rw [slice_fuse]
  congr 1; omega   -- arithmetic (const_fold on Int): 12 + (off - 12) = off, with no enclosing guard

end VIR.BPrime
