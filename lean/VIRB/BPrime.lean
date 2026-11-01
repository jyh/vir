/-
  B′, the Lean mirror (PREDICTIONS-amend-10). Program 1.
  The I1 operators are FIELDS of one structure `Carrier`, never axioms. `vlen`, `advance` and `read_u32` are DEFINED, so
  the I1 slice and read laws are theorems. The wire is `List Int` and a slice is the unindexed pair (wire, offset),
  mirroring the MetaPRL arm's `wirebuf = list{int}` and `vslice = wirebuf * int` (B′ branch, vir.ml).
-/
namespace VIR.BPrime

abbrev WireBuf := List Int
abbrev VSlice := WireBuf × Int

/-- C4vir: the uninterpreted part of the VIR. 8 fields, one per MetaPRL `prim` of vir.ml (amend-10 B2). -/
structure Carrier where
  State : Type
  VErr : Type
  wire_u32 : WireBuf → Int → Int
  can_access : Int → Int → Bool
  has_tokens : State → Int → Bool
  dec_tokens : State → Int → State
  errTruncated : VErr
  errUnauth : VErr

variable (C : Carrier)

/-- `vresult = (state × vslice) + verr`. -/
abbrev Out := (C.State × VSlice) ⊕ C.VErr

def MAGIC : Int := 1297303345

/-! ## The A.2 forms, DEFINED (as MetaPRL's `define`s) -/
def vlen (s : VSlice) : Int := (s.1.length : Int) - s.2
def advance {α : Type} (b : VSlice) (i : Int) (k : VSlice → α) : α := k (b.1, b.2 + i)
def read_u32 {α : Type} (b : VSlice) (j : Int) (k : Int → α) : α := k (C.wire_u32 b.1 (b.2 + j))
def vguard {α : Type} (c : Bool) (e1 e2 : α) : α := if c then e1 else e2
def let_lin {α β : Type} (op : α) (k : α → β) : β := k op
def vreturn (a : C.State × VSlice) : Out C := .inl a
def vdrop (c : C.VErr) : Out C := .inr c

/-! ## The I1 laws, PROVED from the definitions (never fields) -/
theorem slice_law (b : VSlice) (i : Int) : advance b i vlen = vlen b - i := by
  simp only [advance, vlen]; omega
theorem read_law (b : VSlice) (i j : Int) (k : Int → Out C) :
    advance b i (fun s => read_u32 C s j k) = k (C.wire_u32 b.1 (b.2 + (i + j))) := by
  simp only [advance, read_u32, Int.add_assoc]

/-! ## I2 -/
def parse_header (b0 : VSlice) (k : VSlice → Int → Int → Out C) : Out C :=
  vguard (decide (vlen b0 ≥ 24))
    (read_u32 C b0 0 fun magic =>
      vguard (magic == MAGIC)
        (read_u32 C b0 4 fun sender => read_u32 C b0 8 fun topic => advance b0 12 fun s => k s sender topic)
        (vdrop C C.errUnauth))
    (vdrop C C.errTruncated)

def check_rate_limit (st : C.State) (p : Int) (k : C.State → Out C) : Out C :=
  vguard (C.has_tokens st p) (let_lin (C.dec_tokens st p) k) (vdrop C C.errUnauth)

def verify_acl (p t : Int) (k : Out C) : Out C :=
  vguard (C.can_access p t) k (vdrop C C.errUnauth)

def emit_payload (s : VSlice) (st : C.State) : Out C := advance s 12 fun payload => vreturn C (st, payload)

/-! ## I3 and A.3 -/
def U (b0 : VSlice) (st : C.State) : Out C :=
  parse_header C b0 fun s1 sender topic =>
    check_rate_limit C st sender fun st2 => verify_acl C sender topic (emit_payload C s1 st2)

def F (b0 : VSlice) (st : C.State) : Out C :=
  vguard (decide (vlen b0 ≥ 24))
    (read_u32 C b0 0 fun magic => read_u32 C b0 4 fun sender => read_u32 C b0 8 fun topic =>
      vguard ((magic == MAGIC) && (C.can_access sender topic && C.has_tokens st sender))
        (let_lin (C.dec_tokens st sender) fun st2 => advance b0 24 fun payload_slice => vreturn C (st2, payload_slice))
        (vdrop C C.errUnauth))
    (vdrop C C.errTruncated)

/-! ## The GIVEN rules used by the chain (I5), proved here over the carrier -/
theorem beta_lin {α β : Type} (v : α) (e : α → β) : let_lin v e = e v := rfl
theorem guard_merge {α : Type} (c1 c2 : Bool) (eok eerr : α) :
    vguard c1 (vguard c2 eok eerr) eerr = vguard (c1 && c2) eok eerr := by
  cases c1 <;> cases c2 <;> rfl
theorem slice_fuse {α : Type} (b : VSlice) (i j : Int) (e : VSlice → α) :
    advance b i (fun s1 => advance s1 j e) = advance b (i + j) e := by
  simp only [advance, Int.add_assoc]

/-! ## The AUX rules (E8), counted by C3 -/
theorem aux_read_past_guard {α : Type} (c : Bool) (b : VSlice) (j : Int) (k : Int → α) (d : α) :
    vguard c (read_u32 C b j k) d = read_u32 C b j (fun v => vguard c (k v) d) := rfl
theorem aux_advance_past_guard {α : Type} (b : VSlice) (i : Int) (c : Bool) (k : VSlice → α) (d : α) :
    advance b i (fun s => vguard c (k s) d) = vguard c (advance b i k) d := rfl
theorem aux_guard_swap {α : Type} (c1 c2 : Bool) (e d : α) :
    vguard c1 (vguard c2 e d) d = vguard c2 (vguard c1 e d) d := by
  cases c1 <;> cases c2 <;> rfl

/-- I4 under B′: the SCORED chain, the same rewrite steps as `VIR.router_fusion`. No typing premise. -/
theorem router_fusion_bp (b0 : VSlice) (st : C.State) : U C b0 st = F C b0 st := by
  unfold U F parse_header check_rate_limit verify_acl emit_payload
  congr 1; congr 1; funext magic
  rw [aux_read_past_guard]; congr 1; funext sender
  rw [aux_read_past_guard]; congr 1; funext topic
  simp only [beta_lin]
  simp only [aux_advance_past_guard]
  rw [aux_guard_swap (C.has_tokens st sender) (C.can_access sender topic)]
  rw [slice_fuse]
  rw [guard_merge (C.can_access sender topic) (C.has_tokens st sender),
      guard_merge (magic == MAGIC) (C.can_access sender topic && C.has_tokens st sender)]
  rfl   -- const_fold (I5): 12 + 12 = 24 on Int literals

end VIR.BPrime
