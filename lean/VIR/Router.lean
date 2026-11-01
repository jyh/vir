/-
  The router (inputs I2-I4): the three specs, the unfused term U (B.1's order) and the fused term F (A.3),
  and the goal I4, `U = F` as equality of denotations.
-/
import VIR.Rules

namespace VIR

variable (acl : Principal → TopicId → Bool)

/-! ## I2: the spec bodies, each with its continuation hole -/
def parseHeader {n : Nat} (b0 : Slice n)
    (k : Slice (n - 12) → Principal → TopicId → 24 ≤ n → Out) : Out :=
  guard (24 ≤ n) (fun h =>
    readU32 b0 0 fun magic =>
    guard (magic = MAGIC) (fun _ =>
      readU32 b0 4 fun sender =>
      readU32 b0 8 fun topic =>
      advance b0 12 (by omega) fun s => k s sender topic h)
      (.drop .unauthOrRate))
    (.drop .truncated)

def checkRateLimit (st : State) (p : Principal) (k : State → Out) : Out :=
  guard (hasTokens st p) (fun _ => letLin (decTokens st p) k) (.drop .unauthOrRate)

def verifyAcl (p : Principal) (t : TopicId) (k : Out) : Out :=
  guard (canAccess acl p t) (fun _ => k) (.drop .unauthOrRate)

def emitPayload {m : Nat} (s : Slice m) (h : 12 ≤ m) (st : State) : Out :=
  advance s 12 h fun p => .ret st _ p

/-! ## I3: the unfused term (B.1's order: rate limit, then ACL) -/
def U {n : Nat} (b0 : Slice n) (st : State) : Out :=
  parseHeader b0 fun s1 sender topic h =>
    checkRateLimit st sender fun st' =>
      verifyAcl acl sender topic (emitPayload s1 (by omega) st')

/-! ## A.3's fused term, as written -/
def F {n : Nat} (b0 : Slice n) (st : State) : Out :=
  guard (24 ≤ n) (fun h =>
    readU32 b0 0 fun magic =>
    readU32 b0 4 fun sender =>
    readU32 b0 8 fun topic =>
    guard (magic = MAGIC ∧ canAccess acl sender topic ∧ hasTokens st sender) (fun _ =>
      letLin (decTokens st sender) fun st' =>
      advance b0 24 h fun p => .ret st' _ p)
      (.drop .unauthOrRate))
    (.drop .truncated)

/-! ## I4 -/
/-! ### The AUX rules the chain uses (E8). Names `aux_*` are counted by the harness (C3). -/

/-- A pure read hoists out of a guard that does not mention its value. -/
theorem aux_read_past_guard {n : Nat} (c : Prop) [Decidable c] (b : Slice n) (j : Nat)
    (k : UInt32 → Out) (e : Out) :
    guard c (fun _ => readU32 b j k) e = readU32 b j (fun v => guard c (fun _ => k v) e) := rfl

/-- An advance sinks below a guard that does not mention the slice. -/
theorem aux_advance_past_guard {n : Nat} (b : Slice n) (i : Nat) (hi : i ≤ n) (c : Prop) [Decidable c]
    (k : Slice (n - i) → Out) (e : Out) :
    advance b i hi (fun s => guard c (fun _ => k s) e) = guard c (fun _ => advance b i hi k) e := rfl

/-- Two guards with one error branch commute (the ACL-before-rate-limit reorder). -/
theorem aux_guard_swap (a b : Prop) [Decidable a] [Decidable b] (k e : Out) :
    guard a (fun _ => guard b (fun _ => k) e) e = guard b (fun _ => guard a (fun _ => k) e) e := by
  unfold guard; by_cases ha : a <;> by_cases hb : b <;> simp [ha, hb]

/-- I4, the SCORED proof: a rewrite chain over the 7 given rules and the aux rules above. -/
theorem router_fusion {n : Nat} (b0 : Slice n) (st : State) : U acl b0 st = F acl b0 st := by
  unfold U F parseHeader checkRateLimit verifyAcl emitPayload
  congr 1; funext h
  congr 1; funext magic
  rw [aux_read_past_guard]; congr 1; funext sender
  rw [aux_read_past_guard]; congr 1; funext topic
  simp only [beta_lin]
  simp only [aux_advance_past_guard]
  rw [aux_guard_swap (hasTokens st sender) (canAccess acl sender topic)]
  rw [slice_fuse b0 12 12 (by omega) (by omega) (by omega)
      (fun m p => Out.ret (decTokens st sender) m p)]
  rw [guard_merge (canAccess acl sender topic) (hasTokens st sender),
      guard_merge (magic = MAGIC) (canAccess acl sender topic ∧ hasTokens st sender)]

/-- The SHORTCUT, recorded as a finding (not scored): a case split on the three tests proves I4
    without the rewrite chain. mojave's arm records the same shortcut on its side. -/
theorem router_fusion_casesplit {n : Nat} (b0 : Slice n) (st : State) : U acl b0 st = F acl b0 st := by
  unfold U F parseHeader checkRateLimit verifyAcl emitPayload
  by_cases h24 : 24 ≤ n
  · have fuse := slice_fuse b0 12 12 (by omega) (by omega) (by omega)
      (fun m s => Out.ret (decTokens st (b0.rd 4)) m s)
    simp only [guard, readU32, letLin, h24, dite_true] at fuse ⊢
    by_cases hm : b0.rd 0 = MAGIC <;> by_cases ha : canAccess acl (b0.rd 4) (b0.rd 8) <;>
      by_cases ht : hasTokens st (b0.rd 4) <;> simp [hm, ha, ht]
    exact fuse
  · simp [guard, h24]

end VIR
