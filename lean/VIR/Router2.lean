/-
  PROGRAM 2 (inputs/program2-inputs.md, J1-J5), Lean arm L-IDX shallow: the B.1-faithful router with a DYNAMIC payload.
-/
import VIR.Router

namespace VIR

/-- J1 `take{s; k; p. …}`: the first `k` bytes of `s`. -/
def Slice.take {m : Nat} (s : Slice m) (k : Nat) (h : k ≤ m) : Slice k := ⟨s.buf, s.off, by have := s.fits; omega⟩
def take {m : Nat} (s : Slice m) (k : Nat) (h : k ≤ m) (c : Slice k → Out) : Out := c (s.take k h)

variable (acl : Principal → TopicId → Bool)

/-! ## J2 -/
def parseHeader2 {n : Nat} (b0 : Slice n)
    (k : Slice (n - 12) → Principal → TopicId → UInt32 → UInt32 → 24 ≤ n → Out) : Out :=
  guard (24 ≤ n) (fun h =>
    readU32 b0 0 fun magic =>
    guard (magic = MAGIC) (fun _ =>
      readU32 b0 4 fun sender => readU32 b0 8 fun topic =>
      readU32 b0 12 fun off => readU32 b0 16 fun len =>
      advance b0 12 (by omega) fun s => k s sender topic off len h)
      (.drop .unauthOrRate))
    (.drop .truncated)

def emitPayload2 {m : Nat} (s : Slice m) (off k : Nat) (st : State) : Out :=
  guard (24 ≤ off ∧ off + k ≤ m + 12) (fun h =>
    advance s (off - 12) (by omega) fun p => take p k (by omega) fun q => .ret st _ q)
    (.drop .badPayload)

/-! ## J3, J4 -/
def U2 {n : Nat} (b0 : Slice n) (st : State) : Out :=
  parseHeader2 b0 fun s1 sender topic off len _ =>
    checkRateLimit st sender fun st' =>
      verifyAcl acl sender topic (emitPayload2 s1 off.toNat len.toNat st')

def F2 {n : Nat} (b0 : Slice n) (st : State) : Out :=
  guard (24 ≤ n) (fun _ =>
    readU32 b0 0 fun magic => readU32 b0 4 fun sender => readU32 b0 8 fun topic =>
    readU32 b0 12 fun off => readU32 b0 16 fun len =>
    guard (magic = MAGIC ∧ canAccess acl sender topic ∧ hasTokens st sender) (fun _ =>
      letLin (decTokens st sender) fun st' =>
      guard (24 ≤ off.toNat ∧ off.toNat + len.toNat ≤ n) (fun h2 =>
        advance b0 off.toNat (by omega) fun p => take p len.toNat (by omega) fun q => .ret st' _ q)
        (.drop .badPayload))
      (.drop .unauthOrRate))
    (.drop .truncated)

/-! ## The rules program 2 adds -/

/-- The dependent twin of `Slice.congr_heq`: the continuation also receives a proof about the length. -/
theorem Slice.congr_heq_dep {N : Nat} (e : (m : Nat) → m = N → Slice m → Out) {m₁ m₂ : Nat}
    (h₁ : m₁ = N) (h₂ : m₂ = N) {x : Slice m₁} {y : Slice m₂} (hxy : HEq x y) : e m₁ h₁ x = e m₂ h₂ y := by
  subst h₁; subst h₂; cases hxy; rfl

/-- `[slice_fuse]` in its DEPENDENT form: the continuation may use the length relation (as mojave's conditional
    `slice_fuse_c` carries its side condition). A form of a GIVEN rule, not an aux rule. -/
theorem slice_fuse_dep {n : Nat} (b : Slice n) (i j : Nat) (h₁ : i ≤ n) (h₂ : j ≤ n - i) (h₃ : i + j ≤ n)
    (e : (m : Nat) → m = n - (i + j) → Slice m → Out) :
    advance b i h₁ (fun s₁ => advance s₁ j h₂ (fun s₂ => e _ (by omega) s₂))
      = advance b (i + j) h₃ (fun s₂ => e _ rfl s₂) := by
  unfold advance
  exact Slice.congr_heq_dep e _ _ (Slice.adv_adv_heq b i j h₁ h₂ h₃)

/-- AUX (program 2, Q3): an advance by `i` IS an advance by `j` when `i = j` — the equation is supplied by an
    ENCLOSING guard (here `12 ≤ off`), so this is the context-dependent rewrite J5 needs. -/
theorem aux_advance_idx {n : Nat} (b : Slice n) (i j : Nat) (hij : i = j) (hi : i ≤ n) (hj : j ≤ n)
    (e : (m : Nat) → m = n - j → Slice m → Out) :
    advance b i hi (fun s => e _ (by omega) s) = advance b j hj (fun s => e _ rfl s) := by
  subst hij; rfl

/-- AUX (program 2): an advance sinks below a guard whose ok-branch USES the guard's proof. -/
theorem aux_advance_past_dguard {n : Nat} (b : Slice n) (i : Nat) (hi : i ≤ n) (c : Prop) [Decidable c]
    (k : Slice (n - i) → c → Out) (e : Out) :
    advance b i hi (fun s => guard c (fun h => k s h) e) = guard c (fun h => advance b i hi (fun s => k s h)) e := rfl

/-- AUX (program 2): two guards whose conditions are equal as propositions are the same guard. -/
theorem aux_guard_cond_eq (c d : Prop) [Decidable c] [Decidable d] (hcd : c ↔ d)
    (ok : d → Out) (e : Out) : guard c (fun h => ok (hcd.mp h)) e = guard d ok e := by
  unfold guard; by_cases h : d
  · simp [h, hcd.mpr h]
  · have : ¬c := fun hc => h (hcd.mp hc)
    simp [h, this]

/-- J5, the SCORED chain (I7) for program 2. -/
theorem router2_fusion {n : Nat} (b0 : Slice n) (st : State) : U2 acl b0 st = F2 acl b0 st := by
  unfold U2 F2 parseHeader2 checkRateLimit verifyAcl emitPayload2
  congr 1; funext h
  congr 1; funext magic
  rw [aux_read_past_guard]; congr 1; funext sender
  rw [aux_read_past_guard]; congr 1; funext topic
  rw [aux_read_past_guard]; congr 1; funext off
  rw [aux_read_past_guard]; congr 1; funext len
  simp only [beta_lin]
  simp only [aux_advance_past_guard]
  simp only [aux_advance_past_dguard]
  rw [aux_guard_swap (hasTokens st sender) (canAccess acl sender topic)]
  rw [guard_merge (canAccess acl sender topic) (hasTokens st sender),
      guard_merge (magic = MAGIC) (canAccess acl sender topic ∧ hasTokens st sender)]
  congr 1; funext _
  have hcd : (24 ≤ off.toNat ∧ off.toNat + len.toNat ≤ n - 12 + 12) ↔ (24 ≤ off.toNat ∧ off.toNat + len.toNat ≤ n) := by
    constructor <;> intro ⟨a, b⟩ <;> exact ⟨a, by omega⟩
  rw [← aux_guard_cond_eq _ _ hcd]
  congr 1; funext h2
  rw [slice_fuse_dep b0 12 (off.toNat - 12) (by omega) (by omega) (by omega)
      (fun m hm p => take p len.toNat (by omega) fun q => Out.ret (decTokens st sender) _ q)]
  exact aux_advance_idx b0 (12 + (off.toNat - 12)) off.toNat (by omega) (by omega) (by omega)
      (fun m hm p => take p len.toNat (by omega) fun q => Out.ret (decTokens st sender) _ q)

end VIR
