/-
  STATUS-vir row 15, the L-F4 test (predictions/PREDICTIONS-amend-7.md, pinned at vir 8c163d0 BEFORE this file existed).
  Program 2's shallow L-IDX chain restated with slice LENGTHS and OFFSETS as `Int` (mojave's model B).
  J2-J4 are unchanged; Router2.lean is not edited. Every rule is restated over `SliceZ`/`OutZ` under its program-2 name.
-/
import VIR.Core

namespace VIR.Z

/-- A zero-copy slice of `n` bytes, with `n` an `Int`. -/
structure SliceZ (n : Int) where
  buf  : ByteArray
  off  : Int
  fits : 0 ≤ off ∧ 0 ≤ n ∧ off + n ≤ buf.size

def SliceZ.adv {n : Int} (s : SliceZ n) (i : Int) (_h : 0 ≤ i ∧ i ≤ n) : SliceZ (n - i) :=
  ⟨s.buf, s.off + i, by have := s.fits; omega⟩

def SliceZ.take {m : Int} (s : SliceZ m) (k : Int) (_h : 0 ≤ k ∧ k ≤ m) : SliceZ k :=
  ⟨s.buf, s.off, by have := s.fits; omega⟩

def SliceZ.rd {n : Int} (s : SliceZ n) (j : Nat) : UInt32 :=
  let g := fun k => (s.buf.get! ((s.off + j + k).toNat)).toUInt32
  g 0 ||| (g 1 <<< 8) ||| (g 2 <<< 16) ||| (g 3 <<< 24)

inductive OutZ
  | ret  (st : State) (len : Int) (s : SliceZ len)
  | drop (c : Code)

def guard (c : Prop) [Decidable c] (ok : c → OutZ) (err : OutZ) : OutZ := if h : c then ok h else err
def readU32 {n : Int} (s : SliceZ n) (j : Nat) (k : UInt32 → OutZ) : OutZ := k (s.rd j)
def advance {n : Int} (s : SliceZ n) (i : Int) (h : 0 ≤ i ∧ i ≤ n) (k : SliceZ (n - i) → OutZ) : OutZ := k (s.adv i h)
def take {m : Int} (s : SliceZ m) (k : Int) (h : 0 ≤ k ∧ k ≤ m) (c : SliceZ k → OutZ) : OutZ := c (s.take k h)
def letLin {α : Type} (x : α) (k : α → OutZ) : OutZ := k x

variable (acl : Principal → TopicId → Bool)

/-! ## J2-J4 over Int -/
def parseHeader2 {n : Int} (b0 : SliceZ n)
    (k : SliceZ (n - 12) → Principal → TopicId → UInt32 → UInt32 → 24 ≤ n → OutZ) : OutZ :=
  guard (24 ≤ n) (fun h =>
    readU32 b0 0 fun magic =>
    guard (magic = MAGIC) (fun _ =>
      readU32 b0 4 fun sender => readU32 b0 8 fun topic =>
      readU32 b0 12 fun off => readU32 b0 16 fun len =>
      advance b0 12 (by omega) fun s => k s sender topic off len h)
      (.drop .unauthOrRate))
    (.drop .truncated)

def checkRateLimit (st : State) (p : Principal) (k : State → OutZ) : OutZ :=
  guard (hasTokens st p) (fun _ => letLin (decTokens st p) k) (.drop .unauthOrRate)

def verifyAcl (p : Principal) (t : TopicId) (k : OutZ) : OutZ :=
  guard (canAccess acl p t) (fun _ => k) (.drop .unauthOrRate)

def emitPayload2 {m : Int} (s : SliceZ m) (off : Int) (k : Nat) (st : State) : OutZ :=
  guard (24 ≤ off ∧ off + k ≤ m + 12) (fun h =>
    advance s (off - 12) (by omega) fun p => take p k (by omega) fun q => .ret st _ q)
    (.drop .badPayload)

def U2 {n : Int} (b0 : SliceZ n) (st : State) : OutZ :=
  parseHeader2 b0 fun s1 sender topic off len _ =>
    checkRateLimit st sender fun st' =>
      verifyAcl acl sender topic (emitPayload2 s1 (off.toNat : Int) len.toNat st')

def F2 {n : Int} (b0 : SliceZ n) (st : State) : OutZ :=
  guard (24 ≤ n) (fun _ =>
    readU32 b0 0 fun magic => readU32 b0 4 fun sender => readU32 b0 8 fun topic =>
    readU32 b0 12 fun off => readU32 b0 16 fun len =>
    guard (magic = MAGIC ∧ canAccess acl sender topic ∧ hasTokens st sender) (fun _ =>
      letLin (decTokens st sender) fun st' =>
      guard (24 ≤ (off.toNat : Int) ∧ (off.toNat : Int) + len.toNat ≤ n) (fun h2 =>
        advance b0 (off.toNat : Int) (by omega) fun p => take p len.toNat (by omega) fun q => .ret st' _ q)
        (.drop .badPayload))
      (.drop .unauthOrRate))
    (.drop .truncated)

/-! ## The rules (GIVEN and AUX), over Int -/
theorem beta_lin {α : Type} (x : α) (e : α → OutZ) : letLin x e = e x := rfl

theorem guard_merge (c₁ c₂ : Prop) [Decidable c₁] [Decidable c₂] (ok err : OutZ) :
    guard c₁ (fun _ => guard c₂ (fun _ => ok) err) err = guard (c₁ ∧ c₂) (fun _ => ok) err := by
  unfold guard; by_cases h₁ : c₁ <;> by_cases h₂ : c₂ <;> simp [h₁, h₂]

theorem SliceZ.heq_of {m₁ m₂ : Int} (s₁ : SliceZ m₁) (s₂ : SliceZ m₂) (hm : m₁ = m₂)
    (hb : s₁.buf = s₂.buf) (ho : s₁.off = s₂.off) : HEq s₁ s₂ := by
  subst hm
  cases s₁; cases s₂
  simp only at hb ho
  subst hb; subst ho
  rfl

theorem SliceZ.adv_adv_heq {n : Int} (s : SliceZ n) (i j : Int) (h₁ : 0 ≤ i ∧ i ≤ n) (h₂ : 0 ≤ j ∧ j ≤ n - i)
    (h₃ : 0 ≤ i + j ∧ i + j ≤ n) : HEq ((s.adv i h₁).adv j h₂) (s.adv (i + j) h₃) :=
  SliceZ.heq_of _ _ (by omega) rfl (by simp [SliceZ.adv, Int.add_assoc])

theorem SliceZ.congr_heq_dep {N : Int} (e : (m : Int) → m = N → SliceZ m → OutZ) {m₁ m₂ : Int}
    (h₁ : m₁ = N) (h₂ : m₂ = N) {x : SliceZ m₁} {y : SliceZ m₂} (hxy : HEq x y) : e m₁ h₁ x = e m₂ h₂ y := by
  subst h₁; subst h₂; cases hxy; rfl

theorem slice_fuse_dep {n : Int} (b : SliceZ n) (i j : Int) (h₁ : 0 ≤ i ∧ i ≤ n) (h₂ : 0 ≤ j ∧ j ≤ n - i)
    (h₃ : 0 ≤ i + j ∧ i + j ≤ n) (e : (m : Int) → m = n - (i + j) → SliceZ m → OutZ) :
    advance b i h₁ (fun s₁ => advance s₁ j h₂ (fun s₂ => e _ (by omega) s₂))
      = advance b (i + j) h₃ (fun s₂ => e _ rfl s₂) := by
  unfold advance
  exact SliceZ.congr_heq_dep e _ _ (SliceZ.adv_adv_heq b i j h₁ h₂ h₃)

theorem aux_read_past_guard {n : Int} (c : Prop) [Decidable c] (b : SliceZ n) (j : Nat)
    (k : UInt32 → OutZ) (e : OutZ) :
    guard c (fun _ => readU32 b j k) e = readU32 b j (fun v => guard c (fun _ => k v) e) := rfl

theorem aux_advance_past_guard {n : Int} (b : SliceZ n) (i : Int) (hi : 0 ≤ i ∧ i ≤ n) (c : Prop) [Decidable c]
    (k : SliceZ (n - i) → OutZ) (e : OutZ) :
    advance b i hi (fun s => guard c (fun _ => k s) e) = guard c (fun _ => advance b i hi k) e := rfl

theorem aux_guard_swap (a b : Prop) [Decidable a] [Decidable b] (k e : OutZ) :
    guard a (fun _ => guard b (fun _ => k) e) e = guard b (fun _ => guard a (fun _ => k) e) e := by
  unfold guard; by_cases ha : a <;> by_cases hb : b <;> simp [ha, hb]

theorem aux_advance_idx {n : Int} (b : SliceZ n) (i j : Int) (hij : i = j) (hi : 0 ≤ i ∧ i ≤ n) (hj : 0 ≤ j ∧ j ≤ n)
    (e : (m : Int) → m = n - j → SliceZ m → OutZ) :
    advance b i hi (fun s => e _ (by omega) s) = advance b j hj (fun s => e _ rfl s) := by
  subst hij; rfl

theorem aux_advance_past_dguard {n : Int} (b : SliceZ n) (i : Int) (hi : 0 ≤ i ∧ i ≤ n) (c : Prop) [Decidable c]
    (k : SliceZ (n - i) → c → OutZ) (e : OutZ) :
    advance b i hi (fun s => guard c (fun h => k s h) e) = guard c (fun h => advance b i hi (fun s => k s h)) e := rfl

theorem aux_guard_cond_eq (c d : Prop) [Decidable c] [Decidable d] (hcd : c ↔ d)
    (ok : d → OutZ) (e : OutZ) : guard c (fun h => ok (hcd.mp h)) e = guard d ok e := by
  unfold guard; by_cases h : d
  · simp [h, hcd.mpr h]
  · have : ¬c := fun hc => h (hcd.mp hc)
    simp [h, this]

/-- J5 over Int, the SCORED chain of the variant. The two side proofs amend-7 tests are written with the
    guard hypotheses CLEARED (`clear h2` / `clear h`): if they build, those rewrites are context-free. -/
theorem router2z_fusion {n : Int} (b0 : SliceZ n) (st : State) : U2 acl b0 st = F2 acl b0 st := by
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
  have hcd : (24 ≤ (off.toNat : Int) ∧ (off.toNat : Int) + len.toNat ≤ n - 12 + 12) ↔
      (24 ≤ (off.toNat : Int) ∧ (off.toNat : Int) + len.toNat ≤ n) := by
    clear h; constructor <;> intro ⟨a, b⟩ <;> exact ⟨a, by omega⟩
  rw [← aux_guard_cond_eq _ _ hcd]
  congr 1; funext h2
  rw [slice_fuse_dep b0 12 ((off.toNat : Int) - 12) (by omega) (by omega) (by omega)
      (fun m hm p => take p len.toNat (by omega) fun q => OutZ.ret (decTokens st sender) _ q)]
  exact aux_advance_idx b0 (12 + ((off.toNat : Int) - 12)) (off.toNat : Int) (by clear h2; omega) (by omega) (by omega)
      (fun m hm p => take p len.toNat (by omega) fun q => OutZ.ret (decTokens st sender) _ q)

end VIR.Z
