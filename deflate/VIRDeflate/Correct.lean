/-
OBJECT-DEFLATE under X1 (a): CORRECTNESS by simulation (STATUS-vir 293 (c); DECLARATIONS-DEFLATE.md S-18, declared before
this file existed).

S-18's shape: a FORWARD simulation plus DETERMINISM. This first piece is the outer argument, checked before any triple:
- `iterS` composes (`iterS_add`), DONE and REJECT are fixed points of `stepS` on a world (`stepS_fixed`);
- every store the iteration reaches from `initStore` is a world satisfying Safety's `Inv` (`reach_inv`);
- so two terminal stores reached from `initStore` are equal (`term_unique`);
- so `CorrectStmt` follows from the forward statement `FwdStmt` alone (`correct_of_fwd`).
-/
import VIRDeflate.Safety

namespace VIRDeflate.Step
open VIRL1 VIRL2

/-! ## The iteration composes -/

theorem iterS_add (p : Int) : ∀ (j k : Nat) (σ : Store), iterS p (j + k) σ = (iterS p j σ).bind (iterS p k)
  | 0, k, σ => by simp [iterS]
  | j + 1, k, σ => by
    rw [show j + 1 + k = (j + k) + 1 by omega]
    simp only [iterS]
    cases stepS p σ with
    | none => rfl
    | some σ1 => simp only [Option.bind_some]; exact iterS_add p j k σ1

/-- `Reach p σ σ'`: the iteration from σ reaches σ' (S-18). -/
def Reach (p : Int) (σ σ' : Store) : Prop := ∃ k, iterS p k σ = some σ'

theorem Reach.refl (p : Int) (σ : Store) : Reach p σ σ := ⟨0, rfl⟩

theorem Reach.trans {p : Int} {σ₁ σ₂ σ₃ : Store} (h₁ : Reach p σ₁ σ₂) (h₂ : Reach p σ₂ σ₃) : Reach p σ₁ σ₃ := by
  obtain ⟨j, hj⟩ := h₁
  obtain ⟨k, hk⟩ := h₂
  exact ⟨j + k, by rw [iterS_add, hj]; simpa using hk⟩

theorem Reach.step {p : Int} {σ σ' : Store} (h : stepS p σ = some σ') : Reach p σ σ' := ⟨1, by simp [iterS, h]⟩

/-! ## DONE and REJECT are fixed points of `stepS` -/

theorem stepS_fixed {σ : Store} {p : Int} {L : Nat} {f : Int → Int} (hw : World σ p L f) (hL : 0 < L)
    (ht : f cMODE = mDONE ∨ f cMODE = mREJECT) : stepS p σ = some σ := by
  obtain ⟨k₁, hk₁, h₁⟩ := step_dispatchN hw hL (f cMODE) rfl
  have hn : modes.lookup (f cMODE) = none := by
    rcases ht with h | h <;> rw [h] <;> rfl
  rw [hn] at h₁
  have hrun := run₂_of_stepsN h₁ rfl KSTEP (by simp only [KSTEP]; omega)
  unfold stepS
  rw [hrun]
  simp [capA]

theorem iterS_fixed {σ : Store} {p : Int} {L : Nat} {f : Int → Int} (hw : World σ p L f) (hL : 0 < L)
    (ht : f cMODE = mDONE ∨ f cMODE = mREJECT) : ∀ k, iterS p k σ = some σ
  | 0 => rfl
  | k + 1 => by simp [iterS, stepS_fixed hw hL ht, iterS_fixed hw hL ht k]

/-! ## Every reached store is a world with the invariant -/

theorem reach_inv (b : Array Nat) (om : Nat) (lit : Bool) (p : Int) (hb : ∀ x ∈ b, x < 256) :
    ∀ (k : Nat) (σ₀ σ : Store) (f₀ : Int → Int), World σ₀ p (L0 b.size om) f₀ → Inv b om lit f₀ →
      iterS p k σ₀ = some σ → ∃ f, World σ p (L0 b.size om) f ∧ Inv b om lit f := by
  have hL : 0 < L0 b.size om := by unfold L0; omega
  intro k
  induction k with
  | zero =>
    intro σ₀ σ f₀ hw hi h
    simp only [iterS, Option.some.injEq] at h
    exact ⟨f₀, h ▸ hw, hi⟩
  | succ k ih =>
    intro σ₀ σ f₀ hw hi h
    by_cases ht : f₀ cMODE = mDONE ∨ f₀ cMODE = mREJECT
    · simp only [iterS, stepS_fixed hw hL ht, Option.bind_some] at h
      exact ih σ₀ σ f₀ hw hi h
    · push Not at ht
      obtain ⟨σ', f', hst, hw', hi', _⟩ := stepSafe b om lit p σ₀ f₀ hb hw hi ht.1 ht.2
      simp only [iterS, hst, Option.bind_some] at h
      exact ih σ' σ f' hw' hi' h

theorem init_reach_inv (b : Array Nat) (om : Nat) (lit : Bool) (p : Int) (hb : ∀ x ∈ b, x < 256) (k : Nat) (σ : Store)
    (h : iterS p k (initStore b om lit p) = some σ) : ∃ f, World σ p (L0 b.size om) f ∧ Inv b om lit f :=
  reach_inv b om lit p hb k _ σ _ (initStore_world b om lit p) (Inv_init b om lit) h

def Terminal (p : Int) (σ : Store) : Prop := modeOf p σ = mDONE ∨ modeOf p σ = mREJECT

/-- **(Det)** Two terminal stores reached from `initStore` are the same store. -/
theorem term_unique (b : Array Nat) (om : Nat) (lit : Bool) (p : Int) (hb : ∀ x ∈ b, x < 256) {j k : Nat}
    {σ₁ σ₂ : Store} (h₁ : iterS p j (initStore b om lit p) = some σ₁) (t₁ : Terminal p σ₁)
    (h₂ : iterS p k (initStore b om lit p) = some σ₂) (t₂ : Terminal p σ₂) : σ₁ = σ₂ := by
  have hL : 0 < L0 b.size om := by unfold L0; omega
  -- the earlier one is a fixed point, so the later one is it
  have key : ∀ {j k : Nat} {σ₁ σ₂ : Store}, j ≤ k → iterS p j (initStore b om lit p) = some σ₁ → Terminal p σ₁ →
      iterS p k (initStore b om lit p) = some σ₂ → σ₁ = σ₂ := by
    intro j k σ₁ σ₂ hjk h₁ t₁ h₂
    obtain ⟨f₁, hw₁, _⟩ := init_reach_inv b om lit p hb j σ₁ h₁
    have ht : f₁ cMODE = mDONE ∨ f₁ cMODE = mREJECT := by
      unfold Terminal at t₁; rwa [modeOf_world hw₁ hL] at t₁
    rw [show k = j + (k - j) by omega, iterS_add, h₁, Option.bind_some, iterS_fixed hw₁ hL ht] at h₂
    exact Option.some.inj h₂
  rcases le_total j k with h | h
  · exact key h h₁ t₁ h₂
  · exact (key h h₂ t₂ h₁).symm

/-! ## TABLE: from `initStore` to HDR, with the bit table CORRECT (S-18 R, clause 2) -/

theorem World.agree {σ : Store} {p : Int} {L : Nat} {f g : Int → Int} (hf : World σ p L f) (hg : World σ p L g) {i : Int}
    (h0 : 0 ≤ i) (hL : i < L) : f i = g i :=
  Option.some.inj ((hf.cell i h0 hL).symm.trans (hg.cell i h0 hL))

/-- Every bit-table cell below c holds S1's bit (D4's `bitAt`, = `(v >>> i) &&& 1` by `bitAt_eq`). -/
def BitsUpTo (f : Int → Int) (c : Int) : Prop :=
  ∀ v i : Nat, v < 256 → i ≤ 7 → 8 * (v : Int) + i < c → f (BT + (8 * v + i)) = bitAt v i

/-- **TABLE, one step, exactly:** the cell written is S1's bit, cells 1–3 are untouched, and the counter advances or HDR is
reached at 2,048. -/
theorem table_one {b : Array Nat} {om : Nat} {lit : Bool} {σ : Store} {p : Int} {f : Int → Int}
    (hw : World σ p (L0 b.size om) f) (hi : Inv b om lit f) (hm : f cMODE = mTABLE) (hb : BitsUpTo f (8 * f cTB + f cTI)) :
    ∃ σ' f', stepS p σ = some σ' ∧ World σ' p (L0 b.size om) f' ∧ Inv b om lit f' ∧
      BitsUpTo f' (8 * f cTB + f cTI + 1) ∧ (∀ c : Int, (c = 1 ∨ c = 2 ∨ c = 3) → f' c = f c) ∧
      ((8 * f cTB + f cTI + 1 < 2048 ∧ f' cMODE = mTABLE ∧ 8 * f' cTB + f' cTI = 8 * f cTB + f cTI + 1) ∨
       (8 * f cTB + f cTI + 1 = 2048 ∧ f' cMODE = mHDR)) := by
  have hL : 2068 ≤ L0 b.size om := by unfold L0; omega
  obtain ⟨tb0, tb256, ti0, ti7⟩ := hi.1.tb_rng hm
  obtain ⟨σ', f', hS', hw', hi', _⟩ := safeI_table hw hi hm
  have hS := stepS_table hw hL (f cTB).toNat (f cTI).toNat hm (by omega) (by omega) (by omega) (by omega)
  simp only [show ((f cTB).toNat : Int) = f cTB by omega, show ((f cTI).toNat : Int) = f cTI by omega] at hS
  rw [hS] at hS'
  have hσ := (Option.some.inj hS').symm
  refine ⟨σ', f', hS.trans hS', hw', hi', ?_⟩
  set c0 := 8 * f cTB + f cTI with hc0
  set nb := tblNext (f cTB) (f cTI) with hnb
  have hnb1 : 8 * nb.1 + nb.2 = c0 + 1 := by simp only [hnb, hc0, tblNext]; split_ifs <;> simp <;> omega
  have hnbr : 0 ≤ nb.2 ∧ nb.2 ≤ 7 ∧ 0 ≤ nb.1 ∧ nb.1 ≤ 256 := by
    simp only [hnb, tblNext]; split_ifs <;> simp <;> omega
  set g := Function.update (Function.update (Function.update f (20 + c0) (bitAt (f cTB) (f cTI).toNat)) 18 nb.1) 19 nb.2
    with hg
  have hgw : World ⟨tblH σ.H p (f cTB) (f cTI), σ.R⟩ p (L0 b.size om) g := by
    unfold tblH
    exact ((hw.store (i := 20 + c0) (by omega) (by unfold L0; omega)).store (i := 18) (by norm_num)
      (by unfold L0; omega)).store (i := 19) (by norm_num) (by unfold L0; omega)
  have u : ∀ c : Int, c ≠ 20 + c0 → c ≠ 18 → c ≠ 19 → g c = f c := fun c a1 a2 a3 => by
    rw [hg, upd_eq _ _ a3, upd_eq _ _ a2, upd_eq _ _ a1]
  have eTB : g cTB = nb.1 := by simp [hg, cTB]
  have eTI : g cTI = nb.2 := by simp [hg, cTI]
  have eC : g (BT + c0) = bitAt (f cTB) (f cTI).toNat := by
    rw [hg, upd_eq _ _ (by unfold BT; omega), upd_eq _ _ (by unfold BT; omega)]; simp [BT]
  -- the world after the step, as an explicit function g' that agrees with f' on the region
  obtain ⟨g', hgw', hg'⟩ : ∃ g' : Int → Int, World σ' p (L0 b.size om) g' ∧
      (∀ c : Int, c ≠ 0 → g' c = g c) ∧ True := by
    by_cases h256 : nb.1 = 256
    · rw [if_pos h256] at hσ
      refine ⟨Function.update g 0 1, hσ ▸ hgw.store (i := 0) (by norm_num) (by unfold L0; omega), fun c hc => upd_eq _ _ hc, trivial⟩
    · rw [if_neg h256] at hσ
      exact ⟨g, hσ ▸ hgw, fun _ _ => rfl, trivial⟩
  have ag : ∀ c : Int, 0 ≤ c → c < L0 b.size om → f' c = g' c := fun c h0 h1 => hw'.agree hgw' h0 h1
  refine ⟨?_, ?_, ?_⟩
  · intro v i hv hi7 hlt
    rw [ag _ (by unfold BT; omega) (by unfold BT L0; omega), hg'.1 _ (by unfold BT; omega)]
    by_cases hc : 8 * (v : Int) + i = c0
    · have hv' : (v : Int) = f cTB := by omega
      have hi' : i = (f cTI).toNat := by omega
      rw [hc, eC, hv', hi']
    · rw [u _ (by unfold BT; omega) (by unfold BT; omega) (by unfold BT; omega)]
      exact hb v i hv hi7 (by omega)
  · intro c hc
    rw [ag _ (by omega) (by unfold L0; omega), hg'.1 _ (by omega), u _ (by omega) (by omega) (by omega)]
  · by_cases h256 : nb.1 = 256
    · right
      refine ⟨by omega, ?_⟩
      rw [if_pos h256] at hσ
      have := hw'.agree (hσ ▸ hgw.store (i := 0) (by norm_num) (by unfold L0; omega)) (i := 0) (by norm_num)
        (by unfold L0; omega)
      simp only [cMODE]; rw [this]; simp [mHDR]
    · left
      rw [if_neg h256] at hσ
      have a0 := hw'.agree (hσ ▸ hgw) (i := 0) (by norm_num) (by unfold L0; omega)
      have a18 := hw'.agree (hσ ▸ hgw) (i := 18) (by norm_num) (by unfold L0; omega)
      have a19 := hw'.agree (hσ ▸ hgw) (i := 19) (by norm_num) (by unfold L0; omega)
      refine ⟨by omega, ?_, ?_⟩
      · simp only [cMODE]; rw [a0, u _ (by omega) (by norm_num) (by norm_num)]; exact hm
      · simp only [cTB, cTI] at eTB eTI ⊢; rw [a18, a19, eTB, eTI]; omega

/-- **TABLE, to its end:** from any TABLE world with the bits below its counter correct, the iteration reaches HDR with all
2,048 bits correct and cells 1–3 untouched. -/
theorem table_run {b : Array Nat} {om : Nat} {lit : Bool} {p : Int} :
    ∀ (r : Nat) (σ : Store) (f : Int → Int), World σ p (L0 b.size om) f → Inv b om lit f → f cMODE = mTABLE →
      BitsUpTo f (8 * f cTB + f cTI) → 2048 - (8 * f cTB + f cTI) = r →
      ∃ σ' f', Reach p σ σ' ∧ World σ' p (L0 b.size om) f' ∧ Inv b om lit f' ∧ f' cMODE = mHDR ∧ BitsUpTo f' 2048 ∧
        (∀ c : Int, (c = 1 ∨ c = 2 ∨ c = 3) → f' c = f c) := by
  intro r
  induction r with
  | zero =>
    intro σ f hw hi hm _ hr
    obtain ⟨tb0, tb256, ti0, ti7⟩ := hi.1.tb_rng hm
    omega
  | succ r ih =>
    intro σ f hw hi hm hb hr
    obtain ⟨σ1, f1, hS, hw1, hi1, hb1, hc1, hk⟩ := table_one hw hi hm hb
    rcases hk with ⟨_, hm1, hc⟩ | ⟨hend, hm1⟩
    · obtain ⟨σ', f', hR, hw', hi', hm', hb', hc'⟩ :=
        ih σ1 f1 hw1 hi1 hm1 (by rw [hc]; exact hb1) (by omega)
      exact ⟨σ', f', (Reach.step hS).trans hR, hw', hi', hm', hb', fun c h => (hc' c h).trans (hc1 c h)⟩
    · exact ⟨σ1, f1, Reach.step hS, hw1, hi1, hm1, by rw [← hend]; exact hb1, hc1⟩

/-- **The start:** from `initStore`, HDR with every bit correct, the cursor at 0 and the output empty. -/
theorem init_to_hdr (b : Array Nat) (om : Nat) (lit : Bool) (p : Int) :
    ∃ σ f, Reach p (initStore b om lit p) σ ∧ World σ p (L0 b.size om) f ∧ Inv b om lit f ∧ f cMODE = mHDR ∧
      BitsUpTo f 2048 ∧ f cBY = 0 ∧ f cBI = 0 ∧ f cM = 0 := by
  have z : ∀ i : Int, 0 ≤ i → i < 15 → initCell b om lit i = 0 := fun i h0 h1 =>
    initCell_zero b om lit i h0 (by omega) (by omega) (by omega) (by omega) (by omega)
  have e0 : initCell b om lit cMODE = mTABLE := z _ (by decide) (by decide)
  have e18 : initCell b om lit cTB = 0 := initCell_zero b om lit _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have e19 : initCell b om lit cTI = 0 := initCell_zero b om lit _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨σ, f, hR, hw, hi, hm, hb, hc⟩ := table_run (2048 - (8 * initCell b om lit cTB + initCell b om lit cTI)).toNat
    (initStore b om lit p) (initCell b om lit) (initStore_world b om lit p) (Inv_init b om lit) e0
    (by intro v i _ _ h; rw [e18, e19] at h; omega) (by rw [e18, e19]; rfl)
  exact ⟨σ, f, hR, hw, hi, hm, hb, by show f 1 = 0; rw [hc 1 (by simp)]; exact z 1 (by norm_num) (by norm_num),
    by show f 2 = 0; rw [hc 2 (by simp)]; exact z 2 (by norm_num) (by norm_num), by show f 3 = 0; rw [hc 3 (by simp)]; exact z 3 (by norm_num) (by norm_num)⟩

/-! ## S-18's relation R, and the step helper -/

/-- **R (S-18):** Safety's invariant, the bit table correct, the bit position, and the output. -/
structure Rel (b : Array Nat) (om : Nat) (lit : Bool) (f : Int → Int) (st : St) : Prop where
  inv : Inv b om lit f
  bits : BitsUpTo f 2048
  pos : 8 * f cBY + f cBI = st.pos
  m : f cM = st.out.size
  out : ∀ i : Nat, i < st.out.size → f (IN + b.size + i) = st.out.getD i 0

/-- f' agrees with f on the region outside the cells S names. -/
def Keeps (L : Nat) (f f' : Int → Int) (S : Int → Prop) : Prop := ∀ c : Int, 0 ≤ c → c < L → ¬ S c → f' c = f c

theorem Keeps.trans {L : Nat} {f g h : Int → Int} {S T : Int → Prop} (h₁ : Keeps L f g S) (h₂ : Keeps L g h T)
    (hST : ∀ c, S c → T c) : Keeps L f h T := fun c h0 h1 hc => (h₂ c h0 h1 hc).trans (h₁ c h0 h1 (fun hs => hc (hST c hs)))

theorem Keeps.refl (L : Nat) (f : Int → Int) (S : Int → Prop) : Keeps L f f S := fun _ _ _ _ => rfl

/-- **A step to a store the mode lemma names exactly:** the next world carries Safety's invariant (by `stepSafe`) and agrees
on the region with the explicit contents g. -/
theorem step_to {b : Array Nat} {om : Nat} {lit : Bool} {σ σ' : Store} {p : Int} {f g : Int → Int} (hb : ∀ x ∈ b, x < 256)
    (hw : World σ p (L0 b.size om) f) (hi : Inv b om lit f) (hd : f cMODE ≠ mDONE) (hr : f cMODE ≠ mREJECT)
    (hS : stepS p σ = some σ') (hg : World σ' p (L0 b.size om) g) :
    ∃ f', World σ' p (L0 b.size om) f' ∧ Inv b om lit f' ∧ ∀ c : Int, 0 ≤ c → c < L0 b.size om → f' c = g c := by
  obtain ⟨σ'', f', hS', hw', hi', _⟩ := stepSafe b om lit p σ f hb hw hi hd hr
  rw [hS] at hS'
  cases hS'
  exact ⟨f', hw', hi', fun c h0 h1 => hw'.agree hg h0 h1⟩

/-! ## The bit reader: READ simulates `bitsGo` (S-18's first triple) -/

theorem go_bit (e : Env) (st : St) :
    go bit e st = if st.pos / 8 < e.inp.size then
      .ok ((e.inp.getD (st.pos / 8) 0 >>> (st.pos % 8)) &&& 1, { st with pos := st.pos + 1 }) else .error "truncated" := by
  unfold bit
  simp only [go_bind, go_read, go_get]
  split_ifs <;> rfl

theorem go_bitsGo_succ (j i acc : Nat) (e : Env) (st : St) :
    go (bitsGo (j + 1) i acc) e st = (match go bit e st with
      | .ok (x, s1) => go (bitsGo j (i + 1) (acc + x * 2 ^ i)) e s1
      | .error r => .error r) := by
  simp only [bitsGo]
  rw [go_bind]
  rcases go bit e st with r | ⟨x, s1⟩ <;> rfl

def rdSet (c : Int) : Prop := c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 2068 ∨ c = 2069 ∨ c = 2070

/-- **READ, one step, against S's `bit`.** -/
theorem read_one {b : Array Nat} {om : Nat} {lit : Bool} {p : Int} {σ : Store} {f : Int → Int} {st : St}
    (hb : ∀ x ∈ b, x < 256) (hw : World σ p (L0 b.size om) f) (hR : Rel b om lit f st) (hm : f cMODE = mREAD) :
    (∀ x s1, go bit ⟨b, om⟩ st = .ok (x, s1) →
      ∃ σ' f', stepS p σ = some σ' ∧ World σ' p (L0 b.size om) f' ∧ Rel b om lit f' s1 ∧ s1.out = st.out ∧
        f' cK = f cK - 1 ∧ f' cACC = f cACC + x * f cWT ∧ f' cWT = 2 * f cWT ∧ f' cRET = f cRET ∧
        f' cMODE = (if f cK - 1 = 0 then f cRET else mREAD) ∧ Keeps (L0 b.size om) f f' rdSet) ∧
    (∀ r, go bit ⟨b, om⟩ st = .error r →
      ∃ σ' f', stepS p σ = some σ' ∧ World σ' p (L0 b.size om) f' ∧ f' cMODE = mREJECT) := by
  have hL : 2080 + b.size ≤ L0 b.size om := by unfold L0; omega
  have hmem : (mREAD, readN) ∈ modes := by unfold modes; simp
  have hfit := modes_fit (mREAD, readN) hmem (by decide)
  have hi := hR.inv
  have hn := hi.1.n_eq
  have hbr := hi.1.by_rng
  have hir := hi.1.bi_rng
  have hpos := hR.pos
  have hd : f cMODE ≠ mDONE := by rw [hm]; decide
  have hrj : f cMODE ≠ mREJECT := by rw [hm]; decide
  rw [go_bit]
  by_cases hlt : f cBY < b.size
  · have hp8 : st.pos / 8 = (f cBY).toNat := by omega
    have hp8' : st.pos % 8 = (f cBI).toNat := by omega
    have hsz : st.pos / 8 < (⟨b, om⟩ : Env).inp.size := by simp only; omega
    rw [if_pos hsz]
    refine ⟨fun x s1 hx => ?_, fun r hr => by simp at hr⟩
    simp only [Except.ok.injEq, Prod.mk.injEq] at hx
    obtain ⟨hx, hs1⟩ := hx
    subst hs1
    obtain ⟨hv, hv8⟩ := hi.1.byte hb (f cBY).toNat (by omega)
    set v := b[(f cBY).toNat]'(by omega) with hvdef
    have hbiE : ((f cBI).toNat : Int) = f cBI := by omega
    have ht := hR.bits v (f cBI).toNat hv8 (by omega) (by omega)
    rw [hbiE] at ht
    have hxv : (x : Int) = bitAt v (f cBI).toNat := by
      rw [bitAt_eq v _ hv8 (by omega), ← hx, hp8, hp8']
      simp [Array.getD, show (f cBY).toNat < b.size by omega, hvdef]
    have hstep := readbit_step hw (f cBY).toNat (f cBI).toNat b.size v (f cK) (f cACC) (f cWT)
      (f cRET) (f (BT + (8 * (v : Int) + f cBI))) hL (by omega) (by omega) hn (by omega) (by omega)
      hv hv8 (by rw [hbiE]) rfl rfl rfl rfl
    have hS := stepS_of_mode hw (by unfold L0; omega) hm rfl hfit.1 hfit.2 hstep
    simp only [show ((f cBY).toNat : Int) = f cBY by omega, show ((f cBI).toNat : Int) = f cBI by omega] at hS
    set t := f (BT + (8 * (v : Int) + f cBI)) with htdef
    set f1 := Function.update (Function.update (Function.update (Function.update (Function.update f 1
      (tblNext (f cBY) (f cBI)).1) 2 (tblNext (f cBY) (f cBI)).2) 2069 (f cACC + t * f cWT)) 2070 (2 * f cWT)) 2068
      (f cK - 1) with hf1
    have hw1 : World ⟨rdH σ.H p (f cBY) (f cBI) (f cACC) (f cWT) (f cK) t, σ.R⟩ p (L0 b.size om) f1 := by
      unfold rdH
      exact ((((hw.store (i := 1) (by norm_num) (by unfold L0; omega)).store (i := 2) (by norm_num) (by unfold L0; omega)).store
        (i := 2069) (by norm_num) (by unfold L0; omega)).store (i := 2070) (by norm_num) (by unfold L0; omega)).store
        (i := 2068) (by norm_num) (by unfold L0; omega)
    set g := if f cK - 1 = 0 then Function.update f1 0 (f cRET) else f1 with hgdef
    obtain ⟨σ', hS', hwg⟩ : ∃ σ', stepS p σ = some σ' ∧ World σ' p (L0 b.size om) g := by
      by_cases hk : f cK - 1 = 0
      · rw [if_pos hk] at hS
        refine ⟨_, hS, ?_⟩
        rw [hgdef, if_pos hk]
        exact hw1.store (i := 0) (by norm_num) (by unfold L0; omega)
      · rw [if_neg hk] at hS
        exact ⟨_, hS, by rw [hgdef, if_neg hk]; exact hw1⟩
    obtain ⟨f', hw', hi', ag⟩ := step_to hb hw hi hd hrj hS' hwg
    have gf : ∀ c : Int, ¬ rdSet c → g c = f c := by
      intro c hc
      unfold rdSet at hc
      have h0 : c ≠ 0 := by omega
      have h1 : c ≠ 1 := by omega
      have h2 : c ≠ 2 := by omega
      have h3 : c ≠ 2068 := by omega
      have h4 : c ≠ 2069 := by omega
      have h5 : c ≠ 2070 := by omega
      have : f1 c = f c := by rw [hf1, upd_eq _ _ h3, upd_eq _ _ h5, upd_eq _ _ h4, upd_eq _ _ h2, upd_eq _ _ h1]
      rw [hgdef]; split_ifs
      · rw [upd_eq _ _ h0, this]
      · exact this
    have gne0 : ∀ c : Int, c ≠ 0 → g c = f1 c := by
      intro c hc; rw [hgdef]; split_ifs
      · exact upd_eq _ _ hc
      · rfl
    have keeps : Keeps (L0 b.size om) f f' rdSet := fun c h0 h1 hc => (ag c h0 h1).trans (gf c hc)
    have e1 : f' cBY = (tblNext (f cBY) (f cBI)).1 := by
      rw [ag _ (by decide) (by unfold cBY L0; omega), gne0 _ (by decide)]; simp [hf1, cBY]
    have e2 : f' cBI = (tblNext (f cBY) (f cBI)).2 := by
      rw [ag _ (by decide) (by unfold cBI L0; omega), gne0 _ (by decide)]; simp [hf1, cBI]
    have hnb1 : 8 * (tblNext (f cBY) (f cBI)).1 + (tblNext (f cBY) (f cBI)).2 = 8 * f cBY + f cBI + 1 := by
      simp only [tblNext]; split_ifs <;> simp <;> omega
    refine ⟨σ', f', hS', hw', ⟨hi', ?_, ?_, ?_, ?_⟩, rfl, ?_, ?_, ?_, ?_, ?_, keeps⟩
    · intro v' i' hv' hi7 hlt'
      rw [keeps _ (by unfold BT; omega) (by unfold BT L0; omega) (by unfold rdSet BT; omega)]
      exact hR.bits v' i' hv' hi7 hlt'
    · rw [e1, e2, hnb1, hpos]; push_cast; ring
    · rw [keeps _ (by decide) (by unfold cM L0; omega) (by unfold rdSet cM; omega)]; exact hR.m
    · intro i hi2
      change i < st.out.size at hi2
      have hm' := hi.1.m_rng
      have hm2 := hR.m
      have hc : IN + (b.size : Int) + i < L0 b.size om := by unfold IN L0; push_cast; omega
      rw [keeps _ (by unfold IN; omega) hc (by unfold rdSet IN; omega)]
      exact hR.out i hi2
    · rw [ag _ (by decide) (by unfold cK L0; omega), gne0 _ (by decide)]; simp [hf1, cK]
    · rw [ag _ (by decide) (by unfold cACC L0; omega), gne0 _ (by decide)]
      simp [hf1, cACC, Function.update_apply]
      exact Or.inl (ht.trans hxv.symm)
    · rw [ag _ (by decide) (by unfold cWT L0; omega), gne0 _ (by decide)]; simp [hf1, cWT, Function.update_apply]
    · rw [keeps _ (by decide) (by unfold cRET L0; omega) (by unfold rdSet cRET; omega)]
    · rw [ag _ (by decide) (by unfold cMODE L0; omega), hgdef]
      by_cases hk : f cK - 1 = 0
      · rw [if_pos hk, if_pos hk]; simp [cMODE]
      · rw [if_neg hk, if_neg hk, hf1]; simp [cMODE, Function.update_apply]; exact hm
  · have hsz : ¬ (st.pos / 8 < (⟨b, om⟩ : Env).inp.size) := by simp only; omega
    rw [if_neg hsz]
    refine ⟨fun x s1 hx => by simp at hx, fun r _ => ?_⟩
    have hstep := readbit_trunc hw (by unfold L0; omega) (f cBY) b.size rfl hn (by omega)
    have hS := stepS_of_mode hw (by unfold L0; omega) hm rfl hfit.1 hfit.2 hstep
    have hwr := (hw.store (i := 14) (v := 1) (by norm_num) (by unfold L0; omega)).store (i := 0) (v := 99) (by norm_num)
      (by unfold L0; omega)
    exact ⟨_, _, hS, hwr, by simp [cMODE, mREJECT]⟩

/-- **READ ↔ `bitsGo`.** From a READ world with k = j + 1, acc and wt = 2^i, related to st: if S's `bitsGo (j+1) i acc`
returns a from st', the iteration reaches the return mode with acc = a, related to st' (the output unchanged), touching only
the mode, the cursor and READ's own cells; if S rejects, the iteration reaches REJECT. -/
theorem read_sim {b : Array Nat} {om : Nat} {lit : Bool} {p : Int} (hb : ∀ x ∈ b, x < 256) :
    ∀ (j i acc : Nat) (σ : Store) (f : Int → Int) (st : St), World σ p (L0 b.size om) f → Rel b om lit f st →
      f cMODE = mREAD → f cK = j + 1 → f cACC = acc → f cWT = 2 ^ i →
      (∀ a st', go (bitsGo (j + 1) i acc) ⟨b, om⟩ st = .ok (a, st') →
        ∃ σ' f', Reach p σ σ' ∧ World σ' p (L0 b.size om) f' ∧ Rel b om lit f' st' ∧ f' cMODE = f cRET ∧
          f' cACC = a ∧ st'.out = st.out ∧ Keeps (L0 b.size om) f f' rdSet) ∧
      (∀ r, go (bitsGo (j + 1) i acc) ⟨b, om⟩ st = .error r →
        ∃ σ' f', Reach p σ σ' ∧ World σ' p (L0 b.size om) f' ∧ f' cMODE = mREJECT) := by
  have hL : 2080 + b.size ≤ L0 b.size om := by unfold L0; omega
  have hmem : (mREAD, readN) ∈ modes := by unfold modes; simp
  have hfit := modes_fit (mREAD, readN) hmem (by decide)
  intro j
  induction j with
  | zero =>
    intro i acc σ f st hw hR hm hk hacc hwt
    obtain ⟨hok, herr⟩ := read_one hb hw hR hm
    constructor
    · intro a st' h
      rw [go_bitsGo_succ] at h
      rcases hbit : go bit ⟨b, om⟩ st with r | ⟨x, s1⟩
      · rw [hbit] at h; simp at h
      · rw [hbit] at h
        simp only [bitsGo, go_pure, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨ha, hs⟩ := h
        subst hs
        obtain ⟨σ', f', hS, hw', hR', hout, _, hacc', _, _, hm', keeps⟩ := hok x s1 hbit
        refine ⟨σ', f', Reach.step hS, hw', hR', ?_, ?_, hout, keeps⟩
        · rw [hm', if_pos (by rw [hk]; simp)]
        · rw [hacc', hacc, hwt, ← ha]; push_cast; ring
    · intro r h
      rw [go_bitsGo_succ] at h
      rcases hbit : go bit ⟨b, om⟩ st with r' | ⟨x, s1⟩
      · obtain ⟨σ', f', hS, hw', hm'⟩ := herr r' hbit
        exact ⟨σ', f', Reach.step hS, hw', hm'⟩
      · rw [hbit] at h; simp [bitsGo, go_pure] at h
  | succ j ih =>
    intro i acc σ f st hw hR hm hk hacc hwt
    obtain ⟨hok, herr⟩ := read_one hb hw hR hm
    have next : ∀ x s1, go bit ⟨b, om⟩ st = .ok (x, s1) → ∃ σ1 f1, stepS p σ = some σ1 ∧
        World σ1 p (L0 b.size om) f1 ∧ Rel b om lit f1 s1 ∧ s1.out = st.out ∧ f1 cRET = f cRET ∧
        Keeps (L0 b.size om) f f1 rdSet ∧ f1 cMODE = mREAD ∧ f1 cK = (j : Int) + 1 ∧
        f1 cACC = ((acc + x * 2 ^ i : Nat) : Int) ∧ f1 cWT = 2 ^ (i + 1) := by
      intro x s1 hbit
      obtain ⟨σ1, f1, hS, hw1, hR1, hout1, hk1, hacc1, hwt1, hrt1, hm1, keeps1⟩ := hok x s1 hbit
      refine ⟨σ1, f1, hS, hw1, hR1, hout1, hrt1, keeps1, ?_, ?_, ?_, ?_⟩
      · rw [hm1, if_neg (by rw [hk]; push_cast; omega)]
      · rw [hk1, hk]; push_cast; ring
      · rw [hacc1, hacc, hwt]; push_cast; ring
      · rw [hwt1, hwt]; ring
    constructor
    · intro a st' h
      rw [go_bitsGo_succ] at h
      rcases hbit : go bit ⟨b, om⟩ st with r | ⟨x, s1⟩
      · rw [hbit] at h; simp at h
      · rw [hbit] at h
        obtain ⟨σ1, f1, hS, hw1, hR1, hout1, hrt1, keeps1, hm1, hk1, hacc1, hwt1⟩ := next x s1 hbit
        obtain ⟨σ', f', hR', hw', hR'', hmo, hacco, hout', keeps'⟩ :=
          (ih (i + 1) (acc + x * 2 ^ i) σ1 f1 s1 hw1 hR1 hm1 hk1 hacc1 hwt1).1 a st' h
        exact ⟨σ', f', (Reach.step hS).trans hR', hw', hR'', by rw [hmo, hrt1], hacco, by rw [hout', hout1],
          keeps1.trans keeps' (fun c h => h)⟩
    · intro r h
      rw [go_bitsGo_succ] at h
      rcases hbit : go bit ⟨b, om⟩ st with r' | ⟨x, s1⟩
      · obtain ⟨σ', f', hS, hw', hm'⟩ := herr r' hbit
        exact ⟨σ', f', Reach.step hS, hw', hm'⟩
      · rw [hbit] at h
        obtain ⟨σ1, f1, hS, hw1, hR1, _, _, _, hm1, hk1, hacc1, hwt1⟩ := next x s1 hbit
        obtain ⟨σ', f', hR', hw', hm'⟩ := (ih (i + 1) (acc + x * 2 ^ i) σ1 f1 s1 hw1 hR1 hm1 hk1 hacc1 hwt1).2 r h
        exact ⟨σ', f', (Reach.step hS).trans hR', hw', hm'⟩

/-! ## The triple toolkit (S-18): `Sim A pre post` -/

/-- Control cells: R observes none of them (the mode, cells 4–19, cursor-2, and everything above the output). -/
def ctl (n om : Nat) (c : Int) : Prop := c = 0 ∨ (4 ≤ c ∧ c < 20) ∨ (2068 ≤ c ∧ c < 2080) ∨ IN + n + om ≤ c

/-- R survives any change to control cells alone. -/
theorem Rel.of_keeps {b : Array Nat} {om : Nat} {lit : Bool} {f f' : Int → Int} {st : St} {S : Int → Prop}
    (hR : Rel b om lit f st) (hi' : Inv b om lit f') (hk : Keeps (L0 b.size om) f f' S)
    (hS : ∀ c, S c → ctl b.size om c) : Rel b om lit f' st where
  inv := hi'
  bits v i hv hi7 hlt := by
    rw [hk _ (by unfold BT; omega) (by unfold BT L0; omega) (fun h => by have := hS _ h; unfold ctl BT IN at *; omega)]
    exact hR.bits v i hv hi7 hlt
  pos := by
    rw [hk _ (by decide) (by unfold cBY L0; omega) (fun h => by have := hS _ h; unfold ctl cBY IN at *; omega),
      hk _ (by decide) (by unfold cBI L0; omega) (fun h => by have := hS _ h; unfold ctl cBI IN at *; omega)]
    exact hR.pos
  m := by
    rw [hk _ (by decide) (by unfold cM L0; omega) (fun h => by have := hS _ h; unfold ctl cM IN at *; omega)]
    exact hR.m
  out i hi2 := by
    have hm' := hR.inv.1.m_rng
    have hm2 := hR.m
    have hc : IN + (b.size : Int) + i < L0 b.size om := by unfold IN L0; push_cast; omega
    rw [hk _ (by unfold IN; omega) hc (fun h => by have := hS _ h; unfold ctl IN at *; omega)]
    exact hR.out i hi2

/-- **The triple** (S-18): from any world satisfying pre, S's ok result is reached with post, and S's error with REJECT. -/
def Sim (b : Array Nat) (om : Nat) (p : Int) {α : Type} (A : M α) (pre : (Int → Int) → St → Prop)
    (post : α → (Int → Int) → St → Prop) : Prop :=
  ∀ σ f st, World σ p (L0 b.size om) f → pre f st →
    (∀ a st', go A ⟨b, om⟩ st = .ok (a, st') →
      ∃ σ' f', Reach p σ σ' ∧ World σ' p (L0 b.size om) f' ∧ post a f' st') ∧
    (∀ r, go A ⟨b, om⟩ st = .error r → ∃ σ' f', Reach p σ σ' ∧ World σ' p (L0 b.size om) f' ∧ f' cMODE = mREJECT)

section Toolkit
variable {b : Array Nat} {om : Nat} {p : Int} {α β : Type}

theorem Sim.bind {A : M α} {k : α → M β} {pre : (Int → Int) → St → Prop} {mid : α → (Int → Int) → St → Prop}
    {post : β → (Int → Int) → St → Prop} (h1 : Sim b om p A pre mid) (h2 : ∀ a, Sim b om p (k a) (mid a) post) :
    Sim b om p (A >>= k) pre post := by
  intro σ f st hw hp
  obtain ⟨hok, herr⟩ := h1 σ f st hw hp
  constructor
  · intro c st' h
    rw [go_bind] at h
    rcases hA : go A ⟨b, om⟩ st with r | ⟨a, s1⟩
    · rw [hA] at h; simp at h
    · rw [hA] at h
      obtain ⟨σ1, f1, hR1, hw1, hm1⟩ := hok a s1 hA
      obtain ⟨σ', f', hR', hw', hp'⟩ := (h2 a σ1 f1 s1 hw1 hm1).1 c st' h
      exact ⟨σ', f', hR1.trans hR', hw', hp'⟩
  · intro r h
    rw [go_bind] at h
    rcases hA : go A ⟨b, om⟩ st with r' | ⟨a, s1⟩
    · exact herr r' hA
    · rw [hA] at h
      obtain ⟨σ1, f1, hR1, hw1, hm1⟩ := hok a s1 hA
      obtain ⟨σ', f', hR', hw', hp'⟩ := (h2 a σ1 f1 s1 hw1 hm1).2 r h
      exact ⟨σ', f', hR1.trans hR', hw', hp'⟩

theorem Sim.mono {A : M α} {pre pre' : (Int → Int) → St → Prop} {post post' : α → (Int → Int) → St → Prop}
    (h : Sim b om p A pre post) (hpre : ∀ f st, pre' f st → pre f st) (hpost : ∀ a f st, post a f st → post' a f st) :
    Sim b om p A pre' post' := by
  intro σ f st hw hp
  obtain ⟨hok, herr⟩ := h σ f st hw (hpre f st hp)
  exact ⟨fun a st' h' => (hok a st' h').imp fun σ' ⟨f', hR, hw', hq⟩ => ⟨f', hR, hw', hpost _ _ _ hq⟩, herr⟩

/-- A machine step before S does anything. -/
theorem Sim.step {A : M α} {pre pre' : (Int → Int) → St → Prop} {post : α → (Int → Int) → St → Prop}
    (hs : ∀ σ f st, World σ p (L0 b.size om) f → pre f st →
      ∃ σ1 f1, stepS p σ = some σ1 ∧ World σ1 p (L0 b.size om) f1 ∧ pre' f1 st)
    (h : Sim b om p A pre' post) : Sim b om p A pre post := by
  intro σ f st hw hp
  obtain ⟨σ1, f1, hS, hw1, hp1⟩ := hs σ f st hw hp
  obtain ⟨hok, herr⟩ := h σ1 f1 st hw1 hp1
  exact ⟨fun a st' h' => (hok a st' h').imp fun σ' ⟨f', hR, hw', hq⟩ => ⟨f', (Reach.step hS).trans hR, hw', hq⟩,
    fun r h' => (herr r h').imp fun σ' ⟨f', hR, hw', hq⟩ => ⟨f', (Reach.step hS).trans hR, hw', hq⟩⟩

theorem Sim.pure {a : α} {pre : (Int → Int) → St → Prop} {post : α → (Int → Int) → St → Prop}
    (h : ∀ f st, pre f st → post a f st) : Sim b om p (Pure.pure a : M α) pre post := by
  intro σ f st hw hp
  refine ⟨fun a' st' h' => ?_, fun r h' => by rw [go_pure] at h'; simp at h'⟩
  rw [go_pure] at h'
  simp only [Except.ok.injEq, Prod.mk.injEq] at h'
  obtain ⟨rfl, rfl⟩ := h'
  exact ⟨σ, f, Reach.refl p σ, hw, h f st hp⟩

/-- S rejects, and the machine reaches REJECT. -/
theorem Sim.reject {r : String} {pre : (Int → Int) → St → Prop} {post : α → (Int → Int) → St → Prop}
    (h : ∀ σ f st, World σ p (L0 b.size om) f → pre f st →
      ∃ σ' f', Reach p σ σ' ∧ World σ' p (L0 b.size om) f' ∧ f' cMODE = mREJECT) :
    Sim b om p (VIRDeflate.reject r : M α) pre post := by
  intro σ f st hw hp
  exact ⟨fun a st' h' => by rw [go_reject] at h'; simp at h', fun _ _ => h σ f st hw hp⟩

theorem Sim.reject_bind {r : String} {k : α → M β} {pre : (Int → Int) → St → Prop} {post : β → (Int → Int) → St → Prop}
    (h : ∀ σ f st, World σ p (L0 b.size om) f → pre f st →
      ∃ σ' f', Reach p σ σ' ∧ World σ' p (L0 b.size om) f' ∧ f' cMODE = mREJECT) :
    Sim b om p (VIRDeflate.reject r >>= k) pre post := Sim.bind (mid := fun _ _ _ => False) (Sim.reject h)
  (fun _ σ f st _ hp => absurd hp id)

theorem Sim.get {k : St → M α} {pre : (Int → Int) → St → Prop} {post : α → (Int → Int) → St → Prop}
    (h : ∀ s, Sim b om p (k s) (fun f st => pre f st ∧ st = s) post) : Sim b om p (MonadState.get >>= k) pre post := by
  intro σ f st hw hp
  have := h st σ f st hw ⟨hp, rfl⟩
  simp only [go_bind, go_get]
  exact this

theorem Sim.read {k : Env → M α} {pre : (Int → Int) → St → Prop} {post : α → (Int → Int) → St → Prop}
    (h : Sim b om p (k ⟨b, om⟩) pre post) : Sim b om p (MonadReader.read >>= k) pre post := by
  intro σ f st hw hp
  have := h σ f st hw hp
  simp only [go_bind, go_read]
  exact this

theorem Sim.ite {c : Prop} [Decidable c] {t e : M α} {pre : (Int → Int) → St → Prop} {post : α → (Int → Int) → St → Prop}
    (ht : c → Sim b om p t pre post) (he : ¬ c → Sim b om p e pre post) : Sim b om p (if c then t else e) pre post := by
  split
  · exact ht ‹_›
  · exact he ‹_›

end Toolkit

/-- **`bits K` from a READ world** (K ≥ 1, acc 0, wt 1): the corollary of `read_sim` in the triple form, with the start
world f₀ and state st₀ as ghosts. -/
theorem bits_sim {b : Array Nat} {om : Nat} {lit : Bool} {p : Int} (hb : ∀ x ∈ b, x < 256) (K : Nat) (f₀ : Int → Int)
    (st₀ : St) :
    Sim b om p (bits (K + 1))
      (fun f st => f = f₀ ∧ st = st₀ ∧ Rel b om lit f st ∧ f cMODE = mREAD ∧ f cK = K + 1 ∧ f cACC = 0 ∧ f cWT = 1)
      (fun a f' st' => Rel b om lit f' st' ∧ f' cMODE = f₀ cRET ∧ f' cACC = a ∧ st'.out = st₀.out ∧
        Keeps (L0 b.size om) f₀ f' rdSet ∧ st₀.pos < st'.pos) := by
  rintro σ f st hw ⟨rfl, rfl, hR, hm, hk, hacc, hwt⟩
  have := read_sim (lit := lit) hb K 0 0 σ f st hw hR hm hk (by simpa using hacc) (by simpa using hwt)
  refine ⟨fun a st' h => ?_, this.2⟩
  obtain ⟨σ', f', hR', hw', hR'', hm', ha, ho, hkp⟩ := this.1 a st' h
  exact ⟨σ', f', hR', hw', hR'', hm', ha, ho, hkp, ((adv_bits K) ⟨b, om⟩ st a st' h).1⟩

/-! ## CorrectStmt from the forward statement -/

/-- **The forward statement (S-18 (F-ok), (F-err)):** what the spec does, the iteration reaches. -/
def FwdStmt : Prop :=
  ∀ (b : Array Nat) (om : Nat) (lit : Bool) (p : Int), (∀ x ∈ b, x < 256) →
    (∀ o, run lit b om = .ok o →
      ∃ k σ', iterS p k (initStore b om lit p) = some σ' ∧ modeOf p σ' = mDONE ∧ outOf p b.size σ' = o) ∧
    (∀ r, run lit b om = .error r →
      ∃ k σ', iterS p k (initStore b om lit p) = some σ' ∧ modeOf p σ' = mREJECT)

theorem mDONE_ne_mREJECT : mDONE ≠ mREJECT := by decide

/-- **CORRECTNESS from the forward simulation and determinism (S-18).** -/
theorem correct_of_fwd (hf : FwdStmt) : CorrectStmt := by
  intro b om lit p hb
  obtain ⟨hok, herr⟩ := hf b om lit p hb
  constructor
  · intro o
    constructor
    · rintro ⟨k, σ', hit, hm, ho⟩
      cases hr : run lit b om with
      | ok o' =>
        obtain ⟨k', σ'', hit', hm', ho'⟩ := hok o' hr
        have := term_unique b om lit p hb hit (Or.inl hm) hit' (Or.inl hm')
        subst this
        rw [← ho, ← ho']
      | error r =>
        obtain ⟨k', σ'', hit', hm'⟩ := herr r hr
        have := term_unique b om lit p hb hit (Or.inl hm) hit' (Or.inr hm')
        subst this
        exact absurd (hm.symm.trans hm') mDONE_ne_mREJECT
    · intro hr
      exact (hok o hr).imp fun k ⟨σ', hit, hm, ho⟩ => ⟨σ', hit, hm, ho⟩
  · constructor
    · rintro ⟨k, σ', hit, hm⟩
      cases hr : run lit b om with
      | ok o' =>
        obtain ⟨k', σ'', hit', hm', _⟩ := hok o' hr
        have := term_unique b om lit p hb hit (Or.inr hm) hit' (Or.inl hm')
        subst this
        exact absurd (hm'.symm.trans hm) mDONE_ne_mREJECT
      | error r => exact ⟨r, rfl⟩
    · rintro ⟨r, hr⟩
      exact herr r hr

end VIRDeflate.Step
