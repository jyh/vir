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

/-! ## The block header: HDR, HDRB, HDRD -/

theorem reqF_keeps (L : Nat) (f : Int → Int) (k rt : Int) :
    Keeps L f (reqF f k rt) (fun c => c = 0 ∨ (2068 ≤ c ∧ c ≤ 2071)) :=
  fun c _ _ hc => reqF_eq f k rt c (by omega)

theorem reqF_vals (f : Int → Int) (k rt : Int) :
    reqF f k rt cMODE = mREAD ∧ reqF f k rt cK = k ∧ reqF f k rt cACC = 0 ∧ reqF f k rt cWT = 1 ∧ reqF f k rt cRET = rt := by
  simp [reqF, Function.update_apply, cMODE, cK, cACC, cWT, cRET, mREAD]

/-- A step whose next contents are known exactly, on a related world: R carries over when only control cells changed. -/
theorem next_rel {b : Array Nat} {om : Nat} {lit : Bool} {σ σ' : Store} {p : Int} {f g : Int → Int} {st : St}
    {S : Int → Prop} (hb : ∀ x ∈ b, x < 256) (hw : World σ p (L0 b.size om) f) (hR : Rel b om lit f st)
    (hd : f cMODE ≠ mDONE) (hr : f cMODE ≠ mREJECT) (hS : stepS p σ = some σ') (hg : World σ' p (L0 b.size om) g)
    (hk : Keeps (L0 b.size om) f g S) (hSc : ∀ c, S c → ctl b.size om c) :
    ∃ f', World σ' p (L0 b.size om) f' ∧ Rel b om lit f' st ∧ Keeps (L0 b.size om) f f' S ∧
      ∀ c : Int, 0 ≤ c → c < L0 b.size om → f' c = g c := by
  obtain ⟨f', hw', hi', ag⟩ := step_to hb hw hR.inv hd hr hS hg
  have hk' : Keeps (L0 b.size om) f f' S := fun c h0 h1 hc => (ag c h0 h1).trans (hk c h0 h1 hc)
  exact ⟨f', hw', hR.of_keeps hi' hk' hSc, hk', ag⟩

theorem hdr_next {b : Array Nat} {om : Nat} {lit : Bool} {σ : Store} {p : Int} {f : Int → Int} {st : St}
    (hb : ∀ x ∈ b, x < 256) (hw : World σ p (L0 b.size om) f) (hR : Rel b om lit f st) (hm : f cMODE = mHDR) :
    ∃ σ1 f1, stepS p σ = some σ1 ∧ World σ1 p (L0 b.size om) f1 ∧ Rel b om lit f1 st ∧ f1 cMODE = mREAD ∧ f1 cK = 1 ∧
      f1 cACC = 0 ∧ f1 cWT = 1 ∧ f1 cRET = mHDRB ∧ f1 cBF = f cBF := by
  have hL : 2080 ≤ L0 b.size om := by unfold L0; omega
  obtain ⟨hS, hg, -, -⟩ := safe_hdr' hw hL hR.inv.1 hm
  obtain ⟨f1, hw1, hR1, hk1, ag⟩ := next_rel hb hw hR (by rw [hm]; decide) (by rw [hm]; decide) hS hg
    (reqF_keeps _ f 1 3) (fun c hc => by unfold ctl IN; omega)
  obtain ⟨v1, v2, v3, v4, v5⟩ := reqF_vals f 1 3
  refine ⟨_, f1, hS, hw1, hR1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [ag _ (by decide) (by unfold cMODE; omega)]; exact v1
  · rw [ag _ (by decide) (by unfold cK; omega)]; exact v2
  · rw [ag _ (by decide) (by unfold cACC; omega)]; exact v3
  · rw [ag _ (by decide) (by unfold cWT; omega)]; exact v4
  · rw [ag _ (by decide) (by unfold cRET; omega)]; exact v5
  · exact hk1 _ (by decide) (by unfold cBF; omega) (by unfold cBF; omega)

theorem hdrb_next {b : Array Nat} {om : Nat} {lit : Bool} {σ : Store} {p : Int} {f : Int → Int} {st : St}
    (hb : ∀ x ∈ b, x < 256) (hw : World σ p (L0 b.size om) f) (hR : Rel b om lit f st) (hm : f cMODE = mHDRB) :
    ∃ σ1 f1, stepS p σ = some σ1 ∧ World σ1 p (L0 b.size om) f1 ∧ Rel b om lit f1 st ∧ f1 cMODE = mREAD ∧ f1 cK = 2 ∧
      f1 cACC = 0 ∧ f1 cWT = 1 ∧ f1 cRET = mHDRD ∧ f1 cBF = f cACC := by
  have hL : 2080 ≤ L0 b.size om := by unfold L0; omega
  obtain ⟨hS, hg, -, -⟩ := safe_hdrb hw hL hR.inv.1 hm
  have hk : Keeps (L0 b.size om) f (reqF (Function.update f 4 (f cACC)) 2 4)
      (fun c => c = 0 ∨ c = 4 ∨ (2068 ≤ c ∧ c ≤ 2071)) := fun c _ _ hc => by
    rw [reqF_eq _ 2 4 c (by omega), upd_eq _ _ (by omega)]
  obtain ⟨f1, hw1, hR1, hk1, ag⟩ := next_rel hb hw hR (by rw [hm]; decide) (by rw [hm]; decide) hS hg hk
    (fun c hc => by unfold ctl IN; omega)
  obtain ⟨v1, v2, v3, v4, v5⟩ := reqF_vals (Function.update f 4 (f cACC)) 2 4
  refine ⟨_, f1, hS, hw1, hR1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [ag _ (by decide) (by unfold cMODE; omega)]; exact v1
  · rw [ag _ (by decide) (by unfold cK; omega)]; exact v2
  · rw [ag _ (by decide) (by unfold cACC; omega)]; exact v3
  · rw [ag _ (by decide) (by unfold cWT; omega)]; exact v4
  · rw [ag _ (by decide) (by unfold cRET; omega)]; exact v5
  · rw [ag _ (by decide) (by unfold cBF; omega), reqF_eq _ 2 4 _ (by unfold cBF; omega)]; simp [cBF]

/-- **HDRD:** by BTYPE (acc): SHDR, FIXLENS with fill 0, DHDR, or REJECT; BFINAL's cell is kept. -/
theorem hdrd_next {b : Array Nat} {om : Nat} {lit : Bool} {σ : Store} {p : Int} {f : Int → Int} {st : St}
    (hb : ∀ x ∈ b, x < 256) (hw : World σ p (L0 b.size om) f) (hR : Rel b om lit f st) (hm : f cMODE = mHDRD) :
    ∃ σ1 f1, stepS p σ = some σ1 ∧ World σ1 p (L0 b.size om) f1 ∧ Rel b om lit f1 st ∧ f1 cBF = f cBF ∧
      (f cACC = 0 → f1 cMODE = mSHDR) ∧ (f cACC = 1 → f1 cMODE = mFIXLENS ∧ f1 cFILL = 0) ∧
      (f cACC = 2 → f1 cMODE = mDHDR) ∧ (f cACC ≠ 0 → f cACC ≠ 1 → f cACC ≠ 2 → f1 cMODE = mREJECT) := by
  have hL : 2080 ≤ L0 b.size om := by unfold L0; omega
  have hmem : (mHDRD, hdrdN) ∈ modes := by unfold modes; simp
  have hfit := modes_fit (mHDRD, hdrdN) hmem (by decide)
  have hS := stepS_of_mode hw (by omega) hm rfl hfit.1 hfit.2 (hdrd_step hw hL (f cACC) rfl)
  set a := f cACC with ha
  set g : Int → Int := if a = 0 then Function.update f 0 5 else if a = 1 then Function.update (Function.update f 10 0) 0 6
    else if a = 2 then Function.update f 0 7 else Function.update (Function.update f 14 2) 0 99 with hgdef
  have hg : World ⟨hdrdH σ.H p a, σ.R⟩ p (L0 b.size om) g := by
    simp only [hdrdH, hgdef]
    split_ifs
    · exact hw.store (i := 0) (by norm_num) (by omega)
    · exact (hw.store (i := 10) (by norm_num) (by omega)).store (i := 0) (by norm_num) (by omega)
    · exact hw.store (i := 0) (by norm_num) (by omega)
    · exact (hw.store (i := 14) (by norm_num) (by omega)).store (i := 0) (by norm_num) (by omega)
  have hk : Keeps (L0 b.size om) f g (fun c => c = 0 ∨ c = 10 ∨ c = 14) := fun c _ _ hc => by
    simp only [hgdef]; split_ifs <;> simp [Function.update_apply, show c ≠ 0 by omega, show c ≠ 10 by omega,
      show c ≠ 14 by omega]
  obtain ⟨f1, hw1, hR1, hk1, ag⟩ := next_rel hb hw hR (by rw [hm]; decide) (by rw [hm]; decide) hS hg hk
    (fun c hc => by unfold ctl IN; omega)
  have a0 := ag 0 (by norm_num) (by omega)
  have a10 := ag 10 (by norm_num) (by omega)
  refine ⟨_, f1, hS, hw1, hR1, hk1 _ (by decide) (by unfold cBF; omega) (by unfold cBF; omega), fun h => ?_, fun h => ?_,
    fun h => ?_, fun h0 h1 h2 => ?_⟩
  · simp only [cMODE]; rw [a0, hgdef, if_pos h]; simp [mSHDR]
  · simp only [cMODE, cFILL]; rw [a0, a10, hgdef, if_neg (by omega), if_pos h]; simp [mFIXLENS]
  · simp only [cMODE]; rw [a0, hgdef, if_neg (by omega), if_neg (by omega), if_pos h]; simp [mDHDR]
  · simp only [cMODE]; rw [a0, hgdef, if_neg h0, if_neg h1, if_neg h2]; simp [mREJECT]

/-! ## The block loop (S2) against the three block bodies -/

/-- `bits K` from a READ world, with a frame predicate carried across: Q holds of the start, and Q' of the end, whenever the
end touched only READ's cells, kept the output and moved the position forward from inside the input. -/
theorem bits_sim' {b : Array Nat} {om : Nat} {lit : Bool} {p : Int} (hb : ∀ x ∈ b, x < 256) (K : Nat) (rt : Int)
    (Q Q' : (Int → Int) → St → Prop)
    (hQ : ∀ f st f' st', Q f st → Keeps (L0 b.size om) f f' rdSet → st'.out = st.out → st.pos < st'.pos →
      st.pos < 8 * b.size → Q' f' st') :
    Sim b om p (bits (K + 1))
      (fun f st => (Rel b om lit f st ∧ f cMODE = mREAD ∧ f cK = K + 1 ∧ f cACC = 0 ∧ f cWT = 1 ∧ f cRET = rt) ∧ Q f st)
      (fun a f' st' => Rel b om lit f' st' ∧ f' cMODE = rt ∧ f' cACC = a ∧ Q' f' st') := by
  rintro σ f st hw ⟨⟨hR, hm, hk, hacc, hwt, hrt⟩, hq⟩
  have := read_sim (lit := lit) hb K 0 0 σ f st hw hR hm hk (by simpa using hacc) (by simpa using hwt)
  refine ⟨fun a st' h => ?_, this.2⟩
  obtain ⟨σ', f', hR', hw', hR'', hm', ha, ho, hkp⟩ := this.1 a st' h
  obtain ⟨hlt, hin⟩ := (adv_bits K) ⟨b, om⟩ st a st' h
  exact ⟨σ', f', hR', hw', hR'', by rw [hm', hrt], ha, hQ f st f' st' hq hkp ho hlt hin⟩

/-- A triple for a spec action that never moves the position back carries the unread-bits bound. -/
theorem Sim.measure {b : Array Nat} {om : Nat} {p : Int} {α : Type} {A : M α} {pre : (Int → Int) → St → Prop}
    {post : α → (Int → Int) → St → Prop} (h : Sim b om p A pre post) (hA : Mono A) (F : Nat) :
    Sim b om p A (fun f st => pre f st ∧ 8 * b.size - st.pos < F) (fun a f st => post a f st ∧ 8 * b.size - st.pos < F) := by
  rintro σ f st hw ⟨hp, hF⟩
  obtain ⟨hok, herr⟩ := h σ f st hw hp
  refine ⟨fun a st' h' => ?_, herr⟩
  obtain ⟨σ', f', hR, hw', hq⟩ := hok a st' h'
  have := hA ⟨b, om⟩ st a st' h'
  exact ⟨σ', f', hR, hw', hq, by omega⟩

/-- The mode a block body ends in: DONE after the final block, else HDR. -/
def endMode (bf : Int) : Int := if bf = 1 then mDONE else mHDR

/-- S5's fixed block, as `blocks` writes it. -/
def fixedBody (lit : Bool) : M Unit := fixedCodes lit >>= fun LD => huff LD.1 LD.2

theorem mono_fixedBody (lit : Bool) : Mono (fixedBody lit) :=
  mono_bind (mono_fixedCodes lit) fun LD => mono_huff LD.1 LD.2

/-- What each block body owes (S-18's table, rows `stored`, `dynamic` and the fixed `huff`). -/
def BodySim (b : Array Nat) (om : Nat) (lit : Bool) (p : Int) (A : M Unit) (md : Int) (extra : (Int → Int) → Prop) : Prop :=
  ∀ bf : Int, Sim b om p A (fun f st => Rel b om lit f st ∧ f cMODE = md ∧ f cBF = bf ∧ extra f)
    (fun _ f st => Rel b om lit f st ∧ f cMODE = endMode bf)

/-- **S2's block loop is simulated, given the three bodies.** -/
theorem blocks_sim {b : Array Nat} {om : Nat} {lit : Bool} {p : Int} (hb : ∀ x ∈ b, x < 256)
    (HS : BodySim b om lit p stored mSHDR (fun _ => True))
    (HF : BodySim b om lit p (fixedBody lit) mFIXLENS (fun f => f cFILL = 0))
    (HD : BodySim b om lit p dynamic mDHDR (fun _ => True)) :
    ∀ fuel, Sim b om p (blocks lit fuel)
      (fun f st => Rel b om lit f st ∧ f cMODE = mHDR ∧ 8 * b.size - st.pos < fuel)
      (fun _ f st => Rel b om lit f st ∧ f cMODE = mDONE) := by
  have hL : 2080 ≤ L0 b.size om := by unfold L0; omega
  intro fuel
  induction fuel with
  | zero => rintro σ f st hw ⟨_, _, h⟩; omega
  | succ fuel ih =>
    simp only [blocks]
    refine Sim.step (pre' := fun f st => (Rel b om lit f st ∧ f cMODE = mREAD ∧ f cK = (0 : Nat) + 1 ∧ f cACC = 0 ∧
      f cWT = 1 ∧ f cRET = mHDRB) ∧ 8 * b.size - st.pos < fuel + 1) ?_ ?_
    · rintro σ f st hw ⟨hR, hm, hfu⟩
      obtain ⟨σ1, f1, hS, hw1, hR1, h1, h2, h3, h4, h5, -⟩ := hdr_next hb hw hR hm
      exact ⟨σ1, f1, hS, hw1, ⟨hR1, h1, by rw [h2]; norm_num, h3, h4, h5⟩, hfu⟩
    refine Sim.bind (bits_sim' hb 0 mHDRB (fun _ st => 8 * b.size - st.pos < fuel + 1)
      (fun _ st => 8 * b.size - st.pos < fuel) (fun _ _ _ _ h _ _ hlt hin => by omega)) (fun bf => ?_)
    refine Sim.step (pre' := fun f st => (Rel b om lit f st ∧ f cMODE = mREAD ∧ f cK = (1 : Nat) + 1 ∧ f cACC = 0 ∧
      f cWT = 1 ∧ f cRET = mHDRD) ∧ (f cBF = bf ∧ 8 * b.size - st.pos < fuel)) ?_ ?_
    · rintro σ f st hw ⟨hR, hm, ha, hfu⟩
      obtain ⟨σ1, f1, hS, hw1, hR1, h1, h2, h3, h4, h5, h6⟩ := hdrb_next hb hw hR hm
      exact ⟨σ1, f1, hS, hw1, ⟨hR1, h1, by rw [h2]; norm_num, h3, h4, h5⟩, by rw [h6, ha], hfu⟩
    refine Sim.bind (bits_sim' hb 1 mHDRD (fun f st => f cBF = bf ∧ 8 * b.size - st.pos < fuel)
      (fun f st => f cBF = bf ∧ 8 * b.size - st.pos < fuel) (fun f st f' st' hq hk _ hlt _ => ⟨?_, by omega⟩))
      (fun bt => ?_)
    · rw [hk _ (by decide) (by unfold cBF L0; omega) (by unfold rdSet cBF; omega)]; exact hq.1
    have cont : Sim b om p (if bf = 1 then Pure.pure () else blocks lit fuel)
        (fun f st => (Rel b om lit f st ∧ f cMODE = endMode bf) ∧ 8 * b.size - st.pos < fuel)
        (fun _ f st => Rel b om lit f st ∧ f cMODE = mDONE) := by
      refine Sim.ite (fun h1 => Sim.pure ?_) (fun h1 => (ih.mono ?_ (fun _ _ _ h => h)))
      · rintro f st ⟨⟨hR, hm⟩, _⟩
        refine ⟨hR, ?_⟩
        rw [hm, endMode, if_pos (by exact_mod_cast h1)]
      · rintro f st ⟨⟨hR, hm⟩, hfu⟩
        refine ⟨hR, ?_, hfu⟩
        rw [hm, endMode, if_neg (by exact_mod_cast h1)]
    refine Sim.step (pre' := fun f st => (Rel b om lit f st ∧ f cBF = bf ∧ (bt = 0 → f cMODE = mSHDR) ∧
      (bt = 1 → f cMODE = mFIXLENS ∧ f cFILL = 0) ∧ (bt = 2 → f cMODE = mDHDR) ∧
      (bt ≠ 0 → bt ≠ 1 → bt ≠ 2 → f cMODE = mREJECT)) ∧ 8 * b.size - st.pos < fuel) ?_ ?_
    · rintro σ f st hw ⟨hR, hm, ha, hbf, hfu⟩
      obtain ⟨σ1, f1, hS, hw1, hR1, e4, d0, d1, d2, d3⟩ := hdrd_next hb hw hR hm
      rw [ha] at d0 d1 d2 d3
      refine ⟨σ1, f1, hS, hw1, ⟨hR1, by rw [e4, hbf], fun h => d0 (by simp [h]), fun h => d1 (by simp [h]),
        fun h => d2 (by simp [h]), fun h0 h1 h2 => d3 (by omega) (by omega) (by omega)⟩, hfu⟩
    refine Sim.ite (fun h0 => ?_) (fun h0 => Sim.ite (fun h1 => ?_) (fun h1 => Sim.ite (fun h2 => ?_) (fun h2 => ?_)))
    · exact Sim.bind (((HS bf).measure mono_stored fuel).mono
        (fun f st ⟨⟨hR, hbf, d0, _⟩, hfu⟩ => ⟨⟨hR, d0 h0, hbf, trivial⟩, hfu⟩) (fun _ _ _ h => h)) (fun _ => cont)
    · rw [← bind_assoc]
      exact Sim.bind (((HF bf).measure (mono_fixedBody lit) fuel).mono
        (fun f st ⟨⟨hR, hbf, _, d1, _⟩, hfu⟩ => ⟨⟨hR, (d1 h1).1, hbf, (d1 h1).2⟩, hfu⟩) (fun _ _ _ h => h)) (fun _ => cont)
    · exact Sim.bind (((HD bf).measure mono_dynamic fuel).mono
        (fun f st ⟨⟨hR, hbf, _, _, d2, _⟩, hfu⟩ => ⟨⟨hR, d2 h2, hbf, trivial⟩, hfu⟩) (fun _ _ _ h => h)) (fun _ => cont)
    · exact Sim.reject_bind (fun σ f st hw ⟨⟨_, _, _, _, _, d3⟩, _⟩ => ⟨σ, f, Reach.refl p σ, hw, d3 h0 h1 h2⟩)

/-! ## Stored blocks (S3): SHDR, SLEN, SNLEN, SCOPY -/

theorem xor_ffff (x : Nat) (hx : x < 65536) : x ^^^ 65535 = 65535 - x := by
  have h1 : (BitVec.ofNat 16 x ^^^ BitVec.ofNat 16 65535).toNat = x ^^^ 65535 := by
    rw [BitVec.toNat_xor, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx]
  have h2 : BitVec.ofNat 16 x ^^^ BitVec.ofNat 16 65535 = ~~~ BitVec.ofNat 16 x := by
    rw [show (BitVec.ofNat 16 65535 : BitVec 16) = BitVec.allOnes 16 from rfl, BitVec.xor_allOnes]
  rw [← h1, h2, BitVec.toNat_not, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx]

/-- S3's check `nlen ≠ len ^^^ 0xFFFF` is the step's `nlen + len ≠ 65535`, on 16-bit fields. -/
theorem nlen_check (len nlen : Nat) (h1 : len < 65536) (h2 : nlen < 65536) :
    nlen ≠ len ^^^ 0xFFFF ↔ ¬ ((nlen : Int) + len = 65535) := by
  rw [show (0xFFFF : Nat) = 65535 from rfl, xor_ffff len h1]; omega

theorem stepS_fit {σ σ' : Store} {p : Int} {L : Nat} {f : Int → Int} {k : Int} {t : NT} (hw : World σ p L f) (hL : 0 < L)
    (hm : f cMODE = k) (hk : modes.lookup k = some t) (hmem : (k, t) ∈ modes) (hne : k ≠ mTABLE)
    (h : Steps₂ (closeAt p (t.c ["w"]), σ) (.ret (.const (.cap p)), σ')) : stepS p σ = some σ' :=
  stepS_of_mode hw hL hm hk (modes_fit (k, t) hmem hne).1 (modes_fit (k, t) hmem hne).2 h

/-- R survives a change to control cells and the cursor, when the new cursor is the new position and the output is kept. -/
theorem Rel.of_keeps' {b : Array Nat} {om : Nat} {lit : Bool} {f f' : Int → Int} {st st' : St} {S : Int → Prop}
    (hR : Rel b om lit f st) (hi' : Inv b om lit f') (hk : Keeps (L0 b.size om) f f' S)
    (hS : ∀ c, S c → ctl b.size om c ∨ c = 1 ∨ c = 2) (hpos : 8 * f' cBY + f' cBI = st'.pos) (hout : st'.out = st.out) :
    Rel b om lit f' st' where
  inv := hi'
  bits v i hv hi7 hlt := by
    rw [hk _ (by unfold BT; omega) (by unfold BT L0; omega) (fun h => by have := hS _ h; unfold ctl BT IN at *; omega)]
    exact hR.bits v i hv hi7 hlt
  pos := hpos
  m := by
    rw [hk _ (by decide) (by unfold cM L0; omega) (fun h => by have := hS _ h; unfold ctl cM IN at *; omega), hout]
    exact hR.m
  out i hi2 := by
    rw [hout] at hi2 ⊢
    have hm' := hR.inv.1.m_rng
    have hm2 := hR.m
    have hc : IN + (b.size : Int) + i < L0 b.size om := by unfold IN L0; push_cast; omega
    rw [hk _ (by unfold IN; omega) hc (fun h => by have := hS _ h; unfold ctl IN at *; omega)]
    exact hR.out i hi2

def alignSt (st : St) : St := { st with pos := 8 * ((st.pos + 7) / 8) }

theorem shdr_next {b : Array Nat} {om : Nat} {lit : Bool} {σ : Store} {p : Int} {f : Int → Int} {st : St}
    (hb : ∀ x ∈ b, x < 256) (hw : World σ p (L0 b.size om) f) (hR : Rel b om lit f st) (hm : f cMODE = mSHDR) :
    ∃ σ1 f1, stepS p σ = some σ1 ∧ World σ1 p (L0 b.size om) f1 ∧ Rel b om lit f1 (alignSt st) ∧ f1 cMODE = mREAD ∧
      f1 cK = 16 ∧ f1 cACC = 0 ∧ f1 cWT = 1 ∧ f1 cRET = mSLEN ∧ f1 cBF = f cBF := by
  have hL : 2080 ≤ L0 b.size om := by unfold L0; omega
  have hS := stepS_fit hw (by omega) hm rfl (by unfold modes; simp) (by decide) (shdr_step hw hL (f cBY) (f cBI) rfl rfl)
  set nb := if f cBI = 0 then f cBY else f cBY + 1 with hnb
  have hg := ((hw.store (i := 1) (v := nb) (by norm_num) (by omega)).store (i := 2) (v := 0) (by norm_num)
    (by omega)).req (by omega) 16 8
  have hk : Keeps (L0 b.size om) f (reqF (Function.update (Function.update f 1 nb) 2 0) 16 8)
      (fun c => c = 0 ∨ c = 1 ∨ c = 2 ∨ (2068 ≤ c ∧ c ≤ 2071)) := fun c _ _ hc => by
    rw [reqF_eq _ 16 8 c (by omega), upd_eq _ _ (by omega), upd_eq _ _ (by omega)]
  obtain ⟨f1, hw1, hi1, ag⟩ := step_to hb hw hR.inv (by rw [hm]; decide) (by rw [hm]; decide) hS hg
  have hk1 : Keeps (L0 b.size om) f f1 (fun c => c = 0 ∨ c = 1 ∨ c = 2 ∨ (2068 ≤ c ∧ c ≤ 2071)) :=
    fun c h0 h1 hc => (ag c h0 h1).trans (hk c h0 h1 hc)
  have e1 : f1 cBY = nb := by
    rw [ag _ (by decide) (by unfold cBY; omega), reqF_eq _ _ _ _ (by unfold cBY; omega)]; simp [cBY]
  have e2 : f1 cBI = 0 := by
    rw [ag _ (by decide) (by unfold cBI; omega), reqF_eq _ _ _ _ (by unfold cBI; omega)]; simp [cBI]
  have hpos := hR.pos
  have hbi := hR.inv.1.bi_rng
  obtain ⟨v1, v2, v3, v4, v5⟩ := reqF_vals (Function.update (Function.update f 1 nb) 2 0) 16 8
  refine ⟨_, f1, hS, hw1, hR.of_keeps' hi1 hk1 (fun c hc => by unfold ctl IN; omega) ?_ rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [e1, e2, hnb]; simp only [alignSt]
    split_ifs with h <;> omega
  · rw [ag _ (by decide) (by unfold cMODE; omega)]; exact v1
  · rw [ag _ (by decide) (by unfold cK; omega)]; exact v2
  · rw [ag _ (by decide) (by unfold cACC; omega)]; exact v3
  · rw [ag _ (by decide) (by unfold cWT; omega)]; exact v4
  · rw [ag _ (by decide) (by unfold cRET; omega)]; exact v5
  · exact hk1 _ (by decide) (by unfold cBF; omega) (by unfold cBF; omega)

theorem slen_next {b : Array Nat} {om : Nat} {lit : Bool} {σ : Store} {p : Int} {f : Int → Int} {st : St}
    (hb : ∀ x ∈ b, x < 256) (hw : World σ p (L0 b.size om) f) (hR : Rel b om lit f st) (hm : f cMODE = mSLEN) :
    ∃ σ1 f1, stepS p σ = some σ1 ∧ World σ1 p (L0 b.size om) f1 ∧ Rel b om lit f1 st ∧ f1 cMODE = mREAD ∧
      f1 cK = 16 ∧ f1 cACC = 0 ∧ f1 cWT = 1 ∧ f1 cRET = mSNLEN ∧ f1 cBF = f cBF ∧ f1 cPEND = f cACC := by
  have hL : 2080 ≤ L0 b.size om := by unfold L0; omega
  have hS := stepS_fit hw (by omega) hm rfl (by unfold modes; simp) (by decide) (slen_step hw hL (f cACC) rfl)
  have hg := (hw.store (i := 5) (v := f cACC) (by norm_num) (by omega)).req (by omega) 16 9
  have hk : Keeps (L0 b.size om) f (reqF (Function.update f 5 (f cACC)) 16 9)
      (fun c => c = 0 ∨ c = 5 ∨ (2068 ≤ c ∧ c ≤ 2071)) := fun c _ _ hc => by
    rw [reqF_eq _ 16 9 c (by omega), upd_eq _ _ (by omega)]
  obtain ⟨f1, hw1, hR1, hk1, ag⟩ := next_rel hb hw hR (by rw [hm]; decide) (by rw [hm]; decide) hS hg hk
    (fun c hc => by unfold ctl IN; omega)
  obtain ⟨v1, v2, v3, v4, v5⟩ := reqF_vals (Function.update f 5 (f cACC)) 16 9
  refine ⟨_, f1, hS, hw1, hR1, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [ag _ (by decide) (by unfold cMODE; omega)]; exact v1
  · rw [ag _ (by decide) (by unfold cK; omega)]; exact v2
  · rw [ag _ (by decide) (by unfold cACC; omega)]; exact v3
  · rw [ag _ (by decide) (by unfold cWT; omega)]; exact v4
  · rw [ag _ (by decide) (by unfold cRET; omega)]; exact v5
  · exact hk1 _ (by decide) (by unfold cBF; omega) (by unfold cBF; omega)
  · rw [ag _ (by decide) (by unfold cPEND; omega), reqF_eq _ _ _ _ (by unfold cPEND; omega)]; simp [cPEND]

theorem snlen_next {b : Array Nat} {om : Nat} {lit : Bool} {σ : Store} {p : Int} {f : Int → Int} {st : St}
    (hb : ∀ x ∈ b, x < 256) (hw : World σ p (L0 b.size om) f) (hR : Rel b om lit f st) (hm : f cMODE = mSNLEN) :
    ∃ σ1 f1, stepS p σ = some σ1 ∧ World σ1 p (L0 b.size om) f1 ∧ Rel b om lit f1 st ∧
      Keeps (L0 b.size om) f f1 (fun c => c = 0 ∨ c = 14) ∧
      f1 cMODE = (if f cACC + f cPEND = 65535 then (if f cN < f cBY + f cPEND then mREJECT
        else if f cOUTMAX < f cM + f cPEND then mREJECT else mSCOPY) else mREJECT) := by
  have hL : 2080 ≤ L0 b.size om := by unfold L0; omega
  have hS := stepS_fit hw (by omega) hm rfl (by unfold modes; simp) (by decide)
    (snlen_step hw hL (f cACC) (f cPEND) (f cBY) (f cN) (f cM) (f cOUTMAX) rfl rfl rfl rfl rfl rfl)
  set g : Int → Int := if f cACC + f cPEND = 65535 then (if f cN < f cBY + f cPEND then
      Function.update (Function.update f 14 1) 0 99 else if f cOUTMAX < f cM + f cPEND then
      Function.update (Function.update f 14 4) 0 99 else Function.update f 0 10)
    else Function.update (Function.update f 14 3) 0 99 with hgdef
  have hg : World ⟨snlenH σ.H p (f cACC) (f cPEND) (f cBY) (f cN) (f cM) (f cOUTMAX), σ.R⟩ p (L0 b.size om) g := by
    simp only [snlenH, hgdef]
    split_ifs
    · exact (hw.store (i := 14) (by norm_num) (by omega)).store (i := 0) (by norm_num) (by omega)
    · exact (hw.store (i := 14) (by norm_num) (by omega)).store (i := 0) (by norm_num) (by omega)
    · exact hw.store (i := 0) (by norm_num) (by omega)
    · exact (hw.store (i := 14) (by norm_num) (by omega)).store (i := 0) (by norm_num) (by omega)
  have hk : Keeps (L0 b.size om) f g (fun c => c = 0 ∨ c = 14) := fun c _ _ hc => by
    simp only [hgdef]; split_ifs <;> simp [Function.update_apply, show c ≠ 0 by omega, show c ≠ 14 by omega]
  obtain ⟨f1, hw1, hR1, hk1, ag⟩ := next_rel hb hw hR (by rw [hm]; decide) (by rw [hm]; decide) hS hg hk
    (fun c hc => by unfold ctl IN; omega)
  refine ⟨_, f1, hS, hw1, hR1, hk1, ?_⟩
  simp only [cMODE]
  rw [ag 0 (by norm_num) (by omega), hgdef]
  split_ifs <;> simp [mREJECT, mSCOPY]

theorem push_extract (o b : Array Nat) (q k : Nat) (hq : q < b.size) :
    o ++ b.extract q (q + (k + 1)) = (o.push (b.getD q 0)) ++ b.extract (q + 1) (q + 1 + k) := by
  apply Array.ext'
  simp only [Array.toList_append, Array.toList_push, Array.toList_extract, List.extract_eq_drop_take]
  rw [show q + (k + 1) - q = k + 1 by omega, show q + 1 + k - (q + 1) = k by omega,
    List.drop_eq_getElem_cons (by simpa using hq), List.take_succ_cons]
  simp [Array.getD, hq]

/-- **SCOPY, one byte.** -/
theorem scopy_next {b : Array Nat} {om : Nat} {lit : Bool} {σ : Store} {p : Int} {f : Int → Int} {st : St}
    (hb : ∀ x ∈ b, x < 256) (hw : World σ p (L0 b.size om) f) (hR : Rel b om lit f st) (hm : f cMODE = mSCOPY)
    (hk : f cPEND ≠ 0) (hin : st.pos / 8 < b.size) (hom : st.out.size < om) :
    ∃ σ1 f1, stepS p σ = some σ1 ∧ World σ1 p (L0 b.size om) f1 ∧
      Rel b om lit f1 ⟨st.pos + 8, st.out.push (b.getD (st.pos / 8) 0)⟩ ∧ f1 cMODE = mSCOPY ∧
      f1 cPEND = f cPEND - 1 ∧ f1 cBF = f cBF := by
  have hL : 2080 + b.size + om ≤ L0 b.size om := by unfold L0; omega
  have hi := hR.inv
  have hbi0 : f cBI = 0 := hi.2.align (Or.inr (Or.inr hm))
  have hpos := hR.pos
  have hmm := hR.m
  have hbr := hi.1.by_rng
  have hq : (st.pos / 8 : Nat) = (f cBY).toNat := by omega
  obtain ⟨hv, hv8⟩ := hi.1.byte hb (f cBY).toNat (by omega)
  have hS := stepS_fit hw (by omega) hm rfl (by unfold modes; simp) (by decide)
    (scopy_byte hw (f cBY).toNat b.size st.out.size om (f cPEND) ((b[(f cBY).toNat]'(by omega) : Nat) : Int) hL rfl hk (by omega)
      hi.1.n_eq (by omega) hv (by rw [hmm]) hom)
  set x : Int := ((b[(f cBY).toNat]'(by omega) : Nat) : Int) with hx
  set g := Function.update (Function.update (Function.update (Function.update f (2080 + b.size + st.out.size) x) 1
    ((f cBY).toNat + 1)) 3 (st.out.size + 1)) 5 (f cPEND - 1) with hgdef
  have hg : World ⟨(((σ.H.insert (p + (2080 + b.size + st.out.size)) x).insert (p + 1) ((f cBY).toNat + 1)).insert (p + 3)
      (st.out.size + 1)).insert (p + 5) (f cPEND - 1), σ.R⟩ p (L0 b.size om) g :=
    (((hw.store (i := 2080 + b.size + st.out.size) (by omega) (by omega)).store (i := 1) (by norm_num) (by omega)).store
      (i := 3) (by norm_num) (by omega)).store (i := 5) (by norm_num) (by omega)
  obtain ⟨f1, hw1, hi1, ag⟩ := step_to hb hw hi (by rw [hm]; decide) (by rw [hm]; decide) hS hg
  have gf : ∀ c : Int, c ≠ 2080 + b.size + st.out.size → c ≠ 1 → c ≠ 3 → c ≠ 5 → g c = f c := fun c a b' c' d => by
    rw [hgdef, upd_eq _ _ d, upd_eq _ _ c', upd_eq _ _ b', upd_eq _ _ a]
  have kf : ∀ c : Int, 0 ≤ c → c < L0 b.size om → c ≠ 2080 + b.size + st.out.size → c ≠ 1 → c ≠ 3 → c ≠ 5 →
      f1 c = f c := fun c h0 h1 a b' c' d => (ag c h0 h1).trans (gf c a b' c' d)
  have e1 : f1 cBY = (f cBY).toNat + 1 := by rw [ag _ (by decide) (by unfold cBY; omega)]; simp [hgdef, cBY]
  have eBI : f1 cBI = 0 := by
    rw [kf _ (by decide) (by unfold cBI; omega) (by unfold cBI; omega) (by decide) (by decide) (by decide)]; exact hbi0
  have e3 : f1 cM = st.out.size + 1 := by rw [ag _ (by decide) (by unfold cM; omega)]; simp [hgdef, cM]
  have e5 : f1 cPEND = f cPEND - 1 := by rw [ag _ (by decide) (by unfold cPEND; omega)]; simp [hgdef, cPEND]
  have eo : f1 (2080 + b.size + st.out.size) = x := by
    rw [ag _ (by omega) (by omega)]; simp only [hgdef, Function.update_apply]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]; simp
  refine ⟨_, f1, hS, hw1, ⟨hi1, ?_, ?_, ?_, ?_⟩, ?_, e5, ?_⟩
  · intro v i hv' hi7 hlt
    rw [kf _ (by unfold BT; omega) (by unfold BT L0; omega) (by unfold BT; omega) (by unfold BT; omega)
      (by unfold BT; omega) (by unfold BT; omega)]
    exact hR.bits v i hv' hi7 hlt
  · rw [e1, eBI]; simp only; omega
  · rw [e3]; simp
  · intro i hi2
    simp only [Array.size_push] at hi2 ⊢
    by_cases hlt : i < st.out.size
    · rw [kf _ (by unfold IN; omega) (by unfold IN L0; push_cast; omega) (by unfold IN; omega) (by unfold IN; omega)
        (by unfold IN; omega) (by unfold IN; omega), hR.out i hlt]
      simp [Array.getD, hlt, Array.getElem_push, show i < st.out.size + 1 by omega]
    · have hie : i = st.out.size := by omega
      subst hie
      simp only [IN]; rw [eo, hx]
      simp [Array.getD, hq, show (f cBY).toNat < b.size by omega]
  · rw [kf _ (by decide) (by unfold cMODE; omega) (by unfold cMODE; omega) (by decide) (by decide) (by decide)]; exact hm
  · rw [kf _ (by decide) (by unfold cBF; omega) (by unfold cBF; omega) (by decide) (by decide) (by decide)]

/-- **SCOPY to the block's end:** k bytes are copied, as S3's one `extract`, and the block ends by BFINAL. -/
theorem scopy_run {b : Array Nat} {om : Nat} {lit : Bool} {p : Int} (hb : ∀ x ∈ b, x < 256) (bf : Int) :
    ∀ (k : Nat) (σ : Store) (f : Int → Int) (st : St), World σ p (L0 b.size om) f → Rel b om lit f st →
      f cMODE = mSCOPY → f cPEND = k → f cBF = bf → st.pos / 8 + k ≤ b.size → st.out.size + k ≤ om →
      ∃ σ' f', Reach p σ σ' ∧ World σ' p (L0 b.size om) f' ∧
        Rel b om lit f' ⟨st.pos + 8 * k, st.out ++ b.extract (st.pos / 8) (st.pos / 8 + k)⟩ ∧ f' cMODE = endMode bf := by
  have hL : 2080 ≤ L0 b.size om := by unfold L0; omega
  intro k
  induction k with
  | zero =>
    intro σ f st hw hR hm hk hbf _ _
    have hS := stepS_fit hw (by omega) hm rfl (by unfold modes; simp) (by decide) (scopy_end hw hL bf (by simpa using hk) hbf)
    have hg := hw.store (i := 0) (v := if bf = 1 then 98 else 1) (by norm_num) (by omega)
    obtain ⟨f1, hw1, hR1, _, ag⟩ := next_rel hb hw hR (by rw [hm]; decide) (by rw [hm]; decide) hS hg
      (fun c _ _ hc => upd_eq _ _ (show c ≠ 0 by omega)) (fun c hc => by unfold ctl; omega)
    have e : st.out ++ b.extract (st.pos / 8) (st.pos / 8) = st.out := by apply Array.ext'; simp
    refine ⟨_, f1, Reach.step hS, hw1, by simp only [Nat.mul_zero, Nat.add_zero, e]; exact hR1, ?_⟩
    simp only [cMODE]; rw [ag 0 (by norm_num) (by omega)]; simp [endMode, mDONE, mHDR]
  | succ k ih =>
    intro σ f st hw hR hm hk hbf hin hom
    obtain ⟨σ1, f1, hS, hw1, hR1, hm1, hk1, hbf1⟩ := scopy_next hb hw hR hm (by rw [hk]; omega) (by omega) (by omega)
    obtain ⟨σ', f', hR', hw', hRel, hmo⟩ := ih σ1 f1 _ hw1 hR1 hm1 (by rw [hk1, hk]; push_cast; ring) (by rw [hbf1, hbf])
      (by simp only; omega) (by simp only [Array.size_push]; omega)
    refine ⟨σ', f', (Reach.step hS).trans hR', hw', ?_, hmo⟩
    have e1 : (st.pos + 8) / 8 = st.pos / 8 + 1 := by omega
    simp only [e1] at hRel
    rw [push_extract st.out b (st.pos / 8) k (by omega)]
    convert hRel using 2
    omega

theorem Sim.align' {b : Array Nat} {om : Nat} {p : Int} {pre : (Int → Int) → St → Prop} :
    Sim b om p align (fun f st => pre f (alignSt st)) (fun _ f st => pre f st) := by
  intro σ f st hw hp
  have e : go align ⟨b, om⟩ st = .ok ((), alignSt st) := rfl
  refine ⟨fun a st' h => ?_, fun r h => by rw [e] at h; simp at h⟩
  rw [e] at h
  simp only [Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨-, rfl⟩ := h
  exact ⟨σ, f, Reach.refl p σ, hw, hp⟩

theorem Sim.set' {b : Array Nat} {om : Nat} {p : Int} {t : St} {pre : (Int → Int) → St → Prop}
    {post : PUnit → (Int → Int) → St → Prop}
    (h : ∀ σ f st, World σ p (L0 b.size om) f → pre f st →
      ∃ σ' f', Reach p σ σ' ∧ World σ' p (L0 b.size om) f' ∧ post ⟨⟩ f' t) :
    Sim b om p (MonadStateOf.set t : M PUnit) pre post := by
  intro σ f st hw hp
  refine ⟨fun a st' h' => ?_, fun r h' => by rw [go_set] at h'; simp at h'⟩
  rw [go_set] at h'
  simp only [Except.ok.injEq, Prod.mk.injEq] at h'
  obtain ⟨-, rfl⟩ := h'
  cases a
  exact h σ f st hw hp

theorem cap16 {b : Array Nat} {om : Nat} {lit : Bool} {f : Int → Int} {st : St} (hR : Rel b om lit f st)
    (hm : f cMODE = mSLEN ∨ f cMODE = mSNLEN) : 0 ≤ f cACC ∧ f cACC < 65536 := by
  have h := hR.inv.2.ret (by rcases hm with hm | hm <;> rw [hm] <;> simp [readRets])
  rcases hm with hm | hm <;> rw [hm] at h <;> simpa [kcap, mSLEN, mSNLEN, mHDRB, mHDRD] using h

/-- **S3 is simulated: `stored` from SHDR ends in the block's end mode (S-18's `stored` row).** -/
theorem stored_sim {b : Array Nat} {om : Nat} {lit : Bool} {p : Int} (hb : ∀ x ∈ b, x < 256) :
    BodySim b om lit p stored mSHDR (fun _ => True) := by
  have hL : 2080 ≤ L0 b.size om := by unfold L0; omega
  intro bf
  unfold stored
  refine Sim.step (pre' := fun f st => (fun f st => (Rel b om lit f st ∧ f cMODE = mREAD ∧ f cK = (15 : Nat) + 1 ∧
    f cACC = 0 ∧ f cWT = 1 ∧ f cRET = mSLEN) ∧ f cBF = bf) f (alignSt st)) ?_ ?_
  · rintro σ f st hw ⟨hR, hm, hbf, -⟩
    obtain ⟨σ1, f1, hS, hw1, hR1, h1, h2, h3, h4, h5, h6⟩ := shdr_next hb hw hR hm
    exact ⟨σ1, f1, hS, hw1, ⟨hR1, h1, by rw [h2]; norm_num, h3, h4, h5⟩, by rw [h6, hbf]⟩
  refine Sim.bind (Sim.align' (pre := fun f st => (Rel b om lit f st ∧ f cMODE = mREAD ∧ f cK = (15 : Nat) + 1 ∧
    f cACC = 0 ∧ f cWT = 1 ∧ f cRET = mSLEN) ∧ f cBF = bf)) (fun _ => ?_)
  refine Sim.bind (bits_sim' hb 15 mSLEN (fun f _ => f cBF = bf) (fun f _ => f cBF = bf)
    (fun f st f' st' hq hk _ _ _ => by
      rw [hk _ (by decide) (by unfold cBF L0; omega) (by unfold rdSet cBF; omega)]; exact hq)) (fun len => ?_)
  refine Sim.step (pre' := fun f st => (Rel b om lit f st ∧ f cMODE = mREAD ∧ f cK = (15 : Nat) + 1 ∧ f cACC = 0 ∧
    f cWT = 1 ∧ f cRET = mSNLEN) ∧ (f cBF = bf ∧ f cPEND = len ∧ len < 65536)) ?_ ?_
  · rintro σ f st hw ⟨hR, hm, ha, hbf⟩
    have hcap := cap16 hR (Or.inl hm)
    obtain ⟨σ1, f1, hS, hw1, hR1, h1, h2, h3, h4, h5, h6, h7⟩ := slen_next hb hw hR hm
    exact ⟨σ1, f1, hS, hw1, ⟨hR1, h1, by rw [h2]; norm_num, h3, h4, h5⟩, by rw [h6, hbf], by rw [h7, ha], by omega⟩
  refine Sim.bind (bits_sim' hb 15 mSNLEN (fun f _ => f cBF = bf ∧ f cPEND = len ∧ len < 65536)
    (fun f _ => f cBF = bf ∧ f cPEND = len ∧ len < 65536)
    (fun f st f' st' hq hk _ _ _ => ⟨by rw [hk _ (by decide) (by unfold cBF L0; omega) (by unfold rdSet cBF; omega)]; exact hq.1,
      by rw [hk _ (by decide) (by unfold cPEND L0; omega) (by unfold rdSet cPEND; omega)]; exact hq.2.1, hq.2.2⟩))
    (fun nlen => ?_)
  refine Sim.step (pre' := fun f st => Rel b om lit f st ∧ f cBF = bf ∧ f cPEND = len ∧ len < 65536 ∧ nlen < 65536 ∧
    f cMODE = (if (nlen : Int) + len = 65535 then (if (b.size : Int) < st.pos / 8 + len then mREJECT
      else if (om : Int) < st.out.size + len then mREJECT else mSCOPY) else mREJECT)) ?_ ?_
  · rintro σ f st hw ⟨hR, hm, ha, hbf, hpd, hlen⟩
    have hcap := cap16 hR (Or.inr hm)
    have hbi0 := hR.inv.2.align (Or.inr (Or.inl hm))
    have hpos := hR.pos
    obtain ⟨σ1, f1, hS, hw1, hR1, hk1, hmode⟩ := snlen_next hb hw hR hm
    refine ⟨σ1, f1, hS, hw1, hR1, by rw [hk1 _ (by decide) (by unfold cBF; omega) (by unfold cBF; omega), hbf],
      by rw [hk1 _ (by decide) (by unfold cPEND; omega) (by unfold cPEND; omega), hpd], hlen, by omega, ?_⟩
    rw [hmode, ha, hpd, hR.inv.1.n_eq, hR.inv.1.om_eq, hR.m, show f cBY = ((st.pos / 8 : Nat) : Int) by omega]
    push_cast; rfl
  refine Sim.ite (fun hc => Sim.reject_bind ?_) (fun hc => ?_)
  · rintro σ f st hw ⟨-, -, -, hl, hn, hmode⟩
    refine ⟨σ, f, Reach.refl p σ, hw, ?_⟩
    rw [hmode, if_neg ((nlen_check len nlen hl hn).mp hc)]
  have hc' : ∀ (hl : len < 65536) (hn : nlen < 65536), (nlen : Int) + len = 65535 := fun hl hn => by
    have := (nlen_check len nlen hl hn).not; tauto
  refine Sim.read (Sim.get (fun s => ?_))
  refine Sim.ite (fun h2 => Sim.reject_bind ?_) (fun h2 => Sim.ite (fun h3 => Sim.reject_bind ?_) (fun h3 => ?_))
  · rintro σ f st hw ⟨⟨-, -, -, hl, hn, hmode⟩, rfl⟩
    refine ⟨σ, f, Reach.refl p σ, hw, ?_⟩
    rw [hmode, if_pos (hc' hl hn), if_pos (by simp only at h2; omega)]
  · rintro σ f st hw ⟨⟨-, -, -, hl, hn, hmode⟩, rfl⟩
    refine ⟨σ, f, Reach.refl p σ, hw, ?_⟩
    rw [hmode, if_pos (hc' hl hn), if_neg (by simp only at h2; omega), if_pos (by simp only at h3; omega)]
  · refine Sim.set' ?_
    rintro σ f st hw ⟨⟨hR, hbf, hpd, hl, hn, hmode⟩, rfl⟩
    have hm' : f cMODE = mSCOPY := by
      rw [hmode, if_pos (hc' hl hn), if_neg (by simp only at h2; omega), if_neg (by simp only at h3; omega)]
    obtain ⟨σ', f', hR', hw', hRel, hmo⟩ := scopy_run hb bf len σ f st hw hR hm' hpd hbf
      (by simp only at h2; omega) (by simp only at h3; omega)
    exact ⟨σ', f', hR', hw', hRel, hmo⟩

/-! ## DECODE simulates S4's `decodeGo` (S-18's `decodeGo` row) -/

/-- **S-18's code relation:** the table t holds what `decodeGo` reads of `assign lens`. -/
def TblRel (n om : Nat) (f : Int → Int) (t : Int) (lens : Array Nat) : Prop :=
  ∀ l : Nat, 1 ≤ l → l ≤ 15 →
    f (tbase n om t + l) = blCount lens l ∧ f (tbase n om t + 16 + l) = (nextCodes lens).getD l 0 ∧
    (∀ j : Nat, j < blCount lens l → f (tbase n om t + 64 + f (tbase n om t + 32 + l) + j) = (symsOf lens l).getD j 0) ∧
    0 ≤ f (tbase n om t + 32 + l) ∧ f (tbase n om t + 32 + l) + blCount lens l ≤ 288

/-- The cells a DECODE step writes on a hit or an advance. -/
def decSet (n om : Nat) (c : Int) : Prop :=
  c = 0 ∨ c = 1 ∨ c = 2 ∨ c = X0 n om ∨ c = X0 n om + 1 ∨ c = X0 n om + 4

theorem decSet_ctl (n om : Nat) (c : Int) (h : decSet n om c) : ctl n om c ∨ c = 1 ∨ c = 2 := by
  unfold decSet X0 at h; unfold ctl IN; omega

theorem lookup_assign (lens : Array Nat) (l v : Nat) (hl : l < 16) :
    lookup (assign lens) l v = if (nextCodes lens).getD l 0 ≤ v ∧ v < (nextCodes lens).getD l 0 + blCount lens l then
      some ((symsOf lens l).getD (v - (nextCodes lens).getD l 0) 0) else none := by
  unfold lookup; rw [assign_count _ _ hl, assign_syms _ _ hl, assign_first]

/-- **DECODE, one step, against S's `bit` and `lookup`.** -/
theorem decode_one {b : Array Nat} {om : Nat} {lit : Bool} {p : Int} {σ : Store} {f : Int → Int} {st : St}
    (hb : ∀ x ∈ b, x < 256) (hw : World σ p (L0 b.size om) f) (hR : Rel b om lit f st) (hm : f cMODE = mDECODE)
    (lens : Array Nat) (l v : Nat) (hl : f (X0 b.size om) = l) (hv : f (X0 b.size om + 1) = v)
    (hT : TblRel b.size om f (f (X0 b.size om + 2)) lens) :
    (∀ x s1, go bit ⟨b, om⟩ st = .ok (x, s1) →
      ∃ σ1 f1, stepS p σ = some σ1 ∧ World σ1 p (L0 b.size om) f1 ∧
        (∀ s, lookup (assign lens) l (2 * v + x) = some s → Rel b om lit f1 s1 ∧
          f1 cMODE = f (X0 b.size om + 3) ∧ f1 (X0 b.size om + 4) = s ∧ Keeps (L0 b.size om) f f1 (decSet b.size om)) ∧
        (lookup (assign lens) l (2 * v + x) = none → l = 15 → f1 cMODE = mREJECT) ∧
        (lookup (assign lens) l (2 * v + x) = none → l ≠ 15 → Rel b om lit f1 s1 ∧ f1 cMODE = mDECODE ∧
          f1 (X0 b.size om) = l + 1 ∧ f1 (X0 b.size om + 1) = 2 * v + x ∧ Keeps (L0 b.size om) f f1 (decSet b.size om))) ∧
    (∀ r, go bit ⟨b, om⟩ st = .error r →
      ∃ σ1 f1, stepS p σ = some σ1 ∧ World σ1 p (L0 b.size om) f1 ∧ f1 cMODE = mREJECT) := by
  have hLn : 2080 + b.size ≤ L0 b.size om := by unfold L0; omega
  have hL : 2080 ≤ L0 b.size om := by unfold L0; omega
  have hmem : (mDECODE, decodeN) ∈ modes := by unfold modes; simp
  have hfit := modes_fit (mDECODE, decodeN) hmem (by decide)
  have hi := hR.inv
  have hn := hi.1.n_eq
  have hbr := hi.1.by_rng
  have hir := hi.1.bi_rng
  have hpos := hR.pos
  have hd : f cMODE ≠ mDONE := by rw [hm]; decide
  have hrj : f cMODE ≠ mREJECT := by rw [hm]; decide
  obtain ⟨hfr, hl1, hl15, hpair, hsane⟩ := hi.2.dec hm
  have ht02 : 0 ≤ f (X0 b.size om + 2) ∧ f (X0 b.size om + 2) ≤ 2 := by
    rcases hpair with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> norm_num
  rw [hl] at hl1 hl15
  have hl1' : 1 ≤ l := by omega
  have hl15' : l ≤ 15 := by omega
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
    obtain ⟨hvb, hv8⟩ := hi.1.byte hb (f cBY).toNat (by omega)
    set vb := b[(f cBY).toNat]'(by omega) with hvbdef
    have hbiE : ((f cBI).toNat : Int) = f cBI := by omega
    have htb := hR.bits vb (f cBI).toNat hv8 (by omega) (by omega)
    have hxv : (x : Int) = bitAt vb (f cBI).toNat := by
      rw [bitAt_eq vb _ hv8 (by omega), ← hx, hp8, hp8']
      simp [Array.getD, show (f cBY).toNat < b.size by omega, hvbdef]
    set t := f (X0 b.size om + 2) with htd
    set rt := f (X0 b.size om + 3) with hrtd
    set tb : Int := 2080 + (b.size : Int) + om + 337 + 352 * t with htbd
    have htbase : tbase b.size om t = tb := by rw [htbd]; unfold tbase LB0; ring
    have hs := hsane l (by omega) (by omega)
    rw [htbase] at hs
    obtain ⟨hTc, hTf, hTs, -, -⟩ := hT l hl1' hl15'
    rw [htbase] at hTc hTf hTs
    set bit := f (BT + (8 * (vb : Int) + ((f cBI).toNat : Int))) with hbitd
    have hbitx : bit = x := htb.trans hxv.symm
    have hS := stepS_of_mode hw (by unfold L0; omega) hm rfl hfit.1 hfit.2
      (decode_step hw (f cBY).toNat (f cBI).toNat b.size vb om (X0 b.size om) l v t rt bit tb
        (f (tb + 16 + l)) (f (tb + l)) (f (tb + 32 + l))
        (f (tb + 64 + f (tb + 32 + l) + (2 * v + bit - f (tb + 16 + l)))) hLn (by omega) (by omega) hn hi.1.om_eq hi.1.x_eq
        (by omega) (by omega) hvb hv8 rfl (by unfold X0; omega) (by unfold X0 L0; omega) hl hv rfl rfl htbd.symm
        (by omega) (by unfold X0 L0 at *; omega) (by omega) (by omega)
        rfl rfl rfl (fun hh => ⟨by omega, by unfold L0; omega⟩) rfl)
    simp only [decH, show ((f cBY).toNat : Int) = f cBY by omega, show ((f cBI).toNat : Int) = f cBI by omega] at hS
    rw [hTf, hTc, hbitx] at hS
    set fs : Nat := (nextCodes lens).getD l 0 with hfsd
    set c : Nat := blCount lens l with hcd
    have hlk := lookup_assign lens l (2 * v + x) (by omega)
    set nb := tblNext (f cBY) (f cBI) with hnbd
    have hnb1 : 8 * nb.1 + nb.2 = 8 * f cBY + f cBI + 1 := by
      simp only [hnbd, tblNext]; split_ifs <;> simp <;> omega
    have hposR : 8 * nb.1 + nb.2 = ((st.pos + 1 : Nat) : Int) := by rw [hnb1, hpos]; push_cast; ring
    have hX4 : X0 b.size om + 4 < L0 b.size om := by unfold X0 L0; omega
    have hXL : X0 b.size om + 1 < L0 b.size om := by unfold X0 L0; omega
    by_cases hhit : (fs : Int) ≤ 2 * v + x ∧ (2 * v + x : Int) < fs + c
    · rw [if_pos hhit] at hS
      set sy := f (tb + 64 + f (tb + 32 + l) + (2 * v + x - fs)) with hsyd
      set g := Function.update (Function.update (Function.update (Function.update f 1 nb.1) 2 nb.2)
        (X0 b.size om + 4) sy) 0 rt with hgd
      have hg : World _ p (L0 b.size om) g :=
        (((hw.store (i := 1) (by norm_num) (by omega)).store (i := 2) (by norm_num) (by omega)).store
          (i := X0 b.size om + 4) (by unfold X0; omega) hX4).store (i := 0) (by norm_num) (by omega)
      obtain ⟨f1, hw1, hi1, ag⟩ := step_to hb hw hi hd hrj hS hg
      have hk : Keeps (L0 b.size om) f f1 (decSet b.size om) := fun c h0 h1 hc => by
        unfold decSet at hc
        rw [ag c h0 h1, hgd, upd_eq _ _ (by omega), upd_eq _ _ (by omega), upd_eq _ _ (by omega), upd_eq _ _ (by omega)]
      refine ⟨_, f1, hS, hw1, fun s hs' => ?_, fun hn' => ?_, fun hn' => ?_⟩
      · rw [hlk, if_pos (by exact_mod_cast hhit)] at hs'
        simp only [Option.some.injEq] at hs'
        refine ⟨hR.of_keeps' hi1 hk (decSet_ctl _ _) ?_ rfl, ?_, ?_, hk⟩
        · rw [ag _ (by decide) (by unfold cBY; omega), ag _ (by decide) (by unfold cBI; omega)]
          simp only [hgd, cBY, cBI, Function.update_apply]
          simp only [show (1 : Int) ≠ 0 by decide, show (2 : Int) ≠ 0 by decide, show (1 : Int) ≠ 2 by decide,
            show (1 : Int) ≠ X0 b.size om + 4 by unfold X0; omega, show (2 : Int) ≠ X0 b.size om + 4 by unfold X0; omega,
            if_false, if_true]
          exact hposR
        · rw [ag _ (by decide) (by unfold cMODE; omega)]; simp [hgd, cMODE]
        · rw [ag _ (by unfold X0; omega) hX4, hgd, upd_eq _ _ (by unfold X0; omega)]
          simp only [Function.update_self, hsyd]
          rw [← hs']
          have hj : (2 * v + x - fs : Nat) < c := by omega
          have := hTs (2 * v + x - fs) hj
          rw [show (2 * (v : Int) + x - fs) = ((2 * v + x - fs : Nat) : Int) by omega]
          exact this
      · rw [hlk, if_pos (by exact_mod_cast hhit)] at hn'; simp at hn'
      · rw [hlk, if_pos (by exact_mod_cast hhit)] at hn'; simp at hn'
    · rw [if_neg hhit] at hS
      have hnone : lookup (assign lens) l (2 * v + x) = none := by
        rw [hlk, if_neg (by intro h; exact hhit (by exact_mod_cast h))]
      by_cases h15 : (l : Int) = 15
      · rw [if_pos h15] at hS
        have hg := (hw.store (i := 14) (v := 7) (by norm_num) (by omega)).store (i := 0) (v := 99) (by norm_num) (by omega)
        refine ⟨_, _, hS, hg, fun s hs' => by rw [hnone] at hs'; simp at hs', fun _ _ => by simp [cMODE, mREJECT],
          fun _ h => absurd (by exact_mod_cast h15) h⟩
      · rw [if_neg h15] at hS
        set g := Function.update (Function.update (Function.update (Function.update f 1 nb.1) 2 nb.2)
          (X0 b.size om) (l + 1)) (X0 b.size om + 1) (2 * v + x) with hgd
        have hg : World _ p (L0 b.size om) g :=
          (((hw.store (i := 1) (by norm_num) (by omega)).store (i := 2) (by norm_num) (by omega)).store
            (i := X0 b.size om) (by unfold X0; omega) (by unfold X0 L0; omega)).store (i := X0 b.size om + 1)
            (by unfold X0; omega) hXL
        obtain ⟨f1, hw1, hi1, ag⟩ := step_to hb hw hi hd hrj hS hg
        have hk : Keeps (L0 b.size om) f f1 (decSet b.size om) := fun c h0 h1 hc => by
          unfold decSet at hc
          rw [ag c h0 h1, hgd, upd_eq _ _ (by omega), upd_eq _ _ (by omega), upd_eq _ _ (by omega), upd_eq _ _ (by omega)]
        refine ⟨_, f1, hS, hw1, fun s hs' => by rw [hnone] at hs'; simp at hs', fun _ h => absurd (by exact_mod_cast h) h15,
          fun _ _ => ⟨hR.of_keeps' hi1 hk (decSet_ctl _ _) ?_ rfl, ?_, ?_, ?_, hk⟩⟩
        · rw [ag _ (by decide) (by unfold cBY; omega), ag _ (by decide) (by unfold cBI; omega)]
          simp only [hgd, cBY, cBI, Function.update_apply]
          simp only [show (1 : Int) ≠ X0 b.size om by unfold X0; omega, show (2 : Int) ≠ X0 b.size om by unfold X0; omega,
            show (1 : Int) ≠ X0 b.size om + 1 by unfold X0; omega, show (2 : Int) ≠ X0 b.size om + 1 by unfold X0; omega,
            show (1 : Int) ≠ 2 by decide, if_false, if_true]
          exact hposR
        · rw [ag _ (by decide) (by unfold cMODE; omega), hgd]
          simp only [cMODE] at hm ⊢
          rw [upd_eq _ _ (by unfold X0; omega), upd_eq _ _ (by unfold X0; omega), upd_eq _ _ (by decide),
            upd_eq _ _ (by decide)]
          exact hm
        · rw [ag _ (by unfold X0; omega) (by unfold X0 L0; omega), hgd, upd_eq _ _ (by omega)]; simp
        · rw [ag _ (by unfold X0; omega) hXL, hgd]; simp
  · have hsz : ¬ (st.pos / 8 < (⟨b, om⟩ : Env).inp.size) := by simp only; omega
    rw [if_neg hsz]
    refine ⟨fun x s1 hx => by simp at hx, fun r _ => ?_⟩
    have hS := stepS_of_mode hw (by unfold L0; omega) hm rfl hfit.1 hfit.2
      (decode_trunc hw hL (f cBY) (f cBI) b.size om (X0 b.size om) rfl rfl hn hi.1.om_eq hi.1.x_eq (by omega))
    have hwr := (hw.store (i := 14) (v := 1) (by norm_num) (by omega)).store (i := 0) (v := 99) (by norm_num) (by omega)
    exact ⟨_, _, hS, hwr, by simp [cMODE, mREJECT]⟩

/-- `TblRel` survives any change outside the three tables. -/
theorem TblRel.keep {n om : Nat} {f f' : Int → Int} {t : Int} {lens : Array Nat} {S : Int → Prop}
    (hT : TblRel n om f t lens) (ht : 0 ≤ t ∧ t ≤ 2) (hk : Keeps (L0 n om) f f' S)
    (hS : ∀ c, S c → c < tbase n om 0 ∨ X0 n om ≤ c) : TblRel n om f' t lens := by
  have tb0 : tbase n om 0 ≤ tbase n om t := by unfold tbase; omega
  have tb2 : tbase n om t + 352 ≤ X0 n om := by unfold tbase LB0 X0; omega
  have hX : X0 n om < L0 n om := by unfold X0 L0; omega
  have k : ∀ c, tbase n om t ≤ c → c < tbase n om t + 352 → f' c = f c := fun c h1 h2 =>
    hk c (by unfold tbase LB0 at *; omega) (by omega) (fun h => by have := hS c h; omega)
  intro l hl1 hl15
  obtain ⟨h1, h2, h3, s1, s2⟩ := hT l hl1 hl15
  have e32 : f' (tbase n om t + 32 + l) = f (tbase n om t + 32 + l) := k _ (by omega) (by omega)
  refine ⟨by rw [k _ (by omega) (by omega)]; exact h1, by rw [k _ (by omega) (by omega)]; exact h2, fun j hj => ?_,
    by rw [e32]; exact s1, by rw [e32]; exact s2⟩
  rw [e32]
  have hj' : (j : Int) < blCount lens l := by exact_mod_cast hj
  rw [k _ (by omega) (by omega)]
  exact h3 j hj

theorem decSet_out (n om : Nat) (c : Int) (h : decSet n om c) : c < tbase n om 0 ∨ X0 n om ≤ c := by
  unfold decSet at h; unfold tbase LB0 X0 at *; omega

/-- **DECODE ↔ `decodeGo`** (S-18's row): from DECODE at length ℓ with the read value v, against `assign lens` held in the
table the request names. -/
theorem decode_sim {b : Array Nat} {om : Nat} {lit : Bool} {p : Int} (hb : ∀ x ∈ b, x < 256) (lens : Array Nat) :
    ∀ (fuel l v : Nat) (σ : Store) (f : Int → Int) (st : St), l + fuel = 16 → World σ p (L0 b.size om) f →
      Rel b om lit f st → f cMODE = mDECODE → f (X0 b.size om) = l → f (X0 b.size om + 1) = v →
      TblRel b.size om f (f (X0 b.size om + 2)) lens →
      (∀ s st', go (decodeGo (assign lens) fuel l v) ⟨b, om⟩ st = .ok (s, st') →
        ∃ σ' f', Reach p σ σ' ∧ World σ' p (L0 b.size om) f' ∧ Rel b om lit f' st' ∧
          f' cMODE = f (X0 b.size om + 3) ∧ f' (X0 b.size om + 4) = s ∧ Keeps (L0 b.size om) f f' (decSet b.size om)) ∧
      (∀ r, go (decodeGo (assign lens) fuel l v) ⟨b, om⟩ st = .error r →
        ∃ σ' f', Reach p σ σ' ∧ World σ' p (L0 b.size om) f' ∧ f' cMODE = mREJECT) := by
  intro fuel
  induction fuel with
  | zero =>
    intro l v σ f st hl hw hR hm hX
    obtain ⟨_, _, hl15, _⟩ := hR.inv.2.dec hm
    omega
  | succ fuel ih =>
    intro l v σ f st hl hw hR hm hX hV hT
    obtain ⟨_, _, _, hpair, hsane⟩ := hR.inv.2.dec hm
    have ht02 : 0 ≤ f (X0 b.size om + 2) ∧ f (X0 b.size om + 2) ≤ 2 := by
      rcases hpair with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> norm_num
    obtain ⟨hok, herr⟩ := decode_one hb hw hR hm lens l v hX hV hT
    rw [decodeGo_succ]
    constructor
    · intro s st' h
      rw [go_bind] at h
      rcases hbit : go bit ⟨b, om⟩ st with r | ⟨x, s1⟩
      · rw [hbit] at h; simp at h
      · rw [hbit] at h
        dsimp only at h
        obtain ⟨σ1, f1, hS, hw1, hhit, h15, hadv⟩ := hok x s1 hbit
        rcases hlk : lookup (assign lens) l (2 * v + x) with _ | s0
        · rw [hlk] at h
          by_cases hl15 : l = 15
          · subst hl15
            have : fuel = 0 := by omega
            subst this
            simp [decodeGo, go_reject] at h
          · obtain ⟨hR1, hm1, hX1, hV1, hk1⟩ := hadv hlk hl15
            have hT1 := hT.keep ht02 hk1 (decSet_out _ _)
            rw [← hk1 (X0 b.size om + 2) (by unfold X0; omega) (by unfold X0 L0; omega) (by unfold decSet X0; omega)] at hT1
            obtain ⟨σ', f', hR', hw', hR'', hm', hs', hk'⟩ :=
              (ih (l + 1) (2 * v + x) σ1 f1 s1 (by omega) hw1 hR1 hm1 (by rw [hX1]; push_cast; ring) (by rw [hV1]; push_cast; ring)
                hT1).1 s st' h
            refine ⟨σ', f', (Reach.step hS).trans hR', hw', hR'', ?_, hs', hk1.trans hk' (fun c h => h)⟩
            rw [hm', hk1 (X0 b.size om + 3) (by unfold X0; omega) (by unfold X0 L0; omega) (by unfold decSet X0; omega)]
        · rw [hlk] at h
          simp only [go_pure, Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          obtain ⟨hR1, hm1, hs1, hk1⟩ := hhit s0 hlk
          exact ⟨σ1, f1, Reach.step hS, hw1, hR1, hm1, hs1, hk1⟩
    · intro r h
      rw [go_bind] at h
      rcases hbit : go bit ⟨b, om⟩ st with r' | ⟨x, s1⟩
      · obtain ⟨σ1, f1, hS, hw1, hm1⟩ := herr r' hbit
        exact ⟨σ1, f1, Reach.step hS, hw1, hm1⟩
      · rw [hbit] at h
        dsimp only at h
        obtain ⟨σ1, f1, hS, hw1, hhit, h15, hadv⟩ := hok x s1 hbit
        rcases hlk : lookup (assign lens) l (2 * v + x) with _ | s0
        · rw [hlk] at h
          by_cases hl15 : l = 15
          · exact ⟨σ1, f1, Reach.step hS, hw1, h15 hlk hl15⟩
          · obtain ⟨hR1, hm1, hX1, hV1, hk1⟩ := hadv hlk hl15
            have hT1 := hT.keep ht02 hk1 (decSet_out _ _)
            rw [← hk1 (X0 b.size om + 2) (by unfold X0; omega) (by unfold X0 L0; omega) (by unfold decSet X0; omega)] at hT1
            obtain ⟨σ', f', hR', hw', hm'⟩ :=
              (ih (l + 1) (2 * v + x) σ1 f1 s1 (by omega) hw1 hR1 hm1 (by rw [hX1]; push_cast; ring) (by rw [hV1]; push_cast; ring)
                hT1).2 r h
            exact ⟨σ', f', (Reach.step hS).trans hR', hw', hm'⟩
        · rw [hlk] at h; simp [go_pure] at h

/-! ## S7's loop: SYM, SYMD, LENX, DSTD, DSTX, COPY -/

theorem InvG.roVal {b : Array Nat} {om : Nat} {lit : Bool} {f : Int → Int} (h : InvG b om lit f) :
    (∀ i : Nat, i < 29 → f (X0 b.size om + 16 + i) = LBASE.getD i 0) ∧
    (∀ i : Nat, i < 29 → f (X0 b.size om + 45 + i) = LEXTRA.getD i 0) ∧
    (∀ i : Nat, i < 30 → f (X0 b.size om + 74 + i) = DBASE.getD i 0) ∧
    (∀ i : Nat, i < 30 → f (X0 b.size om + 104 + i) = DEXTRA.getD i 0) := by
  have hx : ∀ i : Int, X0 b.size om + 16 ≤ i → i < X0 b.size om + 153 → f i = initCell b om lit i := h.ro
  unfold X0 at hx ⊢
  refine ⟨fun i hi => ?_, fun i hi => ?_, fun i hi => ?_, fun i hi => ?_⟩
  · rw [hx _ (by omega) (by omega)]; unfold initCell X0; dsimp only
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]
    have e : (2080 + (b.size : Int) + (om : Int) + 1393 + 16 + (i : Int) - (2080 + (b.size : Int) + (om : Int) + 1393) - 16).toNat = i := by
      omega
    rw [e]
  · rw [hx _ (by omega) (by omega)]; unfold initCell X0; dsimp only
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_pos (by omega)]
    have e : (2080 + (b.size : Int) + (om : Int) + 1393 + 45 + (i : Int) - (2080 + (b.size : Int) + (om : Int) + 1393) - 45).toNat = i := by
      omega
    rw [e]
  · rw [hx _ (by omega) (by omega)]; unfold initCell X0; dsimp only
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_neg (by omega), if_pos (by omega)]
    have e : (2080 + (b.size : Int) + (om : Int) + 1393 + 74 + (i : Int) - (2080 + (b.size : Int) + (om : Int) + 1393) - 74).toNat = i := by
      omega
    rw [e]
  · rw [hx _ (by omega) (by omega)]; unfold initCell X0; dsimp only
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_neg (by omega), if_neg (by omega), if_pos (by omega)]
    have e : (2080 + (b.size : Int) + (om : Int) + 1393 + 104 + (i : Int) - (2080 + (b.size : Int) + (om : Int) + 1393) - 104).toNat = i := by
      omega
    rw [e]

/-- The cells a DECODE request writes. -/
def reqDecF (f : Int → Int) (X tg rt : Int) : Int → Int :=
  Function.update (Function.update (Function.update (Function.update (Function.update f X 1) (X + 1) 0) (X + 2) tg)
    (X + 3) rt) 0 14

theorem World.reqDec {σ : Store} {p : Int} {L : Nat} {f : Int → Int} (hw : World σ p L f) {X : Int} (hX0 : 4 ≤ X)
    (hXL : X + 4 < L) (tg rt : Int) : World ⟨reqDecH σ.H p X tg rt, σ.R⟩ p L (reqDecF f X tg rt) := by
  unfold reqDecH reqDecF
  exact ((((hw.store (i := X) (by omega) (by omega)).store (i := X + 1) (by omega) (by omega)).store (i := X + 2)
    (by omega) (by omega)).store (i := X + 3) (by omega) (by omega)).store (i := 0) (by norm_num) (by omega)

def decReqSet (n om : Nat) (c : Int) : Prop := c = 0 ∨ (X0 n om ≤ c ∧ c ≤ X0 n om + 3)

theorem reqDecF_keeps (L n om : Nat) (f : Int → Int) (tg rt : Int) :
    Keeps L f (reqDecF f (X0 n om) tg rt) (decReqSet n om) := fun c _ _ hc => by
  unfold decReqSet at hc
  simp only [reqDecF]
  rw [upd_eq _ _ (by omega), upd_eq _ _ (by omega), upd_eq _ _ (by omega), upd_eq _ _ (by omega), upd_eq _ _ (by omega)]

theorem reqDecF_vals (f : Int → Int) (X tg rt : Int) (hX : 4 ≤ X) :
    reqDecF f X tg rt cMODE = mDECODE ∧ reqDecF f X tg rt X = 1 ∧ reqDecF f X tg rt (X + 1) = 0 ∧
      reqDecF f X tg rt (X + 2) = tg ∧ reqDecF f X tg rt (X + 3) = rt := by
  simp only [reqDecF, cMODE, Function.update_apply]
  refine ⟨by simp [mDECODE], ?_, ?_, ?_, ?_⟩ <;> split_ifs <;> first | omega | rfl

/-- What a decode request leaves: R, the request's cells, every table and every cell outside the request kept. -/
def DecReady (b : Array Nat) (om : Nat) (lit : Bool) (f : Int → Int) (st : St) (tg rt : Int) : Prop :=
  Rel b om lit f st ∧ f cMODE = mDECODE ∧ f (X0 b.size om) = (1 : Nat) ∧ f (X0 b.size om + 1) = (0 : Nat) ∧
    f (X0 b.size om + 2) = tg ∧ f (X0 b.size om + 3) = rt

theorem sym_next {b : Array Nat} {om : Nat} {lit : Bool} {σ : Store} {p : Int} {f : Int → Int} {st : St}
    (hb : ∀ x ∈ b, x < 256) (hw : World σ p (L0 b.size om) f) (hR : Rel b om lit f st) (hm : f cMODE = mSYM) :
    ∃ σ1 f1, stepS p σ = some σ1 ∧ World σ1 p (L0 b.size om) f1 ∧ DecReady b om lit f1 st 1 mSYMD ∧
      Keeps (L0 b.size om) f f1 (decReqSet b.size om) := by
  have hL : 2080 ≤ L0 b.size om := by unfold L0; omega
  have hX4 : X0 b.size om + 4 < L0 b.size om := by unfold X0 L0; omega
  have hS := stepS_fit hw (by omega) hm rfl (by unfold modes; simp) (by decide)
    (sym_step hw hL (X0 b.size om) hR.inv.1.x_eq (by unfold X0; omega) hX4)
  obtain ⟨f1, hw1, hR1, hk1, ag⟩ := next_rel hb hw hR (by rw [hm]; decide) (by rw [hm]; decide) hS
    (hw.reqDec (by unfold X0; omega) hX4 1 15) (reqDecF_keeps _ b.size om f 1 15)
    (fun c hc => by unfold decReqSet at hc; unfold ctl IN X0 at *; omega)
  obtain ⟨v1, v2, v3, v4, v5⟩ := reqDecF_vals f (X0 b.size om) 1 15 (by unfold X0; omega)
  refine ⟨_, f1, hS, hw1, ⟨hR1, ?_, ?_, ?_, ?_, ?_⟩, hk1⟩
  · rw [ag _ (by decide) (by unfold cMODE; omega)]; exact v1
  · rw [ag _ (by unfold X0; omega) (by unfold X0 L0; omega)]; simpa using v2
  · rw [ag _ (by unfold X0; omega) (by unfold X0 L0; omega)]; simpa using v3
  · rw [ag _ (by unfold X0; omega) (by unfold X0 L0; omega)]; exact v4
  · rw [ag _ (by unfold X0; omega) (by unfold X0 L0; omega)]; exact v5

theorem lenx_next {b : Array Nat} {om : Nat} {lit : Bool} {σ : Store} {p : Int} {f : Int → Int} {st : St}
    (hb : ∀ x ∈ b, x < 256) (hw : World σ p (L0 b.size om) f) (hR : Rel b om lit f st) (hm : f cMODE = mLENX) :
    ∃ σ1 f1, stepS p σ = some σ1 ∧ World σ1 p (L0 b.size om) f1 ∧ DecReady b om lit f1 st 2 mDSTD ∧
      f1 cPEND = f cPEND + f cACC ∧ Keeps (L0 b.size om) f f1 (fun c => c = 5 ∨ decReqSet b.size om c) := by
  have hL : 2080 ≤ L0 b.size om := by unfold L0; omega
  have hX4 : X0 b.size om + 4 < L0 b.size om := by unfold X0 L0; omega
  have hS := stepS_fit hw (by omega) hm rfl (by unfold modes; simp) (by decide)
    (lenx_step hw hL (X0 b.size om) (f cACC) (f cPEND) hR.inv.1.x_eq (by unfold X0; omega) hX4 rfl rfl)
  have hg := (hw.store (i := 5) (v := f cPEND + f cACC) (by norm_num) (by omega)).reqDec (X := X0 b.size om)
    (by unfold X0; omega) hX4 2 17
  have hk : Keeps (L0 b.size om) f (reqDecF (Function.update f 5 (f cPEND + f cACC)) (X0 b.size om) 2 17)
      (fun c => c = 5 ∨ decReqSet b.size om c) := fun c h0 h1 hc => by
    rw [reqDecF_keeps _ b.size om _ 2 17 c h0 h1 (fun h => hc (Or.inr h)), upd_eq _ _ (fun h => hc (Or.inl h))]
  obtain ⟨f1, hw1, hR1, hk1, ag⟩ := next_rel hb hw hR (by rw [hm]; decide) (by rw [hm]; decide) hS hg hk
    (fun c hc => by unfold decReqSet at hc; unfold ctl IN X0 at *; omega)
  obtain ⟨v1, v2, v3, v4, v5⟩ := reqDecF_vals (Function.update f 5 (f cPEND + f cACC)) (X0 b.size om) 2 17
    (by unfold X0; omega)
  refine ⟨_, f1, hS, hw1, ⟨hR1, ?_, ?_, ?_, ?_, ?_⟩, ?_, hk1⟩
  · rw [ag _ (by decide) (by unfold cMODE; omega)]; exact v1
  · rw [ag _ (by unfold X0; omega) (by unfold X0 L0; omega)]; simpa using v2
  · rw [ag _ (by unfold X0; omega) (by unfold X0 L0; omega)]; simpa using v3
  · rw [ag _ (by unfold X0; omega) (by unfold X0 L0; omega)]; exact v4
  · rw [ag _ (by unfold X0; omega) (by unfold X0 L0; omega)]; exact v5
  · rw [ag _ (by decide) (by unfold cPEND; omega)]
    simp only [reqDecF, cPEND]
    rw [upd_eq _ _ (by decide), upd_eq _ _ (by unfold X0; omega), upd_eq _ _ (by unfold X0; omega),
      upd_eq _ _ (by unfold X0; omega), upd_eq _ _ (by unfold X0; omega)]
    simp

/-- A `READ`-K request's result: k = 0 is the return mode with acc 0 (S's `bits 0`), else a READ world. -/
def KReady (f : Int → Int) (K : Nat) (rt : Int) : Prop :=
  (K = 0 → f cMODE = rt ∧ f cACC = 0) ∧
  (K ≠ 0 → f cMODE = mREAD ∧ f cK = K ∧ f cACC = 0 ∧ f cWT = 1 ∧ f cRET = rt)

theorem reqKF_ready (g : Int → Int) (K : Nat) (rt : Int) : KReady (reqKF g K rt) K rt := by
  unfold KReady reqKF
  refine ⟨fun h => ?_, fun h => ?_⟩
  · subst h; simp [cMODE, cACC, Function.update_apply]
  · rw [if_neg (by exact_mod_cast h)]; exact reqF_vals g K rt

theorem reqKF_keeps (L : Nat) (g : Int → Int) (k rt : Int) :
    Keeps L g (reqKF g k rt) (fun c => c = 0 ∨ (2068 ≤ c ∧ c ≤ 2071)) := fun c h0 h1 hc => by
  unfold reqKF; split_ifs
  · rw [upd_eq _ _ (by omega), upd_eq _ _ (by omega)]
  · exact reqF_keeps L g k rt c h0 h1 hc

/-- `bits K` from a `KReady` world, K possibly 0. -/
theorem bitsK_sim {b : Array Nat} {om : Nat} {lit : Bool} {p : Int} (hb : ∀ x ∈ b, x < 256) (K : Nat) (rt : Int)
    (Q Q' : (Int → Int) → St → Prop) (hQ0 : ∀ f st, Q f st → Q' f st)
    (hQ : ∀ f st f' st', Q f st → Keeps (L0 b.size om) f f' rdSet → st'.out = st.out → st.pos < st'.pos →
      st.pos < 8 * b.size → Q' f' st') :
    Sim b om p (bits K) (fun f st => (Rel b om lit f st ∧ KReady f K rt) ∧ Q f st)
      (fun a f' st' => Rel b om lit f' st' ∧ f' cMODE = rt ∧ f' cACC = a ∧ Q' f' st') := by
  cases K with
  | zero =>
    exact Sim.pure (fun f st ⟨⟨hR, hk0, _⟩, hq⟩ => ⟨hR, (hk0 rfl).1, by rw [(hk0 rfl).2]; rfl, hQ0 f st hq⟩)
  | succ K =>
    exact (bits_sim' hb K rt Q Q' hQ).mono (fun f st ⟨⟨hR, _, hk⟩, hq⟩ => by
      obtain ⟨a1, a2, a3, a4, a5⟩ := hk (by omega)
      exact ⟨⟨hR, a1, by rw [a2]; push_cast; ring, a3, a4, a5⟩, hq⟩) (fun _ _ _ h => h)

def symdSet (n om : Nat) (m : Nat) (c : Int) : Prop :=
  c = 0 ∨ c = 3 ∨ c = 5 ∨ c = 14 ∨ (2068 ≤ c ∧ c ≤ 2071) ∨ c = IN + n + m

/-- **SYMD, one step**, by the decoded symbol s. -/
theorem symd_next {b : Array Nat} {om : Nat} {lit : Bool} {σ : Store} {p : Int} {f : Int → Int} {st : St}
    (hb : ∀ x ∈ b, x < 256) (hw : World σ p (L0 b.size om) f) (hR : Rel b om lit f st) (hm : f cMODE = mSYMD)
    (s : Nat) (hs : f (X0 b.size om + 4) = s) :
    ∃ σ1 f1, stepS p σ = some σ1 ∧ World σ1 p (L0 b.size om) f1 ∧ Keeps (L0 b.size om) f f1 (symdSet b.size om st.out.size) ∧
      (s < 256 → st.out.size = om → f1 cMODE = mREJECT) ∧
      (s < 256 → st.out.size ≠ om → Rel b om lit f1 ⟨st.pos, st.out.push s⟩ ∧ f1 cMODE = mSYM) ∧
      (s = 256 → Rel b om lit f1 st ∧ f1 cMODE = endMode (f cBF)) ∧
      (256 < s → s ≤ 285 → Rel b om lit f1 st ∧ f1 cPEND = LBASE.getD (s - 257) 0 ∧
        KReady f1 (LEXTRA.getD (s - 257) 0) mLENX) ∧
      (285 < s → f1 cMODE = mREJECT) := by
  have hL : 2080 ≤ L0 b.size om := by unfold L0; omega
  have hi := hR.inv
  have hXL : X0 b.size om + 134 < L0 b.size om := by unfold X0 L0; omega
  have hmm := hR.m
  have hmr := hi.1.m_rng
  obtain ⟨rLB, rLE, -, -⟩ := hi.1.roVal
  have hs288 := hi.2.sym (Or.inl hm)
  rw [hs] at hs288
  set m : Int := (st.out.size : Int) with hmd
  set lb := f (X0 b.size om + 16 + ((s : Int) - 257)) with hlbd
  set le := f (X0 b.size om + 45 + ((s : Int) - 257)) with hled
  have hS := stepS_fit hw (by omega) hm rfl (by unfold modes; simp) (by decide)
    (symd_step hw hL (X0 b.size om) s m om b.size (f cBF) lb le hi.1.x_eq (by unfold X0; omega) hXL hs hmm hi.1.om_eq
      hi.1.n_eq rfl (fun _ h2 => ⟨by omega, by unfold L0; omega⟩) rfl rfl)
  set g : Int → Int := if (s : Int) < 256 then (if m = om then Function.update (Function.update f 14 4) 0 99
      else Function.update (Function.update (Function.update f (2080 + b.size + m) s) 3 (m + 1)) 0 13)
    else if (s : Int) = 256 then Function.update f 0 (if f cBF = 1 then 98 else 1)
    else if (s : Int) ≤ 285 then reqKF (Function.update f 5 lb) le 16
    else Function.update (Function.update f 14 8) 0 99 with hgd
  have hg : World ⟨symdH σ.H p s m om b.size (f cBF) lb le, σ.R⟩ p (L0 b.size om) g := by
    rw [hgd]
    by_cases h1 : (s : Int) < 256
    · by_cases h2 : m = om
      · simp only [symdH, if_pos h1, if_pos h2]
        exact (hw.store (i := 14) (by norm_num) (by omega)).store (i := 0) (by norm_num) (by omega)
      · simp only [symdH, if_pos h1, if_neg h2]
        exact ((hw.store (i := 2080 + b.size + m) (by omega) (by unfold L0; omega)).store (i := 3) (by norm_num)
          (by omega)).store (i := 0) (by norm_num) (by omega)
    · by_cases h3 : (s : Int) = 256
      · simp only [symdH, if_neg h1, if_pos h3]
        exact hw.store (i := 0) (by norm_num) (by omega)
      · by_cases h4 : (s : Int) ≤ 285
        · simp only [symdH, if_neg h1, if_neg h3, if_pos h4]
          exact (hw.store (i := 5) (v := lb) (by norm_num) (by omega)).reqK (by omega) le 16
        · simp only [symdH, if_neg h1, if_neg h3, if_neg h4]
          exact (hw.store (i := 14) (by norm_num) (by omega)).store (i := 0) (by norm_num) (by omega)
  have hk : Keeps (L0 b.size om) f g (symdSet b.size om st.out.size) := fun c h0 h1 hc => by
    unfold symdSet IN at hc
    rw [hgd]
    by_cases hA : (s : Int) < 256
    · by_cases hB : m = om
      · simp only [if_pos hA, if_pos hB]; rw [upd_eq _ _ (by omega), upd_eq _ _ (by omega)]
      · simp only [if_pos hA, if_neg hB]; rw [upd_eq _ _ (by omega), upd_eq _ _ (by omega), upd_eq _ _ (by omega)]
    · by_cases hC : (s : Int) = 256
      · simp only [if_neg hA, if_pos hC]; rw [upd_eq _ _ (by omega)]
      · by_cases hD : (s : Int) ≤ 285
        · simp only [if_neg hA, if_neg hC, if_pos hD]
          rw [reqKF_keeps _ _ le 16 c h0 h1 (by omega), upd_eq _ _ (by omega)]
        · simp only [if_neg hA, if_neg hC, if_neg hD]; rw [upd_eq _ _ (by omega), upd_eq _ _ (by omega)]
  obtain ⟨f1, hw1, hi1, ag⟩ := step_to hb hw hi (by rw [hm]; decide) (by rw [hm]; decide) hS hg
  have hk1 : Keeps (L0 b.size om) f f1 (symdSet b.size om st.out.size) := fun c h0 h1 hc => (ag c h0 h1).trans (hk c h0 h1 hc)
  have a0 := ag 0 (by norm_num) (by omega)
  refine ⟨_, f1, hS, hw1, hk1, fun h1 h2 => ?_, fun h1 h2 => ?_, fun h1 => ?_, fun h1 h2 => ?_, fun h1 => ?_⟩
  · simp only [cMODE]; rw [a0, hgd, if_pos (by exact_mod_cast h1), if_pos (by rw [hmd, h2])]; simp [mREJECT]
  · have hne : m ≠ om := by rw [hmd]; exact_mod_cast h2
    have hlt : st.out.size < om := by omega
    have eg : g = Function.update (Function.update (Function.update f (2080 + b.size + m) s) 3 (m + 1)) 0 13 := by
      rw [hgd, if_pos (by exact_mod_cast h1), if_neg hne]
    rw [eg] at ag
    refine ⟨⟨hi1, ?_, ?_, ?_, ?_⟩, ?_⟩
    · intro v i hv hi7 hl
      rw [hk1 _ (by unfold BT; omega) (by unfold BT L0; omega) (by unfold symdSet BT IN; omega)]
      exact hR.bits v i hv hi7 hl
    · rw [hk1 _ (by decide) (by unfold cBY L0; omega) (by unfold symdSet cBY IN; omega),
        hk1 _ (by decide) (by unfold cBI L0; omega) (by unfold symdSet cBI IN; omega)]
      exact hR.pos
    · rw [ag _ (by decide) (by unfold cM; omega)]; simp [cM, hmd]
    · intro i hi2
      simp only [Array.size_push] at hi2
      by_cases hlt' : i < st.out.size
      · rw [hk1 _ (by unfold IN; omega) (by unfold IN L0; push_cast; omega) (by unfold symdSet IN; omega), hR.out i hlt']
        simp [Array.getD, hlt', Array.getElem_push, show i < st.out.size + 1 by omega]
      · have hie : i = st.out.size := by omega
        subst hie
        rw [ag _ (by unfold IN; omega) (by unfold IN L0; push_cast; omega)]
        simp only [IN, Function.update_apply]
        rw [if_neg (by omega), if_neg (by omega), if_pos (by rw [hmd])]
        simp [Array.getD]
    · simp only [cMODE]; rw [a0, eg]; simp [mSYM]
  · have eg : g = Function.update f 0 (if f cBF = 1 then 98 else 1) := by
      rw [hgd, if_neg (by rw [h1]; norm_num), if_pos (by rw [h1]; norm_num)]
    have hkg : Keeps (L0 b.size om) f f1 (fun c => c = 0) := fun c h0 h1 hc => by
      rw [ag c h0 h1, eg, upd_eq _ _ hc]
    refine ⟨hR.of_keeps hi1 hkg (fun c hc => by unfold ctl; omega), ?_⟩
    simp only [cMODE]; rw [a0, eg]; simp [endMode, mDONE, mHDR]
  · have eg : g = reqKF (Function.update f 5 lb) le 16 := by
      rw [hgd, if_neg (by push_cast; omega), if_neg (by push_cast; omega), if_pos (by push_cast; omega)]
    have hlb : lb = LBASE.getD (s - 257) 0 := by
      rw [hlbd, show (s : Int) - 257 = ((s - 257 : Nat) : Int) by omega]; exact rLB _ (by omega)
    have hle : le = LEXTRA.getD (s - 257) 0 := by
      rw [hled, show (s : Int) - 257 = ((s - 257 : Nat) : Int) by omega]; exact rLE _ (by omega)
    rw [hle] at eg
    have hkg : Keeps (L0 b.size om) f f1 (fun c => c = 0 ∨ c = 5 ∨ (2068 ≤ c ∧ c ≤ 2071)) := fun c h0 h1 hc => by
      rw [ag c h0 h1, eg, reqKF_keeps _ _ _ 16 c h0 h1 (by omega), upd_eq _ _ (by omega)]
    refine ⟨hR.of_keeps hi1 hkg (fun c hc => by unfold ctl IN; omega), ?_, ?_⟩
    · rw [ag _ (by decide) (by unfold cPEND; omega), eg, ← hlb]
      unfold reqKF; split_ifs
      · simp [cPEND, Function.update_apply]
      · rw [reqF_eq _ _ _ _ (by unfold cPEND; omega)]; simp [cPEND]
    · have r := reqKF_ready (Function.update f 5 lb) (LEXTRA.getD (s - 257) 0) 16
      have e : ∀ c : Int, 0 ≤ c → c < L0 b.size om → f1 c = reqKF (Function.update f 5 lb) (LEXTRA.getD (s - 257) 0) 16 c :=
        fun c h0 h1 => by rw [ag c h0 h1, eg]
      unfold KReady at r ⊢
      simp only [cMODE, cACC, cK, cWT, cRET] at r ⊢
      rw [e 0 (by norm_num) (by omega), e 2069 (by norm_num) (by omega), e 2068 (by norm_num) (by omega),
        e 2070 (by norm_num) (by omega), e 2071 (by norm_num) (by omega)]
      exact r
  · simp only [cMODE]
    rw [a0, hgd, if_neg (by push_cast; omega), if_neg (by push_cast; omega), if_neg (by push_cast; omega)]; simp [mREJECT]

theorem dbase_pos : ∀ d, d < 30 → 1 ≤ DBASE.getD d 0 := by decide

/-- **DSTD, one step**, by the decoded distance symbol d. -/
theorem dstd_next {b : Array Nat} {om : Nat} {lit : Bool} {σ : Store} {p : Int} {f : Int → Int} {st : St}
    (hb : ∀ x ∈ b, x < 256) (hw : World σ p (L0 b.size om) f) (hR : Rel b om lit f st) (hm : f cMODE = mDSTD)
    (d : Nat) (hd : f (X0 b.size om + 4) = d) :
    ∃ σ1 f1, stepS p σ = some σ1 ∧ World σ1 p (L0 b.size om) f1 ∧
      (30 ≤ d → f1 cMODE = mREJECT) ∧
      (d < 30 → Rel b om lit f1 st ∧ f1 cDIST = DBASE.getD d 0 ∧ KReady f1 (DEXTRA.getD d 0) mDSTX ∧
        Keeps (L0 b.size om) f f1 (fun c => c = 0 ∨ c = 6 ∨ (2068 ≤ c ∧ c ≤ 2071))) := by
  have hL : 2080 ≤ L0 b.size om := by unfold L0; omega
  have hi := hR.inv
  have hXL : X0 b.size om + 134 < L0 b.size om := by unfold X0 L0; omega
  obtain ⟨-, -, rDB, rDE⟩ := hi.1.roVal
  have hs288 := hi.2.sym (Or.inr (Or.inl hm))
  rw [hd] at hs288
  set db := f (X0 b.size om + 74 + d) with hdbd
  set de := f (X0 b.size om + 104 + d) with hded
  have hS := stepS_fit hw (by omega) hm rfl (by unfold modes; simp) (by decide)
    (dstd_step hw hL (X0 b.size om) d db de hi.1.x_eq (by unfold X0; omega) hXL hd (by omega) rfl rfl)
  by_cases h30 : (30 : Int) ≤ d
  · rw [if_pos h30] at hS
    have hg := (hw.store (i := 14) (v := 9) (by norm_num) (by omega)).store (i := 0) (v := 99) (by norm_num) (by omega)
    exact ⟨_, _, hS, hg, fun _ => by simp [cMODE, mREJECT], fun h => absurd h (by omega)⟩
  · rw [if_neg h30] at hS
    have hdb : db = DBASE.getD d 0 := rDB d (by omega)
    have hde : de = DEXTRA.getD d 0 := rDE d (by omega)
    have hg := (hw.store (i := 6) (v := db) (by norm_num) (by omega)).reqK (by omega) de 18
    have hk : Keeps (L0 b.size om) f (reqKF (Function.update f 6 db) de 18)
        (fun c => c = 0 ∨ c = 6 ∨ (2068 ≤ c ∧ c ≤ 2071)) := fun c h0 h1 hc => by
      rw [reqKF_keeps _ _ de 18 c h0 h1 (by omega), upd_eq _ _ (by omega)]
    obtain ⟨f1, hw1, hR1, hk1, ag⟩ := next_rel hb hw hR (by rw [hm]; decide) (by rw [hm]; decide) hS hg hk
      (fun c hc => by unfold ctl IN; omega)
    refine ⟨_, f1, hS, hw1, fun h => absurd h (by omega), fun _ => ⟨hR1, ?_, ?_, hk1⟩⟩
    · rw [ag _ (by decide) (by unfold cDIST; omega), ← hdb]
      unfold reqKF; split_ifs
      · simp [cDIST, Function.update_apply]
      · rw [reqF_eq _ _ _ _ (by unfold cDIST; omega)]; simp [cDIST]
    · have r := reqKF_ready (Function.update f 6 db) (DEXTRA.getD d 0) 18
      rw [← hde] at r
      unfold KReady at r ⊢
      simp only [cMODE, cACC, cK, cWT, cRET] at r ⊢
      rw [ag 0 (by norm_num) (by omega), ag 2069 (by norm_num) (by omega), ag 2068 (by norm_num) (by omega),
        ag 2070 (by norm_num) (by omega), ag 2071 (by norm_num) (by omega)]
      rw [hde] at r ⊢
      exact r

/-- **DSTX, one step:** S7's two checks in S7's order, then COPY. -/
theorem dstx_next {b : Array Nat} {om : Nat} {lit : Bool} {σ : Store} {p : Int} {f : Int → Int} {st : St}
    (hb : ∀ x ∈ b, x < 256) (hw : World σ p (L0 b.size om) f) (hR : Rel b om lit f st) (hm : f cMODE = mDSTX) :
    ∃ σ1 f1, stepS p σ = some σ1 ∧ World σ1 p (L0 b.size om) f1 ∧
      (f cM < f cDIST + f cACC → f1 cMODE = mREJECT) ∧
      (¬ f cM < f cDIST + f cACC → f cOUTMAX < f cM + f cPEND → f1 cMODE = mREJECT) ∧
      (¬ f cM < f cDIST + f cACC → ¬ f cOUTMAX < f cM + f cPEND → Rel b om lit f1 st ∧ f1 cMODE = mCOPY ∧
        f1 cDIST = f cDIST + f cACC ∧ Keeps (L0 b.size om) f f1 (fun c => c = 0 ∨ c = 6)) := by
  have hL : 2080 ≤ L0 b.size om := by unfold L0; omega
  have hS := stepS_fit hw (by omega) hm rfl (by unfold modes; simp) (by decide)
    (dstx_step hw hL (f cACC) (f cDIST) (f cM) (f cPEND) (f cOUTMAX) rfl rfl rfl rfl rfl)
  by_cases h1 : f cM < f cDIST + f cACC
  · rw [if_pos h1] at hS
    have hg := (hw.store (i := 14) (v := 10) (by norm_num) (by omega)).store (i := 0) (v := 99) (by norm_num) (by omega)
    exact ⟨_, _, hS, hg, fun _ => by simp [cMODE, mREJECT], fun h => absurd h1 h, fun h => absurd h1 h⟩
  · rw [if_neg h1] at hS
    by_cases h2 : f cOUTMAX < f cM + f cPEND
    · rw [if_pos h2] at hS
      have hg := (hw.store (i := 14) (v := 4) (by norm_num) (by omega)).store (i := 0) (v := 99) (by norm_num) (by omega)
      exact ⟨_, _, hS, hg, fun h => absurd h h1, fun _ _ => by simp [cMODE, mREJECT], fun _ h => absurd h2 h⟩
    · rw [if_neg h2] at hS
      have hg := (hw.store (i := 6) (v := f cDIST + f cACC) (by norm_num) (by omega)).store (i := 0) (v := 19)
        (by norm_num) (by omega)
      have hk : Keeps (L0 b.size om) f (Function.update (Function.update f 6 (f cDIST + f cACC)) 0 19)
          (fun c => c = 0 ∨ c = 6) := fun c _ _ hc => by rw [upd_eq _ _ (by omega), upd_eq _ _ (by omega)]
      obtain ⟨f1, hw1, hR1, hk1, ag⟩ := next_rel hb hw hR (by rw [hm]; decide) (by rw [hm]; decide) hS hg hk
        (fun c hc => by unfold ctl IN; omega)
      refine ⟨_, f1, hS, hw1, fun h => absurd h h1, fun _ h => absurd h h2, fun _ _ => ⟨hR1, ?_, ?_, hk1⟩⟩
      · rw [ag _ (by decide) (by unfold cMODE; omega)]; simp [cMODE, mCOPY]
      · rw [ag _ (by decide) (by unfold cDIST; omega)]; simp [cDIST, Function.update_apply]

def copySet (n om : Nat) (c : Int) : Prop := c = 0 ∨ c = 3 ∨ c = 5 ∨ (IN + n ≤ c ∧ c < IN + n + om)

theorem copyBack_size (d : Nat) : ∀ k (o : Array Nat), (copyBack d k o).size = o.size + k
  | 0, o => rfl
  | k + 1, o => by rw [copyBack, copyBack_size d k]; simp; omega

/-- **COPY to its end:** k bytes, each `o[m − dist]`, exactly S7's `copyBack`, then SYM. -/
theorem copy_run {b : Array Nat} {om : Nat} {lit : Bool} {p : Int} (hb : ∀ x ∈ b, x < 256) (d : Nat) (hd1 : 1 ≤ d) :
    ∀ (k : Nat) (σ : Store) (f : Int → Int) (st : St), World σ p (L0 b.size om) f → Rel b om lit f st →
      f cMODE = mCOPY → f cPEND = k → f cDIST = d → d ≤ st.out.size → st.out.size + k ≤ om →
      ∃ σ' f', Reach p σ σ' ∧ World σ' p (L0 b.size om) f' ∧ Rel b om lit f' ⟨st.pos, copyBack d k st.out⟩ ∧
        f' cMODE = mSYM ∧ Keeps (L0 b.size om) f f' (copySet b.size om) := by
  have hL : 2080 ≤ L0 b.size om := by unfold L0; omega
  intro k
  induction k with
  | zero =>
    intro σ f st hw hR hm hk hd hdm hom
    have hS := stepS_fit hw (by omega) hm rfl (by unfold modes; simp) (by decide) (copy_end hw hL (by simpa using hk))
    have hg := hw.store (i := 0) (v := 13) (by norm_num) (by omega)
    obtain ⟨f1, hw1, hR1, hk1, ag⟩ := next_rel hb hw hR (by rw [hm]; decide) (by rw [hm]; decide) hS hg
      (S := fun c => c = 0) (fun c _ _ hc => upd_eq _ _ hc) (fun c hc => by unfold ctl; omega)
    refine ⟨_, f1, Reach.step hS, hw1, by simpa [copyBack] using hR1, ?_, fun c h0 h1 hc => hk1 c h0 h1
      (fun h => hc (by unfold copySet; omega))⟩
    rw [ag _ (by decide) (by unfold cMODE; omega)]; simp [cMODE, mSYM]
  | succ k ih =>
    intro σ f st hw hR hm hk hd hdm hom
    have hi := hR.inv
    have hmm := hR.m
    set m := st.out.size with hmd
    have hy := hR.out (m - d) (by omega)
    have hS := stepS_fit hw (by omega) hm rfl (by unfold modes; simp) (by decide)
      (copy_byte hw hL (f cPEND) b.size m d (st.out.getD (m - d) 0) rfl (by rw [hk]; omega) hi.1.n_eq hmm hd
        (by omega) (by unfold L0; omega) (by simp only [IN] at hy; rw [← hy]; congr 1; omega) (by omega)
        (by unfold L0; omega))
    set y : Int := ((st.out.getD (m - d) 0 : Nat) : Int) with hyd
    set g := Function.update (Function.update (Function.update f (2080 + b.size + m) y) 3 (m + 1)) 5 (f cPEND - 1)
      with hgd
    have hg : World _ p (L0 b.size om) g :=
      ((hw.store (i := 2080 + b.size + m) (by omega) (by unfold L0; omega)).store (i := 3) (by norm_num)
        (by omega)).store (i := 5) (by norm_num) (by omega)
    obtain ⟨f1, hw1, hi1, ag⟩ := step_to hb hw hi (by rw [hm]; decide) (by rw [hm]; decide) hS hg
    have kf : Keeps (L0 b.size om) f f1 (fun c => c = 2080 + b.size + m ∨ c = 3 ∨ c = 5) := fun c h0 h1 hc => by
      rw [ag c h0 h1, hgd, upd_eq _ _ (by omega), upd_eq _ _ (by omega), upd_eq _ _ (by omega)]
    have hR1 : Rel b om lit f1 ⟨st.pos, st.out.push (st.out.getD (st.out.size - d) 0)⟩ := by
      refine ⟨hi1, ?_, ?_, ?_, ?_⟩
      · intro v i hv hi7 hl
        rw [kf _ (by unfold BT; omega) (by unfold BT L0; omega) (by unfold BT; omega)]; exact hR.bits v i hv hi7 hl
      · rw [kf _ (by decide) (by unfold cBY L0; omega) (by unfold cBY; omega),
          kf _ (by decide) (by unfold cBI L0; omega) (by unfold cBI; omega)]; exact hR.pos
      · rw [ag _ (by decide) (by unfold cM; omega)]; simp [hgd, cM, hmd]
      · intro i hi2
        simp only [Array.size_push] at hi2
        by_cases hlt : i < m
        · have hlt' : i < st.out.size := hlt
          rw [kf _ (by unfold IN; omega) (by unfold IN L0; push_cast; omega) (by unfold IN; omega), hR.out i hlt']
          simp [Array.getD, hlt', Array.getElem_push, show i < st.out.size + 1 by omega]
        · have hie : i = m := by omega
          subst hie
          rw [ag _ (by unfold IN; omega) (by unfold IN L0; push_cast; omega)]
          simp only [IN, hgd, Function.update_apply]
          rw [if_neg (by omega), if_neg (by omega)]
          simp [Array.getD, hyd, hmd]
    have hm1 : f1 cMODE = mCOPY := by rw [kf _ (by decide) (by unfold cMODE; omega) (by unfold cMODE; omega)]; exact hm
    have hk1 : f1 cPEND = k := by
      rw [ag _ (by decide) (by unfold cPEND; omega)]; simp only [hgd, cPEND, Function.update_self]
      rw [show (5 : Int) = cPEND from rfl, hk]; push_cast; ring
    have hd1' : f1 cDIST = d := by rw [kf _ (by decide) (by unfold cDIST; omega) (by unfold cDIST; omega)]; exact hd
    obtain ⟨σ', f', hR', hw', hRel, hmo, hk'⟩ := ih _ f1 _ hw1 hR1 hm1 hk1 hd1' (by simp; omega) (by simp; omega)
    refine ⟨σ', f', (Reach.step hS).trans hR', hw', by simpa [copyBack] using hRel, hmo, fun c h0 h1 hc => ?_⟩
    rw [hk' c h0 h1 hc, kf c h0 h1 (by unfold copySet IN at hc; omega)]

/-- `decode (assign lens)` from a decode request, in the triple form, with a frame predicate. -/
theorem decode_Sim {b : Array Nat} {om : Nat} {lit : Bool} {p : Int} (hb : ∀ x ∈ b, x < 256) (lens : Array Nat)
    (tg rt : Int) (Q Q' : (Int → Int) → St → Prop)
    (hQ : ∀ f st f' st', Q f st → Keeps (L0 b.size om) f f' (decSet b.size om) → st.pos < st'.pos →
      st.pos < 8 * b.size → Q' f' st') :
    Sim b om p (decode (assign lens)) (fun f st => (DecReady b om lit f st tg rt ∧ TblRel b.size om f tg lens) ∧ Q f st)
      (fun s f' st' => Rel b om lit f' st' ∧ f' cMODE = rt ∧ f' (X0 b.size om + 4) = s ∧ Q' f' st') := by
  rintro σ f st hw ⟨⟨⟨hR, hm, hl, hv, ht, hrt⟩, hT⟩, hq⟩
  rw [← ht] at hT
  have := decode_sim (lit := lit) hb lens 15 1 0 σ f st (by norm_num) hw hR hm hl hv hT
  refine ⟨fun s st' h => ?_, this.2⟩
  obtain ⟨σ', f', hR', hw', hR'', hm', hs', hk'⟩ := this.1 s st' h
  obtain ⟨hlt, hin⟩ := adv_decode (assign lens) ⟨b, om⟩ st s st' h
  exact ⟨σ', f', hR', hw', hR'', by rw [hm', hrt], hs', hQ f st f' st' hq hk' hlt hin⟩

theorem decSet_frame {n om : Nat} {f f' : Int → Int} {lensL lensD : Array Nat} (hk : Keeps (L0 n om) f f' (decSet n om))
    (h1 : TblRel n om f 1 lensL) (h2 : TblRel n om f 2 lensD) :
    TblRel n om f' 1 lensL ∧ TblRel n om f' 2 lensD ∧ ∀ c : Int, 3 ≤ c → c < 20 → f' c = f c :=
  ⟨h1.keep (by norm_num) hk (decSet_out _ _), h2.keep (by norm_num) hk (decSet_out _ _),
    fun c h0 h1 => hk c (by omega) (by unfold L0; omega) (by unfold decSet X0; omega)⟩

theorem rdSet_frame {n om : Nat} {f f' : Int → Int} {lensL lensD : Array Nat} (hk : Keeps (L0 n om) f f' rdSet)
    (h1 : TblRel n om f 1 lensL) (h2 : TblRel n om f 2 lensD) :
    TblRel n om f' 1 lensL ∧ TblRel n om f' 2 lensD ∧ ∀ c : Int, 3 ≤ c → c < 20 → f' c = f c :=
  ⟨h1.keep (by norm_num) hk (fun c h => by unfold rdSet at h; unfold tbase LB0; omega),
    h2.keep (by norm_num) hk (fun c h => by unfold rdSet at h; unfold tbase LB0; omega),
    fun c h0 h1 => hk c (by omega) (by unfold L0; omega) (by unfold rdSet; omega)⟩

/-- The loop's frame: BFINAL, both tables, and the unread-bits bound. -/
def HFrame (n om : Nat) (bf : Int) (lensL lensD : Array Nat) (F : Nat) (f : Int → Int) (st : St) : Prop :=
  f cBF = bf ∧ TblRel n om f 1 lensL ∧ TblRel n om f 2 lensD ∧ 8 * n - st.pos < F

theorem HFrame.of_keeps {n om : Nat} {bf : Int} {lensL lensD : Array Nat} {F : Nat} {f f' : Int → Int} {st st' : St}
    {S : Int → Prop} (h : HFrame n om bf lensL lensD F f st) (hk : Keeps (L0 n om) f f' S)
    (hS : ∀ c, S c → c ≠ 4 ∧ (c < tbase n om 0 ∨ X0 n om ≤ c)) (hp : st.pos ≤ st'.pos) :
    HFrame n om bf lensL lensD F f' st' :=
  ⟨by rw [hk cBF (by decide) (by unfold cBF L0; omega) (fun hc => (hS _ hc).1 rfl)]; exact h.1,
    h.2.1.keep (by norm_num) hk (fun c hc => (hS c hc).2), h.2.2.1.keep (by norm_num) hk (fun c hc => (hS c hc).2),
    by have := h.2.2.2; omega⟩

theorem symdSet_out {n om : Nat} (m : Nat) (hm : m ≤ om) (c : Int) (h : symdSet n om m c) :
    c ≠ 4 ∧ (c < tbase n om 0 ∨ X0 n om ≤ c) := by
  unfold symdSet IN at h; unfold tbase LB0 X0; omega

/-- **S7's loop is simulated** (S-18's `huffLoop` row): from SYM, with both tables related to their lengths. -/
theorem huff_sim {b : Array Nat} {om : Nat} {lit : Bool} {p : Int} (hb : ∀ x ∈ b, x < 256) (bf : Int)
    (lensL lensD : Array Nat) :
    ∀ fuel, Sim b om p (huffLoop (assign lensL) (assign lensD) fuel)
      (fun f st => (Rel b om lit f st ∧ f cMODE = mSYM) ∧ HFrame b.size om bf lensL lensD fuel f st)
      (fun _ f st => Rel b om lit f st ∧ f cMODE = endMode bf) := by
  have hL : 2080 ≤ L0 b.size om := by unfold L0; omega
  intro fuel
  induction fuel with
  | zero => rintro σ f st hw ⟨_, _, _, _, h⟩; omega
  | succ fuel ih =>
    simp only [huffLoop]
    refine Sim.step (pre' := fun f st => (DecReady b om lit f st 1 mSYMD ∧ TblRel b.size om f 1 lensL) ∧
      HFrame b.size om bf lensL lensD (fuel + 1) f st) ?_ ?_
    · rintro σ f st hw ⟨⟨hR, hm⟩, hF⟩
      obtain ⟨σ1, f1, hS, hw1, hD, hk⟩ := sym_next hb hw hR hm
      have hF1 := hF.of_keeps (st' := st) hk (fun c hc => by unfold decReqSet at hc; unfold tbase LB0 X0 at *; omega) le_rfl
      exact ⟨σ1, f1, hS, hw1, ⟨hD, hF1.2.1⟩, hF1⟩
    refine Sim.bind (decode_Sim hb lensL 1 mSYMD (HFrame b.size om bf lensL lensD (fuel + 1))
      (HFrame b.size om bf lensL lensD fuel) (fun f st f' st' hq hk hlt hin => ?_)) (fun s => ?_)
    · have := hq.of_keeps (st' := st') hk (fun c hc => ⟨by unfold decSet X0 at hc; omega, decSet_out _ _ c hc⟩) hlt.le
      exact ⟨this.1, this.2.1, this.2.2.1, by have := hq.2.2.2; omega⟩
    refine Sim.step (pre' := fun f st => HFrame b.size om bf lensL lensD fuel f st ∧
        (s < 256 → st.out.size = om → f cMODE = mREJECT) ∧
        (s < 256 → st.out.size ≠ om → Rel b om lit f ⟨st.pos, st.out.push s⟩ ∧ f cMODE = mSYM) ∧
        (s = 256 → Rel b om lit f st ∧ f cMODE = endMode bf) ∧
        (256 < s → s ≤ 285 → Rel b om lit f st ∧ f cPEND = LBASE.getD (s - 257) 0 ∧
          KReady f (LEXTRA.getD (s - 257) 0) mLENX) ∧
        (285 < s → f cMODE = mREJECT)) ?_ ?_
    · rintro σ f st hw ⟨hR, hm, hs, hF⟩
      have hmr : st.out.size ≤ om := by have := hR.m; have := hR.inv.1.m_rng; omega
      obtain ⟨σ1, f1, hS, hw1, hk, a1, a2, a3, a4, a5⟩ := symd_next hb hw hR hm s hs
      have hF1 := hF.of_keeps (st' := st) hk (symdSet_out _ hmr) le_rfl
      exact ⟨σ1, f1, hS, hw1, hF1, a1, a2, fun h => by rw [← hF.1]; exact a3 h, a4, a5⟩
    refine Sim.ite (fun h1 => ?_) (fun h1 => Sim.ite (fun h2 => ?_) (fun h2 => Sim.ite (fun h3 => ?_) (fun h3 => ?_)))
    · -- a literal
      refine Sim.read (Sim.get (fun s0 => Sim.ite (fun ho => Sim.reject_bind ?_) (fun ho => ?_)))
      · rintro σ f st hw ⟨⟨_, a1, _⟩, rfl⟩
        exact ⟨σ, f, Reach.refl p σ, hw, a1 h1 ho⟩
      refine Sim.bind (mid := fun _ f st => (Rel b om lit f st ∧ f cMODE = mSYM) ∧
        HFrame b.size om bf lensL lensD fuel f st) (Sim.set' ?_) (fun _ => ih)
      rintro σ f st hw ⟨⟨hF, _, a2, _⟩, rfl⟩
      obtain ⟨hR1, hm1⟩ := a2 h1 ho
      exact ⟨σ, f, Reach.refl p σ, hw, ⟨hR1, hm1⟩, hF⟩
    · -- the end of the block
      exact Sim.pure (fun f st ⟨_, _, _, a3, _⟩ => a3 h2)
    · -- a length
      have hs1 : 256 < s := by omega
      refine Sim.bind (bitsK_sim (lit := lit) hb (LEXTRA.getD (s - 257) 0) mLENX
        (fun f st => HFrame b.size om bf lensL lensD fuel f st ∧ f cPEND = LBASE.getD (s - 257) 0)
        (fun f st => HFrame b.size om bf lensL lensD fuel f st ∧ f cPEND = LBASE.getD (s - 257) 0)
        (fun _ _ h => h) (fun f st f' st' hq hk _ hlt _ => ⟨hq.1.of_keeps hk
          (fun c hc => by unfold rdSet at hc; unfold tbase LB0 X0; omega) hlt.le,
          by rw [hk cPEND (by decide) (by unfold cPEND L0; omega) (by unfold rdSet cPEND; omega)]; exact hq.2⟩) |>.mono
        (fun f st ⟨hF, _, _, _, a4, _⟩ => ⟨⟨(a4 hs1 h3).1, (a4 hs1 h3).2.2⟩, hF, (a4 hs1 h3).2.1⟩)
        (fun _ _ _ h => h)) (fun x => ?_)
      refine Sim.step (pre' := fun f st => (DecReady b om lit f st 2 mDSTD ∧ TblRel b.size om f 2 lensD) ∧
        (HFrame b.size om bf lensL lensD fuel f st ∧ f cPEND = LBASE.getD (s - 257) 0 + x)) ?_ ?_
      · rintro σ f st hw ⟨hR, hm, ha, hF, hp⟩
        obtain ⟨σ1, f1, hS, hw1, hD, hp1, hk⟩ := lenx_next hb hw hR hm
        have hF1 := hF.of_keeps (st' := st) hk (fun c hc => by simp only [decReqSet, X0] at hc; unfold tbase LB0 X0; omega)
          le_rfl
        exact ⟨σ1, f1, hS, hw1, ⟨hD, hF1.2.2.1⟩, hF1, by rw [hp1, hp, ha]⟩
      refine Sim.bind (decode_Sim hb lensD 2 mDSTD
        (fun f st => HFrame b.size om bf lensL lensD fuel f st ∧ f cPEND = LBASE.getD (s - 257) 0 + x)
        (fun f st => HFrame b.size om bf lensL lensD fuel f st ∧ f cPEND = LBASE.getD (s - 257) 0 + x)
        (fun f st f' st' hq hk hlt _ => ⟨hq.1.of_keeps hk (fun c hc => ⟨by unfold decSet X0 at hc; omega,
          decSet_out _ _ c hc⟩) hlt.le,
          by rw [hk cPEND (by decide) (by unfold cPEND L0; omega) (by unfold decSet X0 cPEND; omega)]; exact hq.2⟩))
        (fun d => ?_)
      refine Sim.step (pre' := fun f st => (30 ≤ d → f cMODE = mREJECT) ∧
        (d < 30 → (Rel b om lit f st ∧ KReady f (DEXTRA.getD d 0) mDSTX) ∧ (HFrame b.size om bf lensL lensD fuel f st ∧
          f cPEND = LBASE.getD (s - 257) 0 + x ∧ f cDIST = DBASE.getD d 0))) ?_ ?_
      · rintro σ f st hw ⟨hR, hm, hd, hF, hp⟩
        obtain ⟨σ1, f1, hS, hw1, r1, r2⟩ := dstd_next hb hw hR hm d hd
        refine ⟨σ1, f1, hS, hw1, r1, fun h => ?_⟩
        obtain ⟨hR1, hd1, hK, hk⟩ := r2 h
        exact ⟨⟨hR1, hK⟩, hF.of_keeps hk (fun c hc => by unfold tbase LB0 X0; omega) le_rfl,
          by rw [hk cPEND (by decide) (by unfold cPEND L0; omega) (by unfold cPEND; omega)]; exact hp, hd1⟩
      refine Sim.ite (fun h30 => Sim.reject_bind (fun σ f st hw ⟨r1, _⟩ => ⟨σ, f, Reach.refl p σ, hw, r1 h30⟩))
        (fun h30 => ?_)
      have hd30 : d < 30 := by omega
      refine Sim.bind ((bitsK_sim (lit := lit) hb (DEXTRA.getD d 0) mDSTX
        (fun f st => HFrame b.size om bf lensL lensD fuel f st ∧ f cPEND = LBASE.getD (s - 257) 0 + x ∧
          f cDIST = DBASE.getD d 0)
        (fun f st => HFrame b.size om bf lensL lensD fuel f st ∧ f cPEND = LBASE.getD (s - 257) 0 + x ∧
          f cDIST = DBASE.getD d 0)
        (fun _ _ h => h) (fun f st f' st' hq hk _ hlt _ => ⟨hq.1.of_keeps hk
          (fun c hc => by unfold rdSet at hc; unfold tbase LB0 X0; omega) hlt.le,
          by rw [hk cPEND (by decide) (by unfold cPEND L0; omega) (by unfold rdSet cPEND; omega)]; exact hq.2.1,
          by rw [hk cDIST (by decide) (by unfold cDIST L0; omega) (by unfold rdSet cDIST; omega)]; exact hq.2.2⟩)).mono
        (fun f st ⟨_, r2⟩ => r2 hd30) (fun _ _ _ h => h)) (fun y => ?_)
      refine Sim.step (pre' := fun f st =>
        (DBASE.getD d 0 + y > st.out.size → f cMODE = mREJECT) ∧
        (¬ DBASE.getD d 0 + y > st.out.size → st.out.size + (LBASE.getD (s - 257) 0 + x) > om → f cMODE = mREJECT) ∧
        (¬ DBASE.getD d 0 + y > st.out.size → ¬ st.out.size + (LBASE.getD (s - 257) 0 + x) > om →
          Rel b om lit f st ∧ f cMODE = mCOPY ∧ f cDIST = (DBASE.getD d 0 + y : Nat) ∧
          f cPEND = (LBASE.getD (s - 257) 0 + x : Nat) ∧ HFrame b.size om bf lensL lensD fuel f st)) ?_ ?_
      · rintro σ f st hw ⟨hR, hm, ha, hF, hp, hdist⟩
        obtain ⟨σ1, f1, hS, hw1, r1, r2, r3⟩ := dstx_next hb hw hR hm
        have hM := hR.m
        have hO := hR.inv.1.om_eq
        refine ⟨σ1, f1, hS, hw1, fun h => r1 (by rw [hM, hdist, ha]; push_cast; omega),
          fun h h' => r2 (by rw [hM, hdist, ha]; push_cast; omega) (by rw [hO, hM, hp]; push_cast; omega),
          fun h h' => ?_⟩
        obtain ⟨hR1, hm1, hd1, hk⟩ := r3 (by rw [hM, hdist, ha]; push_cast; omega) (by rw [hO, hM, hp]; push_cast; omega)
        exact ⟨hR1, hm1, by rw [hd1, hdist, ha]; push_cast; ring,
          by rw [hk cPEND (by decide) (by unfold cPEND L0; omega) (by unfold cPEND; omega), hp]; push_cast; ring,
          hF.of_keeps hk (fun c hc => by unfold tbase LB0 X0; omega) le_rfl⟩
      refine Sim.read (Sim.get (fun s0 => Sim.ite (fun hfar => Sim.reject_bind ?_)
        (fun hfar => Sim.ite (fun hov => Sim.reject_bind ?_) (fun hov => ?_))))
      · rintro σ f st hw ⟨⟨r1, _⟩, rfl⟩
        exact ⟨σ, f, Reach.refl p σ, hw, r1 hfar⟩
      · rintro σ f st hw ⟨⟨_, r2, _⟩, rfl⟩
        exact ⟨σ, f, Reach.refl p σ, hw, r2 hfar hov⟩
      refine Sim.bind (mid := fun _ f st => (Rel b om lit f st ∧ f cMODE = mSYM) ∧
        HFrame b.size om bf lensL lensD fuel f st) (Sim.set' ?_) (fun _ => ih)
      rintro σ f st hw ⟨⟨_, _, r3⟩, rfl⟩
      obtain ⟨hR, hm, hd, hp, hF⟩ := r3 hfar hov
      have hd1 := dbase_pos d hd30
      obtain ⟨σ', f', hR', hw', hRel, hmo, hk⟩ := copy_run hb (DBASE.getD d 0 + y) (by omega)
        (LBASE.getD (s - 257) 0 + x) σ f st hw hR hm hp hd (by omega) (by simp only at hov; omega)
      exact ⟨σ', f', hR', hw', ⟨hRel, hmo⟩, hF.of_keeps hk (fun c hc => by
        have := hR.m; have := hR.inv.1.m_rng
        unfold copySet IN at hc; unfold tbase LB0 X0; omega) le_rfl⟩
    · exact Sim.reject (fun σ f st hw ⟨_, _, _, _, _, a5⟩ => ⟨σ, f, Reach.refl p σ, hw, a5 (by omega)⟩)

/-! ## BUILD (S4's construction, S-10/S-11): ZERO and COUNT need only progress and a frame -/

/-- The cells a BUILD step may write: its own cursor cells and the target table. -/
def bset (tbb : Int) (c : Int) : Prop := c = 0 ∨ c = 12 ∨ c = 13 ∨ c = 14 ∨ (2075 ≤ c ∧ c ≤ 2078) ∨ (tbb ≤ c ∧ c < tbb + 352)

theorem buildInv_of {b : Array Nat} {om : Nat} {lit : Bool} {f : Int → Int} {st : St} (hR : Rel b om lit f st)
    (hm : f cMODE = mBUILD) : buildInv b.size om f := by
  have := hR.inv.2.cur; rw [hm, facts_build] at this; exact this

theorem bset_ctl {n om : Nat} {t : Int} (ht : 0 ≤ t ∧ t ≤ 2) (c : Int) (h : bset (tbase n om t) c) : ctl n om c := by
  unfold bset tbase LB0 at h; unfold ctl IN; omega

theorem build_mem : (mBUILD, buildN) ∈ modes := by unfold modes; simp

/-- **ZERO, to its end.** -/
theorem zero_run {b : Array Nat} {om : Nat} {lit : Bool} {p : Int} (hb : ∀ x ∈ b, x < 256) :
    ∀ (r : Nat) (σ : Store) (f : Int → Int) (st : St), World σ p (L0 b.size om) f → Rel b om lit f st →
      f cMODE = mBUILD → f cPHASE = 0 → 16 - f cINDEX = r →
      ∃ σ' f', Reach p σ σ' ∧ World σ' p (L0 b.size om) f' ∧ Rel b om lit f' st ∧ f' cMODE = mBUILD ∧
        f' cPHASE = 1 ∧ f' cINDEX = 0 ∧ Keeps (L0 b.size om) f f' (bset (f (X0 b.size om + 7))) := by
  have hL : 2080 ≤ L0 b.size om := by unfold L0; omega
  have hXL : X0 b.size om + 8 < L0 b.size om := by unfold X0 L0; omega
  intro r
  induction r with
  | zero =>
    intro σ f st hw hR hm hph hr
    have hB := buildInv_of hR hm
    obtain ⟨ht0, ht2, htb, -, hz, -, -, -, -⟩ := hB
    have hj := (hz hph).2.1
    have hS := stepS_fit hw (by omega) hm rfl build_mem (by decide)
      (build_zero_end hw hL (f cINDEX) (X0 b.size om) (f (X0 b.size om + 7)) hph rfl hR.inv.1.x_eq rfl
        (by unfold X0; omega) hXL (by omega))
    have hg := (hw.store (i := 12) (v := 1) (by norm_num) (by omega)).store (i := 13) (v := 0) (by norm_num) (by omega)
    obtain ⟨f1, hw1, hR1, hk1, ag⟩ := next_rel hb hw hR (by rw [hm]; decide) (by rw [hm]; decide) hS hg
      (S := fun c => c = 12 ∨ c = 13) (fun c _ _ hc => by rw [upd_eq _ _ (by omega), upd_eq _ _ (by omega)])
      (fun c hc => by unfold ctl; omega)
    refine ⟨_, f1, Reach.step hS, hw1, hR1, ?_, ?_, ?_, fun c h0 h1 hc => hk1 c h0 h1 (fun h => hc (by unfold bset; omega))⟩
    · rw [hk1 _ (by decide) (by unfold cMODE; omega) (by unfold cMODE; omega)]; exact hm
    · rw [ag _ (by decide) (by unfold cPHASE; omega)]; simp [cPHASE, Function.update_apply]
    · rw [ag _ (by decide) (by unfold cINDEX; omega)]; simp [cINDEX]
  | succ r ih =>
    intro σ f st hw hR hm hph hr
    have hB := buildInv_of hR hm
    obtain ⟨ht0, ht2, htb, -, hz, -, -, -, -⟩ := hB
    have hj := (hz hph).1
    set tbb := f (X0 b.size om + 7) with htbbd
    have htL : tbb + 352 ≤ L0 b.size om := by rw [htb]; unfold tbase LB0 L0; omega
    have ht0' : 0 ≤ tbb := by rw [htb]; unfold tbase LB0; omega
    have hS := stepS_fit hw (by omega) hm rfl build_mem (by decide)
      (build_zero_cell hw hL (f cINDEX) (X0 b.size om) tbb hph rfl hR.inv.1.x_eq rfl
        (by unfold X0; omega) hXL hj (by omega) ht0' htL)
    have hg := (hw.store (i := tbb + f cINDEX) (v := 0) (by omega) (by omega)).store (i := 13) (v := f cINDEX + 1)
      (by norm_num) (by omega)
    obtain ⟨f1, hw1, hR1, hk1, ag⟩ := next_rel hb hw hR (by rw [hm]; decide) (by rw [hm]; decide) hS hg
      (S := fun c => c = tbb + f cINDEX ∨ c = 13) (fun c _ _ hc => by rw [upd_eq _ _ (by omega), upd_eq _ _ (by omega)])
      (fun c hc => by rw [htb] at hc; unfold ctl IN; unfold tbase LB0 at hc; omega)
    have hm1 : f1 cMODE = mBUILD := by rw [hk1 _ (by decide) (by unfold cMODE; omega) (by unfold cMODE; rw [htb]; unfold tbase LB0; omega)]; exact hm
    have hp1 : f1 cPHASE = 0 := by rw [hk1 _ (by decide) (by unfold cPHASE; omega) (by unfold cPHASE; rw [htb]; unfold tbase LB0; omega)]; exact hph
    have hj1 : f1 cINDEX = f cINDEX + 1 := by rw [ag _ (by decide) (by unfold cINDEX; omega)]; simp [cINDEX]
    have ht1 : f1 (X0 b.size om + 7) = tbb := by
      rw [hk1 _ (by unfold X0; omega) (by unfold X0 L0; omega) (by rw [htb]; unfold tbase LB0 X0; omega)]
    obtain ⟨σ', f', hR', hw', hR'', hm', hp', hj', hk'⟩ := ih _ f1 st hw1 hR1 hm1 hp1 (by rw [hj1]; omega)
    rw [ht1] at hk'
    have hk1' : Keeps (L0 b.size om) f f1 (bset tbb) := fun c h0 h1 hc => hk1 c h0 h1 (fun h => hc (by unfold bset; omega))
    exact ⟨σ', f', (Reach.step hS).trans hR', hw', hR'', hm', hp', hj', hk1'.trans hk' (fun c h => h)⟩

/-- BUILD's source and size, from `buildInv`: the source lies inside the lengths area. -/
theorem build_src {n om : Nat} {f : Int → Int} (hB : buildInv n om f) (hhl : 0 ≤ f cHLIT) :
    LB0 n om ≤ f (X0 n om + 5) ∧ 0 ≤ f (X0 n om + 6) ∧ f (X0 n om + 5) + f (X0 n om + 6) ≤ LB0 n om + 337 ∧
      0 ≤ f cTGT ∧ f cTGT ≤ 2 ∧ f (X0 n om + 7) = tbase n om (f cTGT) := by
  obtain ⟨ht0, ht2, htb, hd, -⟩ := hB
  refine ⟨?_, ?_, ?_, ht0, ht2, htb⟩ <;> rcases hd with ⟨_, h1, h2, h3, h4, _⟩ | ⟨_, h1, h2, h3, h4⟩ | ⟨_, h1, h2, h3, h4, _⟩ <;>
    (unfold LB0 at *; omega)

/-- **COUNT, to its end.** -/
theorem count_run {b : Array Nat} {om : Nat} {lit : Bool} {p : Int} (hb : ∀ x ∈ b, x < 256) :
    ∀ (r : Nat) (σ : Store) (f : Int → Int) (st : St), World σ p (L0 b.size om) f → Rel b om lit f st →
      f cMODE = mBUILD → f cPHASE = 1 → f (X0 b.size om + 6) - f cINDEX = r →
      ∃ σ' f', Reach p σ σ' ∧ World σ' p (L0 b.size om) f' ∧ Rel b om lit f' st ∧ f' cMODE = mBUILD ∧
        f' cPHASE = 2 ∧ f' cINDEX = 1 ∧ f' cCODE = 0 ∧ Keeps (L0 b.size om) f f' (bset (f (X0 b.size om + 7))) := by
  have hL : 2080 ≤ L0 b.size om := by unfold L0; omega
  have hXL : X0 b.size om + 8 < L0 b.size om := by unfold X0 L0; omega
  intro r
  induction r with
  | zero =>
    intro σ f st hw hR hm hph hr
    have hB := buildInv_of hR hm
    obtain ⟨hsb0, hnn0, hsbn, ht0, ht2, htb⟩ := build_src hB hR.inv.1.hdr_rng.1
    set tbb := f (X0 b.size om + 7) with htbbd
    have htL : tbb + 352 ≤ L0 b.size om := by rw [htb]; unfold tbase LB0 L0; omega
    have ht0' : 0 ≤ tbb := by rw [htb]; unfold tbase LB0; omega
    have hS := stepS_fit hw (by omega) hm rfl build_mem (by decide)
      (build_count_end hw hL (f cINDEX) (X0 b.size om) tbb _ _ hph rfl hR.inv.1.x_eq rfl rfl rfl
        (by unfold X0; omega) hXL (by omega) ht0' htL)
    have hg := ((((hw.store (i := 12) (v := 2) (by norm_num) (by omega)).store (i := 13) (v := 1) (by norm_num)
      (by omega)).store (i := 2075) (v := 0) (by norm_num) (by omega)).store (i := tbb + 16) (v := 0) (by omega)
      (by omega)).store (i := tbb + 32) (v := 0) (by omega) (by omega)
    obtain ⟨f1, hw1, hR1, hk1, ag⟩ := next_rel hb hw hR (by rw [hm]; decide) (by rw [hm]; decide) hS hg
      (S := bset tbb) (fun c _ _ hc => by
        unfold bset at hc
        rw [upd_eq _ _ (by omega), upd_eq _ _ (by omega), upd_eq _ _ (by omega), upd_eq _ _ (by omega),
          upd_eq _ _ (by omega)])
      (fun c hc => bset_ctl ⟨ht0, ht2⟩ c (htb ▸ hc))
    refine ⟨_, f1, Reach.step hS, hw1, hR1, ?_, ?_, ?_, ?_, hk1⟩
    · rw [ag _ (by decide) (by unfold cMODE; omega)]; simp only [cMODE, Function.update_apply]
      split_ifs <;> first | omega | exact hm
    · rw [ag _ (by decide) (by unfold cPHASE; omega)]; simp only [cPHASE, Function.update_apply]
      rw [if_neg (by rw [htb]; unfold tbase LB0; omega), if_neg (by rw [htb]; unfold tbase LB0; omega)]; simp
    · rw [ag _ (by decide) (by unfold cINDEX; omega)]; simp only [cINDEX, Function.update_apply]
      rw [if_neg (by rw [htb]; unfold tbase LB0; omega), if_neg (by rw [htb]; unfold tbase LB0; omega)]; simp
    · rw [ag _ (by decide) (by unfold cCODE; omega)]; simp only [cCODE, Function.update_apply]
      rw [if_neg (by rw [htb]; unfold tbase LB0; omega), if_neg (by rw [htb]; unfold tbase LB0; omega)]; simp
  | succ r ih =>
    intro σ f st hw hR hm hph hr
    have hB := buildInv_of hR hm
    obtain ⟨hsb0, hnn0, hsbn, ht0, ht2, htb⟩ := build_src hB hR.inv.1.hdr_rng.1
    have hj := (hB.2.2.2.2.2.1 hph).1
    set tbb := f (X0 b.size om + 7) with htbbd
    set sb := f (X0 b.size om + 5) with hsbd
    set j := f cINDEX with hjd
    have htL : tbb + 352 ≤ L0 b.size om := by rw [htb]; unfold tbase LB0 L0; omega
    have ht0' : 0 ≤ tbb := by rw [htb]; unfold tbase LB0; omega
    have hlr := hR.inv.1.lens (sb + j - LB0 b.size om) (by omega) (by omega)
    simp only [LB0] at hlr
    rw [show 2080 + (b.size : Int) + om + (sb + j - (2080 + b.size + om)) = sb + j by ring] at hlr
    set l := f (sb + j) with hld
    have hS := stepS_fit hw (by omega) hm rfl build_mem (by decide)
      (build_count_cell hw hL j (X0 b.size om) tbb sb _ l (f (tbb + l)) hph rfl hR.inv.1.x_eq rfl rfl rfl
        (by unfold X0; omega) hXL (by omega) (by unfold LB0 at hsb0; omega) (by unfold LB0 L0 at *; omega) rfl ht0' htL
        hlr.1 hlr.2 rfl)
    have cont : ∀ σ1 f1, stepS p σ = some σ1 → World σ1 p (L0 b.size om) f1 → Rel b om lit f1 st →
        Keeps (L0 b.size om) f f1 (fun c => c = 13 ∨ c = tbb + l) → f1 cINDEX = j + 1 →
        ∃ σ' f', Reach p σ σ' ∧ World σ' p (L0 b.size om) f' ∧ Rel b om lit f' st ∧ f' cMODE = mBUILD ∧
          f' cPHASE = 2 ∧ f' cINDEX = 1 ∧ f' cCODE = 0 ∧ Keeps (L0 b.size om) f f' (bset tbb) := by
      intro σ1 f1 hS1 hw1 hR1 hk1 hj1
      have nb : ∀ c : Int, (c = 0 ∨ c = 12 ∨ (2072 ≤ c ∧ c < 2080) ∨ X0 b.size om ≤ c) → c < L0 b.size om → f1 c = f c :=
        fun c h1 h2 => hk1 c (by unfold X0 at h1; omega) h2 (by rw [htb]; unfold tbase LB0 X0 at *; omega)
      have hm1 : f1 cMODE = mBUILD := by rw [nb _ (by unfold cMODE; omega) (by unfold cMODE; omega)]; exact hm
      have hp1 : f1 cPHASE = 1 := by rw [nb _ (by unfold cPHASE; omega) (by unfold cPHASE; omega)]; exact hph
      have ht1 : f1 (X0 b.size om + 7) = tbb := nb _ (by omega) (by unfold X0 L0; omega)
      have hn1 : f1 (X0 b.size om + 6) = f (X0 b.size om + 6) := nb _ (by omega) (by unfold X0 L0; omega)
      obtain ⟨σ', f', hR', hw', hR'', hm', hp', hj', hc', hk'⟩ := ih _ f1 st hw1 hR1 hm1 hp1 (by rw [hj1, hn1]; omega)
      rw [ht1] at hk'
      have hk1' : Keeps (L0 b.size om) f f1 (bset tbb) := fun c h0 h1 hc =>
        hk1 c h0 h1 (fun h => hc (by unfold bset; omega))
      exact ⟨σ', f', (Reach.step hS1).trans hR', hw', hR'', hm', hp', hj', hc', hk1'.trans hk' (fun c h => h)⟩
    by_cases h0 : l = 0
    · rw [if_pos h0] at hS
      have hg := hw.store (i := 13) (v := j + 1) (by norm_num) (by omega)
      obtain ⟨f1, hw1, hR1, hk1, ag⟩ := next_rel hb hw hR (by rw [hm]; decide) (by rw [hm]; decide) hS hg
        (S := fun c => c = 13 ∨ c = tbb + l) (fun c _ _ hc => by rw [upd_eq _ _ (by omega)])
        (fun c hc => by rw [htb] at hc; unfold ctl IN; unfold tbase LB0 at hc; omega)
      exact cont _ f1 hS hw1 hR1 hk1 (by rw [ag _ (by decide) (by unfold cINDEX; omega)]; simp [cINDEX])
    · rw [if_neg h0] at hS
      have hg := (hw.store (i := tbb + l) (v := f (tbb + l) + 1) (by omega) (by omega)).store (i := 13) (v := j + 1)
        (by norm_num) (by omega)
      obtain ⟨f1, hw1, hR1, hk1, ag⟩ := next_rel hb hw hR (by rw [hm]; decide) (by rw [hm]; decide) hS hg
        (S := fun c => c = 13 ∨ c = tbb + l) (fun c _ _ hc => by rw [upd_eq _ _ (by omega), upd_eq _ _ (by omega)])
        (fun c hc => by rw [htb] at hc; unfold ctl IN; unfold tbase LB0 at hc; omega)
      exact cont _ f1 hS hw1 hR1 hk1 (by rw [ag _ (by decide) (by unfold cINDEX; omega)]; simp [cINDEX])

/-! ## BUILD's NEXT phase: the first codes -/

/-- S4's `next_code` recurrence, over any counts. -/
def ncode (c : Nat → Int) : Nat → Int
  | 0 => 0
  | k + 1 => 2 * (ncode c k + c k)

/-- **NEXT, to j = 16:** `first[ℓ]` is `ncode` over the table's own counts, which NEXT does not touch. -/
theorem next_run {b : Array Nat} {om : Nat} {lit : Bool} {p : Int} (hb : ∀ x ∈ b, x < 256) :
    ∀ (r : Nat) (σ : Store) (f : Int → Int) (st : St) (j : Nat), World σ p (L0 b.size om) f → Rel b om lit f st →
      f cMODE = mBUILD → f cPHASE = 2 → f cINDEX = j → 1 ≤ j → j + r = 16 →
      f cCODE = ncode (fun k => f (f (X0 b.size om + 7) + k)) (j - 1) →
      (∀ l : Nat, 1 ≤ l → l < j → f (f (X0 b.size om + 7) + 16 + l) = ncode (fun k => f (f (X0 b.size om + 7) + k)) l) →
      ∃ σ' f', Reach p σ σ' ∧ World σ' p (L0 b.size om) f' ∧ Rel b om lit f' st ∧ f' cMODE = mBUILD ∧
        f' cPHASE = 2 ∧ f' cINDEX = 16 ∧ f' (X0 b.size om + 7) = f (X0 b.size om + 7) ∧
        (∀ k : Nat, k < 16 → f' (f (X0 b.size om + 7) + k) = f (f (X0 b.size om + 7) + k)) ∧
        (∀ l : Nat, 1 ≤ l → l ≤ 15 → f' (f (X0 b.size om + 7) + 16 + l) = ncode (fun k => f (f (X0 b.size om + 7) + k)) l) ∧
        Keeps (L0 b.size om) f f' (bset (f (X0 b.size om + 7))) := by
  have hL : 2080 ≤ L0 b.size om := by unfold L0; omega
  have hXL : X0 b.size om + 8 < L0 b.size om := by unfold X0 L0; omega
  intro r
  induction r with
  | zero =>
    intro σ f st j hw hR hm hph hj hj1 hjr hcode hfirst
    refine ⟨σ, f, Reach.refl p σ, hw, hR, hm, hph, by rw [hj]; push_cast; omega, rfl, fun _ _ => rfl,
      fun l h1 h2 => hfirst l h1 (by omega), Keeps.refl _ _ _⟩
  | succ r ih =>
    intro σ f st j hw hR hm hph hj hj1 hjr hcode hfirst
    have hB := buildInv_of hR hm
    obtain ⟨hsb0, hnn0, hsbn, ht0, ht2, htb⟩ := build_src hB hR.inv.1.hdr_rng.1
    set tbb := f (X0 b.size om + 7) with htbbd
    have htL : tbb + 352 ≤ L0 b.size om := by rw [htb]; unfold tbase LB0 L0; omega
    have ht0' : 0 ≤ tbb := by rw [htb]; unfold tbase LB0; omega
    have htbig : 2417 ≤ tbb := by rw [htb]; unfold tbase LB0; omega
    set cf : Nat → Int := fun k => f (tbb + k) with hcf
    set code := f cCODE with hcoded
    set cp := f (tbb + ((j : Int) - 1)) with hcpd
    set op := f (tbb + 32 + ((j : Int) - 1)) with hopd
    have hS := stepS_fit hw (by omega) hm rfl build_mem (by decide)
      (build_next_cell hw hL j (X0 b.size om) tbb code cp op hph hj hR.inv.1.x_eq rfl
        (by unfold X0; omega) hXL (by omega) (by omega) ht0' htL rfl rfl rfl)
    have hg := ((((hw.store (i := 2075) (v := 2 * (code + cp)) (by norm_num) (by omega)).store (i := tbb + 16 + j)
      (v := 2 * (code + cp)) (by omega) (by omega)).store (i := tbb + 32 + j) (v := op + cp) (by omega) (by omega)).store
      (i := tbb + 48 + j) (v := op + cp) (by omega) (by omega)).store (i := 13) (v := j + 1) (by norm_num) (by omega)
    obtain ⟨f1, hw1, hR1, hk1, ag⟩ := next_rel hb hw hR (by rw [hm]; decide) (by rw [hm]; decide) hS hg
      (S := fun c => c = 2075 ∨ c = tbb + 16 + j ∨ c = tbb + 32 + j ∨ c = tbb + 48 + j ∨ c = 13)
      (fun c _ _ hc => by rw [upd_eq _ _ (by omega), upd_eq _ _ (by omega), upd_eq _ _ (by omega), upd_eq _ _ (by omega),
        upd_eq _ _ (by omega)])
      (fun c hc => by rw [htb] at hc; unfold ctl IN; unfold tbase LB0 at hc; omega)
    have nb : ∀ c : Int, 0 ≤ c → c < L0 b.size om → c ≠ 2075 → c ≠ tbb + 16 + j → c ≠ tbb + 32 + j → c ≠ tbb + 48 + j →
        c ≠ 13 → f1 c = f c := fun c h0 h1 a1 a2 a3 a4 a5 => hk1 c h0 h1 (by omega)
    have hm1 : f1 cMODE = mBUILD := by
      rw [nb _ (by decide) (by unfold cMODE; omega) (by decide) (by unfold cMODE; omega) (by unfold cMODE; omega)
        (by unfold cMODE; omega) (by decide)]; exact hm
    have hp1 : f1 cPHASE = 2 := by
      rw [nb _ (by decide) (by unfold cPHASE; omega) (by decide) (by unfold cPHASE; omega) (by unfold cPHASE; omega)
        (by unfold cPHASE; omega) (by decide)]; exact hph
    have ht1 : f1 (X0 b.size om + 7) = tbb := by
      rw [nb _ (by unfold X0; omega) (by unfold X0 L0; omega) (by unfold X0; omega) (by rw [htb]; unfold tbase LB0 X0; omega)
        (by rw [htb]; unfold tbase LB0 X0; omega) (by rw [htb]; unfold tbase LB0 X0; omega) (by unfold X0; omega)]
    have hc1 : ∀ k : Nat, k < 16 → f1 (tbb + k) = f (tbb + k) := fun k hk =>
      nb _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    have hj1' : f1 cINDEX = (j + 1 : Nat) := by rw [ag _ (by decide) (by unfold cINDEX; omega)]; simp [cINDEX]
    have hncode : ∀ l : Nat, l ≤ 16 → ncode (fun k => f1 (f1 (X0 b.size om + 7) + k)) l = ncode cf l := by
      intro l hl
      induction l with
      | zero => rfl
      | succ l ihl => simp only [ncode]; rw [ihl (by omega), ht1, hc1 l (by omega)]
    have hfirstj : f1 (tbb + 16 + j) = ncode cf j := by
      rw [ag _ (by omega) (by omega)]
      simp only [Function.update_apply]
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_true]
      obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
      simp only [ncode]
      rw [show (k + 1 : Nat) - 1 = k by omega] at hcode
      rw [hcode, hcpd]; push_cast; simp [hcf]
    have hcode1 : f1 cCODE = ncode cf j := by
      rw [ag _ (by decide) (by unfold cCODE; omega)]
      simp only [cCODE, Function.update_apply]
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_true]
      obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
      simp only [ncode]
      rw [show (k + 1 : Nat) - 1 = k by omega] at hcode
      rw [hcode, hcpd]; push_cast; simp [hcf]
    obtain ⟨σ', f', hR', hw', hR'', hm', hp', hj', ht', hcs', hfs', hk'⟩ := ih _ f1 st (j + 1) hw1 hR1 hm1 hp1 hj1'
      (by omega) (by omega) (by rw [show j + 1 - 1 = j by omega, hncode j (by omega)]; exact hcode1)
      (fun l h1 h2 => by
        rw [hncode l (by omega), ht1]
        by_cases hl : l = j
        · subst hl; exact hfirstj
        · rw [nb _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
          exact hfirst l h1 (by omega))
    rw [ht1] at ht' hcs' hk'
    have hk1' : Keeps (L0 b.size om) f f1 (bset tbb) := fun c h0 h1 hc => hk1 c h0 h1 (fun h => hc (by unfold bset; omega))
    refine ⟨σ', f', (Reach.step hS).trans hR', hw', hR'', hm', hp', hj', ht', fun k hk => (hcs' k hk).trans
      (hc1 k hk), fun l h1 h2 => ?_, hk1'.trans hk' (fun c h => h)⟩
    have := hfs' l h1 h2
    rw [hncode l (by omega), ht1] at this
    exact this

/-! ## S4's construction, on the spec side: counts and next codes -/

/-- The machine's count over the source cells is S4's `bl_count`, when the source holds the lengths. -/
theorem cnt_eq {f : Int → Int} {sb : Int} {lens : Array Nat} (hs : ∀ j : Nat, j < lens.size → f (sb + j) = lens.getD j 0)
    (l : Nat) : ∀ k, k ≤ lens.size → cnt f sb l k = ((List.range k).filter (fun i => lens.getD i 0 = l)).length := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
    intro hk
    rw [cnt, ih (by omega), List.range_succ, List.filter_append, List.length_append, hs k (by omega)]
    by_cases h : lens.getD k 0 = l
    · rw [if_pos (by exact_mod_cast h)]
      simp only [List.filter_cons, List.filter_nil, h, decide_true, if_true, List.length_singleton]
    · rw [if_neg (by exact_mod_cast h)]
      simp only [List.filter_cons, List.filter_nil, h, decide_false, Bool.false_eq_true, if_false, List.length_nil]

theorem cnt_blCount {f : Int → Int} {sb : Int} {lens : Array Nat} (hs : ∀ j : Nat, j < lens.size → f (sb + j) = lens.getD j 0)
    (l : Nat) (hl : l ≠ 0) : cnt f sb l lens.size = blCount lens l := by
  rw [cnt_eq hs l _ le_rfl, blCount_eq _ _ hl]; rfl

/-- `nextCodes` is the `ncode` recurrence over `bl_count`. -/
theorem nextCodes_ncode (lens : Array Nat) (l : Nat) (hl : l ≤ 15) :
    ((nextCodes lens).getD l 0 : Int) = ncode (fun k => (blCount lens k : Int)) l := by
  have key : ∀ k, k ≤ 15 →
      ((List.range' 1 k).foldl (fun (acc : Nat × Array Nat) l =>
          let c := (acc.1 + blCount lens (l - 1)) <<< 1
          (c, acc.2.push c)) (0, #[0])) =
        (((ncode (fun k => (blCount lens k : Int)) k).toNat),
          ((List.range (k + 1)).map fun i => (ncode (fun k => (blCount lens k : Int)) i).toNat).toArray) := by
    have hnn : ∀ i, 0 ≤ ncode (fun k => (blCount lens k : Int)) i := by
      intro i; induction i with
      | zero => simp [ncode]
      | succ i ih => simp only [ncode]; positivity
    intro k hk
    induction k with
    | zero => simp [ncode]
    | succ k ih =>
      rw [List.range'_concat, List.foldl_append, ih (by omega)]
      simp only [List.foldl_cons, List.foldl_nil, Nat.shiftLeft_eq, pow_one]
      rw [show 1 + 1 * k - 1 = k by omega]
      have e : ((ncode (fun k => (blCount lens k : Int)) k).toNat + blCount lens k) * 2 =
          (ncode (fun k => (blCount lens k : Int)) (k + 1)).toNat := by
        simp only [ncode]
        have := hnn k; omega
      rw [e, List.range_succ (n := k + 1), List.map_append]
      simp
  unfold nextCodes
  rw [key 15 le_rfl]
  simp only
  have hnn : ∀ i, 0 ≤ ncode (fun k => (blCount lens k : Int)) i := by
    intro i; induction i with
    | zero => simp [ncode]
    | succ i ih => simp only [ncode]; positivity
  simp [Array.getD, show l < 16 by omega, Int.toNat_of_nonneg (hnn l)]

/-! ## BUILD's LEFT phase: S4's two checks -/

/-- S4's `left` fold over any counts: `none` is "over-subscribed". -/
def leftF (c : Nat → Int) : Nat → Option Int
  | 0 => some 1
  | k + 1 => match leftF c k with
    | none => none
    | some left => if 2 * left - c (k + 1) < 0 then none else some (2 * left - c (k + 1))

def restS (c : Nat → Int) : Nat → Int
  | 0 => 0
  | k + 1 => restS c k + (if 2 ≤ k + 1 then c (k + 1) else 0)

def totS (c : Nat → Int) : Nat → Int
  | 0 => 0
  | k + 1 => totS c k + c (k + 1)

theorem leftAfter_leftF (lens : Array Nat) : leftAfter lens = leftF (fun l => (blCount lens l : Int)) 15 := by
  have key : ∀ k, (List.range' 1 k).foldl
      (fun (acc : Option Int) l => match acc with
        | none => none
        | some left => let left' := 2 * left - (blCount lens l : Int); if left' < 0 then none else some left')
      (some 1) = leftF (fun l => (blCount lens l : Int)) k := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [List.range'_concat, List.foldl_append, ih]
      simp only [List.foldl_cons, List.foldl_nil, leftF, show 1 + 1 * k = k + 1 by omega]
  exact key 15

theorem leftF_none {c : Nat → Int} : ∀ {j k : Nat}, j ≤ k → leftF c j = none → leftF c k = none := by
  intro j k hjk h
  induction k with
  | zero => have : j = 0 := by omega
            subst this; simp [leftF] at h
  | succ k ih =>
    by_cases hj : j = k + 1
    · subst hj; exact h
    · simp only [leftF, ih (by omega)]

/-- **LEFT, to j = 16, or REJECT at the first negative `left`** (cf: the table's counts, fixed through LEFT). -/
theorem left_run {b : Array Nat} {om : Nat} {lit : Bool} {p : Int} (hb : ∀ x ∈ b, x < 256) (tbb : Int) (cf : Nat → Int) :
    ∀ (r : Nat) (σ : Store) (f : Int → Int) (st : St) (j : Nat), World σ p (L0 b.size om) f → Rel b om lit f st →
      f cMODE = mBUILD → f cPHASE = 3 → f cINDEX = j → 1 ≤ j → j + r = 16 → f (X0 b.size om + 7) = tbb →
      (∀ k : Nat, k < 16 → f (tbb + k) = cf k) →
      leftF cf (j - 1) = some (f cLEFT) → f cREST = restS cf (j - 1) → f cTOTAL = totS cf (j - 1) →
      (leftF cf 15 = none → ∃ σ' f', Reach p σ σ' ∧ World σ' p (L0 b.size om) f' ∧ f' cMODE = mREJECT) ∧
      (∀ v, leftF cf 15 = some v →
        ∃ σ' f', Reach p σ σ' ∧ World σ' p (L0 b.size om) f' ∧ Rel b om lit f' st ∧ f' cMODE = mBUILD ∧
          f' cPHASE = 3 ∧ f' cINDEX = 16 ∧ f' cLEFT = v ∧ f' cREST = restS cf 15 ∧ f' cTOTAL = totS cf 15 ∧
          Keeps (L0 b.size om) f f' (fun c => c = 13 ∨ (2076 ≤ c ∧ c ≤ 2078))) := by
  have hL : 2080 ≤ L0 b.size om := by unfold L0; omega
  have hXL : X0 b.size om + 8 < L0 b.size om := by unfold X0 L0; omega
  intro r
  induction r with
  | zero =>
    intro σ f st j hw hR hm hph hj hj1 hjr htb hcf hl hrs hts
    have hj16 : j = 16 := by omega
    subst hj16
    refine ⟨fun h => by rw [h] at hl; simp at hl, fun v hv => ⟨σ, f, Reach.refl p σ, hw, hR, hm, hph, by rw [hj]; rfl, ?_,
      hrs, hts, Keeps.refl _ _ _⟩⟩
    rw [hv] at hl; exact (Option.some.inj hl).symm
  | succ r ih =>
    intro σ f st j hw hR hm hph hj hj1 hjr htb' hcf hl hrs hts
    have hB := buildInv_of hR hm
    obtain ⟨hsb0, hnn0, hsbn, ht0, ht2, htb⟩ := build_src hB hR.inv.1.hdr_rng.1
    rw [htb'] at htb
    have htL : tbb + 352 ≤ L0 b.size om := by rw [htb]; unfold tbase LB0 L0; omega
    have ht0' : 0 ≤ tbb := by rw [htb]; unfold tbase LB0; omega
    have htbig : 2417 ≤ tbb := by rw [htb]; unfold tbase LB0; omega
    obtain ⟨jj, rfl⟩ : ∃ jj, j = jj + 1 := ⟨j - 1, by omega⟩
    set left := f cLEFT with hleftd
    have hcj : f (tbb + ((jj + 1 : Nat) : Int)) = cf (jj + 1) := hcf (jj + 1) (by omega)
    have hS := stepS_fit hw (by omega) hm rfl build_mem (by decide)
      (build_left_cell hw hL (jj + 1 : Nat) (X0 b.size om) tbb left (f cREST) (f cTOTAL) (cf (jj + 1)) hph hj
        hR.inv.1.x_eq htb' (by unfold X0; omega) hXL (by omega) (by omega) ht0' htL rfl rfl rfl hcj)
    have hl' : leftF cf jj = some left := by simpa using hl
    have hstep : leftF cf (jj + 1) = if 2 * left - cf (jj + 1) < 0 then none else some (2 * left - cf (jj + 1)) := by
      simp only [leftF, hl']
    by_cases hneg : 2 * left - cf (jj + 1) < 0
    · rw [if_pos hneg] at hS
      have hg := (hw.store (i := 14) (v := 5) (by norm_num) (by omega)).store (i := 0) (v := 99) (by norm_num) (by omega)
      have hnone : leftF cf (jj + 1) = none := by rw [hstep, if_pos hneg]
      refine ⟨fun _ => ⟨_, _, Reach.step hS, hg, by simp [cMODE, mREJECT]⟩, fun v hv => ?_⟩
      rw [leftF_none (by omega) hnone] at hv; simp at hv
    · rw [if_neg hneg] at hS
      set g := Function.update (Function.update (Function.update (Function.update f 2076 (2 * left - cf (jj + 1))) 2078
        (f cTOTAL + cf (jj + 1))) 2077 (if 2 ≤ ((jj + 1 : Nat) : Int) then f cREST + cf (jj + 1) else f cREST)) 13
        (((jj + 1 : Nat) : Int) + 1) with hgd
      have hg : World _ p (L0 b.size om) g :=
        (((hw.store (i := 2076) (by norm_num) (by omega)).store (i := 2078) (by norm_num) (by omega)).store (i := 2077)
          (by norm_num) (by omega)).store (i := 13) (by norm_num) (by omega)
      obtain ⟨f1, hw1, hR1, hk1, ag⟩ := next_rel hb hw hR (by rw [hm]; decide) (by rw [hm]; decide) hS hg
        (S := fun c => c = 13 ∨ (2076 ≤ c ∧ c ≤ 2078)) (fun c _ _ hc => by
          rw [hgd, upd_eq _ _ (by omega), upd_eq _ _ (by omega), upd_eq _ _ (by omega), upd_eq _ _ (by omega)])
        (fun c hc => by unfold ctl; omega)
      have nb : ∀ c : Int, 0 ≤ c → c < L0 b.size om → c ≠ 13 → (c < 2076 ∨ 2078 < c) → f1 c = f c :=
        fun c h0 h1 a1 a2 => hk1 c h0 h1 (by omega)
      have hm1 : f1 cMODE = mBUILD := by rw [nb _ (by decide) (by unfold cMODE; omega) (by decide) (by decide)]; exact hm
      have hp1 : f1 cPHASE = 3 := by rw [nb _ (by decide) (by unfold cPHASE; omega) (by decide) (by decide)]; exact hph
      have ht1 : f1 (X0 b.size om + 7) = tbb := by
        rw [nb _ (by unfold X0; omega) (by unfold X0 L0; omega) (by unfold X0; omega) (by unfold X0; omega)]; exact htb'
      have hcf1 : ∀ k : Nat, k < 16 → f1 (tbb + k) = cf k := fun k hk => by
        rw [nb _ (by omega) (by omega) (by omega) (by omega)]; exact hcf k hk
      have hj1' : f1 cINDEX = (jj + 1 + 1 : Nat) := by rw [ag _ (by decide) (by unfold cINDEX; omega)]; simp [hgd, cINDEX]
      have hl1 : f1 cLEFT = 2 * left - cf (jj + 1) := by
        rw [ag _ (by decide) (by unfold cLEFT; omega)]; simp [hgd, cLEFT, Function.update_apply]
      have ht1' : f1 cTOTAL = f cTOTAL + cf (jj + 1) := by
        rw [ag _ (by decide) (by unfold cTOTAL; omega)]; simp [hgd, cTOTAL, Function.update_apply]
      have hr1 : f1 cREST = (if 2 ≤ ((jj + 1 : Nat) : Int) then f cREST + cf (jj + 1) else f cREST) := by
        rw [ag _ (by decide) (by unfold cREST; omega)]; simp [hgd, cREST, Function.update_apply]
      have hsome : leftF cf (jj + 1) = some (f1 cLEFT) := by rw [hstep, if_neg hneg, hl1]
      obtain ⟨hno, hso⟩ := ih _ f1 st (jj + 1 + 1) hw1 hR1 hm1 hp1 hj1' (by omega) (by omega) ht1 hcf1
        (by simpa using hsome)
        (by
          have hrs' : f cREST = restS cf jj := by simpa using hrs
          rw [hr1, show jj + 1 + 1 - 1 = jj + 1 by omega, restS, hrs']
          by_cases h2 : 2 ≤ jj + 1
          · rw [if_pos (by exact_mod_cast h2), if_pos h2]
          · rw [if_neg (by exact_mod_cast h2), if_neg h2]; ring)
        (by
          have hts' : f cTOTAL = totS cf jj := by simpa using hts
          rw [ht1', show jj + 1 + 1 - 1 = jj + 1 by omega, totS, hts'])
      refine ⟨fun h => ?_, fun v hv => ?_⟩
      · obtain ⟨σ', f', hR', hw', hm'⟩ := hno h
        exact ⟨σ', f', (Reach.step hS).trans hR', hw', hm'⟩
      · obtain ⟨σ', f', hR', hw', hR'', hm', hp', hj', hl', hr', ht', hk'⟩ := hso v hv
        have hk1' : Keeps (L0 b.size om) f f1 (fun c => c = 13 ∨ (2076 ≤ c ∧ c ≤ 2078)) := hk1
        exact ⟨σ', f', (Reach.step hS).trans hR', hw', hR'', hm', hp', hj', hl', hr', ht', hk1'.trans hk' (fun c h => h)⟩

/-! ## BUILD's SYMS phase: the symbols, by length then index -/

def filt (lens : Array Nat) (l j : Nat) : List Nat := (List.range j).filter (fun i => lens.getD i 0 = l)

theorem filt_succ (lens : Array Nat) (l j : Nat) :
    filt lens l (j + 1) = filt lens l j ++ (if lens.getD j 0 = l then [j] else []) := by
  unfold filt; rw [List.range_succ, List.filter_append]
  by_cases h : lens.getD j 0 = l
  · rw [if_pos h]; simp only [List.filter_cons, List.filter_nil, h, decide_true, if_true]
  · rw [if_neg h]; simp only [List.filter_cons, List.filter_nil, h, decide_false, Bool.false_eq_true, if_false]

theorem filt_full (lens : Array Nat) (l : Nat) : filt lens l lens.size = symsL lens l := rfl

theorem filt_le (lens : Array Nat) (l : Nat) (hl : l ≠ 0) : ∀ j, j ≤ lens.size → (filt lens l j).length ≤ blCount lens l := by
  intro j hj
  rw [blCount_eq _ _ hl, ← filt_full]
  unfold filt
  rw [show lens.size = j + (lens.size - j) by omega, List.range_add, List.filter_append, List.length_append]
  omega

/-- **SYMS, to j = N:** symbol j goes to `syms[offs[ℓ] + #(earlier symbols of length ℓ)]`. -/
theorem syms_run {b : Array Nat} {om : Nat} {lit : Bool} {p : Int} (hb : ∀ x ∈ b, x < 256) (tbb sb : Int)
    (lens : Array Nat) (o : Nat → Int)
    (hdis : ∀ l l' : Nat, 1 ≤ l → l < l' → l' ≤ 15 → o l + blCount lens l ≤ o l')
    (hob : ∀ l : Nat, 1 ≤ l → l ≤ 15 → 0 ≤ o l ∧ o l + blCount lens l ≤ 288) :
    ∀ (r : Nat) (σ : Store) (f : Int → Int) (st : St) (j : Nat), World σ p (L0 b.size om) f → Rel b om lit f st →
      f cMODE = mBUILD → f cPHASE = 4 → f cINDEX = j → j + r = lens.size →
      f (X0 b.size om + 7) = tbb → f (X0 b.size om + 5) = sb → f (X0 b.size om + 6) = lens.size →
      (∀ i : Nat, i < lens.size → f (sb + i) = lens.getD i 0) →
      (∀ l : Nat, 1 ≤ l → l ≤ 15 → f (tbb + 48 + l) = o l + (filt lens l j).length) →
      (∀ l : Nat, 1 ≤ l → l ≤ 15 → ∀ i (h : i < (filt lens l j).length),
        f (tbb + 64 + o l + i) = (filt lens l j)[i]) →
      ∃ σ' f', Reach p σ σ' ∧ World σ' p (L0 b.size om) f' ∧ Rel b om lit f' st ∧ f' cMODE = mBUILD ∧
        f' cPHASE = 4 ∧ f' cINDEX = lens.size ∧
        (∀ l : Nat, 1 ≤ l → l ≤ 15 → ∀ i (h : i < (filt lens l lens.size).length),
          f' (tbb + 64 + o l + i) = (filt lens l lens.size)[i]) ∧
        Keeps (L0 b.size om) f f' (fun c => c = 13 ∨ (tbb + 48 ≤ c ∧ c < tbb + 352)) := by
  have hL : 2080 ≤ L0 b.size om := by unfold L0; omega
  have hXL : X0 b.size om + 8 < L0 b.size om := by unfold X0 L0; omega
  intro r
  induction r with
  | zero =>
    intro σ f st j hw hR hm hph hj hjr htb hsb hnn hsrc hslot hsyms
    have : j = lens.size := by omega
    subst this
    exact ⟨σ, f, Reach.refl p σ, hw, hR, hm, hph, hj, hsyms, Keeps.refl _ _ _⟩
  | succ r ih =>
    intro σ f st j hw hR hm hph hj hjr htb' hsb hnn hsrc hslot hsyms
    have hB := buildInv_of hR hm
    obtain ⟨hsb0, hnn0, hsbn, ht0, ht2, htb⟩ := build_src hB hR.inv.1.hdr_rng.1
    rw [htb'] at htb
    have htL : tbb + 352 ≤ L0 b.size om := by rw [htb]; unfold tbase LB0 L0; omega
    have htbig : 2417 ≤ tbb := by rw [htb]; unfold tbase LB0; omega
    have hsb0' : LB0 b.size om ≤ sb := hsb ▸ hsb0
    have hsbL : sb + (lens.size : Int) ≤ LB0 b.size om + 337 := by have h := hsbn; rw [hsb, hnn] at h; exact h
    have hsbI : 2080 ≤ sb ∧ sb + (lens.size : Int) < L0 b.size om := by unfold LB0 L0 at *; omega
    have hlr := hR.inv.1.lens (sb + j - LB0 b.size om) (by omega) (by omega)
    simp only [LB0] at hlr
    rw [show 2080 + (b.size : Int) + om + (sb + j - (2080 + b.size + om)) = sb + j by ring, hsrc j (by omega)] at hlr
    set l := lens.getD j 0 with hld
    have hl15 : l ≤ 15 := by omega
    have hcnt : ∀ l' : Nat, l' ≠ 0 → (filt lens l' (j + 1)).length ≤ blCount lens l' := fun l' h => filt_le lens l' h _ (by omega)
    by_cases h0 : l = 0
    · have hS := stepS_fit hw (by omega) hm rfl build_mem (by decide)
        (build_syms_cell hw hL j (X0 b.size om) tbb sb lens.size 0 (f (tbb + 48 + 0)) hph hj hR.inv.1.x_eq htb' hsb hnn
          (by unfold X0; omega) hXL (by omega) (by omega) (by omega) (by rw [hsrc j (by omega), ← hld, h0]; rfl)
          (by omega) htL le_rfl (by norm_num) rfl (fun h => absurd rfl h) (fun h => absurd rfl h))
      simp only [if_true] at hS
      have hg := hw.store (i := 13) (v := (j : Int) + 1) (by norm_num) (by omega)
      obtain ⟨f1, hw1, hR1, hk1, ag⟩ := next_rel hb hw hR (by rw [hm]; decide) (by rw [hm]; decide) hS hg
        (S := fun c => c = 13) (fun c _ _ hc => upd_eq _ _ hc) (fun c hc => by unfold ctl; omega)
      have nb : ∀ c : Int, 0 ≤ c → c < L0 b.size om → c ≠ 13 → f1 c = f c := fun c h0 h1 h => hk1 c h0 h1 h
      have hfs : ∀ l' : Nat, filt lens l' (j + 1) = filt lens l' j ∨ l' = 0 := by
        intro l'; by_cases h : l' = 0
        · exact Or.inr h
        · left; rw [filt_succ, if_neg (by omega), List.append_nil]
      obtain ⟨σ', f', hR', hw', hR'', hm', hp', hj', hsy', hk'⟩ := ih _ f1 st (j + 1) hw1 hR1
        (by rw [nb _ (by decide) (by unfold cMODE; omega) (by decide)]; exact hm)
        (by rw [nb _ (by decide) (by unfold cPHASE; omega) (by decide)]; exact hph)
        (by rw [ag _ (by decide) (by unfold cINDEX; omega)]; simp [cINDEX]) (by omega)
        (by rw [nb _ (by unfold X0; omega) (by unfold X0 L0; omega) (by unfold X0; omega)]; exact htb')
        (by rw [nb _ (by unfold X0; omega) (by unfold X0 L0; omega) (by unfold X0; omega)]; exact hsb)
        (by rw [nb _ (by unfold X0; omega) (by unfold X0 L0; omega) (by unfold X0; omega)]; exact hnn)
        (fun i hi => by rw [nb _ (by omega) (by omega) (by omega)]; exact hsrc i hi)
        (fun l' h1 h2 => by
          rcases hfs l' with he | he
          · rw [he, nb _ (by omega) (by omega) (by omega)]; exact hslot l' h1 h2
          · omega)
        (fun l' h1 h2 i hi => by
          rcases hfs l' with he | he
          · have hob' := hob l' h1 h2
            have := hcnt l' (by omega)
            have hi' : i < (filt lens l' j).length := by rw [← he]; exact hi
            rw [List.getElem_of_eq he hi, nb _ (by rw [he] at this; omega) (by rw [he] at this; omega)
              (by rw [he] at this; omega)]
            exact hsyms l' h1 h2 i hi'
          · omega)
      have hk1' : Keeps (L0 b.size om) f f1 (fun c => c = 13 ∨ (tbb + 48 ≤ c ∧ c < tbb + 352)) :=
        fun c h0 h1 hc => hk1 c h0 h1 (fun h => hc (Or.inl h))
      exact ⟨σ', f', (Reach.step hS).trans hR', hw', hR'', hm', hp', hj', hsy', hk1'.trans hk' (fun c h => h)⟩
    · have hl1 : 1 ≤ l := by omega
      have hfl : filt lens l (j + 1) = filt lens l j ++ [j] := by rw [filt_succ, if_pos rfl]
      have hlen : (filt lens l j).length < blCount lens l := by
        have := hcnt l h0; rw [hfl, List.length_append] at this; simp at this; omega
      set sl := f (tbb + 48 + l) with hsld
      have hsl : sl = o l + (filt lens l j).length := hslot l hl1 hl15
      have hobl := hob l hl1 hl15
      have hS := stepS_fit hw (by omega) hm rfl build_mem (by decide)
        (build_syms_cell hw hL j (X0 b.size om) tbb sb lens.size l sl hph hj hR.inv.1.x_eq htb' hsb hnn
          (by unfold X0; omega) hXL (by omega) (by omega) (by omega) (by rw [hsrc j (by omega)])
          (by omega) htL (by omega) (by omega) rfl (fun _ => by omega) (fun _ => by omega))
      rw [if_neg (by exact_mod_cast h0)] at hS
      have hg := ((hw.store (i := tbb + 64 + sl) (v := (j : Int)) (by omega) (by omega)).store (i := tbb + 48 + l)
        (v := sl + 1) (by omega) (by omega)).store (i := 13) (v := (j : Int) + 1) (by norm_num) (by omega)
      obtain ⟨f1, hw1, hR1, hk1, ag⟩ := next_rel hb hw hR (by rw [hm]; decide) (by rw [hm]; decide) hS hg
        (S := fun c => c = tbb + 64 + sl ∨ c = tbb + 48 + l ∨ c = 13)
        (fun c _ _ hc => by rw [upd_eq _ _ (by omega), upd_eq _ _ (by omega), upd_eq _ _ (by omega)])
        (fun c hc => by rw [htb] at hc; unfold ctl IN; unfold tbase LB0 at hc; omega)
      have nb : ∀ c : Int, 0 ≤ c → c < L0 b.size om → c ≠ tbb + 64 + sl → c ≠ tbb + 48 + l → c ≠ 13 → f1 c = f c :=
        fun c h0 h1 a1 a2 a3 => hk1 c h0 h1 (by omega)
      have hsyN : f1 (tbb + 64 + sl) = j := by
        rw [ag _ (by omega) (by omega)]; simp only [Function.update_apply]
        rw [if_neg (by omega), if_neg (by omega)]; simp
      have hslN : f1 (tbb + 48 + l) = sl + 1 := by
        rw [ag _ (by omega) (by omega)]; simp only [Function.update_apply]
        rw [if_neg (by omega)]; simp
      obtain ⟨σ', f', hR', hw', hR'', hm', hp', hj', hsy', hk'⟩ := ih _ f1 st (j + 1) hw1 hR1
        (by rw [nb _ (by decide) (by unfold cMODE; omega) (by unfold cMODE; omega) (by unfold cMODE; omega) (by decide)]
            exact hm)
        (by rw [nb _ (by decide) (by unfold cPHASE; omega) (by unfold cPHASE; omega) (by unfold cPHASE; omega) (by decide)]
            exact hph)
        (by rw [ag _ (by decide) (by unfold cINDEX; omega)]; simp [cINDEX]) (by omega)
        (by rw [nb _ (by unfold X0; omega) (by unfold X0 L0; omega) (by rw [htb]; unfold tbase LB0 X0; omega)
              (by rw [htb]; unfold tbase LB0 X0; omega) (by unfold X0; omega)]; exact htb')
        (by rw [nb _ (by unfold X0; omega) (by unfold X0 L0; omega) (by rw [htb]; unfold tbase LB0 X0; omega)
              (by rw [htb]; unfold tbase LB0 X0; omega) (by unfold X0; omega)]; exact hsb)
        (by rw [nb _ (by unfold X0; omega) (by unfold X0 L0; omega) (by rw [htb]; unfold tbase LB0 X0; omega)
              (by rw [htb]; unfold tbase LB0 X0; omega) (by unfold X0; omega)]; exact hnn)
        (fun i hi => by
          rw [nb _ (by omega) (by omega) (by rw [htb]; unfold tbase LB0 at *; omega) (by rw [htb]; unfold tbase LB0 at *; omega)
            (by omega)]; exact hsrc i hi)
        (fun l' h1 h2 => by
          by_cases hll : l' = l
          · subst hll; rw [hslN, hsl, hfl]; simp; ring
          · have he : filt lens l' (j + 1) = filt lens l' j := by rw [filt_succ, if_neg (by omega), List.append_nil]
            rw [he, nb _ (by omega) (by omega) (by omega) (by omega) (by omega)]; exact hslot l' h1 h2)
        (fun l' h1 h2 i hi => by
          have hob' := hob l' h1 h2
          by_cases hll : l' = l
          · subst hll
            by_cases hil : i < (filt lens l j).length
            · rw [List.getElem_of_eq hfl hi, List.getElem_append_left hil,
                nb _ (by omega) (by omega) (by rw [hsl]; omega) (by omega) (by omega)]
              exact hsyms l h1 h2 i hil
            · have hie : i = (filt lens l j).length := by rw [hfl] at hi; simp at hi; omega
              subst hie
              rw [List.getElem_of_eq hfl hi, List.getElem_append_right (by omega)]
              simp only [Nat.sub_self, List.getElem_cons_zero]
              rw [show tbb + 64 + o l + ((filt lens l j).length : Int) = tbb + 64 + sl by rw [hsl]; ring]
              exact hsyN
          · have he : filt lens l' (j + 1) = filt lens l' j := by rw [filt_succ, if_neg (by omega), List.append_nil]
            have hi' : i < (filt lens l' j).length := by rw [← he]; exact hi
            have hcb := filt_le lens l' (by omega) j (by omega)
            have hsep : o l' + i < o l ∨ o l + blCount lens l ≤ o l' := by
              rcases Nat.lt_or_gt_of_ne hll with hlt | hgt
              · left; have := hdis l' l h1 hlt hl15; omega
              · right; exact hdis l l' hl1 hgt h2
            rw [List.getElem_of_eq he hi, nb _ (by omega) (by omega) (by rw [hsl]; omega) (by omega) (by omega)]
            exact hsyms l' h1 h2 i hi')
      have hk1' : Keeps (L0 b.size om) f f1 (fun c => c = 13 ∨ (tbb + 48 ≤ c ∧ c < tbb + 352)) :=
        fun c h0 h1 hc => hk1 c h0 h1 (fun h => hc (by omega))
      exact ⟨σ', f', (Reach.step hS).trans hR', hw', hR'', hm', hp', hj', hsy', hk1'.trans hk' (fun c h => h)⟩

/-! ## BUILD's phase ends: NEXT → LEFT or SYMS, and LEFT's incomplete check -/

theorem next_end_next {b : Array Nat} {om : Nat} {lit : Bool} {σ : Store} {p : Int} {f : Int → Int} {st : St}
    (hb : ∀ x ∈ b, x < 256) (hw : World σ p (L0 b.size om) f) (hR : Rel b om lit f st) (hm : f cMODE = mBUILD)
    (hph : f cPHASE = 2) (hj : f cINDEX = 16) :
    ∃ σ1 f1, stepS p σ = some σ1 ∧ World σ1 p (L0 b.size om) f1 ∧ Rel b om lit f1 st ∧ f1 cMODE = mBUILD ∧
      Keeps (L0 b.size om) f f1 (fun c => c = 12 ∨ c = 13 ∨ (2076 ≤ c ∧ c ≤ 2078)) ∧
      (f cCHK = 1 → f1 cPHASE = 3 ∧ f1 cINDEX = 1 ∧ f1 cLEFT = 1 ∧ f1 cREST = 0 ∧ f1 cTOTAL = 0) ∧
      (f cCHK ≠ 1 → f1 cPHASE = 4 ∧ f1 cINDEX = 0) := by
  have hL : 2080 ≤ L0 b.size om := by unfold L0; omega
  have hXL : X0 b.size om + 8 < L0 b.size om := by unfold X0 L0; omega
  have hS := stepS_fit hw (by omega) hm rfl build_mem (by decide)
    (build_next_end hw hL 16 (X0 b.size om) (f (X0 b.size om + 7)) (f cCHK) hph hj hR.inv.1.x_eq rfl
      (by unfold X0; omega) hXL (by norm_num) rfl)
  by_cases hc : f cCHK = 1
  · rw [if_pos hc] at hS
    have hg := ((((hw.store (i := 12) (v := 3) (by norm_num) (by omega)).store (i := 13) (v := 1) (by norm_num)
      (by omega)).store (i := 2076) (v := 1) (by norm_num) (by omega)).store (i := 2077) (v := 0) (by norm_num)
      (by omega)).store (i := 2078) (v := 0) (by norm_num) (by omega)
    obtain ⟨f1, hw1, hR1, hk1, ag⟩ := next_rel hb hw hR (by rw [hm]; decide) (by rw [hm]; decide) hS hg
      (S := fun c => c = 12 ∨ c = 13 ∨ (2076 ≤ c ∧ c ≤ 2078)) (fun c _ _ hc => by
        rw [upd_eq _ _ (by omega), upd_eq _ _ (by omega), upd_eq _ _ (by omega), upd_eq _ _ (by omega),
          upd_eq _ _ (by omega)]) (fun c hc => by unfold ctl; omega)
    refine ⟨_, f1, hS, hw1, hR1, by rw [hk1 _ (by decide) (by unfold cMODE; omega) (by unfold cMODE; omega)]; exact hm,
      hk1, fun _ => ⟨?_, ?_, ?_, ?_, ?_⟩, fun h => absurd hc h⟩
    · rw [ag _ (by decide) (by unfold cPHASE; omega)]; simp [cPHASE, Function.update_apply]
    · rw [ag _ (by decide) (by unfold cINDEX; omega)]; simp [cINDEX, Function.update_apply]
    · rw [ag _ (by decide) (by unfold cLEFT; omega)]; simp [cLEFT, Function.update_apply]
    · rw [ag _ (by decide) (by unfold cREST; omega)]; simp [cREST, Function.update_apply]
    · rw [ag _ (by decide) (by unfold cTOTAL; omega)]; simp [cTOTAL, Function.update_apply]
  · rw [if_neg hc] at hS
    have hg := (hw.store (i := 12) (v := 4) (by norm_num) (by omega)).store (i := 13) (v := 0) (by norm_num) (by omega)
    obtain ⟨f1, hw1, hR1, hk1, ag⟩ := next_rel hb hw hR (by rw [hm]; decide) (by rw [hm]; decide) hS hg
      (S := fun c => c = 12 ∨ c = 13 ∨ (2076 ≤ c ∧ c ≤ 2078)) (fun c _ _ hc => by
        rw [upd_eq _ _ (by omega), upd_eq _ _ (by omega)]) (fun c hc => by unfold ctl; omega)
    refine ⟨_, f1, hS, hw1, hR1, by rw [hk1 _ (by decide) (by unfold cMODE; omega) (by unfold cMODE; omega)]; exact hm,
      hk1, fun h => absurd h hc, fun _ => ⟨?_, ?_⟩⟩
    · rw [ag _ (by decide) (by unfold cPHASE; omega)]; simp [cPHASE, Function.update_apply]
    · rw [ag _ (by decide) (by unfold cINDEX; omega)]; simp [cINDEX, Function.update_apply]

theorem left_end_next {b : Array Nat} {om : Nat} {lit : Bool} {σ : Store} {p : Int} {f : Int → Int} {st : St}
    (hb : ∀ x ∈ b, x < 256) (hw : World σ p (L0 b.size om) f) (hR : Rel b om lit f st) (hm : f cMODE = mBUILD)
    (hph : f cPHASE = 3) (hj : f cINDEX = 16) :
    ∃ σ1 f1, stepS p σ = some σ1 ∧ World σ1 p (L0 b.size om) f1 ∧
      (0 < f cLEFT ∧ bExempt (f (X0 b.size om + 8)) (f (f (X0 b.size om + 7) + 1)) (f cREST) (f cTOTAL) ≠ 1 →
        f1 cMODE = mREJECT) ∧
      (¬ (0 < f cLEFT ∧ bExempt (f (X0 b.size om + 8)) (f (f (X0 b.size om + 7) + 1)) (f cREST) (f cTOTAL) ≠ 1) →
        Rel b om lit f1 st ∧ f1 cMODE = mBUILD ∧ f1 cPHASE = 4 ∧ f1 cINDEX = 0 ∧
        Keeps (L0 b.size om) f f1 (fun c => c = 12 ∨ c = 13)) := by
  have hL : 2080 ≤ L0 b.size om := by unfold L0; omega
  have hXL : X0 b.size om + 8 < L0 b.size om := by unfold X0 L0; omega
  have hB := buildInv_of hR hm
  obtain ⟨hsb0, hnn0, hsbn, ht0, ht2, htb⟩ := build_src hB hR.inv.1.hdr_rng.1
  have htL : f (X0 b.size om + 7) + 352 ≤ L0 b.size om := by rw [htb]; unfold tbase LB0 L0; omega
  have ht0' : 0 ≤ f (X0 b.size om + 7) := by rw [htb]; unfold tbase LB0; omega
  have hS := stepS_fit hw (by omega) hm rfl build_mem (by decide)
    (build_left_end hw hL 16 (X0 b.size om) _ _ _ _ _ _ hph hj hR.inv.1.x_eq rfl (by unfold X0; omega) hXL (by norm_num)
      ht0' htL rfl rfl rfl rfl rfl)
  by_cases hc : 0 < f cLEFT ∧ bExempt (f (X0 b.size om + 8)) (f (f (X0 b.size om + 7) + 1)) (f cREST) (f cTOTAL) ≠ 1
  · rw [if_pos hc] at hS
    have hg := (hw.store (i := 14) (v := 6) (by norm_num) (by omega)).store (i := 0) (v := 99) (by norm_num) (by omega)
    exact ⟨_, _, hS, hg, fun _ => by simp [cMODE, mREJECT], fun h => absurd hc h⟩
  · rw [if_neg hc] at hS
    have hg := (hw.store (i := 12) (v := 4) (by norm_num) (by omega)).store (i := 13) (v := 0) (by norm_num) (by omega)
    obtain ⟨f1, hw1, hR1, hk1, ag⟩ := next_rel hb hw hR (by rw [hm]; decide) (by rw [hm]; decide) hS hg
      (S := fun c => c = 12 ∨ c = 13) (fun c _ _ hc => by rw [upd_eq _ _ (by omega), upd_eq _ _ (by omega)])
      (fun c hc => by unfold ctl; omega)
    refine ⟨_, f1, hS, hw1, fun h => absurd h hc, fun _ => ⟨hR1, ?_, ?_, ?_, hk1⟩⟩
    · rw [hk1 _ (by decide) (by unfold cMODE; omega) (by unfold cMODE; omega)]; exact hm
    · rw [ag _ (by decide) (by unfold cPHASE; omega)]; simp [cPHASE, Function.update_apply]
    · rw [ag _ (by decide) (by unfold cINDEX; omega)]; simp [cINDEX, Function.update_apply]

/-! ## S4's exemptions, against the machine's `bExempt` -/

theorem restS_zero {c : Nat → Int} (hc : ∀ l, 0 ≤ c l) : ∀ k, restS c k = 0 ↔ ∀ l, 2 ≤ l → l ≤ k → c l = 0 := by
  have hnn : ∀ k, 0 ≤ restS c k := by
    intro k; induction k with
    | zero => simp [restS]
    | succ k ih => simp only [restS]; split_ifs <;> linarith [hc (k + 1)]
  intro k
  induction k with
  | zero => simp [restS]; intro l h1 h2; omega
  | succ k ih =>
    simp only [restS]
    constructor
    · intro h l h1 h2
      have := hnn k
      by_cases hl : l = k + 1
      · subst hl; rw [if_pos h1] at h; linarith [hc (k + 1)]
      · have h' : restS c k = 0 := by split_ifs at h <;> linarith [hc (k + 1)]
        exact ih.mp h' l h1 (by omega)
    · intro h
      rw [ih.mpr (fun l h1 h2 => h l h1 (by omega))]
      split_ifs with h2
      · simp [h (k + 1) h2 le_rfl]
      · simp

theorem totS_zero {c : Nat → Int} (hc : ∀ l, 0 ≤ c l) : ∀ k, totS c k = 0 ↔ ∀ l, 1 ≤ l → l ≤ k → c l = 0 := by
  have hnn : ∀ k, 0 ≤ totS c k := by
    intro k; induction k with
    | zero => simp [totS]
    | succ k ih => simp only [totS]; linarith [hc (k + 1)]
  intro k
  induction k with
  | zero => simp [totS]; intro l h1 h2; omega
  | succ k ih =>
    simp only [totS]
    constructor
    · intro h l h1 h2
      have := hnn k
      have := hc (k + 1)
      by_cases hl : l = k + 1
      · subst hl; linarith
      · exact ih.mp (by linarith) l h1 (by omega)
    · intro h
      rw [ih.mpr (fun l h1 h2 => h l h1 (by omega)), h (k + 1) (by omega) le_rfl]; simp

theorem oneSym_iff (lens : Array Nat) :
    oneSymbolLenOne lens = true ↔ blCount lens 1 = 1 ∧ ∀ l, 2 ≤ l → l ≤ 15 → blCount lens l = 0 := by
  unfold oneSymbolLenOne
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range'_1]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, fun l a b => h2 l ⟨a, by omega⟩⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, fun l ⟨a, b⟩ => h2 l a (by omega)⟩

theorem allZero_iff (lens : Array Nat) (h15 : ∀ i, i < lens.size → lens.getD i 0 ≤ 15) :
    lens.all (· = 0) = true ↔ ∀ l, 1 ≤ l → l ≤ 15 → blCount lens l = 0 := by
  rw [Array.all_eq_true]
  constructor
  · intro h l h1 _
    rw [blCount_eq _ _ (by omega)]
    simp only [symsL, List.length_eq_zero_iff, List.filter_eq_nil_iff, List.mem_range, decide_eq_true_eq]
    intro i hi he
    have := h i hi
    simp [Array.getD, hi] at he
    simp at this; omega
  · intro h i hi
    have hv := h15 i hi
    by_contra hne
    simp at hne
    have hpos : blCount lens (lens.getD i 0) ≠ 0 := by
      rw [blCount_eq _ _ (by simp [Array.getD, hi]; omega)]
      simp only [symsL, ne_eq, List.length_eq_zero_iff, List.filter_eq_nil_iff, List.mem_range, decide_eq_true_eq,
        not_forall, not_not]
      exact ⟨i, hi, rfl⟩
    exact hpos (h _ (by simp [Array.getD, hi]; omega) hv)

/-! ## Congruences: S4's folds read only the counts of lengths 1 … 15 -/

theorem ncode_congr {c d : Nat → Int} : ∀ k, (∀ i, i < k → c i = d i) → ncode c k = ncode d k
  | 0, _ => rfl
  | k + 1, h => by simp only [ncode]; rw [ncode_congr k (fun i hi => h i (by omega)), h k (by omega)]

theorem leftF_congr {c d : Nat → Int} : ∀ k, (∀ i, 1 ≤ i → i ≤ k → c i = d i) → leftF c k = leftF d k
  | 0, _ => rfl
  | k + 1, h => by simp only [leftF]; rw [leftF_congr k (fun i h1 h2 => h i h1 (by omega)), h (k + 1) (by omega) le_rfl]

theorem restS_congr {c d : Nat → Int} : ∀ k, (∀ i, 1 ≤ i → i ≤ k → c i = d i) → restS c k = restS d k
  | 0, _ => rfl
  | k + 1, h => by simp only [restS]; rw [restS_congr k (fun i h1 h2 => h i h1 (by omega)), h (k + 1) (by omega) le_rfl]

theorem totS_congr {c d : Nat → Int} : ∀ k, (∀ i, 1 ≤ i → i ≤ k → c i = d i) → totS c k = totS d k
  | 0, _ => rfl
  | k + 1, h => by simp only [totS]; rw [totS_congr k (fun i h1 h2 => h i h1 (by omega)), h (k + 1) (by omega) le_rfl]

/-- The offsets are prefix sums: the run of length l ends at or before the start of every longer one. -/
theorem offOf_le {f : Int → Int} {tbb : Int} (hc : ∀ l : Nat, 1 ≤ l → l ≤ 15 → 0 ≤ f (tbb + l)) :
    ∀ l l' : Nat, 1 ≤ l → l < l' → l' ≤ 16 → offOf f tbb l + f (tbb + l) ≤ offOf f tbb l' := by
  intro l l' h1 h2 h3
  induction l' with
  | zero => omega
  | succ l' ih =>
    simp only [offOf]
    by_cases he : l = l'
    · subst he; rw [if_neg (by omega)]
    · rw [if_neg (by omega)]; have := ih (by omega) (by omega); have := hc l' (by omega) (by omega); linarith

theorem offOf_nonneg {f : Int → Int} {tbb : Int} (hc : ∀ l : Nat, 1 ≤ l → l ≤ 15 → 0 ≤ f (tbb + l)) :
    ∀ l : Nat, l ≤ 16 → 0 ≤ offOf f tbb l := by
  intro l hl
  induction l with
  | zero => simp [offOf]
  | succ l ih => simp only [offOf]; split_ifs <;> [simpa using ih (by omega); linarith [ih (by omega), hc l (by omega) (by omega)]]

/-! ## BUILD assembled: ZERO, COUNT and NEXT -/

theorem bset_far {n om : Nat} {t : Int} (ht : 0 ≤ t ∧ t ≤ 2) (c : Int) (h : bset (tbase n om t) c) :
    c ≠ X0 n om + 5 ∧ c ≠ X0 n om + 6 ∧ c ≠ X0 n om + 7 ∧ c ≠ X0 n om + 8 ∧ c ≠ cTGT ∧ c ≠ cCHK ∧ c ≠ cDYN ∧
      c ≠ cHLIT ∧ c ≠ cHDIST ∧ c ≠ cBF ∧ c ≠ cFILL ∧ (c < LB0 n om ∨ LB0 n om + 337 ≤ c) := by
  unfold bset tbase LB0 at h; unfold X0 cTGT cCHK cDYN cHLIT cHDIST cBF cFILL LB0; omega

/-- **ZERO, COUNT, NEXT:** the table's counts are `bl_count`, its firsts are `next_code`, and its offsets and slots are
the prefix sums, all at the moment NEXT reaches j = 16. -/
theorem build_prefix {b : Array Nat} {om : Nat} {lit : Bool} {p : Int} (hb : ∀ x ∈ b, x < 256) (lens : Array Nat)
    {σ : Store} {f : Int → Int} {st : St} (hw : World σ p (L0 b.size om) f) (hR : Rel b om lit f st)
    (hm : f cMODE = mBUILD) (hph : f cPHASE = 0) (hj : f cINDEX = 0) (hnn : f (X0 b.size om + 6) = lens.size)
    (hsrc : ∀ i : Nat, i < lens.size → f (f (X0 b.size om + 5) + i) = lens.getD i 0) :
    ∃ σ' f', Reach p σ σ' ∧ World σ' p (L0 b.size om) f' ∧ Rel b om lit f' st ∧ f' cMODE = mBUILD ∧
      f' cPHASE = 2 ∧ f' cINDEX = 16 ∧ Keeps (L0 b.size om) f f' (bset (f (X0 b.size om + 7))) ∧
      f' (f (X0 b.size om + 7)) = 0 ∧
      (∀ l : Nat, 1 ≤ l → l ≤ 15 → f' (f (X0 b.size om + 7) + l) = blCount lens l ∧
        f' (f (X0 b.size om + 7) + 16 + l) = (nextCodes lens).getD l 0 ∧
        f' (f (X0 b.size om + 7) + 32 + l) = offOf f' (f (X0 b.size om + 7)) l ∧
        f' (f (X0 b.size om + 7) + 48 + l) = offOf f' (f (X0 b.size om + 7)) l) := by
  have hB := buildInv_of hR hm
  obtain ⟨hsb0, hnn0, hsbn, ht0, ht2, htb⟩ := build_src hB hR.inv.1.hdr_rng.1
  set tbb := f (X0 b.size om + 7) with htbbd
  set sb := f (X0 b.size om + 5) with hsbd
  have far := bset_far (n := b.size) (om := om) ⟨ht0, ht2⟩
  have hX : ∀ c, X0 b.size om ≤ c → c < L0 b.size om → True := fun _ _ _ => trivial
  obtain ⟨σ1, f1, hR1, hw1, hRe1, hm1, hp1, hj1, hk1⟩ := zero_run (lit := lit) hb (16 - 0) σ f st hw hR hm hph (by rw [hj]; rfl)
  rw [← htbbd] at hk1
  have kk1 : ∀ c : Int, 0 ≤ c → c < L0 b.size om → ¬ bset tbb c → f1 c = f c := hk1
  have e7 : f1 (X0 b.size om + 7) = tbb := by
    rw [kk1 _ (by unfold X0; omega) (by unfold X0 L0; omega) (fun h => (far _ (htb ▸ h)).2.2.1 rfl)]
  have e5 : f1 (X0 b.size om + 5) = sb := by
    rw [kk1 _ (by unfold X0; omega) (by unfold X0 L0; omega) (fun h => (far _ (htb ▸ h)).1 rfl)]
  have e6 : f1 (X0 b.size om + 6) = lens.size := by
    rw [kk1 _ (by unfold X0; omega) (by unfold X0 L0; omega) (fun h => (far _ (htb ▸ h)).2.1 rfl)]; exact hnn
  obtain ⟨σ2, f2, hR2, hw2, hRe2, hm2, hp2, hj2, hc2, hk2⟩ :=
    count_run (lit := lit) hb (lens.size - 0) σ1 f1 st hw1 hRe1 hm1 hp1 (by rw [hj1, e6]; simp)
  rw [e7] at hk2
  have kk2 : ∀ c : Int, 0 ≤ c → c < L0 b.size om → ¬ bset tbb c → f2 c = f1 c := hk2
  have e7' : f2 (X0 b.size om + 7) = tbb := by
    rw [kk2 _ (by unfold X0; omega) (by unfold X0 L0; omega) (fun h => (far _ (htb ▸ h)).2.2.1 rfl), e7]
  -- the counts at the start of NEXT
  have hB2 := buildInv_of hRe2 hm2
  obtain ⟨-, -, -, -, -, -, hn2, -, -⟩ := hB2
  obtain ⟨-, -, hz2, -, hcnt2, -⟩ := hn2 (by omega) (by omega)
  rw [e7'] at hz2 hcnt2
  have src2 : ∀ i : Nat, i < lens.size → f2 (sb + i) = lens.getD i 0 := fun i hi => by
    rw [kk2 _ (by unfold LB0 at hsb0; omega) (by unfold LB0 L0 at *; omega)
      (fun h => by have := (far _ (htb ▸ h)).2.2.2.2.2.2.2.2.2.2.2; unfold LB0 at *; omega),
      kk1 _ (by unfold LB0 at hsb0; omega) (by unfold LB0 L0 at *; omega)
      (fun h => by have := (far _ (htb ▸ h)).2.2.2.2.2.2.2.2.2.2.2; unfold LB0 at *; omega)]
    exact hsrc i hi
  have e52 : f2 (X0 b.size om + 5) = sb := by
    rw [kk2 _ (by unfold X0; omega) (by unfold X0 L0; omega) (fun h => (far _ (htb ▸ h)).1 rfl), e5]
  have e62 : f2 (X0 b.size om + 6) = lens.size := by
    rw [kk2 _ (by unfold X0; omega) (by unfold X0 L0; omega) (fun h => (far _ (htb ▸ h)).2.1 rfl), e6]
  rw [e52, e62] at hcnt2
  have hcb2 : ∀ l : Nat, 1 ≤ l → l ≤ 15 → f2 (tbb + l) = blCount lens l := fun l h1 h2 => by
    rw [hcnt2 l (by omega) (by omega)]; simp only [Int.toNat_natCast]
    exact_mod_cast cnt_blCount src2 l (by omega)
  obtain ⟨σ3, f3, hR3, hw3, hRe3, hm3, hp3, hj3, e73, hcs3, hfs3, hk3⟩ :=
    next_run (lit := lit) hb 15 σ2 f2 st 1 hw2 hRe2 hm2 hp2 hj2 le_rfl rfl (by rw [hc2]; rfl) (fun l h1 h2 => by omega)
  rw [e7'] at e73 hcs3 hfs3 hk3
  refine ⟨σ3, f3, hR1.trans (hR2.trans hR3), hw3, hRe3, hm3, hp3, hj3, ?_, ?_, fun l h1 h2 => ⟨?_, ?_, ?_⟩⟩
  · exact (hk1.trans hk2 (fun c h => h)).trans hk3 (fun c h => h)
  · have h0 := hcs3 0 (by norm_num); simp only [Nat.cast_zero, add_zero] at h0; rw [h0]; simpa using hz2
  · rw [hcs3 l (by omega)]; exact hcb2 l h1 h2
  · rw [hfs3 l h1 h2, nextCodes_ncode lens l h2]
    apply ncode_congr
    intro i hi
    by_cases h0 : i = 0
    · subst h0; simpa [blCount] using hz2
    · exact hcb2 i (by omega) (by omega)
  · -- offsets and slots, from the invariant at j = 16
    have hB3 := buildInv_of hRe3 hm3
    obtain ⟨-, -, -, -, -, -, hn3, -, -⟩ := hB3
    obtain ⟨-, -, -, -, -, hoff3⟩ := hn3 (by omega) (by omega)
    rw [e73] at hoff3
    have := hoff3 l (by omega) (by rw [if_pos hp3, hj3]; omega)
    simpa using this

/-! ## BUILD assembled: S4's checks and SYMS, to the table relation -/

def varOf : Mode → Int
  | .normal => 0
  | .strict => 1
  | .dist => 2

theorem exempt_iff (lens : Array Nat) (md : Mode) (h15 : ∀ i, i < lens.size → lens.getD i 0 ≤ 15)
    (cf : Nat → Int) (hcf : ∀ l, 1 ≤ l → l ≤ 15 → cf l = blCount lens l) :
    (match md with
      | .normal => oneSymbolLenOne lens
      | .strict => false
      | .dist => oneSymbolLenOne lens || lens.all (· = 0)) = true ↔
    bExempt (varOf md) (cf 1) (restS cf 15) (totS cf 15) = 1 := by
  have hnn : ∀ l, 0 ≤ (fun l => if 1 ≤ l ∧ l ≤ 15 then cf l else 0) l := by
    intro l; simp only; split_ifs with h
    · rw [hcf l h.1 h.2]; positivity
    · exact le_rfl
  have er : restS cf 15 = restS (fun l => if 1 ≤ l ∧ l ≤ 15 then cf l else 0) 15 :=
    restS_congr 15 (fun i h1 h2 => by simp [h1, h2])
  have et : totS cf 15 = totS (fun l => if 1 ≤ l ∧ l ≤ 15 then cf l else 0) 15 :=
    totS_congr 15 (fun i h1 h2 => by simp [h1, h2])
  have hone : oneSymbolLenOne lens = true ↔ cf 1 = 1 ∧ restS cf 15 = 0 := by
    rw [oneSym_iff, er, restS_zero hnn, hcf 1 le_rfl (by norm_num)]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨by rw [h1]; rfl, fun l a b => ?_⟩
      simp only [show 1 ≤ l by omega, b, and_self, if_true]
      rw [hcf l (by omega) b, h2 l a b]; rfl
    · rintro ⟨h1, h2⟩; refine ⟨by exact_mod_cast h1, fun l a b => ?_⟩
      have := h2 l a b; simp only [show 1 ≤ l by omega, b, and_self, if_true] at this
      rw [hcf l (by omega) b] at this; exact_mod_cast this
  have hall : lens.all (· = 0) = true ↔ totS cf 15 = 0 := by
    rw [allZero_iff lens h15, et, totS_zero hnn]
    constructor
    · intro h l a b; simp only [a, b, and_self, if_true]; rw [hcf l a b, h l a b]; rfl
    · intro h l a b; have := h l a b; simp only [a, b, and_self, if_true] at this
      rw [hcf l a b] at this; exact_mod_cast this
  cases md with
  | normal =>
    simp only [varOf, bExempt]; rw [hone]
    by_cases h1 : cf 1 = 1 <;> by_cases h2 : restS cf 15 = 0 <;> simp [h1, h2]
  | strict => simp [varOf, bExempt]
  | dist =>
    simp only [varOf, bExempt, Bool.or_eq_true]; rw [hone, hall]
    by_cases h1 : cf 1 = 1 <;> by_cases h2 : restS cf 15 = 0 <;> by_cases h3 : totS cf 15 = 0 <;> simp [h1, h2, h3]

/-- What a finished build leaves (before its end step): R, still BUILD at phase 4 with j = N, the table related to the
lengths, and nothing outside the build's own cells touched. -/
def Built (b : Array Nat) (om : Nat) (lit : Bool) (lens : Array Nat) (f f' : Int → Int) (st : St) : Prop :=
  Rel b om lit f' st ∧ f' cMODE = mBUILD ∧ f' cPHASE = 4 ∧ f' cINDEX = lens.size ∧
    TblRel b.size om f' (f cTGT) lens ∧ Keeps (L0 b.size om) f f' (bset (f (X0 b.size om + 7)))

/-- **SYMS to the table relation**, from SYMS at j = 0 with the counts, firsts, offsets and slots in place. -/
theorem syms_finish {b : Array Nat} {om : Nat} {lit : Bool} {p : Int} (hb : ∀ x ∈ b, x < 256) (lens : Array Nat)
    {σ : Store} {f₀ f : Int → Int} {st : St} (hw : World σ p (L0 b.size om) f) (hR : Rel b om lit f st)
    (hm : f cMODE = mBUILD) (hph : f cPHASE = 4) (hj : f cINDEX = 0)
    (h7 : f (X0 b.size om + 7) = f₀ (X0 b.size om + 7)) (htg : f cTGT = f₀ cTGT)
    (h5 : f (X0 b.size om + 5) = f₀ (X0 b.size om + 5)) (h6 : f (X0 b.size om + 6) = lens.size)
    (hsrc : ∀ i : Nat, i < lens.size → f (f (X0 b.size om + 5) + i) = lens.getD i 0)
    (hcnt : ∀ l : Nat, 1 ≤ l → l ≤ 15 → f (f (X0 b.size om + 7) + l) = blCount lens l)
    (hfst : ∀ l : Nat, 1 ≤ l → l ≤ 15 → f (f (X0 b.size om + 7) + 16 + l) = (nextCodes lens).getD l 0)
    (hoff : ∀ l : Nat, 1 ≤ l → l ≤ 15 → f (f (X0 b.size om + 7) + 32 + l) = offOf f (f (X0 b.size om + 7)) l ∧
      f (f (X0 b.size om + 7) + 48 + l) = offOf f (f (X0 b.size om + 7)) l)
    (hk0 : Keeps (L0 b.size om) f₀ f (bset (f₀ (X0 b.size om + 7)))) :
    ∃ σ' f', Reach p σ σ' ∧ World σ' p (L0 b.size om) f' ∧ Built b om lit lens f₀ f' st := by
  have hB := buildInv_of hR hm
  obtain ⟨hsb0, hnn0, hsbn, ht0, ht2, htb⟩ := build_src hB hR.inv.1.hdr_rng.1
  set tbb := f (X0 b.size om + 7) with htbbd
  have hsane : ∀ l : Int, 1 ≤ l → l ≤ 15 → 0 ≤ f (tbb + l) ∧ 0 ≤ f (tbb + 32 + l) ∧
      f (tbb + 32 + l) + f (tbb + l) ≤ 288 := by
    have := (hB.2.2.2.2.2.2.2.1 hph).2.2.1; unfold sane at this; rw [← htb] at this; exact this
  set o : Nat → Int := fun l => offOf f tbb l with hod
  have hcnn : ∀ l : Nat, 1 ≤ l → l ≤ 15 → 0 ≤ f (tbb + l) := fun l h1 h2 => by rw [hcnt l h1 h2]; positivity
  have hdis : ∀ l l' : Nat, 1 ≤ l → l < l' → l' ≤ 15 → o l + blCount lens l ≤ o l' := fun l l' h1 h2 h3 => by
    have := offOf_le hcnn l l' h1 h2 (by omega); rw [hcnt l h1 (by omega)] at this; exact this
  have hob : ∀ l : Nat, 1 ≤ l → l ≤ 15 → 0 ≤ o l ∧ o l + blCount lens l ≤ 288 := fun l h1 h2 => by
    obtain ⟨s0, s1, s2⟩ := hsane l (by omega) (by omega)
    have e1 := (hoff l h1 h2).1
    have e2 := hcnt l h1 h2
    rw [e1] at s1 s2; rw [e2] at s2
    exact ⟨s1, s2.trans_eq' (by ring)⟩
  obtain ⟨σ', f', hR', hw', hRe', hm', hp', hj', hsy', hk'⟩ :=
    syms_run (lit := lit) hb tbb (f (X0 b.size om + 5)) lens o hdis hob lens.size σ f st 0 hw hR hm hph hj (by simp)
      rfl rfl h6 hsrc (fun l h1 h2 => by simp [filt, (hoff l h1 h2).2, hod]) (fun l h1 h2 i hi => by simp [filt] at hi)
  have kk : ∀ c : Int, 0 ≤ c → c < L0 b.size om → (c < tbb + 48 ∨ tbb + 352 ≤ c) → c ≠ 13 → f' c = f c :=
    fun c h0 h1 a b' => hk' c h0 h1 (by omega)
  have htL : tbb + 352 ≤ L0 b.size om := by rw [htb]; unfold tbase LB0 L0; omega
  have ht0' : 2417 ≤ tbb := by rw [htb]; unfold tbase LB0; omega
  refine ⟨σ', f', hR', hw', hRe', hm', hp', hj', ?_, ?_⟩
  · rw [← htg]; unfold TblRel; rw [← htb]
    intro l h1 h2
    have e32 : f' (tbb + 32 + l) = o l := by rw [kk _ (by omega) (by omega) (by omega) (by omega), (hoff l h1 h2).1]
    refine ⟨by rw [kk _ (by omega) (by omega) (by omega) (by omega)]; exact hcnt l h1 h2,
      by rw [kk _ (by omega) (by omega) (by omega) (by omega)]; exact hfst l h1 h2, fun j hj => ?_,
      by rw [e32]; exact (hob l h1 h2).1, by rw [e32]; exact (hob l h1 h2).2⟩
    rw [e32]
    have hlen : (filt lens l lens.size).length = blCount lens l := by rw [filt_full, ← blCount_eq _ _ (by omega)]
    have := hsy' l h1 h2 j (by omega)
    have hj' : j < (symsL lens l).length := by rw [← filt_full]; omega
    rw [this, symsOf_eq, List.getElem_of_eq (filt_full lens l)]
    simp [Array.getD, hj']
  · rw [← h7]
    exact hk0.trans (fun c h0 h1 hc => hk' c h0 h1 (by unfold bset at hc; omega)) (fun c h => by rw [h7] at *; exact h)

theorem offOf_congr' {f g : Int → Int} {tbb : Int} : ∀ l : Nat, (∀ k : Nat, 1 ≤ k → k < l → f (tbb + k) = g (tbb + k)) →
    offOf f tbb l = offOf g tbb l
  | 0, _ => rfl
  | l + 1, h => by
    simp only [offOf]; rw [offOf_congr' l (fun k h1 h2 => h k h1 (by omega))]
    split_ifs with h0
    · rfl
    · rw [h l (by omega) (by omega)]

def exemptB (lens : Array Nat) (md : Mode) : Bool :=
  match md with
  | .normal => oneSymbolLenOne lens
  | .strict => false
  | .dist => oneSymbolLenOne lens || lens.all (· = 0)

/-- S4's `code`, run: over-subscribed, incomplete, or the assignment, with the state untouched. -/
theorem go_code (lens : Array Nat) (md : Mode) (e : Env) (st : St) :
    go (code lens md) e st = match leftF (fun l => (blCount lens l : Int)) 15 with
      | none => .error "over-subscribed"
      | some v => if 0 < v ∧ exemptB lens md = false then .error "incomplete" else .ok (assign lens, st) := by
  unfold code
  rw [leftAfter_leftF]
  rcases leftF (fun l => (blCount lens l : Int)) 15 with _ | v
  · rfl
  · simp only
    by_cases h : 0 < v ∧ exemptB lens md = false
    · rw [if_pos h, if_pos]; · rfl
      cases md <;> simp_all [exemptB]
    · rw [if_neg h, if_neg]; · rfl
      cases md <;> simp_all [exemptB]

/-- **BUILD ↔ S4's `code`** (S-18's `code` row; CHK = 0 is the repaired fixed reading's `pure (assign lens)`). -/
theorem build_tbl {b : Array Nat} {om : Nat} {lit : Bool} {p : Int} (hb : ∀ x ∈ b, x < 256) (lens : Array Nat)
    (md : Mode) {σ : Store} {f : Int → Int} {st : St} (hw : World σ p (L0 b.size om) f) (hR : Rel b om lit f st)
    (hm : f cMODE = mBUILD) (hph : f cPHASE = 0) (hj : f cINDEX = 0) (hnn : f (X0 b.size om + 6) = lens.size)
    (hsrc : ∀ i : Nat, i < lens.size → f (f (X0 b.size om + 5) + i) = lens.getD i 0)
    (h15 : ∀ i, i < lens.size → lens.getD i 0 ≤ 15) :
    (f cCHK ≠ 1 → ∃ σ' f', Reach p σ σ' ∧ World σ' p (L0 b.size om) f' ∧ Built b om lit lens f f' st) ∧
    (f cCHK = 1 → f (X0 b.size om + 8) = varOf md →
      (∀ C st', go (code lens md) ⟨b, om⟩ st = .ok (C, st') → C = assign lens ∧ st' = st ∧
        ∃ σ' f', Reach p σ σ' ∧ World σ' p (L0 b.size om) f' ∧ Built b om lit lens f f' st) ∧
      (∀ r, go (code lens md) ⟨b, om⟩ st = .error r →
        ∃ σ' f', Reach p σ σ' ∧ World σ' p (L0 b.size om) f' ∧ f' cMODE = mREJECT)) := by
  have hB := buildInv_of hR hm
  obtain ⟨hsb0, hnn0, hsbn, ht0, ht2, htb⟩ := build_src hB hR.inv.1.hdr_rng.1
  have far := bset_far (n := b.size) (om := om) ⟨ht0, ht2⟩
  set tbb := f (X0 b.size om + 7) with htbbd
  have htL : tbb + 352 ≤ L0 b.size om := by rw [htb]; unfold tbase LB0 L0; omega
  have htbig : 2417 ≤ tbb := by rw [htb]; unfold tbase LB0; omega
  obtain ⟨σ2, f2, hR2, hw2, hRe2, hm2, hp2, hj2, hk2, hz2, hfacts⟩ := build_prefix (lit := lit) hb lens hw hR hm hph hj hnn hsrc
  rw [← htbbd] at hk2 hz2 hfacts
  obtain ⟨σ3, f3, hS3, hw3, hRe3, hm3, hk3, hc1, hc0⟩ := next_end_next hb hw2 hRe2 hm2 hp2 hj2
  -- what f3 still holds
  have kf3 : ∀ c : Int, 0 ≤ c → c < L0 b.size om → ¬ bset tbb c → c ≠ 12 → c ≠ 13 → (c < 2076 ∨ 2078 < c) → f3 c = f c :=
    fun c h0 h1 a1 a2 a3 a4 => (hk3 c h0 h1 (by omega)).trans (hk2 c h0 h1 a1)
  have kt3 : ∀ c : Int, tbb ≤ c → c < tbb + 64 → f3 c = f2 c := fun c h1 h2 => hk3 c (by omega) (by omega) (by omega)
  have e7 : f3 (X0 b.size om + 7) = tbb := kf3 _ (by unfold X0; omega) (by unfold X0 L0; omega)
    (fun h => (far _ (htb ▸ h)).2.2.1 rfl) (by unfold X0; omega) (by unfold X0; omega) (by unfold X0; omega)
  have e5 : f3 (X0 b.size om + 5) = f (X0 b.size om + 5) := kf3 _ (by unfold X0; omega) (by unfold X0 L0; omega)
    (fun h => (far _ (htb ▸ h)).1 rfl) (by unfold X0; omega) (by unfold X0; omega) (by unfold X0; omega)
  have e6 : f3 (X0 b.size om + 6) = lens.size := by
    rw [kf3 _ (by unfold X0; omega) (by unfold X0 L0; omega) (fun h => (far _ (htb ▸ h)).2.1 rfl) (by unfold X0; omega)
      (by unfold X0; omega) (by unfold X0; omega)]; exact hnn
  have e8 : f3 (X0 b.size om + 8) = f (X0 b.size om + 8) := kf3 _ (by unfold X0; omega) (by unfold X0 L0; omega)
    (fun h => (far _ (htb ▸ h)).2.2.2.1 rfl) (by unfold X0; omega) (by unfold X0; omega) (by unfold X0; omega)
  have etg : f3 cTGT = f cTGT := kf3 _ (by decide) (by unfold cTGT L0; omega) (fun h => (far _ (htb ▸ h)).2.2.2.2.1 rfl)
    (by decide) (by decide) (by decide)
  have echk : f2 cCHK = f cCHK := hk2 _ (by decide) (by unfold cCHK L0; omega) (fun h => (far _ (htb ▸ h)).2.2.2.2.2.1 rfl)
  have src3 : ∀ i : Nat, i < lens.size → f3 (f3 (X0 b.size om + 5) + i) = lens.getD i 0 := fun i hi => by
    rw [e5, kf3 _ (by unfold LB0 at hsb0; omega) (by unfold LB0 L0 at *; omega)
      (fun h => by have := (far _ (htb ▸ h)).2.2.2.2.2.2.2.2.2.2.2; unfold LB0 at *; omega)
      (by unfold LB0 at hsb0; omega) (by unfold LB0 at hsb0; omega) (by unfold LB0 at hsb0; omega)]
    exact hsrc i hi
  have cnt3 : ∀ l : Nat, 1 ≤ l → l ≤ 15 → f3 (tbb + l) = blCount lens l := fun l h1 h2 => by
    rw [kt3 _ (by omega) (by omega)]; exact (hfacts l h1 h2).1
  have fst3 : ∀ l : Nat, 1 ≤ l → l ≤ 15 → f3 (tbb + 16 + l) = (nextCodes lens).getD l 0 := fun l h1 h2 => by
    rw [kt3 _ (by omega) (by omega)]; exact (hfacts l h1 h2).2.1
  have off3 : ∀ l : Nat, l ≤ 16 → offOf f3 tbb l = offOf f2 tbb l := fun l hl =>
    offOf_congr' l (fun k h1 h2 => kt3 _ (by omega) (by omega))
  have oo3 : ∀ l : Nat, 1 ≤ l → l ≤ 15 → f3 (tbb + 32 + l) = offOf f3 tbb l ∧ f3 (tbb + 48 + l) = offOf f3 tbb l :=
    fun l h1 h2 => by
      rw [kt3 _ (by omega) (by omega), kt3 _ (by omega) (by omega), off3 l (by omega)]
      exact (hfacts l h1 h2).2.2
  have hk03 : Keeps (L0 b.size om) f f3 (bset tbb) := fun c h0 h1 hc =>
    (hk3 c h0 h1 (fun h => hc (by unfold bset; omega))).trans (hk2 c h0 h1 hc)
  constructor
  · intro hchk
    obtain ⟨hp4, hj4⟩ := hc0 (by rw [echk]; exact hchk)
    obtain ⟨σ', f', hR', hw', hb'⟩ := syms_finish (lit := lit) (f₀ := f) hb lens hw3 hRe3 hm3 hp4 hj4 (e7.trans htbbd)
      etg e5 e6 src3 (by rw [e7]; exact cnt3) (by rw [e7]; exact fst3) (by rw [e7]; exact oo3) hk03
    exact ⟨σ', f', hR2.trans ((Reach.step hS3).trans hR'), hw', hb'⟩
  · intro hchk hvar
    obtain ⟨hp3, hj3, hl3, hr3, ht3⟩ := hc1 (by rw [echk]; exact hchk)
    set cf : Nat → Int := fun k => f3 (tbb + k) with hcfd
    have hcfb : ∀ l, 1 ≤ l → l ≤ 15 → cf l = blCount lens l := cnt3
    have hlf : leftF (fun l => (blCount lens l : Int)) 15 = leftF cf 15 :=
      leftF_congr 15 (fun i h1 h2 => (hcfb i h1 h2).symm)
    obtain ⟨hno, hso⟩ := left_run (lit := lit) hb tbb cf 15 σ3 f3 st 1 hw3 hRe3 hm3 hp3 hj3 le_rfl rfl e7
      (fun k _ => rfl) (by rw [hl3]; rfl) (by rw [hr3]; rfl) (by rw [ht3]; rfl)
    have hex := exempt_iff lens md h15 cf hcfb
    -- after LEFT: the end check, and SYMS
    have after : ∀ v, leftF cf 15 = some v →
        ∃ σ4 f4, Reach p σ3 σ4 ∧ World σ4 p (L0 b.size om) f4 ∧ Rel b om lit f4 st ∧ f4 cMODE = mBUILD ∧
          f4 cPHASE = 3 ∧ f4 cINDEX = 16 ∧ f4 cLEFT = v ∧
          f4 (X0 b.size om + 8) = varOf md ∧ f4 (f4 (X0 b.size om + 7) + 1) = cf 1 ∧ f4 cREST = restS cf 15 ∧
          f4 cTOTAL = totS cf 15 ∧ Keeps (L0 b.size om) f3 f4 (fun c => c = 13 ∨ (2076 ≤ c ∧ c ≤ 2078)) := by
      intro v hv
      obtain ⟨σ4, f4, hR4, hw4, hRe4, hm4, hp4, hj4, hl4, hr4, ht4, hk4⟩ := hso v hv
      have e74 : f4 (X0 b.size om + 7) = tbb := by
        rw [hk4 _ (by unfold X0; omega) (by unfold X0 L0; omega) (by unfold X0; omega)]; exact e7
      refine ⟨σ4, f4, hR4, hw4, hRe4, hm4, hp4, hj4, hl4, ?_, ?_, hr4, ht4, hk4⟩
      · rw [hk4 _ (by unfold X0; omega) (by unfold X0 L0; omega) (by unfold X0; omega), e8, hvar]
      · rw [e74, hk4 _ (by omega) (by omega) (by omega)]; simp [hcfd]
    constructor
    · intro C st' h
      rw [go_code, hlf] at h
      rcases hv : leftF cf 15 with _ | v
      · rw [hv] at h; simp at h
      · rw [hv] at h
        dsimp only at h
        by_cases hc : 0 < v ∧ exemptB lens md = false
        · rw [if_pos hc] at h; simp at h
        · rw [if_neg hc] at h
          simp only [Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          refine ⟨rfl, rfl, ?_⟩
          obtain ⟨σ4, f4, hR4, hw4, hRe4, hm4, hp4, hj4, hl4, hv4, hc4, hr4, ht4, hk4⟩ := after v hv
          obtain ⟨σ5, f5, hS5, hw5, -, hgo5⟩ := left_end_next hb hw4 hRe4 hm4 hp4 hj4
          have hcond : ¬ (0 < f4 cLEFT ∧ bExempt (f4 (X0 b.size om + 8)) (f4 (f4 (X0 b.size om + 7) + 1)) (f4 cREST)
              (f4 cTOTAL) ≠ 1) := by
            rw [hl4, hv4, hc4, hr4, ht4]
            rintro ⟨h1, h2⟩
            apply hc
            refine ⟨h1, ?_⟩
            cases hE : exemptB lens md
            · rfl
            · exact absurd (hex.mp hE) h2
          obtain ⟨hRe5, hm5, hp5, hj5, hk5⟩ := hgo5 hcond
          have tr : ∀ c : Int, 0 ≤ c → c < L0 b.size om → c ≠ 12 → c ≠ 13 → (c < 2076 ∨ 2078 < c) → f5 c = f3 c :=
            fun c h0 h1 a1 a2 a3 => (hk5 c h0 h1 (by omega)).trans (hk4 c h0 h1 (by omega))
          have e75 : f5 (X0 b.size om + 7) = tbb := by
            rw [tr _ (by unfold X0; omega) (by unfold X0 L0; omega) (by unfold X0; omega) (by unfold X0; omega)
              (by unfold X0; omega)]; exact e7
          have hk05 : Keeps (L0 b.size om) f f5 (bset tbb) := fun c h0 h1 hc =>
            (tr c h0 h1 (by unfold bset at hc; omega) (by unfold bset at hc; omega) (by unfold bset at hc; omega)).trans
              (hk03 c h0 h1 hc)
          obtain ⟨σ', f', hR', hw', hb'⟩ := syms_finish (lit := lit) (f₀ := f) hb lens hw5 hRe5 hm5 hp5 hj5
            (e75.trans htbbd)
            (by rw [tr _ (by decide) (by unfold cTGT L0; omega) (by decide) (by decide) (by decide)]; exact etg)
            (by rw [tr _ (by unfold X0; omega) (by unfold X0 L0; omega) (by unfold X0; omega) (by unfold X0; omega)
              (by unfold X0; omega)]; exact e5)
            (by rw [tr _ (by unfold X0; omega) (by unfold X0 L0; omega) (by unfold X0; omega) (by unfold X0; omega)
              (by unfold X0; omega)]; exact e6)
            (fun i hi => by
              have e55 : f5 (X0 b.size om + 5) = f3 (X0 b.size om + 5) := tr _ (by unfold X0; omega)
                (by unfold X0 L0; omega) (by unfold X0; omega) (by unfold X0; omega) (by unfold X0; omega)
              rw [e55, e5, tr _ (by unfold LB0 at hsb0; omega) (by unfold LB0 L0 at *; omega) (by unfold LB0 at hsb0; omega)
                (by unfold LB0 at hsb0; omega) (by unfold LB0 at hsb0; omega), ← e5]
              exact src3 i hi)
            (fun l h1 h2 => by rw [e75, tr _ (by omega) (by omega) (by omega) (by omega) (by omega)]; exact cnt3 l h1 h2)
            (fun l h1 h2 => by rw [e75, tr _ (by omega) (by omega) (by omega) (by omega) (by omega)]; exact fst3 l h1 h2)
            (fun l h1 h2 => by
              rw [e75, tr _ (by omega) (by omega) (by omega) (by omega) (by omega),
                tr (tbb + 48 + l) (by omega) (by omega) (by omega) (by omega) (by omega),
                offOf_congr' (f := f5) (g := f3) l (fun k a b => tr _ (by omega) (by omega) (by omega) (by omega) (by omega))]
              exact oo3 l h1 h2)
            hk05
          exact ⟨σ', f', hR2.trans ((Reach.step hS3).trans (hR4.trans ((Reach.step hS5).trans hR'))), hw', hb'⟩
    · intro r h
      rw [go_code, hlf] at h
      rcases hv : leftF cf 15 with _ | v
      · obtain ⟨σ', f', hR', hw', hm'⟩ := hno hv
        exact ⟨σ', f', hR2.trans ((Reach.step hS3).trans hR'), hw', hm'⟩
      · rw [hv] at h
        dsimp only at h
        by_cases hc : 0 < v ∧ exemptB lens md = false
        · obtain ⟨σ4, f4, hR4, hw4, hRe4, hm4, hp4, hj4, hl4, hv4, hc4, hr4, ht4, hk4⟩ := after v hv
          obtain ⟨σ5, f5, hS5, hw5, hrej5, -⟩ := left_end_next hb hw4 hRe4 hm4 hp4 hj4
          have hcond : 0 < f4 cLEFT ∧ bExempt (f4 (X0 b.size om + 8)) (f4 (f4 (X0 b.size om + 7) + 1)) (f4 cREST)
              (f4 cTOTAL) ≠ 1 := by
            rw [hl4, hv4, hc4, hr4, ht4]
            refine ⟨hc.1, fun he => ?_⟩
            have := hex.mpr he
            change exemptB lens md = true at this
            rw [hc.2] at this; exact absurd this (by decide)
          exact ⟨σ5, f5, hR2.trans ((Reach.step hS3).trans (hR4.trans (Reach.step hS5))), hw5, hrej5 hcond⟩
        · rw [if_neg hc] at h; simp at h

/-! ## S5's fixed block: FIXLENS, then the L and D builds -/

theorem fixlens_mem : (mFIXLENS, fixlensN) ∈ modes := by unfold modes; simp

/-- **FIXLENS, to the hand-off:** S5's 318 lengths in the lengths area, then BUILD for L with S-11's cells. -/
theorem fixlens_run {b : Array Nat} {om : Nat} {lit : Bool} {p : Int} (hb : ∀ x ∈ b, x < 256) :
    ∀ (r : Nat) (σ : Store) (f : Int → Int) (st : St) (i : Nat), World σ p (L0 b.size om) f → Rel b om lit f st →
      f cMODE = mFIXLENS → f cFILL = i → i + r = 318 → (∀ k : Nat, k < i → f (LB0 b.size om + k) = fixLenI k) →
      ∃ σ' f', Reach p σ σ' ∧ World σ' p (L0 b.size om) f' ∧ Rel b om lit f' st ∧ f' cMODE = mBUILD ∧
        f' cPHASE = 0 ∧ f' cINDEX = 0 ∧ f' (X0 b.size om + 5) = LB0 b.size om ∧ f' (X0 b.size om + 6) = 288 ∧
        f' (X0 b.size om + 7) = tbase b.size om 1 ∧ f' (X0 b.size om + 8) = 0 ∧ f' cTGT = 1 ∧ f' cDYN = 0 ∧
        f' cCHK = (if lit then 1 else 0) ∧ f' cHLIT = 288 ∧ f' cHDIST = 30 ∧ f' cBF = f cBF ∧
        (∀ k : Nat, k < 318 → f' (LB0 b.size om + k) = fixLenI k) := by
  have hL : 2080 ≤ L0 b.size om := by unfold L0; omega
  have hXL : X0 b.size om + 8 < L0 b.size om := by (try unfold X0); unfold L0; omega
  intro r
  induction r with
  | zero =>
    intro σ f st i hw hR hm hi hir hlens
    have hi318 : i = 318 := by omega
    subst hi318
    have hS := stepS_fit hw (by omega) hm rfl fixlens_mem (by decide)
      (fixlens_end hw hL b.size om (if lit then 1 else 0) (X0 b.size om) (by rw [hi]; rfl) hR.inv.1.n_eq hR.inv.1.om_eq
        hR.inv.1.lit_eq hR.inv.1.x_eq (by (try unfold X0); omega) hXL)
    have hg := (((((((((((hw.store (i := X0 b.size om + 5) (v := 2080 + b.size + om) (by (try unfold X0); omega)
      (by (try unfold X0); unfold L0; omega)).store (i := X0 b.size om + 6) (v := 288) (by (try unfold X0); omega) (by (try unfold X0); unfold L0; omega)).store
      (i := X0 b.size om + 7) (v := 2080 + b.size + om + 689) (by (try unfold X0); omega) (by (try unfold X0); unfold L0; omega)).store
      (i := X0 b.size om + 8) (v := 0) (by (try unfold X0); omega) (by (try unfold X0); unfold L0; omega)).store (i := 7) (v := 288)
      (by norm_num) (by omega)).store (i := 8) (v := 30) (by norm_num) (by omega)).store (i := 2072)
      (v := if lit then 1 else 0) (by norm_num) (by omega)).store (i := 12) (v := 0) (by norm_num) (by omega)).store
      (i := 13) (v := 0) (by norm_num) (by omega)).store (i := 2074) (v := 1) (by norm_num) (by omega)).store (i := 2073)
      (v := 0) (by norm_num) (by omega)).store (i := 0) (v := 11) (by norm_num) (by omega)
    obtain ⟨f1, hw1, hR1, hk1, ag⟩ := next_rel hb hw hR (by rw [hm]; decide) (by rw [hm]; decide) hS hg
      (S := fun c => c = 0 ∨ c = 7 ∨ c = 8 ∨ c = 12 ∨ c = 13 ∨ (2072 ≤ c ∧ c ≤ 2074) ∨
        (X0 b.size om + 5 ≤ c ∧ c ≤ X0 b.size om + 8))
      (fun c _ _ hc => by
        simp only [Function.update_apply]
        rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
          if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
          if_neg (by omega), if_neg (by omega)])
      (fun c hc => by unfold ctl IN X0 at *; omega)
    refine ⟨_, f1, Reach.step hS, hw1, hR1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun k hk => ?_⟩
    · show f1 (0) = mBUILD
      rw [ag (0) (by (try unfold X0); omega) (by (try unfold X0); unfold L0; omega)]
      rw [Function.update_self]; simp [mBUILD]
    · show f1 (12) = 0
      rw [ag (12) (by (try unfold X0); omega) (by (try unfold X0); unfold L0; omega)]
      rw [upd_eq _ _ (show (12 : Int) ≠ 0 by (try unfold X0); omega), upd_eq _ _ (show (12 : Int) ≠ 2073 by (try unfold X0); omega), upd_eq _ _ (show (12 : Int) ≠ 2074 by (try unfold X0); omega), upd_eq _ _ (show (12 : Int) ≠ 13 by (try unfold X0); omega), Function.update_self]
    · show f1 (13) = 0
      rw [ag (13) (by (try unfold X0); omega) (by (try unfold X0); unfold L0; omega)]
      rw [upd_eq _ _ (show (13 : Int) ≠ 0 by (try unfold X0); omega), upd_eq _ _ (show (13 : Int) ≠ 2073 by (try unfold X0); omega), upd_eq _ _ (show (13 : Int) ≠ 2074 by (try unfold X0); omega), Function.update_self]
    · show f1 (X0 b.size om + 5) = LB0 b.size om
      rw [ag (X0 b.size om + 5) (by (try unfold X0); omega) (by (try unfold X0); unfold L0; omega)]
      rw [upd_eq _ _ (show (X0 b.size om + 5 : Int) ≠ 0 by (try unfold X0); omega), upd_eq _ _ (show (X0 b.size om + 5 : Int) ≠ 2073 by (try unfold X0); omega), upd_eq _ _ (show (X0 b.size om + 5 : Int) ≠ 2074 by (try unfold X0); omega), upd_eq _ _ (show (X0 b.size om + 5 : Int) ≠ 13 by (try unfold X0); omega), upd_eq _ _ (show (X0 b.size om + 5 : Int) ≠ 12 by (try unfold X0); omega), upd_eq _ _ (show (X0 b.size om + 5 : Int) ≠ 2072 by (try unfold X0); omega), upd_eq _ _ (show (X0 b.size om + 5 : Int) ≠ 8 by (try unfold X0); omega), upd_eq _ _ (show (X0 b.size om + 5 : Int) ≠ 7 by (try unfold X0); omega), upd_eq _ _ (show (X0 b.size om + 5 : Int) ≠ X0 b.size om + 8 by (try unfold X0); omega), upd_eq _ _ (show (X0 b.size om + 5 : Int) ≠ X0 b.size om + 7 by (try unfold X0); omega), upd_eq _ _ (show (X0 b.size om + 5 : Int) ≠ X0 b.size om + 6 by (try unfold X0); omega), Function.update_self]; unfold LB0; ring
    · show f1 (X0 b.size om + 6) = 288
      rw [ag (X0 b.size om + 6) (by (try unfold X0); omega) (by (try unfold X0); unfold L0; omega)]
      rw [upd_eq _ _ (show (X0 b.size om + 6 : Int) ≠ 0 by (try unfold X0); omega), upd_eq _ _ (show (X0 b.size om + 6 : Int) ≠ 2073 by (try unfold X0); omega), upd_eq _ _ (show (X0 b.size om + 6 : Int) ≠ 2074 by (try unfold X0); omega), upd_eq _ _ (show (X0 b.size om + 6 : Int) ≠ 13 by (try unfold X0); omega), upd_eq _ _ (show (X0 b.size om + 6 : Int) ≠ 12 by (try unfold X0); omega), upd_eq _ _ (show (X0 b.size om + 6 : Int) ≠ 2072 by (try unfold X0); omega), upd_eq _ _ (show (X0 b.size om + 6 : Int) ≠ 8 by (try unfold X0); omega), upd_eq _ _ (show (X0 b.size om + 6 : Int) ≠ 7 by (try unfold X0); omega), upd_eq _ _ (show (X0 b.size om + 6 : Int) ≠ X0 b.size om + 8 by (try unfold X0); omega), upd_eq _ _ (show (X0 b.size om + 6 : Int) ≠ X0 b.size om + 7 by (try unfold X0); omega), Function.update_self]
    · show f1 (X0 b.size om + 7) = tbase b.size om 1
      rw [ag (X0 b.size om + 7) (by (try unfold X0); omega) (by (try unfold X0); unfold L0; omega)]
      rw [upd_eq _ _ (show (X0 b.size om + 7 : Int) ≠ 0 by (try unfold X0); omega), upd_eq _ _ (show (X0 b.size om + 7 : Int) ≠ 2073 by (try unfold X0); omega), upd_eq _ _ (show (X0 b.size om + 7 : Int) ≠ 2074 by (try unfold X0); omega), upd_eq _ _ (show (X0 b.size om + 7 : Int) ≠ 13 by (try unfold X0); omega), upd_eq _ _ (show (X0 b.size om + 7 : Int) ≠ 12 by (try unfold X0); omega), upd_eq _ _ (show (X0 b.size om + 7 : Int) ≠ 2072 by (try unfold X0); omega), upd_eq _ _ (show (X0 b.size om + 7 : Int) ≠ 8 by (try unfold X0); omega), upd_eq _ _ (show (X0 b.size om + 7 : Int) ≠ 7 by (try unfold X0); omega), upd_eq _ _ (show (X0 b.size om + 7 : Int) ≠ X0 b.size om + 8 by (try unfold X0); omega), Function.update_self]; unfold tbase LB0; ring
    · show f1 (X0 b.size om + 8) = 0
      rw [ag (X0 b.size om + 8) (by (try unfold X0); omega) (by (try unfold X0); unfold L0; omega)]
      rw [upd_eq _ _ (show (X0 b.size om + 8 : Int) ≠ 0 by (try unfold X0); omega), upd_eq _ _ (show (X0 b.size om + 8 : Int) ≠ 2073 by (try unfold X0); omega), upd_eq _ _ (show (X0 b.size om + 8 : Int) ≠ 2074 by (try unfold X0); omega), upd_eq _ _ (show (X0 b.size om + 8 : Int) ≠ 13 by (try unfold X0); omega), upd_eq _ _ (show (X0 b.size om + 8 : Int) ≠ 12 by (try unfold X0); omega), upd_eq _ _ (show (X0 b.size om + 8 : Int) ≠ 2072 by (try unfold X0); omega), upd_eq _ _ (show (X0 b.size om + 8 : Int) ≠ 8 by (try unfold X0); omega), upd_eq _ _ (show (X0 b.size om + 8 : Int) ≠ 7 by (try unfold X0); omega), Function.update_self]
    · show f1 (2074) = 1
      rw [ag (2074) (by (try unfold X0); omega) (by (try unfold X0); unfold L0; omega)]
      rw [upd_eq _ _ (show (2074 : Int) ≠ 0 by (try unfold X0); omega), upd_eq _ _ (show (2074 : Int) ≠ 2073 by (try unfold X0); omega), Function.update_self]
    · show f1 (2073) = 0
      rw [ag (2073) (by (try unfold X0); omega) (by (try unfold X0); unfold L0; omega)]
      rw [upd_eq _ _ (show (2073 : Int) ≠ 0 by (try unfold X0); omega), Function.update_self]
    · show f1 (2072) = (if lit then 1 else 0)
      rw [ag (2072) (by (try unfold X0); omega) (by (try unfold X0); unfold L0; omega)]
      rw [upd_eq _ _ (show (2072 : Int) ≠ 0 by (try unfold X0); omega), upd_eq _ _ (show (2072 : Int) ≠ 2073 by (try unfold X0); omega), upd_eq _ _ (show (2072 : Int) ≠ 2074 by (try unfold X0); omega), upd_eq _ _ (show (2072 : Int) ≠ 13 by (try unfold X0); omega), upd_eq _ _ (show (2072 : Int) ≠ 12 by (try unfold X0); omega), Function.update_self]
    · show f1 (7) = 288
      rw [ag (7) (by (try unfold X0); omega) (by (try unfold X0); unfold L0; omega)]
      rw [upd_eq _ _ (show (7 : Int) ≠ 0 by (try unfold X0); omega), upd_eq _ _ (show (7 : Int) ≠ 2073 by (try unfold X0); omega), upd_eq _ _ (show (7 : Int) ≠ 2074 by (try unfold X0); omega), upd_eq _ _ (show (7 : Int) ≠ 13 by (try unfold X0); omega), upd_eq _ _ (show (7 : Int) ≠ 12 by (try unfold X0); omega), upd_eq _ _ (show (7 : Int) ≠ 2072 by (try unfold X0); omega), upd_eq _ _ (show (7 : Int) ≠ 8 by (try unfold X0); omega), Function.update_self]
    · show f1 (8) = 30
      rw [ag (8) (by (try unfold X0); omega) (by (try unfold X0); unfold L0; omega)]
      rw [upd_eq _ _ (show (8 : Int) ≠ 0 by (try unfold X0); omega), upd_eq _ _ (show (8 : Int) ≠ 2073 by (try unfold X0); omega), upd_eq _ _ (show (8 : Int) ≠ 2074 by (try unfold X0); omega), upd_eq _ _ (show (8 : Int) ≠ 13 by (try unfold X0); omega), upd_eq _ _ (show (8 : Int) ≠ 12 by (try unfold X0); omega), upd_eq _ _ (show (8 : Int) ≠ 2072 by (try unfold X0); omega), Function.update_self]
    · exact hk1 _ (by decide) (by unfold cBF; omega) (by simp only [cBF, X0]; omega)
    · rw [hk1 _ (by unfold LB0; omega) (by unfold LB0 L0; omega) (by simp only [LB0, X0]; omega)]; exact hlens k hk
  | succ r ih =>
    intro σ f st i hw hR hm hi hir hlens
    have hL' : 2080 + b.size + om + 318 ≤ L0 b.size om := by unfold L0; omega
    have hS := stepS_fit hw (by omega) hm rfl fixlens_mem (by decide)
      (fixlens_step hw i b.size om hL' hi (by omega) hR.inv.1.n_eq hR.inv.1.om_eq)
    have hg := (hw.store (i := 2080 + b.size + om + i) (v := fixLenI i) (by omega) (by omega)).store (i := 10)
      (v := (i : Int) + 1) (by norm_num) (by omega)
    obtain ⟨f1, hw1, hR1, hk1, ag⟩ := next_rel hb hw hR (by rw [hm]; decide) (by rw [hm]; decide) hS hg
      (S := fun c => c = 2080 + b.size + om + i ∨ c = 10) (fun c _ _ hc => by rw [upd_eq _ _ (by omega), upd_eq _ _ (by omega)])
      (fun c hc => by unfold ctl IN; omega)
    obtain ⟨σ', f', hR', hw', hRe', hm', h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, hbf, hl'⟩ :=
      ih _ f1 st (i + 1) hw1 hR1 (by rw [hk1 _ (by decide) (by unfold cMODE; omega) (by unfold cMODE; omega)]; exact hm)
        (by rw [ag _ (by decide) (by unfold cFILL; omega)]; simp [cFILL]) (by omega)
        (fun k hk => by
          by_cases hki : k = i
          · subst hki; rw [ag _ (by unfold LB0; omega) (by unfold LB0 L0; omega)]
            simp only [LB0, Function.update_apply]; rw [if_neg (by omega), if_true]
          · rw [hk1 _ (by unfold LB0; omega) (by unfold LB0 L0; omega) (by unfold LB0; omega)]; exact hlens k (by omega))
    refine ⟨σ', f', (Reach.step hS).trans hR', hw', hRe', hm', h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, ?_, hl'⟩
    rw [hbf, hk1 _ (by decide) (by unfold cBF; omega) (by unfold cBF; omega)]

/-! ## BUILD's end, by target (S-10/S-11) -/

theorem build_end_next {b : Array Nat} {om : Nat} {lit : Bool} {σ : Store} {p : Int} {f : Int → Int} {st : St}
    (hb : ∀ x ∈ b, x < 256) (hw : World σ p (L0 b.size om) f) (hR : Rel b om lit f st) (hm : f cMODE = mBUILD)
    (hph : f cPHASE = 4) (hj : f cINDEX = f (X0 b.size om + 6)) :
    ∃ σ1 f1, stepS p σ = some σ1 ∧ World σ1 p (L0 b.size om) f1 ∧ Rel b om lit f1 st ∧
      (f cTGT = 0 → f1 cMODE = mLENS ∧ Keeps (L0 b.size om) f f1 (fun c => c = 0)) ∧
      (f cTGT = 2 → f1 cMODE = mSYM ∧ Keeps (L0 b.size om) f f1 (fun c => c = 0)) ∧
      (f cTGT = 1 → f1 cMODE = mBUILD ∧ f1 cTGT = 2 ∧ f1 (X0 b.size om + 5) = LB0 b.size om + f cHLIT ∧
        f1 (X0 b.size om + 6) = f cHDIST ∧ f1 (X0 b.size om + 7) = tbase b.size om 2 ∧
        f1 (X0 b.size om + 8) = (if f cDYN = 1 then 2 else 0) ∧ f1 cPHASE = 0 ∧ f1 cINDEX = 0 ∧
        Keeps (L0 b.size om) f f1 (fun c => c = 12 ∨ c = 13 ∨ c = 2074 ∨ (X0 b.size om + 5 ≤ c ∧ c ≤ X0 b.size om + 8))) := by
  have hL : 2080 ≤ L0 b.size om := by unfold L0; omega
  have hXL : X0 b.size om + 8 < L0 b.size om := by unfold X0 L0; omega
  have hB := buildInv_of hR hm
  obtain ⟨hsb0, hnn0, hsbn, ht0, ht2, htb⟩ := build_src hB hR.inv.1.hdr_rng.1
  have hjn : ¬ f cINDEX < f (X0 b.size om + 6) := by omega
  rcases (show f cTGT = 0 ∨ f cTGT = 1 ∨ f cTGT = 2 by omega) with h0 | h1 | h2
  · have hS := stepS_fit hw (by omega) hm rfl build_mem (by decide)
      (build_syms_end_cl hw hL _ (X0 b.size om) _ _ _ hph rfl hR.inv.1.x_eq rfl rfl rfl (by unfold X0; omega) hXL hjn h0)
    have hg := hw.store (i := 0) (v := 12) (by norm_num) (by omega)
    obtain ⟨f1, hw1, hR1, hk1, ag⟩ := next_rel hb hw hR (by rw [hm]; decide) (by rw [hm]; decide) hS hg
      (S := fun c => c = 0) (fun c _ _ hc => upd_eq _ _ hc) (fun c hc => by unfold ctl; omega)
    refine ⟨_, f1, hS, hw1, hR1, fun _ => ⟨?_, hk1⟩, fun h => by omega, fun h => by omega⟩
    rw [ag _ (by decide) (by unfold cMODE; omega)]; simp [cMODE, mLENS]
  · have hS := stepS_fit hw (by omega) hm rfl build_mem (by decide)
      (build_syms_end_l hw hL _ (X0 b.size om) _ _ _ (f cHLIT) (f cHDIST) b.size om (f cDYN) hph rfl hR.inv.1.x_eq rfl rfl rfl
        (by unfold X0; omega) hXL hjn h1 rfl rfl hR.inv.1.n_eq hR.inv.1.om_eq rfl)
    have hg := ((((((hw.store (i := 2074) (v := 2) (by norm_num) (by omega)).store (i := X0 b.size om + 5)
      (v := 2080 + b.size + om + f cHLIT) (by unfold X0; omega) (by unfold X0 L0; omega)).store (i := X0 b.size om + 6)
      (v := f cHDIST) (by unfold X0; omega) (by unfold X0 L0; omega)).store (i := X0 b.size om + 7)
      (v := 2080 + b.size + om + 1041) (by unfold X0; omega) (by unfold X0 L0; omega)).store (i := X0 b.size om + 8)
      (v := if f cDYN = 1 then 2 else 0) (by unfold X0; omega) (by unfold X0 L0; omega)).store (i := 12) (v := 0)
      (by norm_num) (by omega)).store (i := 13) (v := 0) (by norm_num) (by omega)
    obtain ⟨f1, hw1, hR1, hk1, ag⟩ := next_rel hb hw hR (by rw [hm]; decide) (by rw [hm]; decide) hS hg
      (S := fun c => c = 12 ∨ c = 13 ∨ c = 2074 ∨ (X0 b.size om + 5 ≤ c ∧ c ≤ X0 b.size om + 8))
      (fun c _ _ hc => by
        rw [upd_eq _ _ (by omega), upd_eq _ _ (by omega), upd_eq _ _ (by omega), upd_eq _ _ (by omega),
          upd_eq _ _ (by omega), upd_eq _ _ (by omega), upd_eq _ _ (by omega)])
      (fun c hc => by unfold ctl IN X0 at *; omega)
    refine ⟨_, f1, hS, hw1, hR1, fun h => by omega, fun h => by omega, fun _ => ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hk1⟩⟩
    · rw [hk1 _ (by decide) (by unfold cMODE; omega) (by unfold cMODE X0; omega)]; exact hm
    · show f1 (2074) = 2
      rw [ag (2074) (by (try unfold X0); omega) (by (try unfold X0); unfold L0; omega)]
      rw [upd_eq _ _ (show (2074 : Int) ≠ 13 by (try unfold X0); omega), upd_eq _ _ (show (2074 : Int) ≠ 12 by (try unfold X0); omega), upd_eq _ _ (show (2074 : Int) ≠ X0 b.size om + 8 by (try unfold X0); omega), upd_eq _ _ (show (2074 : Int) ≠ X0 b.size om + 7 by (try unfold X0); omega), upd_eq _ _ (show (2074 : Int) ≠ X0 b.size om + 6 by (try unfold X0); omega), upd_eq _ _ (show (2074 : Int) ≠ X0 b.size om + 5 by (try unfold X0); omega), Function.update_self]
    · show f1 (X0 b.size om + 5) = LB0 b.size om + f cHLIT
      rw [ag (X0 b.size om + 5) (by (try unfold X0); omega) (by (try unfold X0); unfold L0; omega)]
      rw [upd_eq _ _ (show (X0 b.size om + 5 : Int) ≠ 13 by (try unfold X0); omega), upd_eq _ _ (show (X0 b.size om + 5 : Int) ≠ 12 by (try unfold X0); omega), upd_eq _ _ (show (X0 b.size om + 5 : Int) ≠ X0 b.size om + 8 by (try unfold X0); omega), upd_eq _ _ (show (X0 b.size om + 5 : Int) ≠ X0 b.size om + 7 by (try unfold X0); omega), upd_eq _ _ (show (X0 b.size om + 5 : Int) ≠ X0 b.size om + 6 by (try unfold X0); omega), Function.update_self]; unfold LB0; ring
    · show f1 (X0 b.size om + 6) = f cHDIST
      rw [ag (X0 b.size om + 6) (by (try unfold X0); omega) (by (try unfold X0); unfold L0; omega)]
      rw [upd_eq _ _ (show (X0 b.size om + 6 : Int) ≠ 13 by (try unfold X0); omega), upd_eq _ _ (show (X0 b.size om + 6 : Int) ≠ 12 by (try unfold X0); omega), upd_eq _ _ (show (X0 b.size om + 6 : Int) ≠ X0 b.size om + 8 by (try unfold X0); omega), upd_eq _ _ (show (X0 b.size om + 6 : Int) ≠ X0 b.size om + 7 by (try unfold X0); omega), Function.update_self]
    · show f1 (X0 b.size om + 7) = tbase b.size om 2
      rw [ag (X0 b.size om + 7) (by (try unfold X0); omega) (by (try unfold X0); unfold L0; omega)]
      rw [upd_eq _ _ (show (X0 b.size om + 7 : Int) ≠ 13 by (try unfold X0); omega), upd_eq _ _ (show (X0 b.size om + 7 : Int) ≠ 12 by (try unfold X0); omega), upd_eq _ _ (show (X0 b.size om + 7 : Int) ≠ X0 b.size om + 8 by (try unfold X0); omega), Function.update_self]; unfold tbase LB0; ring
    · show f1 (X0 b.size om + 8) = (if f cDYN = 1 then 2 else 0)
      rw [ag (X0 b.size om + 8) (by (try unfold X0); omega) (by (try unfold X0); unfold L0; omega)]
      rw [upd_eq _ _ (show (X0 b.size om + 8 : Int) ≠ 13 by (try unfold X0); omega), upd_eq _ _ (show (X0 b.size om + 8 : Int) ≠ 12 by (try unfold X0); omega), Function.update_self]
    · show f1 (12) = 0
      rw [ag (12) (by (try unfold X0); omega) (by (try unfold X0); unfold L0; omega)]
      rw [upd_eq _ _ (show (12 : Int) ≠ 13 by (try unfold X0); omega), Function.update_self]
    · show f1 (13) = 0
      rw [ag (13) (by (try unfold X0); omega) (by (try unfold X0); unfold L0; omega)]
      rw [Function.update_self]
  · have hS := stepS_fit hw (by omega) hm rfl build_mem (by decide)
      (build_syms_end_d hw hL _ (X0 b.size om) _ _ _ hph rfl hR.inv.1.x_eq rfl rfl rfl (by unfold X0; omega) hXL hjn h2)
    have hg := hw.store (i := 0) (v := 13) (by norm_num) (by omega)
    obtain ⟨f1, hw1, hR1, hk1, ag⟩ := next_rel hb hw hR (by rw [hm]; decide) (by rw [hm]; decide) hS hg
      (S := fun c => c = 0) (fun c _ _ hc => upd_eq _ _ hc) (fun c hc => by unfold ctl; omega)
    refine ⟨_, f1, hS, hw1, hR1, fun h => by omega, fun _ => ⟨?_, hk1⟩, fun h => by omega⟩
    rw [ag _ (by decide) (by unfold cMODE; omega)]; simp [cMODE, mSYM]

/-! ## Toolkit: machine prefixes of any length; `huff` over `fuelNow` -/

theorem Sim.reach {b : Array Nat} {om : Nat} {p : Int} {α : Type} {A : M α} {pre pre' : (Int → Int) → St → Prop}
    {post : α → (Int → Int) → St → Prop}
    (hs : ∀ σ f st, World σ p (L0 b.size om) f → pre f st →
      ∃ σ1 f1, Reach p σ σ1 ∧ World σ1 p (L0 b.size om) f1 ∧ pre' f1 st)
    (h : Sim b om p A pre' post) : Sim b om p A pre post := by
  intro σ f st hw hp
  obtain ⟨σ1, f1, hR1, hw1, hp1⟩ := hs σ f st hw hp
  obtain ⟨hok, herr⟩ := h σ1 f1 st hw1 hp1
  exact ⟨fun a st' h' => (hok a st' h').imp fun σ' ⟨f', hR, hw', hq⟩ => ⟨f', hR1.trans hR, hw', hq⟩,
    fun r h' => (herr r h').imp fun σ' ⟨f', hR, hw', hq⟩ => ⟨f', hR1.trans hR, hw', hq⟩⟩

/-- S7's `huff`, from SYM with both tables related. -/
theorem huff_Sim {b : Array Nat} {om : Nat} {lit : Bool} {p : Int} (hb : ∀ x ∈ b, x < 256) (bf : Int)
    (lensL lensD : Array Nat) :
    Sim b om p (huff (assign lensL) (assign lensD))
      (fun f st => (Rel b om lit f st ∧ f cMODE = mSYM) ∧ f cBF = bf ∧ TblRel b.size om f 1 lensL ∧
        TblRel b.size om f 2 lensD)
      (fun _ f st => Rel b om lit f st ∧ f cMODE = endMode bf) := by
  unfold huff
  intro σ f st hw ⟨hRm, hbf, h1, h2⟩
  have e : go fuelNow ⟨b, om⟩ st = .ok (8 * b.size - st.pos + 1, st) := go_fuelNow _ _
  have := huff_sim (lit := lit) hb bf lensL lensD (8 * b.size - st.pos + 1) σ f st hw ⟨hRm, hbf, h1, h2, by omega⟩
  refine ⟨fun a st' h => ?_, fun r h => ?_⟩
  · rw [go_bind, e] at h; exact this.1 a st' h
  · rw [go_bind, e] at h; exact this.2 r h

/-- S4's `code`, in the triple form, from a BUILD start (CHK = 1). -/
theorem code_Sim {b : Array Nat} {om : Nat} {lit : Bool} {p : Int} (hb : ∀ x ∈ b, x < 256) (lens : Array Nat)
    (md : Mode) (f₀ : Int → Int) (h15 : ∀ i, i < lens.size → lens.getD i 0 ≤ 15) :
    Sim b om p (code lens md)
      (fun f st => f = f₀ ∧ Rel b om lit f st ∧ f cMODE = mBUILD ∧ f cPHASE = 0 ∧ f cINDEX = 0 ∧
        f (X0 b.size om + 6) = lens.size ∧ (∀ i : Nat, i < lens.size → f (f (X0 b.size om + 5) + i) = lens.getD i 0) ∧
        f cCHK = 1 ∧ f (X0 b.size om + 8) = varOf md)
      (fun C f' st' => C = assign lens ∧ Built b om lit lens f₀ f' st') := by
  rintro σ f st hw ⟨rfl, hR, hm, hph, hj, hnn, hsrc, hchk, hvar⟩
  obtain ⟨hok, herr⟩ := (build_tbl (lit := lit) hb lens md hw hR hm hph hj hnn hsrc h15).2 hchk hvar
  refine ⟨fun C st' h => ?_, herr⟩
  obtain ⟨hC, rfl, σ', f', hR', hw', hB'⟩ := hok C st' h
  exact ⟨σ', f', hR', hw', hC, hB'⟩

theorem fixedL_getD (k : Nat) (hk : k < 288) : (fixedLLens.getD k 0 : Int) = fixLenI k := by
  have e : fixedLLens.getD k 0 = if k < 144 then 8 else if k < 256 then 9 else if k < 280 then 7 else 8 := by
    simp [fixedLLens, Array.getD, hk]
  rw [e]; unfold fixLenI; split_ifs <;> first | omega | norm_num

theorem fixedD_getD (k : Nat) (hk : k < 30) : (fixedDLens.getD k 0 : Int) = fixLenI (288 + k) := by
  have e : fixedDLens.getD k 0 = 5 := by simp [fixedDLens, Array.getD, hk]
  rw [e]; unfold fixLenI; split_ifs <;> first | omega | norm_num

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

namespace VIRDeflate.Step
open VIRL1 VIRL2

/-! ## The top: the forward statement from the three bodies -/

theorem outOf_world {b : Array Nat} {om : Nat} {lit : Bool} {σ : Store} {p : Int} {f : Int → Int} {st : St}
    (hw : World σ p (L0 b.size om) f) (hR : Rel b om lit f st) : outOf p b.size σ = st.out := by
  have hm := hR.m
  have hmr := hR.inv.1.m_rng
  have hc3 := hw.cell cM (by decide) (by unfold cM L0; omega)
  unfold outOf
  simp only [hc3, Option.getD_some, hm, Int.toNat_natCast]
  apply Array.ext
  · simp
  · intro i h1 h2
    have hi : i < st.out.size := h2
    have hc := hw.cell (IN + b.size + i) (by unfold IN; omega) (by unfold IN L0; push_cast; omega)
    have ho := hR.out i hi
    simp only [IN] at hc ho
    have key : ((σ.H.lookup (p + (2080 + (b.size : Int) + (i : Int)))).getD 0).toNat = st.out[i] := by
      rw [hc, Option.getD_some, ho]; simp [Array.getD, hi]
    have e : ∀ l : List Nat, List.flatMap (fun a : Nat => [(a : Int)]) l = l.map (fun a : Nat => (a : Int)) := by
      intro l; induction l with
      | nil => rfl
      | cons x l ih => simp [List.flatMap_cons, ih]
    simp
    rw [List.getElem_of_eq (e _), List.getElem_map, List.getElem_range]
    exact key

/-- **The forward statement from the three block bodies (S-18).** -/
theorem fwd_of_bodies
    (HS : ∀ b om lit p, (∀ x ∈ b, x < 256) → BodySim b om lit p stored mSHDR (fun _ => True))
    (HF : ∀ b om lit p, (∀ x ∈ b, x < 256) → BodySim b om lit p (fixedBody lit) mFIXLENS (fun f => f cFILL = 0))
    (HD : ∀ b om lit p, (∀ x ∈ b, x < 256) → BodySim b om lit p dynamic mDHDR (fun _ => True)) : FwdStmt := by
  intro b om lit p hb
  have hL : 0 < L0 b.size om := by unfold L0; omega
  obtain ⟨σ, f, hR0, hw, hi, hm, hbits, h1, h2, h3⟩ := init_to_hdr b om lit p
  have hR : Rel b om lit f ⟨0, #[]⟩ := ⟨hi, hbits, by rw [h1, h2]; rfl, by rw [h3]; rfl, fun i h => by simp at h⟩
  have hsim := blocks_sim (lit := lit) (p := p) hb (HS b om lit p hb) (HF b om lit p hb) (HD b om lit p hb)
    (8 * b.size + 1) σ f ⟨0, #[]⟩ hw ⟨hR, hm, by omega⟩
  have hrun := run_adequate lit b om (8 * b.size + 1) (by omega)
  constructor
  · intro o ho
    rw [hrun] at ho
    rcases hg : go (blocks lit (8 * b.size + 1)) ⟨b, om⟩ ⟨0, #[]⟩ with r | ⟨u, s⟩
    · rw [hg] at ho; simp at ho
    · rw [hg] at ho
      simp only [Except.ok.injEq] at ho
      obtain ⟨σ', f', hR', hw', hRel, hmd⟩ := hsim.1 u s hg
      obtain ⟨k, hk⟩ := hR0.trans hR'
      exact ⟨k, σ', hk, by rw [modeOf_world hw' hL]; exact hmd, by rw [outOf_world hw' hRel, ho]⟩
  · intro r hr
    rw [hrun] at hr
    rcases hg : go (blocks lit (8 * b.size + 1)) ⟨b, om⟩ ⟨0, #[]⟩ with r' | ⟨u, s⟩
    · obtain ⟨σ', f', hR', hw', hmd⟩ := hsim.2 r' hg
      obtain ⟨k, hk⟩ := hR0.trans hR'
      exact ⟨k, σ', hk, by rw [modeOf_world hw' hL]; exact hmd⟩
    · rw [hg] at hr; simp at hr

theorem correct_of_bodies
    (HS : ∀ b om lit p, (∀ x ∈ b, x < 256) → BodySim b om lit p stored mSHDR (fun _ => True))
    (HF : ∀ b om lit p, (∀ x ∈ b, x < 256) → BodySim b om lit p (fixedBody lit) mFIXLENS (fun f => f cFILL = 0))
    (HD : ∀ b om lit p, (∀ x ∈ b, x < 256) → BodySim b om lit p dynamic mDHDR (fun _ => True)) : CorrectStmt :=
  correct_of_fwd (fwd_of_bodies HS HF HD)

end VIRDeflate.Step
