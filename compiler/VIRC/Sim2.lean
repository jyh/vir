/-
  O95 compiler, stage S2: the simulation, IR (S1) ↔ word machine. Part 1, AGREEMENT. A term closed below n infers, and lowers,
  the same under any two contexts that agree below n. A λ body is lowered under its own closed context and typed under the
  context where its atom occurs. These lemmas make that one fact rather than two.
-/
import VIRC.Table
import VIRC.Converse

namespace VIRC
open VIRL1 VIRL2

def Agree (n : Nat) (Γ Γ' : Ctx S₂) : Prop := ∀ i, i < n → Γ[i]? = Γ'[i]?

theorem Agree.cons {n Γ Γ'} (τ : Ty₂) (h : Agree n Γ Γ') : Agree (n + 1) (τ :: Γ) (τ :: Γ') := by
  intro i hi; cases i with
  | zero => rfl
  | succ i => simpa using h i (by omega)

theorem offset_agree {n Γ Γ'} (h : Agree n Γ Γ') : ∀ i, i < n → offset Γ i = offset Γ' i := by
  intro i hi
  unfold offset
  congr 2
  apply List.ext_getElem?
  intro j
  rw [List.getElem?_take, List.getElem?_take]
  split
  · exact h j (by omega)
  · rfl

theorem varSlice_agree {n Γ Γ'} (h : Agree n Γ Γ') {i} (hi : i < n) : varSlice Γ i = varSlice Γ' i := by
  simp only [varSlice, offset_agree h i hi, h i hi]

mutual
theorem inferA_agree : ∀ (a : Atom₂) {n Γ Γ'}, Atom.wfB n a = true → Agree n Γ Γ' → inferA Γ a = inferA Γ' a
  | .var m, _, _, _, hw, h => by simp only [Atom.wfB, decide_eq_true_eq] at hw; simp only [inferA, h m hw]
  | .const (.int _), _, _, _, _, _ => rfl
  | .const (.bool _), _, _, _, _, _ => rfl
  | .const .unit, _, _, _, _, _ => rfl
  | .const (.cap _), _, _, _, _, _ => rfl
  | .prim _ _, _, _, _, _, _ => rfl
  | .lam τ e, _, _, _, hw, h => by
      simp only [Atom.wfB] at hw; simp only [inferA, inferT_agree e hw (h.cons τ)]
  | .fix _ _ _, _, _, _, _, _ => rfl
  | .pair a₁ a₂, _, _, _, hw, h => by
      simp only [Atom.wfB, Bool.and_eq_true] at hw; simp only [inferA, inferA_agree a₁ hw.1 h, inferA_agree a₂ hw.2 h]
  | .fst a, _, _, _, hw, h => by simp only [Atom.wfB] at hw; simp only [inferA, inferA_agree a hw h]
  | .snd a, _, _, _, hw, h => by simp only [Atom.wfB] at hw; simp only [inferA, inferA_agree a hw h]
  | .inl _ a, _, _, _, hw, h => by simp only [Atom.wfB] at hw; simp only [inferA, inferA_agree a hw h]
  | .inr _ a, _, _, _, hw, h => by simp only [Atom.wfB] at hw; simp only [inferA, inferA_agree a hw h]
theorem inferT_agree : ∀ (e : Tm₂) {n Γ Γ'}, Tm.wfB n e = true → Agree n Γ Γ' → inferT Γ e = inferT Γ' e
  | .ret a, _, _, _, hw, h => by simp only [Tm.wfB] at hw; simp only [inferT, inferA_agree a hw h]
  | .letE τ _ e₂, _, _, _, hw, h => by
      simp only [Tm.wfB, Bool.and_eq_true] at hw; simp only [inferT, inferT_agree e₂ hw.2 (h.cons τ)]
  | .letOp _ _ τ e, _, _, _, hw, h => by
      simp only [Tm.wfB, Bool.and_eq_true] at hw; simp only [inferT, inferT_agree e hw.2 (h.cons τ)]
  | .app a₁ _, _, _, _, hw, h => by
      simp only [Tm.wfB, Bool.and_eq_true] at hw; simp only [inferT, inferA_agree a₁ hw.1 h]
  | .ite _ e₁ _, _, _, _, hw, h => by
      simp only [Tm.wfB, Bool.and_eq_true] at hw; simp only [inferT, inferT_agree e₁ hw.1.2 h]
  | .case a e₁ _, _, _, _, hw, h => by
      simp only [Tm.wfB, Bool.and_eq_true] at hw
      simp only [inferT, inferA_agree a hw.1.1 h]
      cases inferA _ a with
      | none => rfl
      | some t => cases t <;> simp only [Option.bind_some] <;> exact inferT_agree e₁ hw.1.2 (h.cons _)
end

theorem opCode_agree {n Γ Γ'} (h : Agree n Γ Γ') (o : VIRL2.Op) (as : List Atom₂) (os : List WOpd) (k : WCode)
    (hw : Atom.wfLB n as = true) : opCode Γ o as os k = opCode Γ' o as os k := by
  unfold opCode
  split
  · next m _ _ _ =>
    simp only [Atom.wfLB, Atom.wfB, decide_eq_true_eq, Bool.and_eq_true] at hw
    rw [offset_agree h m hw.1]
  · next m _ _ _ _ _ =>
    simp only [Atom.wfLB, Atom.wfB, decide_eq_true_eq, Bool.and_eq_true] at hw
    rw [offset_agree h m hw.1]
  · rfl

mutual
theorem lower2A_agree : ∀ (a : Atom₂) {n Γ Γ'} (t : Table), Atom.wfB n a = true → Agree n Γ Γ' →
    lower2A Γ a t = lower2A Γ' a t
  | .var m, _, _, _, _, hw, h => by
      simp only [Atom.wfB, decide_eq_true_eq] at hw; simp only [lower2A, varSlice_agree h hw]
  | .const (.int _), _, _, _, _, _, _ => rfl
  | .const (.bool _), _, _, _, _, _, _ => rfl
  | .const .unit, _, _, _, _, _, _ => rfl
  | .const (.cap _), _, _, _, _, _, _ => rfl
  | .prim _ as, _, _, _, t, hw, h => by
      simp only [Atom.wfB] at hw; simp only [lower2A, lower2L_agree as t hw h]
  | .lam _ _, _, _, _, _, _, _ => rfl
  | .fix _ _ _, _, _, _, _, _, _ => rfl
  | .pair a₁ a₂, _, _, _, t, hw, h => by
      simp only [Atom.wfB, Bool.and_eq_true] at hw
      simp only [lower2A, lower2A_agree a₁ t hw.1 h, lower2A_agree a₂ _ hw.2 h]
  | .fst a, _, _, _, t, hw, h => by
      simp only [Atom.wfB] at hw; simp only [lower2A, lower2A_agree a t hw h, inferA_agree a hw h]
  | .snd a, _, _, _, t, hw, h => by
      simp only [Atom.wfB] at hw; simp only [lower2A, lower2A_agree a t hw h, inferA_agree a hw h]
  | .inl _ a, _, _, _, t, hw, h => by
      simp only [Atom.wfB] at hw; simp only [lower2A, lower2A_agree a t hw h, inferA_agree a hw h]
  | .inr _ a, _, _, _, t, hw, h => by
      simp only [Atom.wfB] at hw; simp only [lower2A, lower2A_agree a t hw h, inferA_agree a hw h]
theorem lower2L_agree : ∀ (as : List Atom₂) {n Γ Γ'} (t : Table), Atom.wfLB n as = true → Agree n Γ Γ' →
    lower2L Γ as t = lower2L Γ' as t
  | [], _, _, _, _, _, _ => rfl
  | a :: as, _, _, _, t, hw, h => by
      simp only [Atom.wfLB, Bool.and_eq_true] at hw
      simp only [lower2L, lower2A_agree a t hw.1 h, lower2L_agree as _ hw.2 h]
theorem lower2T_agree : ∀ (e : Tm₂) {n Γ Γ'} (t : Table), Tm.wfB n e = true → Agree n Γ Γ' →
    lower2T Γ e t = lower2T Γ' e t
  | .ret a, _, _, _, t, hw, h => by simp only [Tm.wfB] at hw; simp only [lower2T, lower2A_agree a t hw h]
  | .letE τ e₁ e₂, _, _, _, t, hw, h => by
      simp only [Tm.wfB, Bool.and_eq_true] at hw
      simp only [lower2T, lower2T_agree e₁ t hw.1 h, lower2T_agree e₂ _ hw.2 (h.cons τ)]
  | .letOp o as τ e, _, _, _, t, hw, h => by
      simp only [Tm.wfB, Bool.and_eq_true] at hw
      simp only [lower2T, lower2L_agree as t hw.1 h, lower2T_agree e _ hw.2 (h.cons τ), opCode_agree h o as _ _ hw.1]
  | .app a₁ a₂, _, _, _, t, hw, h => by
      simp only [Tm.wfB, Bool.and_eq_true] at hw
      simp only [lower2T, lower2A_agree a₁ t hw.1 h, lower2A_agree a₂ _ hw.2 h]
  | .ite a e₁ e₂, _, _, _, t, hw, h => by
      simp only [Tm.wfB, Bool.and_eq_true] at hw
      simp only [lower2T, lower2A_agree a t hw.1.1 h, lower2T_agree e₁ _ hw.1.2 h, lower2T_agree e₂ _ hw.2 h]
  | .case a e₁ e₂, _, _, _, t, hw, h => by
      simp only [Tm.wfB, Bool.and_eq_true] at hw
      simp only [lower2T, lower2A_agree a t hw.1.1 h, inferA_agree a hw.1.1 h]
      cases inferA _ a with
      | none => rfl
      | some ty =>
        cases ty with
        | sum t₁ t₂ => simp only [lower2T_agree e₁ _ hw.1.2 (h.cons t₁), lower2T_agree e₂ _ hw.2 (h.cons t₂)]
        | _ => rfl
end

/-! ## Part 2: the value and environment relations. -/
theorem toInt_word {n : Int} (h : inRange n = true) : (BitVec.ofInt 64 n).toInt = n := by
  simp only [inRange, decide_eq_true_eq] at h
  exact BitVec.toInt_ofInt_eq_self (by decide) (by simpa using h.1) (by simpa using h.2)

/-- Entries from index j on are kept (a body's OWN slot, below j, is filled after the body is lowered). -/
def KeepsFrom (j : Nat) (a b : Table) : Prop := a.length ≤ b.length ∧ ∀ i, j ≤ i → i < a.length → b[i]? = a[i]?

theorem KeepsFrom.of_keeps {j} {a b c : Table} (h₁ : Keeps a b) (h₂ : KeepsFrom j b c) : KeepsFrom j a c :=
  ⟨le_trans h₁.1 h₂.1, fun i hj hi => by rw [h₂.2 i hj (lt_of_lt_of_le hi h₁.1), h₁.2 i hi]⟩

theorem KeepsFrom.mono {j j'} {a b : Table} (hj : j ≤ j') (h : KeepsFrom j a b) : KeepsFrom j' a b :=
  ⟨h.1, fun i hi hl => h.2 i (le_trans hj hi) hl⟩

/-- A function body, typed: under its closed context Γb, extended by SOME outer context (agreement makes the rest irrelevant). -/
def BodyOK (Γb : Ctx S₂) (τ : Ty₂) (e : Tm₂) : Prop :=
  ∃ Γ Δ, HasType₂ (Γb ++ Γ) Δ e τ ∧ Tm.wfB Γb.length e = true ∧ Tm.fnOk e = true ∧ Tm.ok2 e = true

/-- Label l of the final table T holds the lowering of body e, lowered from a table of length l + 1 whose later entries T keeps. -/
def CodeAt (T : Table) (l : Nat) (b : Bool) (Γb : Ctx S₂) (e : Tm₂) : Prop :=
  ∃ t, t.length = l + 1 ∧ T[l]? = some (b, (lower2T Γb e t).1) ∧ KeepsFrom (l + 1) (lower2T Γb e t).2 T

inductive VRel (T : Table) (lay : Int → W) (σ : Store) : Ty₂ → Val → List W → Prop where
  | int {n : Int} : inRange n = true → VRel T lay σ (Ty.base BTy.int) (Val.const (.int n)) [BitVec.ofInt 64 n]
  | bool {b : Bool} : VRel T lay σ (Ty.base BTy.bool) (Val.const (.bool b)) [boolW b]
  | unit : VRel T lay σ (Ty.base BTy.unit) (Val.const .unit) [0]
  | cap {p : Int} {n : Nat} : σ.R.lookup p = some n → VRel T lay σ (Ty.base BTy.cap) (Val.const (.cap p)) [lay p, BitVec.ofNat 64 n]
  | lam {τ₁ τ₂ : Ty₂} {e : Tm₂} {l : Nat} : l < 2 ^ 64 → CodeAt T l false [τ₁] e → BodyOK [τ₁] τ₂ e →
      VRel T lay σ (Ty.arr τ₁ τ₂) (Val.code false (lowerT e)) [BitVec.ofNat 64 l]
  | fix {τ₁ τ₂ : Ty₂} {e : Tm₂} {l : Nat} : l < 2 ^ 64 → CodeAt T l true [τ₁, Ty.arr τ₁ τ₂] e →
      BodyOK [τ₁, Ty.arr τ₁ τ₂] τ₂ e → VRel T lay σ (Ty.arr τ₁ τ₂) (Val.code true (lowerT e)) [BitVec.ofNat 64 l]
  | pair {τ₁ τ₂ v₁ v₂ w₁ w₂} : VRel T lay σ τ₁ v₁ w₁ → VRel T lay σ τ₂ v₂ w₂ →
      VRel T lay σ (Ty.prod τ₁ τ₂) (Val.pair v₁ v₂) (w₁ ++ w₂)
  | inl {τ₁ τ₂ v w} : VRel T lay σ τ₁ v w →
      VRel T lay σ (Ty.sum τ₁ τ₂) (Val.inl v) (0 :: w ++ List.replicate (max (size τ₁) (size τ₂) - size τ₁) 0)
  | inr {τ₁ τ₂ v w} : VRel T lay σ τ₂ v w →
      VRel T lay σ (Ty.sum τ₁ τ₂) (Val.inr v) (1 :: w ++ List.replicate (max (size τ₁) (size τ₂) - size τ₂) 0)

theorem VRel.length {T lay σ} : ∀ {τ v ws}, VRel T lay σ τ v ws → ws.length = size τ
  | _, _, _, .int _ => rfl
  | _, _, _, .bool => rfl
  | _, _, _, .unit => rfl
  | _, _, _, .cap _ => rfl
  | _, _, _, .lam _ _ _ => rfl
  | _, _, _, .fix _ _ _ => rfl
  | _, _, _, .pair h₁ h₂ => by simp [size, h₁.length, h₂.length]
  | _, _, _, .inl (τ₁ := τ₁) (τ₂ := τ₂) h => by simp [size, h.length]; omega
  | _, _, _, .inr (τ₁ := τ₁) (τ₂ := τ₂) h => by simp [size, h.length]; omega

inductive EnvRel (T : Table) (lay : Int → W) (σ : Store) : Ctx S₂ → List Val → List W → Prop where
  | nil : EnvRel T lay σ [] [] []
  | cons {τ Γ v ρ ws ρw} : VRel T lay σ τ v ws → EnvRel T lay σ Γ ρ ρw → EnvRel T lay σ (τ :: Γ) (v :: ρ) (ws ++ ρw)

theorem EnvRel.length {T lay σ} : ∀ {Γ ρ ρw}, EnvRel T lay σ Γ ρ ρw → ρw.length = (Γ.map size).sum
  | _, _, _, .nil => rfl
  | _, _, _, .cons h hs => by simp [h.length, hs.length]

/-- A variable's slice reads its value's words. -/
theorem EnvRel.lookup {T lay σ} : ∀ {Γ ρ ρw}, EnvRel T lay σ Γ ρ ρw → ∀ {n τ}, Γ[n]? = some τ →
    ∃ v ws, ρ[n]? = some v ∧ VRel T lay σ τ v ws ∧ evalW ρw (varSlice Γ n) = .ok ws
  | _, _, _, .nil, _, _, h => by simp at h
  | _, _, _, .cons (ws := ws) (ρw := ρw) hv hs, 0, _, h => by
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h; subst h
      refine ⟨_, _, rfl, hv, ?_⟩
      have hl := hv.length
      simp only [varSlice, offset, List.take_zero, List.map_nil, List.sum_nil, List.getElem?_cons_zero, Option.map_some,
        Option.getD_some, evalW, List.drop_zero, List.length_append, hl]
      rw [if_pos (by omega)]
      simp [List.take_append_of_le_length, hl]
  | _, _, _, .cons (τ := τ') (ws := ws) (ρw := ρw) hv hs, n + 1, τ, h => by
      simp only [List.getElem?_cons_succ] at h
      obtain ⟨v, ws', h1, h2, h3⟩ := hs.lookup h
      refine ⟨v, ws', by simpa using h1, h2, ?_⟩
      have hl := hv.length
      have hrest := hs.length
      simp only [varSlice, offset, evalW] at h3 ⊢
      simp only [List.take_succ_cons, List.map_cons, List.sum_cons, List.getElem?_cons_succ, List.length_append] at h3 ⊢
      split at h3
      · rw [if_pos (by omega)]
        rw [show size τ' + ((List.take n _).map size).sum = ws.length + ((List.take n _).map size).sum by rw [hl]]
        rw [← List.drop_drop, List.drop_left]; exact h3
      · cases h3

end VIRC
