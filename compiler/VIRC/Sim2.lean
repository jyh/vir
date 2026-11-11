/-
  O95 compiler, stage S2: the simulation, IR (S1) ↔ word machine. Part 1, AGREEMENT. A term closed below n infers, and lowers,
  the same under any two contexts that agree below n. A λ body is lowered under its own closed context and typed under the
  context where its atom occurs. These lemmas make that one fact rather than two.
-/
import VIRC.Table

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

end VIRC
