/-
  O95 compiler, stage S2 (compiler/DECLARATIONS-S2.md, "Added"): syntax-directed type inference for L2. S2 sizes every value by
  its type (S2-R (a)), and S1's IR erased types, so S2 reads them back from the source. Masks (Δ) play no part in a type.
  `inferT_sound`: a ⊢₂ derivation FIXES the inferred type, so S2's sizes are the derivation's.
-/
import VIRC.Fragment

namespace VIRC
open VIRL1 VIRL2

mutual
def inferA (Γ : Ctx S₂) : Atom₂ → Option Ty₂
  | .var n => Γ[n]?
  | .const (.int _) => some tint
  | .const (.bool _) => some tbool
  | .const .unit => some tunit
  | .const (.cap _) => none
  | .prim p _ => some (.base (S₂.pRes p))
  | .lam τ₁ e => (inferT (τ₁ :: Γ) e).map (.arr τ₁)
  | .fix τ₁ τ₂ _ => some (.arr τ₁ τ₂)
  | .pair a₁ a₂ => (inferA Γ a₁).bind fun t₁ => (inferA Γ a₂).map (.prod t₁)
  | .fst a => (inferA Γ a).bind fun t => match t with
    | .prod t₁ _ => some t₁
    | _ => none
  | .snd a => (inferA Γ a).bind fun t => match t with
    | .prod _ t₂ => some t₂
    | _ => none
  | .inl τ₂ a => (inferA Γ a).map (.sum · τ₂)
  | .inr τ₁ a => (inferA Γ a).map (.sum τ₁)
def inferT (Γ : Ctx S₂) : Tm₂ → Option Ty₂
  | .ret a => inferA Γ a
  | .letE τ₁ _ e₂ => inferT (τ₁ :: Γ) e₂
  | .letOp _ _ τ e => inferT (τ :: Γ) e
  | .app a₁ _ => (inferA Γ a₁).bind fun t => match t with
    | .arr _ t₂ => some t₂
    | _ => none
  | .ite _ e₁ _ => inferT Γ e₁
  | .case a e₁ _ => (inferA Γ a).bind fun t => match t with
    | .sum t₁ _ => inferT (t₁ :: Γ) e₁
    | _ => none
end

mutual
theorem inferA_sound : ∀ {Γ a τ}, HasTypeA₂ Γ a τ → inferA Γ a = some τ
  | _, _, _, .var h _ => by simp [inferA, h]
  | _, _, _, .int => rfl
  | _, _, _, .bool => rfl
  | _, _, _, .unit => rfl
  | _, _, _, .prim _ => rfl
  | _, _, _, .lam _ _ _ _ h => by simp [inferA, inferT_sound h]
  | _, _, _, .fix _ _ _ _ _ => rfl
  | _, _, _, .pair h₁ h₂ => by simp [inferA, inferA_sound h₁, inferA_sound h₂]
  | _, _, _, .fst h => by simp [inferA, inferA_sound h]
  | _, _, _, .snd h => by simp [inferA, inferA_sound h]
  | _, _, _, .inl _ h => by simp [inferA, inferA_sound h]
  | _, _, _, .inr _ h => by simp [inferA, inferA_sound h]
theorem inferT_sound : ∀ {Γ Δ e τ}, HasType₂ Γ Δ e τ → inferT Γ e = some τ
  | _, _, _, _, .ret _ h => inferA_sound h
  | _, _, _, _, .retCap h _ => by simp [inferT, inferA, h]
  | _, _, _, _, .letE _ _ _ h₂ => by simp only [inferT]; exact inferT_sound h₂
  | _, _, _, _, .alloc _ h => by simp only [inferT]; exact inferT_sound h
  | _, _, _, _, .load _ _ _ h => by simp only [inferT]; exact inferT_sound h
  | _, _, _, _, .store _ _ _ _ h => by simp only [inferT]; exact inferT_sound h
  | _, _, _, _, .free _ _ h => by simp only [inferT]; exact inferT_sound h
  | _, _, _, _, .app _ h₁ _ => by simp [inferT, inferA_sound h₁]
  | _, _, _, _, .ite _ h₁ _ => by simp only [inferT]; exact inferT_sound h₁
  | _, _, _, _, .case h h₁ _ => by simp [inferT, inferA_sound h, inferT_sound h₁]
end

end VIRC
