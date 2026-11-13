/-
  O95 compiler, K5-1a (compiler/DECLARATIONS-K5.md, addendum 1, written before this file): the OVERFLOW exit is reached only
  where an IR step computes an int outside [−2⁶³, 2⁶³). DECLARATIONS-S2 l. 39 promised it and no theorem stated it (K5-0).
  New theorems beside Sim2; Sim2.lean is not edited.
-/
import VIRC.S2

namespace VIRC
open VIRL1 VIRL2

/-! ## The in-range predicate, on the IR (S1's image of the program). -/
/-- An IR value is in range when it is not an int, or an int in [−2⁶³, 2⁶³). -/
def Val.inR : VIRC.Val → Prop
  | .const (.int n) => inRange n = true
  | _ => True

mutual
/-- Every primitive sub-operand that evaluates gives an in-range value. -/
def Opd.InR (ρ : List VIRC.Val) : Opd → Prop
  | .var _ => True
  | .const _ => True
  | .prim p os => Opd.InRL ρ os ∧ ∀ v, Opd.eval ρ (.prim p os) = some v → v.inR
  | .code _ _ => True
  | .pair o₁ o₂ => Opd.InR ρ o₁ ∧ Opd.InR ρ o₂
  | .fst o => Opd.InR ρ o
  | .snd o => Opd.InR ρ o
  | .inl o => Opd.InR ρ o
  | .inr o => Opd.InR ρ o
def Opd.InRL (ρ : List VIRC.Val) : List Opd → Prop
  | [] => True
  | o :: os => Opd.InR ρ o ∧ Opd.InRL ρ os
end

/-- The operands the IR step at a state evaluates are in range. -/
def StepInR : St × Store → Prop
  | (.run (.ret o) ρ _, _) => Opd.InR ρ o
  | (.run (.letE _ _) _ _, _) => True
  | (.run (.letOp _ os _) ρ _, _) => Opd.InRL ρ os
  | (.run (.app f x) ρ _, _) => Opd.InR ρ f ∧ Opd.InR ρ x
  | (.run (.ite o _ _) ρ _, _) => Opd.InR ρ o
  | (.run (.case o _ _) ρ _, _) => Opd.InR ρ o
  | (.done _, _) => True

/-- Every state the IR run from I₀ reaches steps on in-range operands. A predicate on VALUES, never on input bytes. -/
def InRangeRun (I₀ : St × Store) : Prop := ∀ n I, IRN n I₀ I → StepInR I

/-! ## (i) A word step to `.ovf` evaluates some head operand to `.ovf`. -/
def WCode.heads : WCode → List WOpd
  | .ret o => [o]
  | .letE _ _ => []
  | .load _ i _ => [i]
  | .store _ i v _ => [i, v]
  | .app f x => [f, x]
  | .ite o _ _ => [o]
  | .case o _ _ _ _ => [o]

theorem stepW_noovf {T : Table} {wc : WCode} {ρw : List W} {kw m W'} (hn : ∀ o ∈ wc.heads, evalW ρw o ≠ .ovf)
    (h : stepW T (.run wc ρw kw, m) = some W') : W'.1 ≠ .ovf := by
  cases wc <;>
    simp only [WCode.heads, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hn <;>
    simp only [stepW] at h <;> (repeat' split at h) <;>
    (try simp only [Option.some.injEq] at h) <;> (try subst h) <;> simp_all

/-! ## (ii) A typed, accepted atom whose IR image is in range never evaluates to `.ovf`. -/
theorem slice_noovf (ρw : List W) (off len : Nat) : evalW ρw (.slice off len) ≠ .ovf := by
  simp only [evalW]; split <;> simp

mutual
theorem opd_noovf {T lay σ} (hT : T.length < 2 ^ 64) : ∀ {a : Atom₂} {Γl Γt : Ctx S₂} {k : Nat} {τ : Ty₂}
    {ρ : List VIRC.Val} {ρw : List W} (t : Table),
    HasTypeA₂ Γt a τ → Atom.wfB k a = true → Agree k Γl Γt → EnvRel T lay σ Γl ρ ρw →
    Atom.fnOk a = true → Atom.ok2 a = true → KeepsFrom t.length (lower2A Γl a t).2 T →
    Opd.InR ρ (lowerA a) → evalW ρw (lower2A Γl a t).1 ≠ .ovf
  | _, Γl, _, _, _, _, ρw, _, .var (n := n) _ _, _, _, _, _, _, _, _ => by
      simp only [lower2A, varSlice]; exact slice_noovf _ _ _
  | _, _, _, _, _, _, _, _, .int, _, _, _, _, _, _, _ => by simp [lower2A, evalW]
  | _, _, _, _, _, _, _, _, .bool, _, _, _, _, _, _, _ => by simp [lower2A, evalW]
  | _, _, _, _, _, _, _, _, .unit, _, _, _, _, _, _, _ => by simp [lower2A, evalW]
  | _, Γl, Γt, k, _, ρ, ρw, t, .prim (p := p) (as := as) hl, hw, hag, he, hf, hok, hk, hin => by
      simp only [Atom.wfB] at hw; simp only [Atom.fnOk] at hf; simp only [Atom.ok2] at hok
      simp only [lower2A] at hk ⊢
      simp only [lowerA, Opd.InR] at hin
      obtain ⟨hinL, hres⟩ := hin
      obtain ⟨vs, hev, hout⟩ := opdL_sim hT t hl hw hag he hf hok hk
      have hall := opdL_noovf hT t hl hw hag he hf hok hk hinL
      rw [eval_prim hev] at hres
      generalize (lower2L Γl as t).1 = os at hout hall ⊢
      cases p <;> simp only [S₂, L1.Prim.args, L1.Prim.res, BTy.ofL1, List.map] at hout ⊢
      all_goals rcases hout with _ | ⟨hv1, hw1, _ | ⟨hv2, hw2, ⟨⟩⟩⟩
      -- add · sub · mul: the one place `chk` can say `.ovf`, and `hres` says the result is in range
      · obtain ⟨x, rfl, hx⟩ := wout_int hv1 hw1; obtain ⟨y, rfl, hy⟩ := wout_int hv2 hw2
        obtain ⟨rx, hx⟩ := hx.resolve_left (hall _ (by simp)); obtain ⟨ry, hy⟩ := hy.resolve_left (hall _ (by simp))
        have hr := hres (.const (.int (x + y))) (by simp [List.mapM_cons, Val.asConst, pInterp, Const.toL1,
          L1.Prim.interp, Const.ofL1])
        simp only [Val.inR] at hr
        simp [primW, evalW, WRes.bind, hx, hy, AOp.apply, toInt_word rx, toInt_word ry, chk, hr]
      · obtain ⟨x, rfl, hx⟩ := wout_int hv1 hw1; obtain ⟨y, rfl, hy⟩ := wout_int hv2 hw2
        obtain ⟨rx, hx⟩ := hx.resolve_left (hall _ (by simp)); obtain ⟨ry, hy⟩ := hy.resolve_left (hall _ (by simp))
        have hr := hres (.const (.int (x - y))) (by simp [List.mapM_cons, Val.asConst, pInterp, Const.toL1,
          L1.Prim.interp, Const.ofL1])
        simp only [Val.inR] at hr
        simp [primW, evalW, WRes.bind, hx, hy, AOp.apply, toInt_word rx, toInt_word ry, chk, hr]
      · obtain ⟨x, rfl, hx⟩ := wout_int hv1 hw1; obtain ⟨y, rfl, hy⟩ := wout_int hv2 hw2
        obtain ⟨rx, hx⟩ := hx.resolve_left (hall _ (by simp)); obtain ⟨ry, hy⟩ := hy.resolve_left (hall _ (by simp))
        have hr := hres (.const (.int (x * y))) (by simp [List.mapM_cons, Val.asConst, pInterp, Const.toL1,
          L1.Prim.interp, Const.ofL1])
        simp only [Val.inR] at hr
        simp [primW, evalW, WRes.bind, hx, hy, AOp.apply, toInt_word rx, toInt_word ry, chk, hr]
      -- lt · le · eq · max: never `.ovf` once the operands are not
      all_goals first
        | (obtain ⟨x, rfl, hx⟩ := wout_int hv1 hw1; obtain ⟨y, rfl, hy⟩ := wout_int hv2 hw2
           obtain ⟨rx, hx⟩ := hx.resolve_left (hall _ (by simp))
           obtain ⟨ry, hy⟩ := hy.resolve_left (hall _ (by simp))
           simp [primW, evalW, WRes.bind, hx, hy, AOp.apply])
        | (obtain ⟨x, rfl, hx⟩ := wout_bool hv1 hw1; obtain ⟨y, rfl, hy⟩ := wout_bool hv2 hw2
           have hx := hx.resolve_left (hall _ (by simp)); have hy := hy.resolve_left (hall _ (by simp))
           simp [primW, evalW, WRes.bind, hx, hy, AOp.apply])
        | (obtain ⟨x, rfl, hx⟩ := wout_bool hv1 hw1
           have hx := hx.resolve_left (hall _ (by simp))
           simp [primW, evalW, WRes.bind, hx])
  | _, _, _, _, _, _, _, _, .lam _ _ _ _ _, _, _, _, _, _, _, _ => by simp [lower2A, evalW]
  | _, _, _, _, _, _, _, _, .fix _ _ _ _ _, _, _, _, _, _, _, _ => by simp [lower2A, evalW]
  | _, Γl, Γt, k, _, ρ, ρw, t, .pair (a₁ := a₁) (a₂ := a₂) h₁ h₂, hw, hag, he, hf, hok, hk, hin => by
      simp only [Atom.wfB, Bool.and_eq_true] at hw; simp only [Atom.fnOk, Bool.and_eq_true] at hf
      simp only [Atom.ok2, Bool.and_eq_true] at hok
      simp only [lowerA, Opd.InR] at hin
      simp only [lower2A] at hk ⊢
      have k₂ := hk.mono (lower2A_keeps Γl a₁ t).1
      have k₁ := KeepsFrom.of_keeps (lower2A_keeps Γl a₂ _) hk
      have n₁ := opd_noovf hT t h₁ hw.1 hag he hf.1 hok.1 k₁ hin.1
      have n₂ := opd_noovf hT _ h₂ hw.2 hag he hf.2 hok.2 k₂ hin.2
      revert n₁ n₂; simp only [evalW]
      cases evalW ρw (lower2A Γl a₁ t).1 <;> cases evalW ρw (lower2A Γl a₂ (lower2A Γl a₁ t).2).1 <;> simp [WRes.bind]
  | _, Γl, Γt, k, _, ρ, ρw, t, .fst (a := a) (τ₁ := τ₁) (τ₂ := τ₂) h, hw, hag, he, hf, hok, hk, hin => by
      simp only [Atom.wfB] at hw; simp only [Atom.fnOk] at hf; simp only [Atom.ok2] at hok
      simp only [lowerA, Opd.InR] at hin
      have hinf : inferA Γl a = some (.prod τ₁ τ₂) := by rw [inferA_agree a hw hag]; exact inferA_sound h
      simp only [lower2A, hinf] at hk ⊢
      have n₁ := opd_noovf hT t h hw hag he hf hok hk hin
      revert n₁; simp only [evalW]; cases evalW ρw (lower2A Γl a t).1 <;> simp [WRes.bind]
  | _, Γl, Γt, k, _, ρ, ρw, t, .snd (a := a) (τ₁ := τ₁) (τ₂ := τ₂) h, hw, hag, he, hf, hok, hk, hin => by
      simp only [Atom.wfB] at hw; simp only [Atom.fnOk] at hf; simp only [Atom.ok2] at hok
      simp only [lowerA, Opd.InR] at hin
      have hinf : inferA Γl a = some (.prod τ₁ τ₂) := by rw [inferA_agree a hw hag]; exact inferA_sound h
      simp only [lower2A, hinf] at hk ⊢
      have n₁ := opd_noovf hT t h hw hag he hf hok hk hin
      revert n₁; simp only [evalW]; cases evalW ρw (lower2A Γl a t).1 <;> simp [WRes.bind]
  | _, Γl, Γt, k, _, ρ, ρw, t, .inl (a := a) (τ₁ := τ₁) (τ₂ := τ₂) _ h, hw, hag, he, hf, hok, hk, hin => by
      simp only [Atom.wfB] at hw; simp only [Atom.fnOk] at hf; simp only [Atom.ok2] at hok
      simp only [lowerA, Opd.InR] at hin
      have hinf : inferA Γl a = some τ₁ := by rw [inferA_agree a hw hag]; exact inferA_sound h
      simp only [lower2A, hinf] at hk ⊢
      have n₁ := opd_noovf hT t h hw hag he hf hok hk hin
      revert n₁; simp only [evalW]; cases evalW ρw (lower2A Γl a t).1 <;> simp [WRes.bind]
  | _, Γl, Γt, k, _, ρ, ρw, t, .inr (a := a) (τ₁ := τ₁) (τ₂ := τ₂) _ h, hw, hag, he, hf, hok, hk, hin => by
      simp only [Atom.wfB] at hw; simp only [Atom.fnOk] at hf; simp only [Atom.ok2] at hok
      simp only [lowerA, Opd.InR] at hin
      have hinf : inferA Γl a = some τ₂ := by rw [inferA_agree a hw hag]; exact inferA_sound h
      simp only [lower2A, hinf] at hk ⊢
      have n₁ := opd_noovf hT t h hw hag he hf hok hk hin
      revert n₁; simp only [evalW]; cases evalW ρw (lower2A Γl a t).1 <;> simp [WRes.bind]
theorem opdL_noovf {T lay σ} (hT : T.length < 2 ^ 64) : ∀ {as : List Atom₂} {Γl Γt : Ctx S₂} {k : Nat} {τs : List Ty₂}
    {ρ : List VIRC.Val} {ρw : List W} (t : Table),
    HasTypeL₂ Γt as τs → Atom.wfLB k as = true → Agree k Γl Γt → EnvRel T lay σ Γl ρ ρw →
    Atom.fnOkL as = true → Atom.ok2L as = true → KeepsFrom t.length (lower2L Γl as t).2 T →
    Opd.InRL ρ (lowerL as) → ∀ o ∈ (lower2L Γl as t).1, evalW ρw o ≠ .ovf
  | _, _, _, _, _, _, _, _, .nil, _, _, _, _, _, _, _ => by simp [lower2L]
  | _, Γl, Γt, k, _, ρ, ρw, t, .cons (a := a) (as := as) h hs, hw, hag, he, hf, hok, hk, hin => by
      simp only [Atom.wfLB, Bool.and_eq_true] at hw; simp only [Atom.fnOkL, Bool.and_eq_true] at hf
      simp only [Atom.ok2L, Bool.and_eq_true] at hok
      simp only [lowerL, Opd.InRL] at hin
      simp only [lower2L] at hk ⊢
      have k₂ := hk.mono (lower2A_keeps Γl a t).1
      have k₁ := KeepsFrom.of_keeps (lower2L_keeps Γl as _) hk
      have n₁ := opd_noovf hT t h hw.1 hag he hf.1 hok.1 k₁ hin.1
      have ns := opdL_noovf hT _ hs hw.2 hag he hf.2 hok.2 k₂ hin.2
      intro o ho
      simp only [List.mem_cons] at ho
      rcases ho with rfl | ho
      · exact n₁
      · exact ns o ho
end

/-! ## (iii) One step: a related run state whose IR step is in range does not step the word machine to `.ovf`. -/
section heads
variable {T : Table} {lay : Int → W} {σ : Store} {Γl Γt : Ctx S₂} {t : Table} {ρ : List VIRC.Val} {ρw : List W}
  {k : List Frame}

theorem heads_ret (hT : T.length < 2 ^ 64) {a : Atom₂} {τ : Ty₂} (ha : HasTypeA₂ Γt a τ)
    (hw : Tm.wfB Γl.length (.ret a) = true) (hag : Agree Γl.length Γl Γt) (he : EnvRel T lay σ Γl ρ ρw)
    (hf : Tm.fnOk (.ret a) = true) (hok : Tm.ok2 (.ret a) = true) (hk : KeepsFrom t.length (lower2T Γl (.ret a) t).2 T)
    (hin : StepInR (.run (lowerT (.ret a)) ρ k, σ)) : ∀ o ∈ (lower2T Γl (.ret a) t).1.heads, evalW ρw o ≠ .ovf := by
  simp only [Tm.wfB] at hw; simp only [Tm.fnOk] at hf; simp only [Tm.ok2] at hok; simp only [lower2T] at hk ⊢
  simp only [lowerT, StepInR] at hin
  intro o ho; simp only [WCode.heads, List.mem_singleton] at ho; subst ho
  exact opd_noovf hT t ha hw hag he hf hok hk hin

theorem heads_load (hT : T.length < 2 ^ 64) {n : Nat} {a : Atom₂} {e : Tm₂} (ha : HasTypeA₂ Γt a tint)
    (hw : Tm.wfB Γl.length (.letOp .load [.var n, a] tint e) = true) (hag : Agree Γl.length Γl Γt)
    (he : EnvRel T lay σ Γl ρ ρw) (hf : Tm.fnOk (.letOp .load [.var n, a] tint e) = true)
    (hok : Tm.ok2 (.letOp .load [.var n, a] tint e) = true)
    (hk : KeepsFrom t.length (lower2T Γl (.letOp .load [.var n, a] tint e) t).2 T)
    (hin : StepInR (.run (lowerT (.letOp .load [.var n, a] tint e)) ρ k, σ)) :
    ∀ o ∈ (lower2T Γl (.letOp .load [.var n, a] tint e) t).1.heads, evalW ρw o ≠ .ovf := by
  simp only [Tm.wfB, Atom.wfLB, Atom.wfB, decide_eq_true_eq, Bool.and_eq_true] at hw
  simp only [Tm.fnOk, Atom.fnOkL, Atom.fnOk, Bool.and_eq_true, true_and] at hf
  simp only [Tm.ok2, Atom.ok2L, Atom.ok2, Bool.and_eq_true, true_and] at hok
  simp only [lower2T, lower2L, lower2A, opCode] at hk ⊢
  simp only [lowerT, lowerL, lowerA, StepInR, Opd.InRL, Opd.InR, true_and] at hin
  intro o ho; simp only [WCode.heads, List.mem_singleton] at ho; subst ho
  exact opd_noovf hT t ha hw.1.2.1 hag he hf.1.1 hok.1.1 (KeepsFrom.of_keeps (lower2T_keeps _ e _) hk) hin.1

theorem heads_store (hT : T.length < 2 ^ 64) {n : Nat} {a₁ a₂ : Atom₂} {e : Tm₂} (ha₁ : HasTypeA₂ Γt a₁ tint)
    (ha₂ : HasTypeA₂ Γt a₂ tint)
    (hw : Tm.wfB Γl.length (.letOp .store [.var n, a₁, a₂] tcap e) = true) (hag : Agree Γl.length Γl Γt)
    (he : EnvRel T lay σ Γl ρ ρw) (hf : Tm.fnOk (.letOp .store [.var n, a₁, a₂] tcap e) = true)
    (hok : Tm.ok2 (.letOp .store [.var n, a₁, a₂] tcap e) = true)
    (hk : KeepsFrom t.length (lower2T Γl (.letOp .store [.var n, a₁, a₂] tcap e) t).2 T)
    (hin : StepInR (.run (lowerT (.letOp .store [.var n, a₁, a₂] tcap e)) ρ k, σ)) :
    ∀ o ∈ (lower2T Γl (.letOp .store [.var n, a₁, a₂] tcap e) t).1.heads, evalW ρw o ≠ .ovf := by
  simp only [Tm.wfB, Atom.wfLB, Atom.wfB, decide_eq_true_eq, Bool.and_eq_true] at hw
  simp only [Tm.fnOk, Atom.fnOkL, Atom.fnOk, Bool.and_eq_true, true_and] at hf
  simp only [Tm.ok2, Atom.ok2L, Atom.ok2, Bool.and_eq_true, true_and] at hok
  simp only [lower2T, lower2L, lower2A, opCode] at hk ⊢
  simp only [lowerT, lowerL, lowerA, StepInR, Opd.InRL, Opd.InR, true_and] at hin
  have k₂ := KeepsFrom.of_keeps (lower2T_keeps _ e _) hk
  intro o ho; simp only [WCode.heads, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl
  · exact opd_noovf hT t ha₁ hw.1.2.1 hag he hf.1.1 hok.1.1 (KeepsFrom.of_keeps (lower2A_keeps Γl a₂ _) k₂) hin.1
  · exact opd_noovf hT _ ha₂ hw.1.2.2.1 hag he hf.1.2.1 hok.1.2.1 (k₂.mono (lower2A_keeps Γl a₁ t).1) hin.2.1

theorem heads_app (hT : T.length < 2 ^ 64) {a₁ a₂ : Atom₂} {τ₁ τ : Ty₂} (h₁ : HasTypeA₂ Γt a₁ (.arr τ₁ τ))
    (h₂ : HasTypeA₂ Γt a₂ τ₁) (hw : Tm.wfB Γl.length (.app a₁ a₂) = true) (hag : Agree Γl.length Γl Γt)
    (he : EnvRel T lay σ Γl ρ ρw) (hf : Tm.fnOk (.app a₁ a₂) = true) (hok : Tm.ok2 (.app a₁ a₂) = true)
    (hk : KeepsFrom t.length (lower2T Γl (.app a₁ a₂) t).2 T) (hin : StepInR (.run (lowerT (.app a₁ a₂)) ρ k, σ)) :
    ∀ o ∈ (lower2T Γl (.app a₁ a₂) t).1.heads, evalW ρw o ≠ .ovf := by
  simp only [Tm.wfB, Bool.and_eq_true] at hw; simp only [Tm.fnOk, Bool.and_eq_true] at hf
  simp only [Tm.ok2, Bool.and_eq_true] at hok
  simp only [lower2T] at hk ⊢
  simp only [lowerT, StepInR] at hin
  intro o ho; simp only [WCode.heads, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl
  · exact opd_noovf hT t h₁ hw.1 hag he hf.1 hok.1 (KeepsFrom.of_keeps (lower2A_keeps Γl a₂ _) hk) hin.1
  · exact opd_noovf hT _ h₂ hw.2 hag he hf.2 hok.2 (hk.mono (lower2A_keeps Γl a₁ t).1) hin.2

theorem heads_ite (hT : T.length < 2 ^ 64) {a : Atom₂} {e₁ e₂ : Tm₂} (h : HasTypeA₂ Γt a tbool)
    (hw : Tm.wfB Γl.length (.ite a e₁ e₂) = true) (hag : Agree Γl.length Γl Γt)
    (he : EnvRel T lay σ Γl ρ ρw) (hf : Tm.fnOk (.ite a e₁ e₂) = true) (hok : Tm.ok2 (.ite a e₁ e₂) = true)
    (hk : KeepsFrom t.length (lower2T Γl (.ite a e₁ e₂) t).2 T)
    (hin : StepInR (.run (lowerT (.ite a e₁ e₂)) ρ k, σ)) :
    ∀ o ∈ (lower2T Γl (.ite a e₁ e₂) t).1.heads, evalW ρw o ≠ .ovf := by
  simp only [Tm.wfB, Bool.and_eq_true] at hw; simp only [Tm.fnOk, Bool.and_eq_true] at hf
  simp only [Tm.ok2, Bool.and_eq_true] at hok
  simp only [lower2T] at hk ⊢
  simp only [lowerT, StepInR] at hin
  intro o ho; simp only [WCode.heads, List.mem_singleton] at ho; subst ho
  exact opd_noovf hT t h hw.1.1 hag he hf.1.1 hok.1.1
    (KeepsFrom.of_keeps (Keeps.trans (lower2T_keeps Γl e₁ _) (lower2T_keeps Γl e₂ _)) hk) hin

theorem heads_case (hT : T.length < 2 ^ 64) {a : Atom₂} {e₁ e₂ : Tm₂} {τ₁ τ₂ : Ty₂} (h : HasTypeA₂ Γt a (.sum τ₁ τ₂))
    (hw : Tm.wfB Γl.length (.case a e₁ e₂) = true) (hag : Agree Γl.length Γl Γt)
    (he : EnvRel T lay σ Γl ρ ρw) (hf : Tm.fnOk (.case a e₁ e₂) = true) (hok : Tm.ok2 (.case a e₁ e₂) = true)
    (hk : KeepsFrom t.length (lower2T Γl (.case a e₁ e₂) t).2 T)
    (hin : StepInR (.run (lowerT (.case a e₁ e₂)) ρ k, σ)) :
    ∀ o ∈ (lower2T Γl (.case a e₁ e₂) t).1.heads, evalW ρw o ≠ .ovf := by
  simp only [Tm.wfB, Bool.and_eq_true] at hw; simp only [Tm.fnOk, Bool.and_eq_true] at hf
  simp only [Tm.ok2, Bool.and_eq_true] at hok
  have hinf : inferA Γl a = some (.sum τ₁ τ₂) := by rw [inferA_agree a hw.1.1 hag]; exact inferA_sound h
  simp only [lower2T, hinf] at hk ⊢
  simp only [lowerT, StepInR] at hin
  intro o ho; simp only [WCode.heads, List.mem_singleton] at ho; subst ho
  exact opd_noovf hT t h hw.1.1 hag he hf.1.1 hok.1.1
    (KeepsFrom.of_keeps (Keeps.trans (lower2T_keeps (τ₁ :: Γl) e₁ _) (lower2T_keeps (τ₂ :: Γl) e₂ _)) hk) hin

/-! ## (iii) One step: a related run state whose IR step is in range does not step the word machine to `.ovf`. -/
theorem step_noovf {τfin} (hT : T.length < 2 ^ 64) {c Wst W'} (h : SRel T lay τfin (.run c ρ k, σ) Wst)
    (hin : StepInR (.run c ρ k, σ)) (hs : stepW T Wst = some W') : W'.1 ≠ .ovf := by
  cases h with
  | run hc hfr hl hm =>
    obtain ⟨e, Γt, Δ, t, rfl, rfl, hk, hty, hw, hag, hf, hok, he⟩ := hc
    refine stepW_noovf ?_ hs
    cases hty with
    | ret _ ha => exact heads_ret hT ha hw hag he hf hok hk hin
    | retCap hg _ =>
      simp only [lower2T, lower2A, WCode.heads, List.mem_singleton]
      intro o ho; subst ho; exact slice_noovf _ _ _
    | letE _ _ h₁ h₂ => simp [lower2T, WCode.heads]
    | alloc _ _ => simp [Tm.ok2] at hok
    | load hg _ ha he' => exact heads_load hT ha hw hag he hf hok hk hin
    | store hg _ ha₁ ha₂ he' => exact heads_store hT ha₁ ha₂ hw hag he hf hok hk hin
    | free _ _ _ => simp [Tm.ok2] at hok
    | app _ h₁ h₂ => exact heads_app hT h₁ h₂ hw hag he hf hok hk hin
    | ite h h₁ h₂ => exact heads_ite hT h hw hag he hf hok hk hin
    | case h h₁ h₂ => exact heads_case hT h hw hag he hf hok hk hin

end heads

/-! ## (iv) The run. -/
theorem WN.from_fault {T : Table} {m} : ∀ {k W'}, WN T k ((.fault : WSt), m) W' → W' = (.fault, m)
  | _, _, .refl _ => rfl
  | _, _, .step h _ => by simp [stepW] at h

theorem s2_run_noovf {T lay τfin} (hT : T.length < 2 ^ 64) : ∀ {k I Wst W'}, SRel T lay τfin I Wst →
    InRangeRun I → WN T k Wst W' → W'.1 ≠ .ovf
  | _, _, _, _, h, _, .refl _ => by cases h <;> simp
  | _, I, Wst, W', h, hin, .step (s' := W₁) hs hrest => by
      obtain ⟨st, σ⟩ := I
      cases st with
      | done v => cases h; simp [stepW] at hs
      | run c ρ k =>
        have h0 : StepInR (.run c ρ k, σ) := hin 0 _ (.refl _)
        rcases sim2_step hT h with ⟨-, W'', h1, h2⟩ | ⟨I₁, h1, W'', hW, rel⟩
        · rw [hs] at h1; cases h1
          have hno := step_noovf hT h h0 hs
          rcases h2 with h2 | h2
          · obtain ⟨st₁, m₁⟩ := W₁; simp only at h2; subst h2
            rw [WN.from_fault hrest]; simp
          · exact absurd h2 hno
        · rw [hs] at hW; cases hW
          rcases rel with rel | ovf
          · exact s2_run_noovf hT rel (fun n I' hr => hin (n + 1) I' (.step h1 hr)) hrest
          · exact absurd ovf (step_noovf hT h h0 hs)

/-- **K5-1a.** Under `s2_refines`'s hypotheses, if every state of the IR run of S1's image steps on in-range operands
(`InRangeRun`), then NO word run from the compiled program reaches the OVERFLOW exit. DECLARATIONS-S2 l. 39's clause, proved. -/
theorem s2_noovf {lay σ m} (Γ₀ : Ctx S₂) (Δ₀ : List Bool) (e : Tm₂) (τ : Ty₂) (ρ₀ : List VIRC.Val) (ρw₀ : List W)
    (hty : HasType₂ Γ₀ Δ₀ e τ) (hw : Tm.wfB Γ₀.length e = true) (hf : Tm.fnOk e = true) (hok : Tm.ok2 e = true)
    (hT : (lower2T Γ₀ e []).2.length < 2 ^ 64)
    (he : EnvRel (lower2T Γ₀ e []).2 lay σ Γ₀ ρ₀ ρw₀) (hl : Layout σ lay) (hm : MemRel lay σ m)
    (hin : InRangeRun (.run (lowerT e) ρ₀ [], σ)) :
    ∀ k W', WN (lower2T Γ₀ e []).2 k (.run (lower2T Γ₀ e []).1 ρw₀ [], m) W' → W'.1 ≠ .ovf :=
  fun _ _ hr => s2_run_noovf hT (s2_init Γ₀ Δ₀ e τ ρ₀ ρw₀ hty hw hf hok he hl hm) hin hr

/-- `s2_refines` (1) without its overflow disjunct, under `InRangeRun`. -/
theorem s2_refines_noovf {lay σ m} (Γ₀ : Ctx S₂) (Δ₀ : List Bool) (e : Tm₂) (τ : Ty₂) (ρ₀ : List VIRC.Val) (ρw₀ : List W)
    (hty : HasType₂ Γ₀ Δ₀ e τ) (hw : Tm.wfB Γ₀.length e = true) (hf : Tm.fnOk e = true) (hok : Tm.ok2 e = true)
    (hT : (lower2T Γ₀ e []).2.length < 2 ^ 64)
    (he : EnvRel (lower2T Γ₀ e []).2 lay σ Γ₀ ρ₀ ρw₀) (hl : Layout σ lay) (hm : MemRel lay σ m)
    (hin : InRangeRun (.run (lowerT e) ρ₀ [], σ)) :
    ∀ n v σ', IRN n (.run (lowerT e) ρ₀ [], σ) (.done v, σ') →
      ∃ k ws m', WN (lower2T Γ₀ e []).2 k (.run (lower2T Γ₀ e []).1 ρw₀ [], m) (.done ws, m') ∧
        VRel (lower2T Γ₀ e []).2 lay σ' τ v ws := by
  intro n v σ' hr
  obtain ⟨k, W', hW, r⟩ := (s2_refines Γ₀ Δ₀ e τ ρ₀ ρw₀ hty hw hf hok hT he hl hm).1 n v σ' hr
  rcases r with ⟨ws, m', rfl, hv⟩ | r
  · exact ⟨k, ws, m', hW, hv⟩
  · exact absurd r (s2_noovf Γ₀ Δ₀ e τ ρ₀ ρw₀ hty hw hf hok hT he hl hm hin k W' hW)

end VIRC
