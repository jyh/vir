/-
  O95 compiler, stage S1: the simulation. Part 1, syntax. `TRel n vs c e` says the IR code `c` in an environment that holds
  `n` LOCAL slots followed by the values `vs` is the L2 term `e`, in which those values have been SUBSTITUTED (L2's ⟶₂ is a
  substitution semantics) and the n locals are still variables. A closed function atom relates to its own lowered code, at
  every n and vs (C2). Lemma `TRel.subst` is the one fact ⟶₂'s substitution needs: substituting the OUTERMOST local moves it
  into the environment.
-/
import VIRC.Lower

namespace VIRC
open VIRL1 VIRL2

/-! ## Substitutions of closed atoms commute (needed once: fix substitutes its argument, then itself). -/
mutual
theorem Atom.subst_comm : ∀ (a : Atom₂) {i j : Nat} (v w : Atom₂), i ≤ j → Atom.wfB 0 v = true → Atom.wfB 0 w = true →
    (a.subst (j + 1) w).subst i v = (a.subst i v).subst j w
  | .var n, i, j, v, w, hij, hv, hw => by
      have cv : ∀ k, Atom.subst v k w = v := fun k => Atom.subst_wfB v w hv (Nat.zero_le k)
      have cw : ∀ k, Atom.subst w k v = w := fun k => Atom.subst_wfB w v hw (Nat.zero_le k)
      simp only [Atom.subst]
      split_ifs <;> simp only [Atom.subst, cv, cw] <;> (try split_ifs) <;>
        first | rfl | (exfalso; omega) | (simp only [Atom.var.injEq]; omega)
  | .const _, _, _, _, _, _, _, _ => rfl
  | .prim _ as, _, _, v, w, hij, hv, hw => by simp only [Atom.subst, Atom.substL_comm as v w hij hv hw]
  | .lam _ e, i, j, v, w, hij, hv, hw => by
      simp only [Atom.subst, Tm.subst_comm e (i := i + 1) (j := j + 1) v w (by omega) hv hw]
  | .fix _ _ e, i, j, v, w, hij, hv, hw => by
      simp only [Atom.subst, Tm.subst_comm e (i := i + 2) (j := j + 2) v w (by omega) hv hw]
  | .pair a₁ a₂, _, _, v, w, hij, hv, hw => by
      simp only [Atom.subst, Atom.subst_comm a₁ v w hij hv hw, Atom.subst_comm a₂ v w hij hv hw]
  | .fst a, _, _, v, w, hij, hv, hw => by simp only [Atom.subst, Atom.subst_comm a v w hij hv hw]
  | .snd a, _, _, v, w, hij, hv, hw => by simp only [Atom.subst, Atom.subst_comm a v w hij hv hw]
  | .inl _ a, _, _, v, w, hij, hv, hw => by simp only [Atom.subst, Atom.subst_comm a v w hij hv hw]
  | .inr _ a, _, _, v, w, hij, hv, hw => by simp only [Atom.subst, Atom.subst_comm a v w hij hv hw]
theorem Atom.substL_comm : ∀ (as : List Atom₂) {i j : Nat} (v w : Atom₂), i ≤ j → Atom.wfB 0 v = true →
    Atom.wfB 0 w = true → Atom.substL i v (Atom.substL (j + 1) w as) = Atom.substL j w (Atom.substL i v as)
  | [], _, _, _, _, _, _, _ => rfl
  | a :: as, _, _, v, w, hij, hv, hw => by
      simp only [Atom.substL, Atom.subst_comm a v w hij hv hw, Atom.substL_comm as v w hij hv hw]
theorem Tm.subst_comm : ∀ (e : Tm₂) {i j : Nat} (v w : Atom₂), i ≤ j → Atom.wfB 0 v = true → Atom.wfB 0 w = true →
    (e.subst (j + 1) w).subst i v = (e.subst i v).subst j w
  | .ret a, _, _, v, w, hij, hv, hw => by simp only [Tm.subst, Atom.subst_comm a v w hij hv hw]
  | .letE _ e₁ e₂, i, j, v, w, hij, hv, hw => by
      simp only [Tm.subst, Tm.subst_comm e₁ v w hij hv hw, Tm.subst_comm e₂ (i := i + 1) (j := j + 1) v w (by omega) hv hw]
  | .letOp _ as _ e, i, j, v, w, hij, hv, hw => by
      simp only [Tm.subst, Atom.substL_comm as v w hij hv hw, Tm.subst_comm e (i := i + 1) (j := j + 1) v w (by omega) hv hw]
  | .app a₁ a₂, _, _, v, w, hij, hv, hw => by
      simp only [Tm.subst, Atom.subst_comm a₁ v w hij hv hw, Atom.subst_comm a₂ v w hij hv hw]
  | .ite a e₁ e₂, _, _, v, w, hij, hv, hw => by
      simp only [Tm.subst, Atom.subst_comm a v w hij hv hw, Tm.subst_comm e₁ v w hij hv hw, Tm.subst_comm e₂ v w hij hv hw]
  | .case a e₁ e₂, i, j, v, w, hij, hv, hw => by
      simp only [Tm.subst, Atom.subst_comm a v w hij hv hw, Tm.subst_comm e₁ (i := i + 1) (j := j + 1) v w (by omega) hv hw,
        Tm.subst_comm e₂ (i := i + 1) (j := j + 1) v w (by omega) hv hw]
end

/-! ## The relation between IR code and L2 terms. -/
mutual
inductive ARel : Nat → List Atom₂ → Opd → Atom₂ → Prop where
  | varL {n vs i} : i < n → ARel n vs (.var i) (.var i)
  | varV {n vs i v} : n ≤ i → vs[i - n]? = some v → ARel n vs (.var i) v
  | const {n vs c} : ARel n vs (.const c) (.const c)
  | prim {n vs p os as} : ARelL n vs os as → ARel n vs (.prim p os) (.prim p as)
  | lam {n vs τ e} : Tm.wfB 1 e = true → Tm.fnOk e = true → ARel n vs (.code false (lowerT e)) (.lam τ e)
  | fix {n vs τ₁ τ₂ e} : Tm.wfB 2 e = true → Tm.fnOk e = true → ARel n vs (.code true (lowerT e)) (.fix τ₁ τ₂ e)
  | pair {n vs o₁ o₂ a₁ a₂} : ARel n vs o₁ a₁ → ARel n vs o₂ a₂ → ARel n vs (.pair o₁ o₂) (.pair a₁ a₂)
  | fst {n vs o a} : ARel n vs o a → ARel n vs (.fst o) (.fst a)
  | snd {n vs o a} : ARel n vs o a → ARel n vs (.snd o) (.snd a)
  | inl {n vs o a τ} : ARel n vs o a → ARel n vs (.inl o) (.inl τ a)
  | inr {n vs o a τ} : ARel n vs o a → ARel n vs (.inr o) (.inr τ a)
inductive ARelL : Nat → List Atom₂ → List Opd → List Atom₂ → Prop where
  | nil {n vs} : ARelL n vs [] []
  | cons {n vs o os a as} : ARel n vs o a → ARelL n vs os as → ARelL n vs (o :: os) (a :: as)
end

inductive TRel : Nat → List Atom₂ → Code → Tm₂ → Prop where
  | ret {n vs o a} : ARel n vs o a → TRel n vs (.ret o) (.ret a)
  | letE {n vs c₁ c₂ τ e₁ e₂} : TRel n vs c₁ e₁ → TRel (n + 1) vs c₂ e₂ → TRel n vs (.letE c₁ c₂) (.letE τ e₁ e₂)
  | letOp {n vs op os c τ as e} : ARelL n vs os as → TRel (n + 1) vs c e →
      TRel n vs (.letOp op os c) (.letOp op as τ e)
  | app {n vs o₁ o₂ a₁ a₂} : ARel n vs o₁ a₁ → ARel n vs o₂ a₂ → TRel n vs (.app o₁ o₂) (.app a₁ a₂)
  | ite {n vs o c₁ c₂ a e₁ e₂} : ARel n vs o a → TRel n vs c₁ e₁ → TRel n vs c₂ e₂ →
      TRel n vs (.ite o c₁ c₂) (.ite a e₁ e₂)
  | case {n vs o c₁ c₂ a e₁ e₂} : ARel n vs o a → TRel (n + 1) vs c₁ e₁ → TRel (n + 1) vs c₂ e₂ →
      TRel n vs (.case o c₁ c₂) (.case a e₁ e₂)

/-! ## Lowering is related to its source (locals only, no environment yet). -/
mutual
theorem lowerA_rel : ∀ (a : Atom₂) {n : Nat}, Atom.wfB n a = true → Atom.fnOk a = true → ARel n [] (lowerA a) a
  | .var m, n, h, _ => by simp only [Atom.wfB, decide_eq_true_eq] at h; exact .varL h
  | .const _, _, _, _ => .const
  | .prim _ as, _, h, hf => by
      simp only [Atom.wfB] at h; simp only [Atom.fnOk] at hf; exact .prim (lowerL_rel as h hf)
  | .lam _ e, _, _, hf => by
      simp only [Atom.fnOk, Bool.and_eq_true] at hf; exact .lam hf.1 hf.2
  | .fix _ _ e, _, _, hf => by
      simp only [Atom.fnOk, Bool.and_eq_true] at hf; exact .fix hf.1 hf.2
  | .pair a₁ a₂, _, h, hf => by
      simp only [Atom.wfB, Bool.and_eq_true] at h; simp only [Atom.fnOk, Bool.and_eq_true] at hf
      exact .pair (lowerA_rel a₁ h.1 hf.1) (lowerA_rel a₂ h.2 hf.2)
  | .fst a, _, h, hf => by simp only [Atom.wfB] at h; simp only [Atom.fnOk] at hf; exact .fst (lowerA_rel a h hf)
  | .snd a, _, h, hf => by simp only [Atom.wfB] at h; simp only [Atom.fnOk] at hf; exact .snd (lowerA_rel a h hf)
  | .inl _ a, _, h, hf => by simp only [Atom.wfB] at h; simp only [Atom.fnOk] at hf; exact .inl (lowerA_rel a h hf)
  | .inr _ a, _, h, hf => by simp only [Atom.wfB] at h; simp only [Atom.fnOk] at hf; exact .inr (lowerA_rel a h hf)
theorem lowerL_rel : ∀ (as : List Atom₂) {n : Nat}, Atom.wfLB n as = true → Atom.fnOkL as = true →
    ARelL n [] (lowerL as) as
  | [], _, _, _ => .nil
  | a :: as, _, h, hf => by
      simp only [Atom.wfLB, Bool.and_eq_true] at h; simp only [Atom.fnOkL, Bool.and_eq_true] at hf
      exact .cons (lowerA_rel a h.1 hf.1) (lowerL_rel as h.2 hf.2)
end

theorem lowerT_rel : ∀ (e : Tm₂) {n : Nat}, Tm.wfB n e = true → Tm.fnOk e = true → TRel n [] (lowerT e) e
  | .ret a, _, h, hf => by simp only [Tm.wfB] at h; simp only [Tm.fnOk] at hf; exact .ret (lowerA_rel a h hf)
  | .letE _ e₁ e₂, _, h, hf => by
      simp only [Tm.wfB, Bool.and_eq_true] at h; simp only [Tm.fnOk, Bool.and_eq_true] at hf
      exact .letE (lowerT_rel e₁ h.1 hf.1) (lowerT_rel e₂ h.2 hf.2)
  | .letOp _ as _ e, _, h, hf => by
      simp only [Tm.wfB, Bool.and_eq_true] at h; simp only [Tm.fnOk, Bool.and_eq_true] at hf
      exact .letOp (lowerL_rel as h.1 hf.1) (lowerT_rel e h.2 hf.2)
  | .app a₁ a₂, _, h, hf => by
      simp only [Tm.wfB, Bool.and_eq_true] at h; simp only [Tm.fnOk, Bool.and_eq_true] at hf
      exact .app (lowerA_rel a₁ h.1 hf.1) (lowerA_rel a₂ h.2 hf.2)
  | .ite a e₁ e₂, _, h, hf => by
      simp only [Tm.wfB, Bool.and_eq_true] at h; simp only [Tm.fnOk, Bool.and_eq_true] at hf
      exact .ite (lowerA_rel a h.1.1 hf.1.1) (lowerT_rel e₁ h.1.2 hf.1.2) (lowerT_rel e₂ h.2 hf.2)
  | .case a e₁ e₂, _, h, hf => by
      simp only [Tm.wfB, Bool.and_eq_true] at h; simp only [Tm.fnOk, Bool.and_eq_true] at hf
      exact .case (lowerA_rel a h.1.1 hf.1.1) (lowerT_rel e₁ h.1.2 hf.1.2) (lowerT_rel e₂ h.2 hf.2)

/-! ## Substituting the outermost local moves it into the environment. The environment's values must be CLOSED. -/
def Closed (vs : List Atom₂) : Prop := ∀ w ∈ vs, Atom.wfB 0 w = true

mutual
theorem ARel.subst : ∀ {m vs o a}, ARel (m + 1) vs o a → ∀ (v : Atom₂), Closed vs → ARel m (v :: vs) o (a.subst m v)
  | m, vs, _, _, .varL (i := i) h, v, _ => by
      by_cases hi : i < m
      · simp only [Atom.subst, if_pos hi]; exact .varL hi
      · have : i = m := by omega
        subst this; simp only [Atom.subst, lt_irrefl, if_false, if_true]
        exact .varV (le_refl _) (by simp)
  | m, vs, _, _, .varV (i := i) (v := w) h hw, v, hc => by
      rw [Atom.subst_wfB w v (hc w (List.mem_of_getElem? hw)) (Nat.zero_le m)]
      exact .varV (by omega) (by rw [show i - m = (i - (m + 1)) + 1 by omega]; simpa using hw)
  | _, _, _, _, .const, _, _ => .const
  | _, _, _, _, .prim h, v, hc => by simp only [Atom.subst]; exact .prim (ARelL.subst h v hc)
  | m, _, _, _, .lam (e := e) h hf, v, _ => by
      simp only [Atom.subst, Tm.subst_wfB e (n := 1) (k := m + 1) v h (by omega)]; exact .lam h hf
  | m, _, _, _, .fix (e := e) h hf, v, _ => by
      simp only [Atom.subst, Tm.subst_wfB e (n := 2) (k := m + 2) v h (by omega)]; exact .fix h hf
  | _, _, _, _, .pair h₁ h₂, v, hc => by simp only [Atom.subst]; exact .pair (ARel.subst h₁ v hc) (ARel.subst h₂ v hc)
  | _, _, _, _, .fst h, v, hc => by simp only [Atom.subst]; exact .fst (ARel.subst h v hc)
  | _, _, _, _, .snd h, v, hc => by simp only [Atom.subst]; exact .snd (ARel.subst h v hc)
  | _, _, _, _, .inl h, v, hc => by simp only [Atom.subst]; exact .inl (ARel.subst h v hc)
  | _, _, _, _, .inr h, v, hc => by simp only [Atom.subst]; exact .inr (ARel.subst h v hc)
theorem ARelL.subst : ∀ {m vs os as}, ARelL (m + 1) vs os as → ∀ (v : Atom₂), Closed vs →
    ARelL m (v :: vs) os (Atom.substL m v as)
  | _, _, _, _, .nil, _, _ => .nil
  | _, _, _, _, .cons h hs, v, hc => .cons (ARel.subst h v hc) (ARelL.subst hs v hc)
end

theorem TRel.subst : ∀ {m vs c e}, TRel (m + 1) vs c e → ∀ (v : Atom₂), Closed vs → TRel m (v :: vs) c (e.subst m v)
  | _, _, _, _, .ret h, v, hc => .ret (ARel.subst h v hc)
  | _, _, _, _, .letE h₁ h₂, v, hc => .letE (TRel.subst h₁ v hc) (TRel.subst h₂ v hc)
  | _, _, _, _, .letOp h₁ h₂, v, hc => .letOp (ARelL.subst h₁ v hc) (TRel.subst h₂ v hc)
  | _, _, _, _, .app h₁ h₂, v, hc => .app (ARel.subst h₁ v hc) (ARel.subst h₂ v hc)
  | _, _, _, _, .ite h h₁ h₂, v, hc => .ite (ARel.subst h v hc) (TRel.subst h₁ v hc) (TRel.subst h₂ v hc)
  | _, _, _, _, .case h h₁ h₂, v, hc => .case (ARel.subst h v hc) (TRel.subst h₁ v hc) (TRel.subst h₂ v hc)

/-- A λ body called with v. -/
theorem TRel.call_lam {e : Tm₂} (h : Tm.wfB 1 e = true) (hf : Tm.fnOk e = true) (v : Atom₂) :
    TRel 0 [v] (lowerT e) (e.subst 0 v) :=
  TRel.subst (lowerT_rel e h hf) v (by simp [Closed])

/-- A fix body called with v: L1 substitutes the argument, then the fix itself (`appFix`). -/
theorem TRel.call_fix {τ₁ τ₂} {e : Tm₂} (h : Tm.wfB 2 e = true) (hf : Tm.fnOk e = true) (v : Atom₂)
    (hv : Atom.wfB 0 v = true) :
    TRel 0 [v, .fix τ₁ τ₂ e] (lowerT e) ((e.subst 0 v).subst 0 (.fix τ₁ τ₂ e)) := by
  have hfx : Atom.wfB 0 (.fix τ₁ τ₂ e : Atom₂) = true := by simpa [Atom.wfB] using h
  rw [← Tm.subst_comm e v _ (le_refl 0) hv hfx]
  have h1 := TRel.subst (m := 1) (lowerT_rel e h hf) (.fix τ₁ τ₂ e) (by simp [Closed])
  exact TRel.subst h1 v (by simp [Closed, hfx])

/-! ## Part 2: evaluation. An environment of CLOSED, C2, self-evaluating values (`Good`), read through `valOf`. -/
def Good (vs : List Atom₂) : Prop := ∀ w ∈ vs, Atom.wfB 0 w = true ∧ Atom.fnOk w = true ∧ Atom.eval w = some w

theorem Good.closed {vs} (h : Good vs) : Closed vs := fun w hw => (h w hw).1

theorem Good.cons {v vs} (hv : Atom.wfB 0 v = true ∧ Atom.fnOk v = true ∧ Atom.eval v = some v) (h : Good vs) :
    Good (v :: vs) := by
  intro w hw; rcases List.mem_cons.mp hw with rfl | hw
  · exact hv
  · exact h w hw

theorem mapM_asConst : ∀ (ws : List Atom₂), (ws.map valOf).mapM Val.asConst = constsOf ws
  | [] => rfl
  | a :: ws => by
      cases a <;> simp [valOf, Val.asConst, constsOf, List.mapM_cons, mapM_asConst ws] <;> cases constsOf ws <;> rfl

/-! Evaluation of a closed C2 atom yields a closed C2 value that evaluates to itself. -/
mutual
theorem Atom.eval_good : ∀ (a : Atom₂) {v : Atom₂}, Atom.eval a = some v → Atom.wfB 0 a = true → Atom.fnOk a = true →
    Atom.wfB 0 v = true ∧ Atom.fnOk v = true ∧ Atom.eval v = some v
  | .var _, _, h, _, _ => by simp [Atom.eval] at h
  | .const c, v, h, _, _ => by simp only [Atom.eval, Option.some.injEq] at h; subst h; simp [Atom.wfB, Atom.fnOk, Atom.eval]
  | .prim p as, v, h, _, _ => by
      simp only [Atom.eval, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨_, _, _, _, c, _, rfl⟩ := h; simp [Atom.wfB, Atom.fnOk, Atom.eval]
  | .lam τ e, v, h, hw, hf => by
      simp only [Atom.eval, Option.some.injEq] at h; subst h; exact ⟨hw, hf, rfl⟩
  | .fix τ₁ τ₂ e, v, h, hw, hf => by
      simp only [Atom.eval, Option.some.injEq] at h; subst h; exact ⟨hw, hf, rfl⟩
  | .pair a₁ a₂, v, h, hw, hf => by
      simp only [Atom.wfB, Bool.and_eq_true] at hw; simp only [Atom.fnOk, Bool.and_eq_true] at hf
      simp only [Atom.eval, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨v₁, h₁, v₂, h₂, rfl⟩ := h
      obtain ⟨w₁, f₁, e₁⟩ := Atom.eval_good a₁ h₁ hw.1 hf.1
      obtain ⟨w₂, f₂, e₂⟩ := Atom.eval_good a₂ h₂ hw.2 hf.2
      simp [Atom.wfB, Atom.fnOk, Atom.eval, w₁, w₂, f₁, f₂, e₁, e₂]
  | .fst a, v, h, hw, hf => by
      simp only [Atom.wfB] at hw; simp only [Atom.fnOk] at hf
      simp only [Atom.eval, Option.bind_eq_some_iff] at h
      obtain ⟨p, hp, hv⟩ := h
      obtain ⟨wp, fp, ep⟩ := Atom.eval_good a hp hw hf
      cases p <;> simp at hv
      subst hv
      simp only [Atom.wfB, Atom.fnOk, Bool.and_eq_true] at wp fp
      simp only [Atom.eval, Option.bind_eq_some_iff, Option.map_eq_some_iff] at ep
      obtain ⟨x, hx, y, hy, hxy⟩ := ep
      simp only [Atom.pair.injEq] at hxy; obtain ⟨rfl, rfl⟩ := hxy
      exact ⟨wp.1, fp.1, hx⟩
  | .snd a, v, h, hw, hf => by
      simp only [Atom.wfB] at hw; simp only [Atom.fnOk] at hf
      simp only [Atom.eval, Option.bind_eq_some_iff] at h
      obtain ⟨p, hp, hv⟩ := h
      obtain ⟨wp, fp, ep⟩ := Atom.eval_good a hp hw hf
      cases p <;> simp at hv
      subst hv
      simp only [Atom.wfB, Atom.fnOk, Bool.and_eq_true] at wp fp
      simp only [Atom.eval, Option.bind_eq_some_iff, Option.map_eq_some_iff] at ep
      obtain ⟨x, hx, y, hy, hxy⟩ := ep
      simp only [Atom.pair.injEq] at hxy; obtain ⟨rfl, rfl⟩ := hxy
      exact ⟨wp.2, fp.2, hy⟩
  | .inl τ a, v, h, hw, hf => by
      simp only [Atom.wfB] at hw; simp only [Atom.fnOk] at hf
      simp only [Atom.eval, Option.map_eq_some_iff] at h
      obtain ⟨x, hx, rfl⟩ := h
      obtain ⟨wx, fx, ex⟩ := Atom.eval_good a hx hw hf
      simp [Atom.wfB, Atom.fnOk, Atom.eval, wx, fx, ex]
  | .inr τ a, v, h, hw, hf => by
      simp only [Atom.wfB] at hw; simp only [Atom.fnOk] at hf
      simp only [Atom.eval, Option.map_eq_some_iff] at h
      obtain ⟨x, hx, rfl⟩ := h
      obtain ⟨wx, fx, ex⟩ := Atom.eval_good a hx hw hf
      simp [Atom.wfB, Atom.fnOk, Atom.eval, wx, fx, ex]
end

theorem Atom.evalL_good : ∀ (as : List Atom₂) {vs : List Atom₂}, Atom.evalL as = some vs → Atom.wfLB 0 as = true →
    Atom.fnOkL as = true → Good vs
  | [], vs, h, _, _ => by simp only [Atom.evalL, Option.some.injEq] at h; subst h; simp [Good]
  | a :: as, vs, h, hw, hf => by
      simp only [Atom.wfLB, Bool.and_eq_true] at hw; simp only [Atom.fnOkL, Bool.and_eq_true] at hf
      simp only [Atom.evalL, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨v, hv, ws, hws, rfl⟩ := h
      exact Good.cons (Atom.eval_good a hv hw.1 hf.1) (Atom.evalL_good as hws hw.2 hf.2)

/-! An atom related at n = 0 to an environment of closed C2 values is itself closed and C2. -/
mutual
theorem ARel.closed : ∀ {vs o a}, ARel 0 vs o a → Good vs → Atom.wfB 0 a = true ∧ Atom.fnOk a = true
  | _, _, _, .varL h, _ => absurd h (Nat.not_lt_zero _)
  | _, _, _, .varV _ hw, hg => by
      have := hg _ (List.mem_of_getElem? hw); exact ⟨this.1, this.2.1⟩
  | _, _, _, .const, _ => by simp [Atom.wfB, Atom.fnOk]
  | _, _, _, .prim h, hg => by
      have := ARelL.closed h hg; simp only [Atom.wfB, Atom.fnOk]; exact this
  | _, _, _, .lam h hf, _ => by simp [Atom.wfB, Atom.fnOk, h, hf]
  | _, _, _, .fix h hf, _ => by simp [Atom.wfB, Atom.fnOk, h, hf]
  | _, _, _, .pair h₁ h₂, hg => by
      have := ARel.closed h₁ hg; have := ARel.closed h₂ hg; simp_all [Atom.wfB, Atom.fnOk]
  | _, _, _, .fst h, hg => by simpa [Atom.wfB, Atom.fnOk] using ARel.closed h hg
  | _, _, _, .snd h, hg => by simpa [Atom.wfB, Atom.fnOk] using ARel.closed h hg
  | _, _, _, .inl h, hg => by simpa [Atom.wfB, Atom.fnOk] using ARel.closed h hg
  | _, _, _, .inr h, hg => by simpa [Atom.wfB, Atom.fnOk] using ARel.closed h hg
theorem ARelL.closed : ∀ {vs os as}, ARelL 0 vs os as → Good vs → Atom.wfLB 0 as = true ∧ Atom.fnOkL as = true
  | _, _, _, .nil, _ => by simp [Atom.wfLB, Atom.fnOkL]
  | _, _, _, .cons h hs, hg => by
      have := ARel.closed h hg; have := ARelL.closed hs hg; simp_all [Atom.wfLB, Atom.fnOkL]
end

/-! THE EVALUATION LEMMA: an IR operand and its L2 atom evaluate to related values (`valOf`), both ways round. -/
mutual
theorem ARel.eval : ∀ {vs o a}, ARel 0 vs o a → Good vs → Opd.eval (vs.map valOf) o = (Atom.eval a).map valOf
  | _, _, _, .varL h, _ => absurd h (Nat.not_lt_zero _)
  | vs, _, _, .varV (i := i) (v := w) _ hw, hg => by
      have := (hg w (List.mem_of_getElem? hw)).2.2
      simp only [Opd.eval, List.getElem?_map, Nat.sub_zero] at hw ⊢; simp [hw, this]
  | _, _, _, .const, _ => by simp [Opd.eval, Atom.eval, valOf]
  | vs, _, _, .prim (p := p) (as := as) h, hg => by
      simp only [Opd.eval, Atom.eval, ARelL.eval h hg]
      cases Atom.evalL as with
      | none => rfl
      | some ws =>
        simp only [Option.map_some, Option.bind_some, mapM_asConst]
        cases constsOf ws with
        | none => rfl
        | some cs => simp only [Option.bind_some, Option.map_map]; rfl
  | _, _, _, .lam _ _, _ => by simp [Opd.eval, Atom.eval, valOf]
  | _, _, _, .fix _ _, _ => by simp [Opd.eval, Atom.eval, valOf]
  | _, _, _, .pair (a₁ := a₁) (a₂ := a₂) h₁ h₂, hg => by
      simp only [Opd.eval, Atom.eval, ARel.eval h₁ hg, ARel.eval h₂ hg]
      cases Atom.eval a₁ <;> cases Atom.eval a₂ <;> simp [valOf]
  | _, _, _, .fst (a := a) h, hg => by
      simp only [Opd.eval, Atom.eval, ARel.eval h hg]
      cases Atom.eval a with
      | none => rfl
      | some w => cases w <;> simp [valOf]
  | _, _, _, .snd (a := a) h, hg => by
      simp only [Opd.eval, Atom.eval, ARel.eval h hg]
      cases Atom.eval a with
      | none => rfl
      | some w => cases w <;> simp [valOf]
  | _, _, _, .inl (a := a) h, hg => by
      simp only [Opd.eval, Atom.eval, ARel.eval h hg]; cases Atom.eval a <;> simp [valOf]
  | _, _, _, .inr (a := a) h, hg => by
      simp only [Opd.eval, Atom.eval, ARel.eval h hg]; cases Atom.eval a <;> simp [valOf]
theorem ARelL.eval : ∀ {vs os as}, ARelL 0 vs os as → Good vs →
    Opd.evalL (vs.map valOf) os = (Atom.evalL as).map (List.map valOf)
  | _, _, _, .nil, _ => rfl
  | _, _, _, .cons (a := a) (as := as) h hs, hg => by
      simp only [Opd.evalL, Atom.evalL, ARel.eval h hg, ARelL.eval hs hg]
      cases Atom.eval a <;> cases Atom.evalL as <;> simp
end

/-! ## The store operations agree. -/
theorem opStep_consts {o : VIRL2.Op} {vs : List Atom₂} {σ r} (h : opStep o vs σ = some r) :
    ∃ cs : List VIRL2.Const, vs = cs.map Atom.const := by
  unfold opStep at h
  split at h <;> first | exact ⟨[_], rfl⟩ | exact ⟨[_, _], rfl⟩ | exact ⟨[_, _, _], rfl⟩ | simp at h

theorem opStep_res {o : VIRL2.Op} {vs : List Atom₂} {σ a σ'} (h : opStep o vs σ = some (a, σ')) :
    ∃ c, a = .const c := by
  unfold opStep at h
  split at h <;> (try simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h) <;>
    first
    | (obtain ⟨_, _, h1, _⟩ := h; exact ⟨_, h1.symm⟩)
    | (obtain ⟨_, h1⟩ := h; exact ⟨_, h1.symm⟩)
    | (obtain ⟨_, _, h1⟩ := h; exact ⟨_, h1.symm⟩)
    | simp at h

theorem constsOf_map : ∀ (cs : List VIRL2.Const), constsOf (cs.map (Atom.const (S := S₂))) = some cs
  | [] => rfl
  | c :: cs => by simp [constsOf, constsOf_map cs]

theorem constsOf_some : ∀ {vs : List Atom₂} {cs}, constsOf vs = some cs → vs = cs.map Atom.const
  | [], cs, h => by simp [constsOf] at h; subst h; rfl
  | .const c :: vs, cs, h => by
      simp only [constsOf, Option.map_eq_some_iff] at h
      obtain ⟨cs', h', rfl⟩ := h; simp [constsOf_some h']
  | .var _ :: _, _, h | .prim _ _ :: _, _, h | .lam _ _ :: _, _, h | .fix _ _ _ :: _, _, h | .pair _ _ :: _, _, h
  | .fst _ :: _, _, h | .snd _ :: _, _, h | .inl _ _ :: _, _, h | .inr _ _ :: _, _, h => by simp [constsOf] at h

/-- IR store operations on the images of L2 values ARE L2's. -/
theorem opIR_valOf (o : VIRL2.Op) (vs : List Atom₂) (σ : Store) :
    opIR o (vs.map valOf) σ = (opStep o vs σ).map fun r => (valOf r.1, r.2) := by
  unfold opIR
  rw [mapM_asConst]
  cases hc : constsOf vs with
  | some cs =>
    rw [constsOf_some hc]
    simp only [Option.bind_some]
    cases hs : opStep o (cs.map Atom.const) σ with
    | none => rfl
    | some r =>
      obtain ⟨a, σ'⟩ := r
      obtain ⟨c, rfl⟩ := opStep_res hs
      rfl
  | none =>
    simp only [Option.bind_none]
    cases hs : opStep o vs σ with
    | none => rfl
    | some r =>
      obtain ⟨cs, rfl⟩ := opStep_consts hs
      rw [constsOf_map] at hc; cases hc

end VIRC
