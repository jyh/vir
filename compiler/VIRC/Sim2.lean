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

/-! ## Part 3: operands. -/
/-- IR values by type, independent of words (the overflow branch still needs the value's SHAPE). -/
inductive VTy : Ty₂ → VIRC.Val → Prop where
  | int {n : Int} : VTy (Ty.base BTy.int) (VIRC.Val.const (.int n))
  | bool {b : Bool} : VTy (Ty.base BTy.bool) (VIRC.Val.const (.bool b))
  | unit : VTy (Ty.base BTy.unit) (VIRC.Val.const .unit)
  | cap {p : Int} : VTy (Ty.base BTy.cap) (VIRC.Val.const (.cap p))
  | code {τ₁ τ₂ : Ty₂} {b : Bool} {c : Code} : VTy (Ty.arr τ₁ τ₂) (VIRC.Val.code b c)
  | pair {τ₁ τ₂ v₁ v₂} : VTy τ₁ v₁ → VTy τ₂ v₂ → VTy (Ty.prod τ₁ τ₂) (VIRC.Val.pair v₁ v₂)
  | inl {τ₁ τ₂ v} : VTy τ₁ v → VTy (Ty.sum τ₁ τ₂) (VIRC.Val.inl v)
  | inr {τ₁ τ₂ v} : VTy τ₂ v → VTy (Ty.sum τ₁ τ₂) (VIRC.Val.inr v)

theorem VRel.vty {T lay σ} : ∀ {τ v ws}, VRel T lay σ τ v ws → VTy τ v
  | _, _, _, .int _ => .int
  | _, _, _, .bool => .bool
  | _, _, _, .unit => .unit
  | _, _, _, .cap _ => .cap
  | _, _, _, .lam _ _ _ => .code
  | _, _, _, .fix _ _ _ => .code
  | _, _, _, .pair h₁ h₂ => .pair h₁.vty h₂.vty
  | _, _, _, .inl h => .inl h.vty
  | _, _, _, .inr h => .inr h.vty

/-- The word outcome of an operand against an IR value at a type: an OVERFLOW, or related words. -/
def WOut (T : Table) (lay : Int → W) (σ : Store) (ρw : List W) (o : WOpd) (τ : Ty₂) (v : VIRC.Val) : Prop :=
  evalW ρw o = .ovf ∨ ∃ ws, evalW ρw o = .ok ws ∧ VRel T lay σ τ v ws

inductive WOutL (T : Table) (lay : Int → W) (σ : Store) (ρw : List W) :
    List WOpd → List Ty₂ → List VIRC.Val → Prop where
  | nil : WOutL T lay σ ρw [] [] []
  | cons {o os τ τs v vs} : VTy τ v → WOut T lay σ ρw o τ v → WOutL T lay σ ρw os τs vs →
      WOutL T lay σ ρw (o :: os) (τ :: τs) (v :: vs)

theorem wout_int {T lay σ ρw o v} (hv : VTy (Ty.base BTy.int) v) (hw : WOut T lay σ ρw o (Ty.base BTy.int) v) :
    ∃ n, v = .const (.int n) ∧ (evalW ρw o = .ovf ∨ (inRange n = true ∧ evalW ρw o = .ok [BitVec.ofInt 64 n])) := by
  cases hv with
  | int =>
    rename_i n
    refine ⟨n, rfl, ?_⟩
    rcases hw with h | ⟨ws, h, hr⟩
    · exact .inl h
    · cases hr with
      | int hn => exact .inr ⟨hn, h⟩

theorem wout_bool {T lay σ ρw o v} (hv : VTy (Ty.base BTy.bool) v) (hw : WOut T lay σ ρw o (Ty.base BTy.bool) v) :
    ∃ b, v = .const (.bool b) ∧ (evalW ρw o = .ovf ∨ evalW ρw o = .ok [boolW b]) := by
  cases hv with
  | bool =>
    rename_i b
    refine ⟨b, rfl, ?_⟩
    rcases hw with h | ⟨ws, h, hr⟩
    · exact .inl h
    · cases hr with
      | bool => exact .inr h

/-- A binary operator over two one-word operands: an overflow in either propagates; otherwise the operator applies. -/
theorem arith_out {ρw : List W} (op : AOp) {o₁ o₂ : WOpd} {x y : W}
    (h₁ : evalW ρw o₁ = .ovf ∨ evalW ρw o₁ = .ok [x]) (h₂ : evalW ρw o₂ = .ovf ∨ evalW ρw o₂ = .ok [y]) :
    evalW ρw (.arith op o₁ o₂) = .ovf ∨ evalW ρw (.arith op o₁ o₂) = op.apply x y := by
  rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂ <;> simp [evalW, WRes.bind, h₁, h₂]

theorem chk_out {T lay σ} (n : Int) :
    chk n = .ovf ∨ ∃ ws, chk n = .ok ws ∧ VRel T lay σ (Ty.base BTy.int) (.const (.int n)) ws := by
  unfold chk; split
  · next h => exact .inr ⟨_, rfl, .int h⟩
  · exact .inl rfl

theorem boolW_band (a b : Bool) : boolW a &&& boolW b = boolW (a && b) := by cases a <;> cases b <;> decide
theorem boolW_bor (a b : Bool) : boolW a ||| boolW b = boolW (a || b) := by cases a <;> cases b <;> decide
theorem boolW_not (a : Bool) : 1 - boolW a = boolW (!a) := by cases a <;> decide

theorem ofInt_eq_iff {a b : Int} (ha : inRange a = true) (hb : inRange b = true) :
    (BitVec.ofInt 64 a = BitVec.ofInt 64 b) ↔ a = b := by
  constructor
  · intro h; have := congrArg BitVec.toInt h; rwa [toInt_word ha, toInt_word hb] at this
  · rintro rfl; rfl

theorem inRange_max {a b : Int} (ha : inRange a = true) (hb : inRange b = true) : inRange (max a b) = true := by
  simp only [inRange, decide_eq_true_eq] at *; omega

theorem eval_prim {ρ : List VIRC.Val} {os : List Opd} {p : L1.Prim} {vs : List VIRC.Val} (h : Opd.evalL ρ os = some vs) :
    Opd.eval ρ (.prim p os) = (vs.mapM Val.asConst).bind fun cs => (pInterp p cs).map VIRC.Val.const := by
  simp [Opd.eval, h]

/-- Binary integer operators: the IR result and the word outcome, from the two operand outcomes. -/
theorem int2 {T lay σ ρw} {o₁ o₂ : WOpd} {x y : Int} (op : AOp)
    (hx : evalW ρw o₁ = .ovf ∨ (inRange x = true ∧ evalW ρw o₁ = .ok [BitVec.ofInt 64 x]))
    (hy : evalW ρw o₂ = .ovf ∨ (inRange y = true ∧ evalW ρw o₂ = .ok [BitVec.ofInt 64 y]))
    (τ : Ty₂) (v : VIRC.Val)
    (hop : inRange x = true → inRange y = true →
      op.apply (BitVec.ofInt 64 x) (BitVec.ofInt 64 y) = .ovf ∨
      ∃ ws, op.apply (BitVec.ofInt 64 x) (BitVec.ofInt 64 y) = .ok ws ∧ VRel T lay σ τ v ws) :
    WOut T lay σ ρw (.arith op o₁ o₂) τ v := by
  rcases hx with hx | ⟨rx, hx⟩
  · exact .inl (by simp [evalW, WRes.bind, hx])
  rcases hy with hy | ⟨ry, hy⟩
  · exact .inl (by simp [evalW, WRes.bind, hx, hy])
  simp only [WOut, evalW, WRes.bind, hx, hy]
  exact hop rx ry

theorem bool2 {T lay σ ρw} {o₁ o₂ : WOpd} {x y : Bool} (op : AOp)
    (hx : evalW ρw o₁ = .ovf ∨ evalW ρw o₁ = .ok [boolW x]) (hy : evalW ρw o₂ = .ovf ∨ evalW ρw o₂ = .ok [boolW y])
    (τ : Ty₂) (v : VIRC.Val)
    (hop : ∃ ws, op.apply (boolW x) (boolW y) = .ok ws ∧ VRel T lay σ τ v ws) :
    WOut T lay σ ρw (.arith op o₁ o₂) τ v := by
  rcases hx with hx | hx
  · exact .inl (by simp [evalW, WRes.bind, hx])
  rcases hy with hy | hy
  · exact .inl (by simp [evalW, WRes.bind, hx, hy])
  simp only [WOut, evalW, WRes.bind, hx, hy]
  exact .inr hop

mutual
theorem opd_sim {T lay σ} (hT : T.length < 2 ^ 64) : ∀ {a : Atom₂} {Γl Γt : Ctx S₂} {k : Nat} {τ : Ty₂}
    {ρ : List VIRC.Val} {ρw : List W} (t : Table),
    HasTypeA₂ Γt a τ → Atom.wfB k a = true → Agree k Γl Γt → EnvRel T lay σ Γl ρ ρw →
    Atom.fnOk a = true → Atom.ok2 a = true → KeepsFrom t.length (lower2A Γl a t).2 T →
    ∃ v, Opd.eval ρ (lowerA a) = some v ∧ VTy τ v ∧ WOut T lay σ ρw (lower2A Γl a t).1 τ v
  | _, Γl, Γt, k, τ, ρ, ρw, t, .var (n := n) hg _, hw, hag, he, _, _, _ => by
      simp only [Atom.wfB, decide_eq_true_eq] at hw
      have hg' : Γl[n]? = some τ := by rw [hag n hw]; exact hg
      obtain ⟨v, ws, h1, h2, h3⟩ := he.lookup hg'
      exact ⟨v, by simpa [lowerA, Opd.eval] using h1, h2.vty, .inr ⟨ws, by simpa [lower2A] using h3, h2⟩⟩
  | _, _, _, _, _, _, _, _, .int (n := n), _, _, _, _, hok, _ => by
      simp only [Atom.ok2] at hok
      exact ⟨_, rfl, .int, .inr ⟨_, rfl, .int hok⟩⟩
  | _, _, _, _, _, _, _, _, .bool, _, _, _, _, _, _ => ⟨_, rfl, .bool, .inr ⟨_, rfl, .bool⟩⟩
  | _, _, _, _, _, _, _, _, .unit, _, _, _, _, _, _ => ⟨_, rfl, .unit, .inr ⟨_, rfl, .unit⟩⟩
  | _, Γl, Γt, k, _, ρ, ρw, t, .prim (p := p) (as := as) hl, hw, hag, he, hf, hok, hk => by
      simp only [Atom.wfB] at hw; simp only [Atom.fnOk] at hf; simp only [Atom.ok2] at hok
      simp only [lower2A] at hk ⊢
      obtain ⟨vs, hev, hout⟩ := opdL_sim hT t hl hw hag he hf hok hk
      simp only [lowerA]
      rw [eval_prim hev]
      generalize (lower2L Γl as t).1 = os at hout ⊢
      cases p <;> simp only [S₂, L1.Prim.args, L1.Prim.res, BTy.ofL1, List.map] at hout ⊢
      all_goals rcases hout with _ | ⟨hv1, hw1, _ | ⟨hv2, hw2, ⟨⟩⟩⟩
      -- add
      · obtain ⟨x, rfl, hx⟩ := wout_int hv1 hw1; obtain ⟨y, rfl, hy⟩ := wout_int hv2 hw2
        refine ⟨.const (.int (x + y)), by simp [List.mapM_cons, Val.asConst, pInterp, Const.toL1, L1.Prim.interp,
          Const.ofL1], .int, ?_⟩
        exact int2 .add hx hy _ _ fun rx ry => by simp only [AOp.apply, toInt_word rx, toInt_word ry]; exact chk_out _
      -- sub
      · obtain ⟨x, rfl, hx⟩ := wout_int hv1 hw1; obtain ⟨y, rfl, hy⟩ := wout_int hv2 hw2
        refine ⟨.const (.int (x - y)), by simp [List.mapM_cons, Val.asConst, pInterp, Const.toL1, L1.Prim.interp,
          Const.ofL1], .int, ?_⟩
        exact int2 .sub hx hy _ _ fun rx ry => by simp only [AOp.apply, toInt_word rx, toInt_word ry]; exact chk_out _
      -- mul
      · obtain ⟨x, rfl, hx⟩ := wout_int hv1 hw1; obtain ⟨y, rfl, hy⟩ := wout_int hv2 hw2
        refine ⟨.const (.int (x * y)), by simp [List.mapM_cons, Val.asConst, pInterp, Const.toL1, L1.Prim.interp,
          Const.ofL1], .int, ?_⟩
        exact int2 .mul hx hy _ _ fun rx ry => by simp only [AOp.apply, toInt_word rx, toInt_word ry]; exact chk_out _
      -- lt
      · obtain ⟨x, rfl, hx⟩ := wout_int hv1 hw1; obtain ⟨y, rfl, hy⟩ := wout_int hv2 hw2
        refine ⟨.const (.bool (decide (x < y))), by simp [List.mapM_cons, Val.asConst, pInterp, Const.toL1,
          L1.Prim.interp, Const.ofL1], .bool, ?_⟩
        exact int2 .lt hx hy _ _ fun rx ry => .inr ⟨_, by simp only [AOp.apply, toInt_word rx, toInt_word ry], .bool⟩
      -- le
      · obtain ⟨x, rfl, hx⟩ := wout_int hv1 hw1; obtain ⟨y, rfl, hy⟩ := wout_int hv2 hw2
        refine ⟨.const (.bool (decide (x ≤ y))), by simp [List.mapM_cons, Val.asConst, pInterp, Const.toL1,
          L1.Prim.interp, Const.ofL1], .bool, ?_⟩
        exact int2 .le hx hy _ _ fun rx ry => .inr ⟨_, by simp only [AOp.apply, toInt_word rx, toInt_word ry], .bool⟩
      -- eq
      · obtain ⟨x, rfl, hx⟩ := wout_int hv1 hw1; obtain ⟨y, rfl, hy⟩ := wout_int hv2 hw2
        refine ⟨.const (.bool (decide (x = y))), by simp [List.mapM_cons, Val.asConst, pInterp, Const.toL1,
          L1.Prim.interp, Const.ofL1], .bool, ?_⟩
        exact int2 .eq hx hy _ _ fun rx ry => .inr ⟨_, by simp only [AOp.apply, ofInt_eq_iff rx ry], .bool⟩
      -- and
      · obtain ⟨x, rfl, hx⟩ := wout_bool hv1 hw1; obtain ⟨y, rfl, hy⟩ := wout_bool hv2 hw2
        refine ⟨.const (.bool (x && y)), by simp [List.mapM_cons, Val.asConst, pInterp, Const.toL1,
          L1.Prim.interp, Const.ofL1], .bool, ?_⟩
        exact bool2 .band hx hy _ _ ⟨_, by simp only [AOp.apply, boolW_band], .bool⟩
      -- or
      · obtain ⟨x, rfl, hx⟩ := wout_bool hv1 hw1; obtain ⟨y, rfl, hy⟩ := wout_bool hv2 hw2
        refine ⟨.const (.bool (x || y)), by simp [List.mapM_cons, Val.asConst, pInterp, Const.toL1,
          L1.Prim.interp, Const.ofL1], .bool, ?_⟩
        exact bool2 .bor hx hy _ _ ⟨_, by simp only [AOp.apply, boolW_bor], .bool⟩
      -- not
      · obtain ⟨x, rfl, hx⟩ := wout_bool hv1 hw1
        refine ⟨.const (.bool (!x)), by simp [List.mapM_cons, Val.asConst, pInterp, Const.toL1,
          L1.Prim.interp, Const.ofL1], .bool, ?_⟩
        rcases hx with hx | hx
        · exact .inl (by simp [primW, evalW, WRes.bind, hx])
        · exact .inr ⟨_, by simp [primW, evalW, WRes.bind, hx]; cases x <;> decide, .bool⟩
      -- max
      · obtain ⟨x, rfl, hx⟩ := wout_int hv1 hw1; obtain ⟨y, rfl, hy⟩ := wout_int hv2 hw2
        refine ⟨.const (.int (max x y)), by simp [List.mapM_cons, Val.asConst, pInterp, Const.toL1,
          L1.Prim.interp, Const.ofL1], .int, ?_⟩
        refine int2 .max hx hy _ _ fun rx ry => .inr ⟨_, rfl, ?_⟩
        simp only [toInt_word rx, toInt_word ry]
        by_cases hxy : x ≤ y
        · rw [if_pos hxy, max_eq_right hxy]; exact .int ry
        · rw [if_neg hxy, max_eq_left (by omega)]; exact .int rx
  | _, Γl, Γt, k, _, ρ, ρw, t, .lam (τ₁ := τ₁) (τ₂ := τ₂) (e := e) (Δ := Δ) _ _ _ _ hb, hw, hag, he, hf, hok, hk => by
      simp only [Atom.fnOk, Bool.and_eq_true] at hf; simp only [Atom.ok2] at hok
      simp only [lower2A] at hk ⊢
      have hkr := lower2T_keeps [τ₁] e (t ++ [(false, placeholder)])
      have hlen' : t.length < (lower2T [τ₁] e (t ++ [(false, placeholder)])).2.length := by
        have := hkr.1; simp at this; omega
      have hTl : T[t.length]? = some (false, (lower2T [τ₁] e (t ++ [(false, placeholder)])).1) := by
        rw [hk.2 t.length (le_refl _) (by simpa using hlen')]; simp [hlen']
      have hlt : t.length < 2 ^ 64 := by have := hk.1; simp at this; omega
      refine ⟨.code false (lowerT e), rfl, .code, .inr ⟨_, rfl, .lam hlt ⟨_, by simp, hTl, ?_⟩ ⟨Γt, Δ, by simpa using hb,
        hf.1, hf.2, hok⟩⟩⟩
      exact ⟨le_trans (by simp) hk.1, fun i hi hl => by
        rw [hk.2 i (by omega) (by simpa using hl), List.getElem?_set_ne (by omega)]⟩
  | _, Γl, Γt, k, _, ρ, ρw, t, .fix (τ₁ := τ₁) (τ₂ := τ₂) (e := e) (Δ := Δ) _ _ _ _ hb, hw, hag, he, hf, hok, hk => by
      simp only [Atom.fnOk, Bool.and_eq_true] at hf; simp only [Atom.ok2] at hok
      simp only [lower2A] at hk ⊢
      have hkr := lower2T_keeps [τ₁, .arr τ₁ τ₂] e (t ++ [(true, placeholder)])
      have hlen' : t.length < (lower2T [τ₁, .arr τ₁ τ₂] e (t ++ [(true, placeholder)])).2.length := by
        have := hkr.1; simp at this; omega
      have hTl : T[t.length]? = some (true, (lower2T [τ₁, .arr τ₁ τ₂] e (t ++ [(true, placeholder)])).1) := by
        rw [hk.2 t.length (le_refl _) (by simpa using hlen')]; simp [hlen']
      have hlt : t.length < 2 ^ 64 := by have := hk.1; simp at this; omega
      refine ⟨.code true (lowerT e), rfl, .code, .inr ⟨_, rfl, .fix hlt ⟨_, by simp, hTl, ?_⟩ ⟨Γt, Δ, by simpa using hb,
        hf.1, hf.2, hok⟩⟩⟩
      exact ⟨le_trans (by simp) hk.1, fun i hi hl => by
        rw [hk.2 i (by omega) (by simpa using hl), List.getElem?_set_ne (by omega)]⟩
  | _, Γl, Γt, k, _, ρ, ρw, t, .pair (a₁ := a₁) (a₂ := a₂) h₁ h₂, hw, hag, he, hf, hok, hk => by
      simp only [Atom.wfB, Bool.and_eq_true] at hw; simp only [Atom.fnOk, Bool.and_eq_true] at hf
      simp only [Atom.ok2, Bool.and_eq_true] at hok
      simp only [lower2A] at hk ⊢
      have k₂ := hk.mono (lower2A_keeps Γl a₁ t).1
      have k₁ := KeepsFrom.of_keeps (lower2A_keeps Γl a₂ _) hk
      obtain ⟨v₁, e₁, t₁, w₁⟩ := opd_sim hT t h₁ hw.1 hag he hf.1 hok.1 k₁
      obtain ⟨v₂, e₂, t₂, w₂⟩ := opd_sim hT _ h₂ hw.2 hag he hf.2 hok.2 k₂
      refine ⟨.pair v₁ v₂, by simp [lowerA, Opd.eval, e₁, e₂], .pair t₁ t₂, ?_⟩
      rcases w₁ with w₁ | ⟨ws₁, w₁, r₁⟩
      · exact .inl (by simp [evalW, WRes.bind, w₁])
      rcases w₂ with w₂ | ⟨ws₂, w₂, r₂⟩
      · exact .inl (by simp [evalW, WRes.bind, w₁, w₂])
      · exact .inr ⟨_, by simp [evalW, WRes.bind, w₁, w₂], .pair r₁ r₂⟩
  | _, Γl, Γt, k, _, ρ, ρw, t, .fst (a := a) (τ₁ := τ₁) (τ₂ := τ₂) h, hw, hag, he, hf, hok, hk => by
      simp only [Atom.wfB] at hw; simp only [Atom.fnOk] at hf; simp only [Atom.ok2] at hok
      have hinf : inferA Γl a = some (.prod τ₁ τ₂) := by rw [inferA_agree a hw hag]; exact inferA_sound h
      simp only [lower2A, hinf] at hk ⊢
      obtain ⟨v, ev, vt, wo⟩ := opd_sim hT t h hw hag he hf hok hk
      cases vt with
      | pair vt₁ vt₂ =>
        rename_i v₁ v₂
        refine ⟨v₁, by simp [lowerA, Opd.eval, ev], vt₁, ?_⟩
        rcases wo with wo | ⟨ws, wo, r⟩
        · exact .inl (by simp [evalW, WRes.bind, wo])
        · cases r with
          | pair r₁ r₂ =>
            refine .inr ⟨_, by simp [evalW, WRes.bind, wo]; rfl, ?_⟩
            rw [← r₁.length, List.take_left]; exact r₁
  | _, Γl, Γt, k, _, ρ, ρw, t, .snd (a := a) (τ₁ := τ₁) (τ₂ := τ₂) h, hw, hag, he, hf, hok, hk => by
      simp only [Atom.wfB] at hw; simp only [Atom.fnOk] at hf; simp only [Atom.ok2] at hok
      have hinf : inferA Γl a = some (.prod τ₁ τ₂) := by rw [inferA_agree a hw hag]; exact inferA_sound h
      simp only [lower2A, hinf] at hk ⊢
      obtain ⟨v, ev, vt, wo⟩ := opd_sim hT t h hw hag he hf hok hk
      cases vt with
      | pair vt₁ vt₂ =>
        rename_i v₁ v₂
        refine ⟨v₂, by simp [lowerA, Opd.eval, ev], vt₂, ?_⟩
        rcases wo with wo | ⟨ws, wo, r⟩
        · exact .inl (by simp [evalW, WRes.bind, wo])
        · cases r with
          | pair r₁ r₂ =>
            refine .inr ⟨_, by simp [evalW, WRes.bind, wo]; rfl, ?_⟩
            rw [← r₁.length, List.drop_left]; exact r₂
  | _, Γl, Γt, k, _, ρ, ρw, t, .inl (a := a) (τ₁ := τ₁) (τ₂ := τ₂) _ h, hw, hag, he, hf, hok, hk => by
      simp only [Atom.wfB] at hw; simp only [Atom.fnOk] at hf; simp only [Atom.ok2] at hok
      have hinf : inferA Γl a = some τ₁ := by rw [inferA_agree a hw hag]; exact inferA_sound h
      simp only [lower2A, hinf] at hk ⊢
      obtain ⟨v, ev, vt, wo⟩ := opd_sim hT t h hw hag he hf hok hk
      refine ⟨.inl v, by simp [lowerA, Opd.eval, ev], .inl vt, ?_⟩
      rcases wo with wo | ⟨ws, wo, r⟩
      · exact .inl (by simp [evalW, WRes.bind, wo])
      · exact .inr ⟨_, by simp [evalW, WRes.bind, wo], .inl r⟩
  | _, Γl, Γt, k, _, ρ, ρw, t, .inr (a := a) (τ₁ := τ₁) (τ₂ := τ₂) _ h, hw, hag, he, hf, hok, hk => by
      simp only [Atom.wfB] at hw; simp only [Atom.fnOk] at hf; simp only [Atom.ok2] at hok
      have hinf : inferA Γl a = some τ₂ := by rw [inferA_agree a hw hag]; exact inferA_sound h
      simp only [lower2A, hinf] at hk ⊢
      obtain ⟨v, ev, vt, wo⟩ := opd_sim hT t h hw hag he hf hok hk
      refine ⟨.inr v, by simp [lowerA, Opd.eval, ev], .inr vt, ?_⟩
      rcases wo with wo | ⟨ws, wo, r⟩
      · exact .inl (by simp [evalW, WRes.bind, wo])
      · exact .inr ⟨_, by simp [evalW, WRes.bind, wo], .inr r⟩
theorem opdL_sim {T lay σ} (hT : T.length < 2 ^ 64) : ∀ {as : List Atom₂} {Γl Γt : Ctx S₂} {k : Nat} {τs : List Ty₂}
    {ρ : List VIRC.Val} {ρw : List W} (t : Table),
    HasTypeL₂ Γt as τs → Atom.wfLB k as = true → Agree k Γl Γt → EnvRel T lay σ Γl ρ ρw →
    Atom.fnOkL as = true → Atom.ok2L as = true → KeepsFrom t.length (lower2L Γl as t).2 T →
    ∃ vs, Opd.evalL ρ (lowerL as) = some vs ∧ WOutL T lay σ ρw (lower2L Γl as t).1 τs vs
  | _, _, _, _, _, _, _, _, .nil, _, _, _, _, _, _ => ⟨[], rfl, .nil⟩
  | _, Γl, Γt, k, _, ρ, ρw, t, .cons (a := a) (as := as) h hs, hw, hag, he, hf, hok, hk => by
      simp only [Atom.wfLB, Bool.and_eq_true] at hw; simp only [Atom.fnOkL, Bool.and_eq_true] at hf
      simp only [Atom.ok2L, Bool.and_eq_true] at hok
      simp only [lower2L] at hk ⊢
      have k₂ := hk.mono (lower2A_keeps Γl a t).1
      have k₁ := KeepsFrom.of_keeps (lower2L_keeps Γl as _) hk
      obtain ⟨v, ev, vt, wo⟩ := opd_sim hT t h hw.1 hag he hf.1 hok.1 k₁
      obtain ⟨vs, evs, wos⟩ := opdL_sim hT _ hs hw.2 hag he hf.2 hok.2 k₂
      exact ⟨v :: vs, by simp [lowerL, Opd.evalL, ev, evs], .cons vt wo wos⟩
end

/-! ## Part 4: memory. A store preserves the layout premise and the memory relation; R never changes (S2-A (a)). -/
theorem store_eq {σ σ' : Store} {p i v : Int} {n : Nat} (hR : σ.R.lookup p = some n) (hs : Store.store p i v σ = some σ') :
    (0 ≤ i ∧ i < n) ∧ σ' = ⟨σ.H.insert (p + i) v, σ.R⟩ := by
  unfold Store.store at hs; simp only [hR] at hs
  split at hs
  · next h => exact ⟨h, (Option.some.inj hs).symm⟩
  · cases hs

/-- Two live cells of distinct (region, index) pairs have distinct L2 addresses. -/
theorem cell_ne {σ : Store} (hw : σ.WF) {p q : Int} {n m : Nat} (hp : σ.R.lookup p = some n) (hq : σ.R.lookup q = some m)
    {i j : Int} (hi : 0 ≤ i ∧ i < n) (hj : 0 ≤ j ∧ j < m) (hne : ¬ (q = p ∧ j = i)) : q + j ≠ p + i := by
  intro h
  by_cases hqp : q = p
  · subst hqp; exact hne ⟨rfl, by omega⟩
  · exact hw.disj q p m n hq hp hqp (q + j) ⟨by omega, by omega⟩ (by rw [h]; exact ⟨by omega, by omega⟩)

theorem layout_store {σ σ' : Store} {lay} {p i v : Int} {n : Nat} (hl : Layout σ lay) (hR : σ.R.lookup p = some n)
    (hv : inRange v = true) (hs : Store.store p i v σ = some σ') : Layout σ' lay ∧ σ'.R = σ.R := by
  obtain ⟨hi, rfl⟩ := store_eq hR hs
  have hmem : p + i ∈ σ.H := (hl.wf.domH _).2 ⟨p, n, hR, ⟨by omega, by omega⟩⟩
  refine ⟨⟨wf_insert_mem hmem hl.wf, hl.fits, hl.disj, fun q m hq j hj => ?_⟩, rfl⟩
  by_cases hc : q = p ∧ (j : Int) = i
  · obtain ⟨rfl, hji⟩ := hc
    exact ⟨v, by rw [hji, Finmap.lookup_insert], hv⟩
  · rw [Finmap.lookup_insert_of_ne _ (cell_ne hl.wf hR hq hi ⟨by omega, by simpa using hj⟩ hc)]
    exact hl.cells q m hq j hj

theorem memrel_store {σ σ' : Store} {lay} {m : WMem} {p i v : Int} {n : Nat} (hl : Layout σ lay) (hm : MemRel lay σ m)
    (hR : σ.R.lookup p = some n) (hs : Store.store p i v σ = some σ') :
    MemRel lay σ' (Function.update m (cellAddr (lay p) (BitVec.ofNat 64 i.toNat)) (BitVec.ofInt 64 v)) := by
  obtain ⟨hi, rfl⟩ := store_eq hR hs
  intro q m' hq j hj w hw
  by_cases hc : q = p ∧ j = i.toNat
  · obtain ⟨rfl, rfl⟩ := hc
    rw [Function.update_self]
    rw [Int.toNat_of_nonneg hi.1, Finmap.lookup_insert] at hw
    cases hw; rfl
  · have hne : cellAddr (lay q) (BitVec.ofNat 64 j) ≠ cellAddr (lay p) (BitVec.ofNat 64 i.toNat) := by
      intro h
      obtain ⟨h1, h2⟩ := cellAddr_inj hl hq hR hj (by omega) h
      exact hc ⟨h1, h2⟩
    rw [Function.update_of_ne hne]
    have hne' : q + (j : Int) ≠ p + i :=
      cell_ne hl.wf hR hq hi ⟨by omega, by simpa using hj⟩ (fun h => hc ⟨h.1, by omega⟩)
    rw [Finmap.lookup_insert_of_ne _ hne'] at hw
    exact hm q m' hq j hj w hw

end VIRC
