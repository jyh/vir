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

/-! ## Part 5: groundwork for the step simulation (loads, capability words, transport across stores with the same R). -/
theorem toInt_ofNat_small {n : Nat} (h : n < 2 ^ 63) : (BitVec.ofNat 64 n).toInt = n := by
  have : BitVec.ofNat 64 n = BitVec.ofInt 64 (n : Int) := by simp
  rw [this]; exact toInt_word (by simp only [inRange, decide_eq_true_eq]; omega)

theorem ofInt_nonneg {i : Int} (h : 0 ≤ i) : BitVec.ofInt 64 i = BitVec.ofNat 64 i.toNat := by
  obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le h
  simp

/-- A live cell's load reads, through the layout, the word of its value. -/
theorem load_sim {σ lay m} (hl : Layout σ lay) (hm : MemRel lay σ m) {p i : Int} {n : Nat}
    (hR : σ.R.lookup p = some n) (hi : 0 ≤ i ∧ i < n) :
    ∃ v, Store.load p i σ = some v ∧ inRange v = true ∧ m (cellAddr (lay p) (BitVec.ofInt 64 i)) = BitVec.ofInt 64 v := by
  obtain ⟨v, hv, hr⟩ := hl.cells p n hR i.toNat (by omega)
  rw [Int.toNat_of_nonneg hi.1] at hv
  refine ⟨v, by simp [Store.load, hR, hi, hv], hr, ?_⟩
  rw [ofInt_nonneg hi.1]
  exact hm p n hR i.toNat (by omega) v (by rw [Int.toNat_of_nonneg hi.1]; exact hv)

/-- The word bounds test agrees with L2's, for an index in range and a live length. -/
theorem bounds_iff {i : Int} {n : Nat} (hi : inRange i = true) (hn : n < 2 ^ 63) :
    (0 ≤ (BitVec.ofInt 64 i).toInt ∧ (BitVec.ofInt 64 i).toInt < (BitVec.ofNat 64 n).toInt) ↔ (0 ≤ i ∧ i < n) := by
  rw [toInt_word hi, toInt_ofNat_small hn]

/-- A two-word slice names the two words of the environment. -/
theorem slice2 {ρw : List W} {off : Nat} {a b : W} (h : (ρw.drop off).take 2 = [a, b]) :
    ρw[off]? = some a ∧ ρw[off + 1]? = some b := by
  have h0 := congrArg (·[0]?) h; have h1 := congrArg (·[1]?) h
  simp [List.getElem?_take, List.getElem?_drop] at h0 h1
  exact ⟨h0, by simpa [Nat.add_comm] using h1⟩

/-- The relations read σ only through R, so a store that keeps R keeps them. -/
theorem VRel.transport {T lay} {σ σ' : Store} (hR : σ'.R = σ.R) : ∀ {τ v ws}, VRel T lay σ τ v ws → VRel T lay σ' τ v ws
  | _, _, _, .int h => .int h
  | _, _, _, .bool => .bool
  | _, _, _, .unit => .unit
  | _, _, _, .cap h => .cap (by rw [hR]; exact h)
  | _, _, _, .lam h₁ h₂ h₃ => .lam h₁ h₂ h₃
  | _, _, _, .fix h₁ h₂ h₃ => .fix h₁ h₂ h₃
  | _, _, _, .pair h₁ h₂ => .pair (VRel.transport hR h₁) (VRel.transport hR h₂)
  | _, _, _, .inl h => .inl (VRel.transport hR h)
  | _, _, _, .inr h => .inr (VRel.transport hR h)

theorem EnvRel.transport {T lay} {σ σ' : Store} (hR : σ'.R = σ.R) : ∀ {Γ ρ ρw}, EnvRel T lay σ Γ ρ ρw → EnvRel T lay σ' Γ ρ ρw
  | _, _, _, .nil => .nil
  | _, _, _, .cons h hs => .cons (h.transport hR) (EnvRel.transport hR hs)

/-! ## Part 6: the state relation. -/
/-- IR code `c` and word code `wc` are the two lowerings of ONE typed, accepted source term, in related environments. -/
def CodeRel (T : Table) (lay : Int → W) (σ : Store) (Γl : Ctx S₂) (ρ : List VIRC.Val) (ρw : List W) (c : Code)
    (wc : WCode) (τ : Ty₂) : Prop :=
  ∃ e Γt Δ t, c = lowerT e ∧ wc = (lower2T Γl e t).1 ∧ KeepsFrom t.length (lower2T Γl e t).2 T ∧
    HasType₂ Γt Δ e τ ∧ Tm.wfB Γl.length e = true ∧ Agree Γl.length Γl Γt ∧ Tm.fnOk e = true ∧ Tm.ok2 e = true ∧
    EnvRel T lay σ Γl ρ ρw

theorem CodeRel.transport {T lay} {σ σ' : Store} (hR : σ'.R = σ.R) {Γl ρ ρw c wc τ}
    (h : CodeRel T lay σ Γl ρ ρw c wc τ) : CodeRel T lay σ' Γl ρ ρw c wc τ := by
  obtain ⟨e, Γt, Δ, t, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  exact ⟨e, Γt, Δ, t, h1, h2, h3, h4, h5, h6, h7, h8, h9.transport hR⟩

/-- The frame stacks: each frame, given a related result of its input type, continues as related code of its output type. -/
inductive FRel2 (T : Table) (lay : Int → W) (σ : Store) : Ty₂ → List Frame → List (WCode × List W) → Ty₂ → Prop where
  | nil {τ} : FRel2 T lay σ τ [] [] τ
  | cons {τin τout τfin : Ty₂} {c : Code} {ρ : List VIRC.Val} {wc : WCode} {ρw : List W} {k kw} :
      (∀ v ws, VRel T lay σ τin v ws → ∃ Γl, CodeRel T lay σ Γl (v :: ρ) (ws ++ ρw) c wc τout) →
      FRel2 T lay σ τout k kw τfin → FRel2 T lay σ τin ((c, ρ) :: k) ((wc, ρw) :: kw) τfin

theorem FRel2.transport {T lay} {σ σ' : Store} (hR : σ'.R = σ.R) : ∀ {τ k kw τfin},
    FRel2 T lay σ τ k kw τfin → FRel2 T lay σ' τ k kw τfin
  | _, _, _, _, .nil => .nil
  | _, _, _, _, .cons hf hs => .cons (fun v ws hv => by
      obtain ⟨Γl, h⟩ := hf v ws (hv.transport hR.symm)
      exact ⟨Γl, h.transport hR⟩) (FRel2.transport hR hs)

/-- IR state against word state, for a run whose final type is τfin. -/
inductive SRel (T : Table) (lay : Int → W) (τfin : Ty₂) : St × Store → WSt × WMem → Prop where
  | run {c ρ k σ wc ρw kw m τ Γl} : CodeRel T lay σ Γl ρ ρw c wc τ → FRel2 T lay σ τ k kw τfin →
      Layout σ lay → MemRel lay σ m → SRel T lay τfin (.run c ρ k, σ) (.run wc ρw kw, m)
  | done {v σ ws m} : VRel T lay σ τfin v ws → SRel T lay τfin (.done v, σ) (.done ws, m)

/-! ## Part 7: the steps, one construct at a time. Each: the IR steps, and the word machine steps to a related state or to `ovf`. -/
def WStepOK (T : Table) (lay : Int → W) (τfin : Ty₂) (I' : St × Store) (Wst : WSt × WMem) : Prop :=
  ∃ W', stepW T Wst = some W' ∧ (SRel T lay τfin I' W' ∨ W'.1 = .ovf)

/-- Where a `ret` goes in the IR: finish, or resume the top frame with the value pushed. -/
def popIR (v : VIRC.Val) (σ : Store) : List Frame → St × Store
  | [] => (.done v, σ)
  | (c, ρ') :: k' => (.run c (v :: ρ') k', σ)

theorem stepIR_ret {o : Opd} {ρ : List VIRC.Val} {k : List Frame} {σ : Store} {v : VIRC.Val} (ev : Opd.eval ρ o = some v) :
    stepIR (.run (.ret o) ρ k, σ) = some (popIR v σ k) := by
  cases k with
  | nil => simp [stepIR, ev, popIR]
  | cons fr k' => obtain ⟨c', ρ'⟩ := fr; simp [stepIR, ev, popIR]

theorem ret_out {T lay τfin σ m} {ρw : List W} {o : WOpd} {v : VIRC.Val} {τ k kw}
    (hfr : FRel2 T lay σ τ k kw τfin) (hl : Layout σ lay) (hm : MemRel lay σ m)
    (wo : WOut T lay σ ρw o τ v) : WStepOK T lay τfin (popIR v σ k) (.run (.ret o) ρw kw, m) := by
  cases hfr with
  | nil =>
    rcases wo with wo | ⟨ws, wo, r⟩
    · exact ⟨(.ovf, m), by simp [stepW, wo], .inr rfl⟩
    · exact ⟨(.done ws, m), by simp [stepW, wo], .inl (.done r)⟩
  | cons hf' hrest =>
    rename_i c ρ' wc ρw' k' kw'
    rcases wo with wo | ⟨ws, wo, r⟩
    · exact ⟨(.ovf, m), by simp [stepW, wo], .inr rfl⟩
    · obtain ⟨Γl', hc⟩ := hf' v ws r
      exact ⟨(.run wc (ws ++ ρw') kw', m), by simp [stepW, wo], .inl (.run hc hrest hl hm)⟩

theorem step_ret {T lay τfin σ m} (hT : T.length < 2 ^ 64) {Γl Γt : Ctx S₂} {t : Table} {a : Atom₂} {τ : Ty₂}
    {ρ ρw k kw} (hty : HasTypeA₂ Γt a τ) (hw : Atom.wfB Γl.length a = true) (hag : Agree Γl.length Γl Γt)
    (he : EnvRel T lay σ Γl ρ ρw) (hf : Atom.fnOk a = true) (hok : Atom.ok2 a = true)
    (hk : KeepsFrom t.length (lower2A Γl a t).2 T) (hfr : FRel2 T lay σ τ k kw τfin) (hl : Layout σ lay)
    (hm : MemRel lay σ m) :
    ∃ I', stepIR (.run (.ret (lowerA a)) ρ k, σ) = some I' ∧
      WStepOK T lay τfin I' (.run (.ret (lower2A Γl a t).1) ρw kw, m) := by
  obtain ⟨v, ev, -, wo⟩ := opd_sim hT t hty hw hag he hf hok hk
  exact ⟨_, stepIR_ret ev, ret_out hfr hl hm wo⟩

theorem step_retCap {T lay τfin σ m} {Γl Γt : Ctx S₂} {n : Nat} {ρ ρw k kw}
    (hg : Γt[n]? = some tcap) (hw : n < Γl.length) (hag : Agree Γl.length Γl Γt)
    (he : EnvRel T lay σ Γl ρ ρw) (hfr : FRel2 T lay σ tcap k kw τfin) (hl : Layout σ lay) (hm : MemRel lay σ m) :
    ∃ I', stepIR (.run (.ret (lowerA (.var n))) ρ k, σ) = some I' ∧
      WStepOK T lay τfin I' (.run (.ret (varSlice Γl n)) ρw kw, m) := by
  have hg' : Γl[n]? = some tcap := by rw [hag n hw]; exact hg
  obtain ⟨v, ws, h1, h2, h3⟩ := he.lookup hg'
  have wo : WOut T lay σ ρw (varSlice Γl n) tcap v := .inr ⟨ws, h3, h2⟩
  exact ⟨_, stepIR_ret (by simpa [lowerA, Opd.eval] using h1), ret_out hfr hl hm wo⟩

theorem step_letE {T lay τfin σ m} {Γl Γt : Ctx S₂} {Δ₁ Δ₂ : List Bool} {t : Table} {τ₁ τ : Ty₂} {e₁ e₂ : Tm₂}
    {ρ ρw k kw}
    (h₁ : HasType₂ Γt Δ₁ e₁ τ₁) (h₂ : HasType₂ (τ₁ :: Γt) Δ₂ e₂ τ)
    (hw : Tm.wfB Γl.length (.letE τ₁ e₁ e₂) = true) (hag : Agree Γl.length Γl Γt)
    (he : EnvRel T lay σ Γl ρ ρw) (hf : Tm.fnOk (.letE τ₁ e₁ e₂) = true) (hok : Tm.ok2 (.letE τ₁ e₁ e₂) = true)
    (hk : KeepsFrom t.length (lower2T Γl (.letE τ₁ e₁ e₂) t).2 T) (hfr : FRel2 T lay σ τ k kw τfin)
    (hl : Layout σ lay) (hm : MemRel lay σ m) :
    ∃ I', stepIR (.run (lowerT (.letE τ₁ e₁ e₂)) ρ k, σ) = some I' ∧
      WStepOK T lay τfin I' (.run (lower2T Γl (.letE τ₁ e₁ e₂) t).1 ρw kw, m) := by
  simp only [Tm.wfB, Bool.and_eq_true] at hw; simp only [Tm.fnOk, Bool.and_eq_true] at hf
  simp only [Tm.ok2, Bool.and_eq_true] at hok
  simp only [lower2T] at hk ⊢
  refine ⟨(.run (lowerT e₁) ρ ((lowerT e₂, ρ) :: k), σ), by simp [lowerT, stepIR], _, rfl,
    .inl (.run (Γl := Γl) (τ := τ₁) ?_ (.cons (τin := τ₁) ?_ hfr) hl hm)⟩
  · exact ⟨e₁, Γt, Δ₁, t, rfl, rfl, KeepsFrom.of_keeps (lower2T_keeps _ e₂ _) hk, h₁, hw.1, hag, hf.1, hok.1, he⟩
  · intro v ws hv
    exact ⟨τ₁ :: Γl, e₂, τ₁ :: Γt, Δ₂, _, rfl, rfl, hk.mono (lower2T_keeps Γl e₁ t).1, h₂, by simpa using hw.2,
      by simpa using hag.cons τ₁, hf.2, hok.2, .cons hv he⟩

/-- The ending of a STUCK IR state, at the word level: the fault exit, or the overflow exit. -/
def WStops (T : Table) (Wst : WSt × WMem) : Prop :=
  ∃ W', stepW T Wst = some W' ∧ (W'.1 = .fault ∨ W'.1 = .ovf)

/-- A capability variable: its IR value and its two words. -/
theorem cap_lookup {T lay σ} {Γl : Ctx S₂} {ρ ρw} (he : EnvRel T lay σ Γl ρ ρw) {n : Nat} (hg : Γl[n]? = some tcap) :
    ∃ p len, ρ[n]? = some (.const (.cap p)) ∧ σ.R.lookup p = some len ∧
      ρw[offset Γl n]? = some (lay p) ∧ ρw[offset Γl n + 1]? = some (BitVec.ofNat 64 len) := by
  obtain ⟨v, ws, h1, h2, h3⟩ := he.lookup hg
  cases h2 with
  | cap hR =>
    rename_i p len
    refine ⟨p, len, h1, hR, ?_⟩
    simp only [varSlice, hg, Option.map_some, Option.getD_some, evalW] at h3
    split at h3
    · simp only [WRes.ok.injEq] at h3
      exact slice2 (by simpa [size, tcap] using h3)
    · cases h3

theorem step_load {T lay τfin σ m} (hT : T.length < 2 ^ 64) {Γl Γt : Ctx S₂} {Δ : List Bool} {t : Table} {n : Nat}
    {a : Atom₂} {e : Tm₂} {τ : Ty₂} {ρ ρw k kw}
    (hg : Γt[n]? = some tcap) (ha : HasTypeA₂ Γt a tint) (he' : HasType₂ (tint :: Γt) (false :: Δ) e τ)
    (hw : Tm.wfB Γl.length (.letOp .load [.var n, a] tint e) = true) (hag : Agree Γl.length Γl Γt)
    (he : EnvRel T lay σ Γl ρ ρw) (hf : Tm.fnOk (.letOp .load [.var n, a] tint e) = true)
    (hok : Tm.ok2 (.letOp .load [.var n, a] tint e) = true)
    (hk : KeepsFrom t.length (lower2T Γl (.letOp .load [.var n, a] tint e) t).2 T) (hfr : FRel2 T lay σ τ k kw τfin)
    (hl : Layout σ lay) (hm : MemRel lay σ m) :
    (stepIR (.run (lowerT (.letOp .load [.var n, a] tint e)) ρ k, σ) = none ∧
        WStops T (.run (lower2T Γl (.letOp .load [.var n, a] tint e) t).1 ρw kw, m)) ∨
    ∃ I', stepIR (.run (lowerT (.letOp .load [.var n, a] tint e)) ρ k, σ) = some I' ∧
      WStepOK T lay τfin I' (.run (lower2T Γl (.letOp .load [.var n, a] tint e) t).1 ρw kw, m) := by
  simp only [Tm.wfB, Atom.wfLB, Atom.wfB, decide_eq_true_eq, Bool.and_eq_true] at hw
  simp only [Tm.fnOk, Atom.fnOkL, Atom.fnOk, Bool.and_eq_true, true_and] at hf
  simp only [Tm.ok2, Atom.ok2L, Atom.ok2, Bool.and_eq_true, true_and] at hok
  simp only [lower2T, lower2L, lower2A, opCode] at hk ⊢
  have hg' : Γl[n]? = some tcap := by rw [hag n hw.1.1]; exact hg
  obtain ⟨p, len, hρ, hR, hb, hn⟩ := cap_lookup he hg'
  obtain ⟨vi, evi, vti, woi⟩ := opd_sim hT t ha hw.1.2.1 hag he hf.1.1 hok.1.1
    (KeepsFrom.of_keeps (lower2T_keeps _ e _) hk)
  obtain ⟨i, rfl, hi⟩ := wout_int vti woi
  have hlen : len < 2 ^ 63 := (hl.fits p len hR).2
  have hIR : stepIR (.run (lowerT (.letOp .load [.var n, a] tint e)) ρ k, σ) =
      (Store.load p i σ).map fun v₀ => (.run (lowerT e) (.const (.int v₀) :: ρ) k, σ) := by
    simp [lowerT, lowerL, lowerA, stepIR, Opd.evalL, Opd.eval, hρ, evi, opIR, Val.asConst, List.mapM_cons, opStep]
    cases Store.load p i σ <;> rfl
  by_cases hbd : 0 ≤ i ∧ i < len
  · obtain ⟨v₀, hv₀, hr₀, hm₀⟩ := load_sim hl hm hR hbd
    refine .inr ⟨_, by rw [hIR, hv₀]; rfl, ?_⟩
    rcases hi with hi | ⟨ri, hi⟩
    · exact ⟨(.ovf, m), by simp [stepW, hb, hn, hi], .inr rfl⟩
    · refine ⟨(.run (lower2T (tint :: Γl) e (lower2A Γl a t).2).1 (BitVec.ofInt 64 v₀ :: ρw) kw, m), ?_, .inl ?_⟩
      · simp only [stepW, hb, hn, hi]; rw [if_pos ((bounds_iff ri hlen).2 hbd), hm₀]
      · refine .run (Γl := tint :: Γl) (τ := τ) ⟨e, tint :: Γt, false :: Δ, _, rfl, rfl,
          hk.mono (lower2A_keeps Γl a t).1, he', by simpa using hw.2, by simpa using hag.cons tint, hf.2, hok.2, ?_⟩ hfr hl hm
        exact .cons (.int hr₀) he
  · refine .inl ⟨by rw [hIR]; simp [Store.load, hR, hbd], ?_⟩
    rcases hi with hi | ⟨ri, hi⟩
    · exact ⟨(.ovf, m), by simp [stepW, hb, hn, hi], .inr rfl⟩
    · refine ⟨(.fault, m), ?_, .inl rfl⟩
      simp only [stepW, hb, hn, hi]; rw [if_neg (fun h => hbd ((bounds_iff ri hlen).1 h))]

theorem step_store {T lay τfin σ m} (hT : T.length < 2 ^ 64) {Γl Γt : Ctx S₂} {Δ : List Bool} {t : Table} {n : Nat}
    {a₁ a₂ : Atom₂} {e : Tm₂} {τ : Ty₂} {ρ ρw k kw}
    (hg : Γt[n]? = some tcap) (ha₁ : HasTypeA₂ Γt a₁ tint) (ha₂ : HasTypeA₂ Γt a₂ tint)
    (he' : HasType₂ (tcap :: Γt) (true :: Δ.set n false) e τ)
    (hw : Tm.wfB Γl.length (.letOp .store [.var n, a₁, a₂] tcap e) = true) (hag : Agree Γl.length Γl Γt)
    (he : EnvRel T lay σ Γl ρ ρw) (hf : Tm.fnOk (.letOp .store [.var n, a₁, a₂] tcap e) = true)
    (hok : Tm.ok2 (.letOp .store [.var n, a₁, a₂] tcap e) = true)
    (hk : KeepsFrom t.length (lower2T Γl (.letOp .store [.var n, a₁, a₂] tcap e) t).2 T)
    (hfr : FRel2 T lay σ τ k kw τfin) (hl : Layout σ lay) (hm : MemRel lay σ m) :
    (stepIR (.run (lowerT (.letOp .store [.var n, a₁, a₂] tcap e)) ρ k, σ) = none ∧
        WStops T (.run (lower2T Γl (.letOp .store [.var n, a₁, a₂] tcap e) t).1 ρw kw, m)) ∨
    ∃ I', stepIR (.run (lowerT (.letOp .store [.var n, a₁, a₂] tcap e)) ρ k, σ) = some I' ∧
      WStepOK T lay τfin I' (.run (lower2T Γl (.letOp .store [.var n, a₁, a₂] tcap e) t).1 ρw kw, m) := by
  simp only [Tm.wfB, Atom.wfLB, Atom.wfB, decide_eq_true_eq, Bool.and_eq_true] at hw
  simp only [Tm.fnOk, Atom.fnOkL, Atom.fnOk, Bool.and_eq_true, true_and] at hf
  simp only [Tm.ok2, Atom.ok2L, Atom.ok2, Bool.and_eq_true, true_and] at hok
  simp only [lower2T, lower2L, lower2A, opCode] at hk ⊢
  have hg' : Γl[n]? = some tcap := by rw [hag n hw.1.1]; exact hg
  obtain ⟨p, len, hρ, hR, hb, hn⟩ := cap_lookup he hg'
  have k₂ := KeepsFrom.of_keeps (lower2T_keeps _ e _) hk
  obtain ⟨v₁, ev₁, vt₁, wo₁⟩ := opd_sim hT t ha₁ hw.1.2.1 hag he hf.1.1 hok.1.1
    (KeepsFrom.of_keeps (lower2A_keeps Γl a₂ _) k₂)
  obtain ⟨v₂, ev₂, vt₂, wo₂⟩ := opd_sim hT _ ha₂ hw.1.2.2.1 hag he hf.1.2.1 hok.1.2.1
    (k₂.mono (lower2A_keeps Γl a₁ t).1)
  obtain ⟨i, rfl, hi⟩ := wout_int vt₁ wo₁
  obtain ⟨x, rfl, hx⟩ := wout_int vt₂ wo₂
  have hlen : len < 2 ^ 63 := (hl.fits p len hR).2
  have hIR : stepIR (.run (lowerT (.letOp .store [.var n, a₁, a₂] tcap e)) ρ k, σ) =
      (Store.store p i x σ).map fun σ' => (.run (lowerT e) (.const (.cap p) :: ρ) k, σ') := by
    simp [lowerT, lowerL, lowerA, stepIR, Opd.evalL, Opd.eval, hρ, ev₁, ev₂, opIR, Val.asConst, List.mapM_cons, opStep]
    cases Store.store p i x σ <;> rfl
  by_cases hbd : 0 ≤ i ∧ i < len
  · have hs : Store.store p i x σ = some ⟨σ.H.insert (p + i) x, σ.R⟩ := by simp [Store.store, hR, hbd]
    refine .inr ⟨_, by rw [hIR, hs]; rfl, ?_⟩
    rcases hi with hi | ⟨ri, hi⟩
    · exact ⟨(.ovf, m), by simp [stepW, hb, hn, hi], .inr rfl⟩
    rcases hx with hx | ⟨rx, hx⟩
    · exact ⟨(.ovf, m), by simp [stepW, hb, hn, hi, hx], .inr rfl⟩
    obtain ⟨hl', hR'⟩ := layout_store hl hR rx hs
    have hm' := memrel_store hl hm hR hs
    refine ⟨(.run (lower2T (tcap :: Γl) e (lower2A Γl a₂ (lower2A Γl a₁ t).2).2).1 (lay p :: BitVec.ofNat 64 len :: ρw) kw,
      Function.update m (cellAddr (lay p) (BitVec.ofInt 64 i)) (BitVec.ofInt 64 x)), ?_, .inl ?_⟩
    · simp only [stepW, hb, hn, hi, hx]; rw [if_pos ((bounds_iff ri hlen).2 hbd)]
    · rw [ofInt_nonneg hbd.1]
      refine .run (Γl := tcap :: Γl) (τ := τ) ⟨e, tcap :: Γt, true :: Δ.set n false, _, rfl, rfl,
        hk.mono (Keeps.trans (lower2A_keeps Γl a₁ t) (lower2A_keeps Γl a₂ _)).1, he', by simpa using hw.2,
        by simpa using hag.cons tcap, hf.2, hok.2, ?_⟩ (hfr.transport hR') hl' hm'
      exact .cons (.cap (by rw [hR']; exact hR)) (he.transport hR')
  · refine .inl ⟨by rw [hIR]; simp [Store.store, hR, hbd], ?_⟩
    rcases hi with hi | ⟨ri, hi⟩
    · exact ⟨(.ovf, m), by simp [stepW, hb, hn, hi], .inr rfl⟩
    rcases hx with hx | ⟨rx, hx⟩
    · exact ⟨(.ovf, m), by simp [stepW, hb, hn, hi, hx], .inr rfl⟩
    · refine ⟨(.fault, m), ?_, .inl rfl⟩
      simp only [stepW, hb, hn, hi, hx]; rw [if_neg (fun h => hbd ((bounds_iff ri hlen).1 h))]

theorem Agree.append (Γ Γ' : Ctx S₂) : Agree Γ.length Γ (Γ ++ Γ') := fun i hi => (List.getElem?_append_left hi).symm

theorem toNat_label {l : Nat} (h : l < 2 ^ 64) : (BitVec.ofNat 64 l).toNat = l := by
  simp only [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

theorem step_app {T lay τfin σ m} (hT : T.length < 2 ^ 64) {Γl Γt : Ctx S₂} {t : Table} {a₁ a₂ : Atom₂}
    {τ₁ τ : Ty₂} {ρ ρw k kw}
    (h₁ : HasTypeA₂ Γt a₁ (.arr τ₁ τ)) (h₂ : HasTypeA₂ Γt a₂ τ₁)
    (hw : Tm.wfB Γl.length (.app a₁ a₂) = true) (hag : Agree Γl.length Γl Γt)
    (he : EnvRel T lay σ Γl ρ ρw) (hf : Tm.fnOk (.app a₁ a₂) = true) (hok : Tm.ok2 (.app a₁ a₂) = true)
    (hk : KeepsFrom t.length (lower2T Γl (.app a₁ a₂) t).2 T) (hfr : FRel2 T lay σ τ k kw τfin)
    (hl : Layout σ lay) (hm : MemRel lay σ m) :
    ∃ I', stepIR (.run (lowerT (.app a₁ a₂)) ρ k, σ) = some I' ∧
      WStepOK T lay τfin I' (.run (lower2T Γl (.app a₁ a₂) t).1 ρw kw, m) := by
  simp only [Tm.wfB, Bool.and_eq_true] at hw; simp only [Tm.fnOk, Bool.and_eq_true] at hf
  simp only [Tm.ok2, Bool.and_eq_true] at hok
  simp only [lower2T] at hk ⊢
  obtain ⟨f, ef, vtf, wof⟩ := opd_sim hT t h₁ hw.1 hag he hf.1 hok.1
    (KeepsFrom.of_keeps (lower2A_keeps Γl a₂ _) hk)
  obtain ⟨v, ev, vtv, wov⟩ := opd_sim hT _ h₂ hw.2 hag he hf.2 hok.2 (hk.mono (lower2A_keeps Γl a₁ t).1)
  rcases wof with wof | ⟨wsf, wof, rf⟩
  · -- the function operand overflowed: the IR still calls (its value is code), the word machine stops at ovf
    cases vtf with
    | code =>
      rename_i b c
      cases b
      · exact ⟨(.run c [v] k, σ), by simp [lowerT, stepIR, ef, ev], (.ovf, m), by simp [stepW, wof], .inr rfl⟩
      · exact ⟨(.run c [v, .code true c] k, σ), by simp [lowerT, stepIR, ef, ev], (.ovf, m), by simp [stepW, wof],
          .inr rfl⟩
  cases rf with
  | lam hlt hcode hbody =>
    rename_i eb l
    obtain ⟨t', ht', hTl, hkeep⟩ := hcode
    obtain ⟨Γ, Δ, hty, hwb, hfb, hob⟩ := hbody
    refine ⟨(.run (lowerT eb) [v] k, σ), by simp [lowerT, stepIR, ef, ev], ?_⟩
    rcases wov with wov | ⟨wsv, wov, rv⟩
    · exact ⟨(.ovf, m), by simp [stepW, wof, wov], .inr rfl⟩
    · refine ⟨(.run (lower2T [τ₁] eb t').1 wsv kw, m), by simp [stepW, wof, wov, toNat_label hlt, hTl], .inl ?_⟩
      refine .run (Γl := [τ₁]) (τ := τ) ⟨eb, [τ₁] ++ Γ, Δ, t', rfl, rfl, by rw [ht']; exact hkeep, hty, hwb,
        Agree.append _ _, hfb, hob, ?_⟩ hfr hl hm
      simpa using EnvRel.cons rv .nil
  | fix hlt hcode hbody =>
    rename_i eb l
    obtain ⟨t', ht', hTl, hkeep⟩ := hcode
    obtain ⟨Γ, Δ, hty, hwb, hfb, hob⟩ := hbody
    refine ⟨(.run (lowerT eb) [v, .code true (lowerT eb)] k, σ), by simp [lowerT, stepIR, ef, ev], ?_⟩
    rcases wov with wov | ⟨wsv, wov, rv⟩
    · exact ⟨(.ovf, m), by simp [stepW, wof, wov], .inr rfl⟩
    · refine ⟨(.run (lower2T [τ₁, .arr τ₁ τ] eb t').1 (wsv ++ [BitVec.ofNat 64 l]) kw, m),
        by simp [stepW, wof, wov, toNat_label hlt, hTl], .inl ?_⟩
      refine .run (Γl := [τ₁, .arr τ₁ τ]) (τ := τ) ⟨eb, [τ₁, .arr τ₁ τ] ++ Γ, Δ, t', rfl, rfl, by rw [ht']; exact hkeep,
        hty, hwb, Agree.append _ _, hfb, hob, ?_⟩ hfr hl hm
      simpa using EnvRel.cons rv (EnvRel.cons (.fix hlt ⟨t', ht', hTl, hkeep⟩ ⟨Γ, Δ, hty, hwb, hfb, hob⟩) .nil)

theorem step_ite {T lay τfin σ m} (hT : T.length < 2 ^ 64) {Γl Γt : Ctx S₂} {Δ : List Bool} {t : Table} {a : Atom₂}
    {e₁ e₂ : Tm₂} {τ : Ty₂} {ρ ρw k kw}
    (h : HasTypeA₂ Γt a tbool) (h₁ : HasType₂ Γt Δ e₁ τ) (h₂ : HasType₂ Γt Δ e₂ τ)
    (hw : Tm.wfB Γl.length (.ite a e₁ e₂) = true) (hag : Agree Γl.length Γl Γt)
    (he : EnvRel T lay σ Γl ρ ρw) (hf : Tm.fnOk (.ite a e₁ e₂) = true) (hok : Tm.ok2 (.ite a e₁ e₂) = true)
    (hk : KeepsFrom t.length (lower2T Γl (.ite a e₁ e₂) t).2 T) (hfr : FRel2 T lay σ τ k kw τfin)
    (hl : Layout σ lay) (hm : MemRel lay σ m) :
    ∃ I', stepIR (.run (lowerT (.ite a e₁ e₂)) ρ k, σ) = some I' ∧
      WStepOK T lay τfin I' (.run (lower2T Γl (.ite a e₁ e₂) t).1 ρw kw, m) := by
  simp only [Tm.wfB, Bool.and_eq_true] at hw; simp only [Tm.fnOk, Bool.and_eq_true] at hf
  simp only [Tm.ok2, Bool.and_eq_true] at hok
  simp only [lower2T] at hk ⊢
  have kA := KeepsFrom.of_keeps (Keeps.trans (lower2T_keeps Γl e₁ _) (lower2T_keeps Γl e₂ _)) hk
  have k₁ := (KeepsFrom.of_keeps (lower2T_keeps Γl e₂ _) hk).mono (lower2A_keeps Γl a t).1
  have k₂ := hk.mono (Keeps.trans (lower2A_keeps Γl a t) (lower2T_keeps Γl e₁ _)).1
  obtain ⟨v, ev, vt, wo⟩ := opd_sim hT t h hw.1.1 hag he hf.1.1 hok.1.1 kA
  obtain ⟨b, rfl, hb⟩ := wout_bool vt wo
  cases b
  · refine ⟨(.run (lowerT e₂) ρ k, σ), by simp [lowerT, stepIR, ev], ?_⟩
    rcases hb with hb | hb
    · exact ⟨(.ovf, m), by simp [stepW, hb], .inr rfl⟩
    · exact ⟨_, by simp [stepW, hb, boolW], .inl (.run (Γl := Γl) ⟨e₂, Γt, Δ, _, rfl, rfl, k₂, h₂, hw.2, hag, hf.2, hok.2, he⟩
        hfr hl hm)⟩
  · refine ⟨(.run (lowerT e₁) ρ k, σ), by simp [lowerT, stepIR, ev], ?_⟩
    rcases hb with hb | hb
    · exact ⟨(.ovf, m), by simp [stepW, hb], .inr rfl⟩
    · exact ⟨_, by simp [stepW, hb, boolW], .inl (.run (Γl := Γl) ⟨e₁, Γt, Δ, _, rfl, rfl, k₁, h₁, hw.1.2, hag, hf.1.2,
        hok.1.2, he⟩ hfr hl hm)⟩

theorem step_case {T lay τfin σ m} (hT : T.length < 2 ^ 64) {Γl Γt : Ctx S₂} {Δ : List Bool} {t : Table} {a : Atom₂}
    {e₁ e₂ : Tm₂} {τ₁ τ₂ τ : Ty₂} {ρ ρw k kw}
    (h : HasTypeA₂ Γt a (.sum τ₁ τ₂)) (h₁ : HasType₂ (τ₁ :: Γt) (false :: Δ) e₁ τ)
    (h₂ : HasType₂ (τ₂ :: Γt) (false :: Δ) e₂ τ)
    (hw : Tm.wfB Γl.length (.case a e₁ e₂) = true) (hag : Agree Γl.length Γl Γt)
    (he : EnvRel T lay σ Γl ρ ρw) (hf : Tm.fnOk (.case a e₁ e₂) = true) (hok : Tm.ok2 (.case a e₁ e₂) = true)
    (hk : KeepsFrom t.length (lower2T Γl (.case a e₁ e₂) t).2 T) (hfr : FRel2 T lay σ τ k kw τfin)
    (hl : Layout σ lay) (hm : MemRel lay σ m) :
    ∃ I', stepIR (.run (lowerT (.case a e₁ e₂)) ρ k, σ) = some I' ∧
      WStepOK T lay τfin I' (.run (lower2T Γl (.case a e₁ e₂) t).1 ρw kw, m) := by
  simp only [Tm.wfB, Bool.and_eq_true] at hw; simp only [Tm.fnOk, Bool.and_eq_true] at hf
  simp only [Tm.ok2, Bool.and_eq_true] at hok
  have hinf : inferA Γl a = some (.sum τ₁ τ₂) := by rw [inferA_agree a hw.1.1 hag]; exact inferA_sound h
  simp only [lower2T, hinf] at hk ⊢
  have kA := KeepsFrom.of_keeps (Keeps.trans (lower2T_keeps (τ₁ :: Γl) e₁ _) (lower2T_keeps (τ₂ :: Γl) e₂ _)) hk
  have k₁ := (KeepsFrom.of_keeps (lower2T_keeps (τ₂ :: Γl) e₂ _) hk).mono (lower2A_keeps Γl a t).1
  have k₂ := hk.mono (Keeps.trans (lower2A_keeps Γl a t) (lower2T_keeps (τ₁ :: Γl) e₁ _)).1
  obtain ⟨v, ev, vt, wo⟩ := opd_sim hT t h hw.1.1 hag he hf.1.1 hok.1.1 kA
  cases vt with
  | inl vt' =>
    rename_i x
    refine ⟨(.run (lowerT e₁) (x :: ρ) k, σ), by simp [lowerT, stepIR, ev], ?_⟩
    rcases wo with wo | ⟨ws, wo, r⟩
    · exact ⟨(.ovf, m), by simp [stepW, wo], .inr rfl⟩
    · cases r with
      | inl r' =>
        rename_i w
        have htake : List.take (size τ₁) (w ++ List.replicate (max (size τ₁) (size τ₂) - size τ₁) 0) = w := by
          rw [← r'.length, List.take_left]
        refine ⟨(.run (lower2T (τ₁ :: Γl) e₁ (lower2A Γl a t).2).1 (w ++ ρw) kw, m), by simp [stepW, wo]; exact htake,
          .inl (.run (Γl := τ₁ :: Γl) ⟨e₁, τ₁ :: Γt, false :: Δ, _, rfl, rfl, k₁, h₁, by simpa using hw.1.2,
            by simpa using hag.cons τ₁, hf.1.2, hok.1.2, .cons r' he⟩ hfr hl hm)⟩
  | inr vt' =>
    rename_i x
    refine ⟨(.run (lowerT e₂) (x :: ρ) k, σ), by simp [lowerT, stepIR, ev], ?_⟩
    rcases wo with wo | ⟨ws, wo, r⟩
    · exact ⟨(.ovf, m), by simp [stepW, wo], .inr rfl⟩
    · cases r with
      | inr r' =>
        rename_i w
        have htake : List.take (size τ₂) (w ++ List.replicate (max (size τ₁) (size τ₂) - size τ₂) 0) = w := by
          rw [← r'.length, List.take_left]
        refine ⟨(.run (lower2T (τ₂ :: Γl) e₂ (lower2T (τ₁ :: Γl) e₁ (lower2A Γl a t).2).2).1 (w ++ ρw) kw, m),
          by simp [stepW, wo]; exact htake, .inl (.run (Γl := τ₂ :: Γl) ⟨e₂, τ₂ :: Γt, false :: Δ, _, rfl, rfl, k₂, h₂,
            by simpa using hw.2, by simpa using hag.cons τ₂, hf.2, hok.2, .cons r' he⟩ hfr hl hm)⟩

end VIRC
