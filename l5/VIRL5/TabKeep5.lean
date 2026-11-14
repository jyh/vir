/-
  O95 layer L5, Lean arm (STATUS 323, LV8-MAP Addendum 6, fork (T)): the TABLE INVARIANT, and the generic frame that carries it
  through every DEFLATE mode whose stores all go to CONSTANT cells. `Tab f` says the bit table is S1's below TABLE's counter (all
  2,048 bits once TABLE has ended). A store `store(w, c, v)` with a constant c outside [20, 2068) cannot touch the table. `tkT`
  checks that syntactically for every store in a term (inside function bodies too, as `opFree` does), ⟶₂ keeps it, and on a Sole
  store such a run leaves every table cell as it was (`TKeep`). The dispatch only loads, so a DEFLATE step in a mode whose body
  passes `tkT` keeps the table (`stepS_tkeep`), and `Tab` survives it (`tab_of_tkeep`).
-/
import VIRL5.SolePres5
import VIRDeflate.Correct

namespace VIRL5
open VIRL1 VIRL2 VIRDeflate.Step

/-! ## The invariant -/

/-- **(T):** every table cell below TABLE's counter holds S1's bit; outside TABLE, all 2,048. -/
def Tab (f : Int → Int) : Prop := BitsUpTo f (if f cMODE = mTABLE then 8 * f cTB + f cTI else 2048)

/-- 2,048 bits is every bit: a byte is < 256 and a bit index ≤ 7. -/
theorem bits_all {f : Int → Int} (h : BitsUpTo f 2048) (c : Int) : BitsUpTo f c :=
  fun v i hv hi _ => h v i hv hi (by omega)

theorem tab_init (b : Array Nat) (om : Nat) (lit : Bool) : Tab (initCell b om lit) := by
  have e0 : initCell b om lit cMODE = mTABLE :=
    initCell_zero b om lit _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have e18 : initCell b om lit cTB = 0 :=
    initCell_zero b om lit _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have e19 : initCell b om lit cTI = 0 :=
    initCell_zero b om lit _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  unfold Tab
  rw [if_pos e0, e18, e19]
  intro v i _ _ h; omega

/-- Tab reads only cells of the region, so two worlds of one store agree on it. -/
theorem tab_congr {σ : Store} {p : Int} {L : Nat} {f g : Int → Int} (hL : 2068 ≤ L) (hf : World σ p L f)
    (hg : World σ p L g) (h : Tab f) : Tab g := by
  have ag : ∀ c : Int, 0 ≤ c → c < 2068 → g c = f c := fun c h0 h1 => hg.agree hf h0 (by omega)
  unfold Tab at h ⊢
  rw [ag cMODE (by decide) (by decide), ag cTB (by decide) (by decide), ag cTI (by decide) (by decide)]
  intro v i hv hi hlt
  rw [ag _ (by unfold BT; omega) (by unfold BT; omega)]
  exact h v i hv hi hlt

/-! ## The frame: a run that never stores into the table -/

/-- The table cells of the region at p are as they were. -/
def TKeep (σ σ' : Store) (p : Int) : Prop := ∀ c : Int, 20 ≤ c → c < 2068 → σ'.H.lookup (p + c) = σ.H.lookup (p + c)

theorem TKeep.refl (σ : Store) (p : Int) : TKeep σ σ p := fun _ _ _ => rfl

theorem TKeep.trans {σ₁ σ₂ σ₃ : Store} {p : Int} (h₁ : TKeep σ₁ σ₂ p) (h₂ : TKeep σ₂ σ₃ p) : TKeep σ₁ σ₃ p :=
  fun c a b => (h₂ c a b).trans (h₁ c a b)

/-- A constant index outside the table. -/
def outTab (i : Int) : Bool := decide (i < 20) || decide (2068 ≤ i)

/-- The index of a three-argument op whose index is a literal integer. -/
def idx? : List Atom₂ → Option Int
  | [_, .const (.int i), _] => some i
  | _ => none

/-- Loads, and stores at a literal index outside the table. -/
def tkOp (o : Op) (as : List Atom₂) : Bool :=
  match o with
  | .load => true
  | .store => match idx? as with
    | some i => outTab i
    | none => false
  | _ => false

theorem idx?_subst {as : List Atom₂} {i : Int} (k : Nat) (v : Atom₂) (h : idx? as = some i) :
    idx? (Atom.substL k v as) = some i := by
  unfold idx? at h
  split at h
  · simp only [Option.some.injEq] at h
    subst h
    simp [idx?, Atom.substL, Atom.subst]
  · simp at h

theorem tkOp_subst {o : Op} {as : List Atom₂} (k : Nat) (v : Atom₂) (h : tkOp o as = true) :
    tkOp o (Atom.substL k v as) = true := by
  cases o
  · simp [tkOp] at h
  · simp [tkOp]
  · simp only [tkOp] at h ⊢
    rcases hi : idx? as with _ | i
    · rw [hi] at h; simp at h
    · rw [hi] at h; rw [idx?_subst k v hi]; exact h
  · simp [tkOp] at h

theorem okOp_of_tk {o : Op} {as : List Atom₂} (h : tkOp o as = true) : okOp o = true := by
  cases o <;> simp_all [tkOp, okOp]

mutual
def tkA : Atom₂ → Bool
  | .var _ => true
  | .const _ => true
  | .prim _ as => tkL as
  | .lam _ e => tkT e
  | .fix _ _ e => tkT e
  | .pair a₁ a₂ => tkA a₁ && tkA a₂
  | .fst a => tkA a
  | .snd a => tkA a
  | .inl _ a => tkA a
  | .inr _ a => tkA a
def tkL : List Atom₂ → Bool
  | [] => true
  | a :: as => tkA a && tkL as
def tkT : Tm₂ → Bool
  | .ret a => tkA a
  | .letE _ e₁ e₂ => tkT e₁ && tkT e₂
  | .letOp o as _ e => tkOp o as && tkL as && tkT e
  | .app a₁ a₂ => tkA a₁ && tkA a₂
  | .ite a e₁ e₂ => tkA a && tkT e₁ && tkT e₂
  | .case a e₁ e₂ => tkA a && tkT e₁ && tkT e₂
end

mutual
theorem tkA_subst : ∀ (a : Atom₂) (k : Nat) (v : Atom₂), tkA v = true → tkA a = true → tkA (a.subst k v) = true
  | .var n, k, v, hv, _ => by
    simp only [Atom.subst]
    split_ifs <;> simp [tkA, hv]
  | .const c, _, _, _, _ => by simp [Atom.subst, tkA]
  | .prim p as, k, v, hv, ha => by
    simp only [Atom.subst, tkA] at ha ⊢; exact tkL_subst as k v hv ha
  | .lam τ e, k, v, hv, ha => by
    simp only [Atom.subst, tkA] at ha ⊢; exact tkT_subst e (k + 1) v hv ha
  | .fix τ₁ τ₂ e, k, v, hv, ha => by
    simp only [Atom.subst, tkA] at ha ⊢; exact tkT_subst e (k + 2) v hv ha
  | .pair a₁ a₂, k, v, hv, ha => by
    simp only [Atom.subst, tkA, Bool.and_eq_true] at ha ⊢
    exact ⟨tkA_subst a₁ k v hv ha.1, tkA_subst a₂ k v hv ha.2⟩
  | .fst a, k, v, hv, ha => by simp only [Atom.subst, tkA] at ha ⊢; exact tkA_subst a k v hv ha
  | .snd a, k, v, hv, ha => by simp only [Atom.subst, tkA] at ha ⊢; exact tkA_subst a k v hv ha
  | .inl τ a, k, v, hv, ha => by simp only [Atom.subst, tkA] at ha ⊢; exact tkA_subst a k v hv ha
  | .inr τ a, k, v, hv, ha => by simp only [Atom.subst, tkA] at ha ⊢; exact tkA_subst a k v hv ha
theorem tkL_subst : ∀ (as : List Atom₂) (k : Nat) (v : Atom₂), tkA v = true → tkL as = true →
    tkL (Atom.substL k v as) = true
  | [], _, _, _, _ => by simp [Atom.substL, tkL]
  | a :: as, k, v, hv, ha => by
    simp only [Atom.substL, tkL, Bool.and_eq_true] at ha ⊢
    exact ⟨tkA_subst a k v hv ha.1, tkL_subst as k v hv ha.2⟩
theorem tkT_subst : ∀ (e : Tm₂) (k : Nat) (v : Atom₂), tkA v = true → tkT e = true → tkT (e.subst k v) = true
  | .ret a, k, v, hv, he => by simp only [Tm.subst, tkT] at he ⊢; exact tkA_subst a k v hv he
  | .letE τ e₁ e₂, k, v, hv, he => by
    simp only [Tm.subst, tkT, Bool.and_eq_true] at he ⊢
    exact ⟨tkT_subst e₁ k v hv he.1, tkT_subst e₂ (k + 1) v hv he.2⟩
  | .letOp o as τ e, k, v, hv, he => by
    simp only [Tm.subst, tkT, Bool.and_eq_true] at he ⊢
    exact ⟨⟨tkOp_subst k v he.1.1, tkL_subst as k v hv he.1.2⟩, tkT_subst e (k + 1) v hv he.2⟩
  | .app a₁ a₂, k, v, hv, he => by
    simp only [Tm.subst, tkT, Bool.and_eq_true] at he ⊢
    exact ⟨tkA_subst a₁ k v hv he.1, tkA_subst a₂ k v hv he.2⟩
  | .ite a e₁ e₂, k, v, hv, he => by
    simp only [Tm.subst, tkT, Bool.and_eq_true] at he ⊢
    exact ⟨⟨tkA_subst a k v hv he.1.1, tkT_subst e₁ k v hv he.1.2⟩, tkT_subst e₂ k v hv he.2⟩
  | .case a e₁ e₂, k, v, hv, he => by
    simp only [Tm.subst, tkT, Bool.and_eq_true] at he ⊢
    exact ⟨⟨tkA_subst a k v hv he.1.1, tkT_subst e₁ (k + 1) v hv he.1.2⟩, tkT_subst e₂ (k + 1) v hv he.2⟩
end

mutual
theorem tkA_eval : ∀ (a v : Atom₂), Atom.eval a = some v → tkA a = true → tkA v = true
  | .var _, v, h, _ => by simp [Atom.eval] at h
  | .const c, v, h, _ => by simp [Atom.eval] at h; subst h; simp [tkA]
  | .prim p as, v, h, _ => by
    simp only [Atom.eval, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨_, _, _, _, c, _, rfl⟩ := h
    simp [tkA]
  | .lam τ e, v, h, ha => by simp [Atom.eval] at h; subst h; exact ha
  | .fix τ₁ τ₂ e, v, h, ha => by simp [Atom.eval] at h; subst h; exact ha
  | .pair a₁ a₂, v, h, ha => by
    simp only [Atom.eval, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨v₁, h₁, v₂, h₂, rfl⟩ := h
    simp only [tkA, Bool.and_eq_true] at ha ⊢
    exact ⟨tkA_eval a₁ v₁ h₁ ha.1, tkA_eval a₂ v₂ h₂ ha.2⟩
  | .fst a, v, h, ha => by
    simp only [Atom.eval, Option.bind_eq_some_iff] at h
    obtain ⟨w, hw, hv⟩ := h
    have := tkA_eval a w hw ha
    cases w <;> simp at hv
    subst hv
    simp only [tkA, Bool.and_eq_true] at this
    exact this.1
  | .snd a, v, h, ha => by
    simp only [Atom.eval, Option.bind_eq_some_iff] at h
    obtain ⟨w, hw, hv⟩ := h
    have := tkA_eval a w hw ha
    cases w <;> simp at hv
    subst hv
    simp only [tkA, Bool.and_eq_true] at this
    exact this.2
  | .inl τ a, v, h, ha => by
    simp only [Atom.eval, Option.map_eq_some_iff] at h
    obtain ⟨w, hw, rfl⟩ := h
    simp only [tkA] at ha ⊢
    exact tkA_eval a w hw ha
  | .inr τ a, v, h, ha => by
    simp only [Atom.eval, Option.map_eq_some_iff] at h
    obtain ⟨w, hw, rfl⟩ := h
    simp only [tkA] at ha ⊢
    exact tkA_eval a w hw ha
end

/-- A pure ⟶ step keeps `tkT`. -/
theorem pure_tk {e e' : Tm₂} (h : Step e e') : tkT e = true → tkT e' = true := by
  induction h with
  | @letRet τ a v e₂ hv =>
    intro hf
    simp only [tkT, Bool.and_eq_true] at hf
    exact tkT_subst e₂ 0 v (tkA_eval a v hv hf.1) hf.2
  | @letStep τ e₁ e₁' e₂ _ ih =>
    intro hf
    simp only [tkT, Bool.and_eq_true] at hf ⊢
    exact ⟨ih hf.1, hf.2⟩
  | @appLam a₁ a₂ τ e v h₁ h₂ =>
    intro hf
    simp only [tkT, Bool.and_eq_true] at hf
    have hl := tkA_eval a₁ _ h₁ hf.1
    simp only [tkA] at hl
    exact tkT_subst e 0 v (tkA_eval a₂ v h₂ hf.2) hl
  | @appFix a₁ a₂ τ₁ τ₂ e v h₁ h₂ =>
    intro hf
    simp only [tkT, Bool.and_eq_true] at hf
    have hl := tkA_eval a₁ _ h₁ hf.1
    have hl' := hl
    simp only [tkA] at hl
    exact tkT_subst _ 0 _ hl' (tkT_subst e 0 v (tkA_eval a₂ v h₂ hf.2) hl)
  | iteT =>
    intro hf; simp only [tkT, Bool.and_eq_true] at hf; exact hf.1.2
  | iteF =>
    intro hf; simp only [tkT, Bool.and_eq_true] at hf; exact hf.2
  | @caseL a e₁ e₂ τ v hv =>
    intro hf
    simp only [tkT, Bool.and_eq_true] at hf
    have hi := tkA_eval a _ hv hf.1.1
    simp only [tkA] at hi
    exact tkT_subst e₁ 0 v hi hf.1.2
  | @caseR a e₁ e₂ τ v hv =>
    intro hf
    simp only [tkT, Bool.and_eq_true] at hf
    have hi := tkA_eval a _ hv hf.1.1
    simp only [tkA] at hi
    exact tkT_subst e₂ 0 v hi hf.2

/-- Evaluating the arguments keeps a literal index. -/
theorem idx?_eval {as vs : List Atom₂} {i : Int} (h : idx? as = some i) (he : Atom.evalL as = some vs) :
    idx? vs = some i := by
  unfold idx? at h
  split at h
  · rename_i a j c
    simp only [Option.some.injEq] at h
    subst h
    cases ha : Atom.eval a <;> cases hc : Atom.eval c <;> simp [Atom.evalL, Atom.eval, ha, hc] at he
    subst he
    simp [idx?]
  · simp at h

/-- A load or a store returns a constant. -/
theorem opStep_val {o : Op} {vs : List Atom₂} {σ σ' : Store} {v : Atom₂} (ho : okOp o = true)
    (h : opStep o vs σ = some (v, σ')) : tkA v = true := by
  cases o <;> simp only [okOp, Bool.false_eq_true] at ho
  · unfold opStep at h
    split at h
    all_goals first | (simp_all; done) | skip
    simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨_, _, rfl, _⟩ := h
    simp [tkA]
  · unfold opStep at h
    split at h
    all_goals first | (simp_all; done) | skip
    simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨_, _, rfl, _⟩ := h
    simp [tkA]

/-- A load or a table-free store keeps the table cells on a Sole store, and returns a constant. -/
theorem opStep_tk {o : Op} {as vs : List Atom₂} {σ σ' : Store} {v : Atom₂} {p : Int} {L : Nat}
    (ho : tkOp o as = true) (he : Atom.evalL as = some vs) (h : opStep o vs σ = some (v, σ')) (hs : Sole σ p L) :
    TKeep σ σ' p := by
  cases o <;> simp only [tkOp, Bool.false_eq_true] at ho
  · -- load
    unfold opStep at h
    split at h
    all_goals first | (simp_all; done) | skip
    simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨_, _, _, rfl⟩ := h
    exact TKeep.refl _ p
  · -- store
    rcases hi : idx? as with _ | i
    · rw [hi] at ho; simp at ho
    rw [hi] at ho
    have hv := idx?_eval hi he
    unfold opStep at h
    split at h
    all_goals first | (simp_all; done) | skip
    rename_i q j w _
    simp only [idx?, Option.some.injEq] at hv
    subst hv
    simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨σ'', hst, _, rfl⟩ := h
    unfold Store.store at hst
    rw [hs.1] at hst
    by_cases hq : q = p
    · subst hq
      rw [Finmap.lookup_singleton_eq] at hst
      simp only at hst
      split_ifs at hst with hb
      simp only [Option.some.injEq] at hst
      subst hst
      intro c c0 c1
      have hne : q + c ≠ q + j := by
        simp only [outTab, Bool.or_eq_true, decide_eq_true_eq] at ho; omega
      exact Finmap.lookup_insert_of_ne _ hne
    · have : (Finmap.singleton p L : Finmap (fun _ : Int => Nat)).lookup q = none := by
        rw [Finmap.lookup_eq_none, Finmap.mem_singleton]; exact hq
      rw [this] at hst
      simp at hst

/-- A ⟶₂ step from a table-free term keeps the term table-free, the store Sole, and the table cells. -/
theorem step₂_tk {p : Int} {L : Nat} {c c' : Config} (h : Step₂ c c') :
    tkT c.1 = true → Sole c.2 p L → tkT c'.1 = true ∧ Sole c'.2 p L ∧ TKeep c.2 c'.2 p := by
  induction h with
  | pure hs => intro hf hσ; exact ⟨pure_tk hs hf, hσ, TKeep.refl _ p⟩
  | @letStep τ e₁ e₁' e₂ σ σ' _ ih =>
    intro hf hσ
    simp only [tkT, Bool.and_eq_true] at hf ⊢
    obtain ⟨h1, h2, h3⟩ := ih hf.1 hσ
    exact ⟨⟨h1, hf.2⟩, h2, h3⟩
  | @op o as τ e vs v σ σ' he hop =>
    intro hf hσ
    simp only [tkT, Bool.and_eq_true] at hf
    obtain ⟨hs', hv⟩ := opStep_sole (okOp_of_tk hf.1.1) hop hσ
    exact ⟨tkT_subst e 0 v (opStep_val (okOp_of_tk hf.1.1) hop) hf.2, hs', opStep_tk hf.1.1 he hop hσ⟩

/-- `run₂` from a table-free term keeps the store Sole and the table cells. -/
theorem run₂_tk {p : Int} {L : Nat} : ∀ (n : Nat) (e : Tm₂) (σ : Store), tkT e = true → Sole σ p L →
    Sole (run₂ n (e, σ)).2 p L ∧ TKeep σ (run₂ n (e, σ)).2 p
  | 0, _, σ, _, hs => ⟨hs, TKeep.refl σ p⟩
  | n + 1, e, σ, hf, hs => by
    simp only [run₂]
    rcases hfn : stepFn₂ e σ with _ | ⟨e', σ'⟩
    · exact ⟨hs, TKeep.refl σ p⟩
    · obtain ⟨hf', hs', hk⟩ := step₂_tk (stepFn₂_sound hfn) hf hs
      obtain ⟨h1, h2⟩ := run₂_tk n e' σ' hf' hs'
      exact ⟨h1, hk.trans h2⟩

/-- A counted path is a prefix of `run₂`. -/
theorem run₂_stepsN {k : Nat} {c d : Config} (h : StepsN k c d) (m : Nat) : run₂ (k + m) c = run₂ m d := by
  induction h with
  | refl => simp
  | @step n c c' c'' s _ ih =>
    rw [show n + 1 + m = (n + m) + 1 by omega, run₂_succ_of (stepFn₂_complete s)]
    exact ih

/-- **The frame:** a DEFLATE step in a mode whose body is table-free keeps the table cells. -/
theorem stepS_tkeep {σ σ' : Store} {p : Int} {L : Nat} {f : Int → Int} {k : Int} {t : NT}
    (hw : World σ p L f) (hs : Sole σ p L) (hL : 0 < L) (hm : f cMODE = k) (hk : modes.lookup k = some t)
    (htk : tkT (t.c ["w"]) = true) (h : stepS p σ = some σ') : TKeep σ σ' p := by
  obtain ⟨k₁, hk₁, h₁⟩ := step_dispatchN hw hL k hm
  rw [hk] at h₁
  have e := run₂_stepsN h₁ (KSTEP - k₁)
  rw [show k₁ + (KSTEP - k₁) = KSTEP by unfold KSTEP; omega] at e
  have hrun := (run₂_tk (KSTEP - k₁) (closeAt p (t.c ["w"])) σ (tkT_subst _ 0 _ (by simp [tkA]) htk) hs).2
  unfold stepS at h
  rw [e] at h
  rcases hr : run₂ (KSTEP - k₁) (closeAt p (t.c ["w"]), σ) with ⟨e', σ''⟩
  rw [hr] at h hrun
  cases e' with
  | ret a =>
    cases a with
    | const c =>
      cases c with
      | cap q =>
        simp only at h
        split_ifs at h
        simp only [Option.some.injEq] at h
        subst h
        exact hrun
      | _ => simp at h
    | _ => simp at h
  | _ => simp at h

/-- **Tab survives a step that keeps the table cells**, from a non-TABLE mode. -/
theorem tab_of_tkeep {σ σ' : Store} {p : Int} {L : Nat} {f f' : Int → Int} (hL : 2068 ≤ L)
    (hw : World σ p L f) (hw' : World σ' p L f') (hk : TKeep σ σ' p) (hnt : f cMODE ≠ mTABLE) (h : Tab f) : Tab f' := by
  unfold Tab at h
  rw [if_neg hnt] at h
  unfold Tab
  apply bits_all
  intro v i hv hi hlt
  have c1 := hw.cell (BT + (8 * v + i)) (by unfold BT; omega) (by unfold BT; omega)
  have c2 := hw'.cell (BT + (8 * v + i)) (by unfold BT; omega) (by unfold BT; omega)
  rw [hk _ (by unfold BT; omega) (by unfold BT; omega), c1] at c2
  rw [← Option.some.inj c2]
  exact h v i hv hi hlt

/-! ## The modes whose every store is to a constant cell outside the table (by evaluation) -/

theorem tk_hdr : tkT (hdrN.c ["w"]) = true := by decide
theorem tk_read : tkT (readN.c ["w"]) = true := by decide
theorem tk_hdrb : tkT (hdrbN.c ["w"]) = true := by decide
theorem tk_hdrd : tkT (hdrdN.c ["w"]) = true := by decide
theorem tk_shdr : tkT (shdrN.c ["w"]) = true := by decide
theorem tk_dhdr : tkT (dhdrN.c ["w"]) = true := by decide
theorem tk_slen : tkT (slenN.c ["w"]) = true := by decide
theorem tk_snlen : tkT (snlenN.c ["w"]) = true := by decide
theorem tk_dstd : tkT (dstdN.c ["w"]) = true := by decide
theorem tk_dstx : tkT (dstxN.c ["w"]) = true := by decide
theorem tk_dh2 : tkT (dh2N.c ["w"]) = true := by decide
theorem tk_dh3 : tkT (dh3N.c ["w"]) = true := by decide
theorem tk_dh4 : tkT (dh4N.c ["w"]) = true := by decide
theorem tk_lrep : tkT (lrepN.c ["w"]) = true := by decide

/-- A control-only control: the TABLE body stores at a computed index, and `tkT` refuses it. -/
theorem tk_table_refused : tkT (tableN.c ["w"]) = false := by decide

end VIRL5
