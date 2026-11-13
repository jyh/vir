/-
OBJECT-DEFLATE under X1 (a): the top-level step (DECLARATIONS-DEFLATE.md S-15, declared before this file). ONE dispatch on the
mode cell over the 28 mode terms of Step.lean; DONE, REJECT and every other value fall through to `ret world`.
The carrying lemma: a mode term compiled under the dispatch's binder `md`, closed at the world and then substituted at the mode
load, IS its standalone `closeAt p (t.c ["w"])`. So every one-step mode lemma of Step.lean transfers to the step unchanged.
-/
import VIRDeflate.Step

namespace VIRDeflate.Step
open VIRL1 VIRL2

/-! ## "Never names `md`, and its closed atoms are closed" -/

def NA.ok (md : String) : NA → Prop
  | .v x => x ≠ md
  | .i _ => True
  | .p2 _ a b => NA.ok md a ∧ NA.ok md b
  | .p1 _ a => NA.ok md a
  | .pair a b => NA.ok md a ∧ NA.ok md b
  | .fst a => NA.ok md a
  | .snd a => NA.ok md a
  | .atom a => ∀ k v, a.subst k v = a

def NT.ok (md : String) : NT → Prop
  | .ret a => NA.ok md a
  | .letE x _ e₁ e₂ => x ≠ md ∧ NT.ok md e₁ ∧ NT.ok md e₂
  | .op x _ _ as e => x ≠ md ∧ (∀ a ∈ as, NA.ok md a) ∧ NT.ok md e
  | .ite a e₁ e₂ => NA.ok md a ∧ NT.ok md e₁ ∧ NT.ok md e₂
  | .app f a => NA.ok md f ∧ NA.ok md a

theorem substL_map (k : Nat) (v : Atom₂) (l : List Atom₂) : Atom.substL k v l = l.map (fun a => a.subst k v) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [Atom.substL, ih]

/-! ## The carrying lemma -/

/-- The variable case: x ≠ "md". Substituting the world c at |Γ₁|+1, then m at |Γ₁|, in `Γ₁ ++ ["md", "w"]`, is substituting
c at |Γ₁| in `Γ₁ ++ ["w"]`. -/
theorem var_carry (x : String) (Γ₁ : List String) (c m : Const) (hx : x ≠ "md") :
    ((Atom.var (List.idxOf x (Γ₁ ++ ["md", "w"])) : Atom₂).subst (Γ₁.length + 1) (.const c)).subst Γ₁.length (.const m) =
      (Atom.var (List.idxOf x (Γ₁ ++ ["w"])) : Atom₂).subst Γ₁.length (.const c) := by
  rw [List.idxOf_append, List.idxOf_append]
  by_cases hm : x ∈ Γ₁
  · have hl := List.idxOf_lt_length_of_mem hm
    simp [hm, Atom.subst, show List.idxOf x Γ₁ < Γ₁.length + 1 by omega, hl]
  · by_cases hw : x = "w"
    · subst hw
      simp [hm, Atom.subst, show 1 + Γ₁.length = Γ₁.length + 1 by omega]
    · have h1 : List.idxOf x ["md", "w"] = 2 := by
        simp [List.idxOf_cons, List.idxOf_nil, show ("md" == x) = false by simpa using Ne.symm hx,
          show ("w" == x) = false by simpa using Ne.symm hw]
      have h2 : List.idxOf x ["w"] = 1 := by
        simp [List.idxOf_cons, List.idxOf_nil, show ("w" == x) = false by simpa using Ne.symm hw]
      simp only [hm, if_false, h1, h2]
      rw [show 2 + Γ₁.length = (Γ₁.length + 1) + 1 by omega, show 1 + Γ₁.length = Γ₁.length + 1 by omega]
      simp [Atom.subst]

theorem NA.carry (c m : Const) : ∀ (a : NA) (Γ₁ : List String), NA.ok "md" a →
    ((a.c (Γ₁ ++ ["md", "w"])).subst (Γ₁.length + 1) (.const c)).subst Γ₁.length (.const m) =
      (a.c (Γ₁ ++ ["w"])).subst Γ₁.length (.const c)
  | .v x, Γ₁, h => var_carry x Γ₁ c m h
  | .i n, _, _ => by simp [NA.c, Atom.subst]
  | .p2 o a b, Γ₁, h => by
    simp [NA.c, Atom.subst, Atom.substL, NA.carry c m a Γ₁ h.1, NA.carry c m b Γ₁ h.2]
  | .p1 o a, Γ₁, h => by simp [NA.c, Atom.subst, Atom.substL, NA.carry c m a Γ₁ h]
  | .pair a b, Γ₁, h => by simp [NA.c, Atom.subst, NA.carry c m a Γ₁ h.1, NA.carry c m b Γ₁ h.2]
  | .fst a, Γ₁, h => by simp [NA.c, Atom.subst, NA.carry c m a Γ₁ h]
  | .snd a, Γ₁, h => by simp [NA.c, Atom.subst, NA.carry c m a Γ₁ h]
  | .atom a, Γ₁, h => by simp only [NA.c]; rw [h, h, h]

theorem NT.carry (c m : Const) : ∀ (t : NT) (Γ₁ : List String), NT.ok "md" t →
    ((t.c (Γ₁ ++ ["md", "w"])).subst (Γ₁.length + 1) (.const c)).subst Γ₁.length (.const m) =
      (t.c (Γ₁ ++ ["w"])).subst Γ₁.length (.const c)
  | .ret a, Γ₁, h => by simp [NT.c, Tm.subst, NA.carry c m a Γ₁ h]
  | .letE x τ e₁ e₂, Γ₁, h => by
    have h2 := NT.carry c m e₂ (x :: Γ₁) h.2.2
    simp only [List.cons_append, List.length_cons] at h2
    simp [NT.c, Tm.subst, NT.carry c m e₁ Γ₁ h.2.1, h2]
  | .op x τ o as e, Γ₁, h => by
    have h2 := NT.carry c m e (x :: Γ₁) h.2.2
    simp only [List.cons_append, List.length_cons] at h2
    have hl : ∀ a ∈ as, ((a.c (Γ₁ ++ ["md", "w"])).subst (Γ₁.length + 1) (.const c)).subst Γ₁.length (.const m) =
        (a.c (Γ₁ ++ ["w"])).subst Γ₁.length (.const c) := fun a ha => NA.carry c m a Γ₁ (h.2.1 a ha)
    simp only [NT.c, Tm.subst, substL_map, List.map_map, h2]
    congr 1
    exact List.map_congr_left (fun a ha => by simpa using hl a ha)
  | .ite a e₁ e₂, Γ₁, h => by
    simp [NT.c, Tm.subst, NA.carry c m a Γ₁ h.1, NT.carry c m e₁ Γ₁ h.2.1, NT.carry c m e₂ Γ₁ h.2.2]
  | .app f a, Γ₁, h => by simp [NT.c, Tm.subst, NA.carry c m f Γ₁ h.1, NA.carry c m a Γ₁ h.2]

abbrev capA (p : Int) : Atom₂ := .const (.cap p)

/-- **The carrying lemma (S-15), at the top:** close at ⟨p⟩, then substitute the mode, and the mode term is its standalone
`closeAt p (t.c ["w"])`. -/
theorem carry_top (p m : Int) (t : NT) (h : NT.ok "md" t) :
    Tm.subst 0 (ci m) (Tm.subst 1 (capA p) (t.c ["md", "w"])) = closeAt p (t.c ["w"]) := by
  simpa [closeAt] using NT.carry (Const.cap p) (Const.int m) t [] h

/-! ## The dispatch (S-15) -/

def dispN : List (Int × NT) → NT
  | [] => .ret (.v "w")
  | (k, t) :: r => .ite (.p2 .eq (.v "md") (.i k)) t (dispN r)

def modes : List (Int × NT) :=
  [(mTABLE, tableN), (mHDR, hdrN), (mREAD, readN), (mHDRB, hdrbN), (mHDRD, hdrdN), (mSHDR, shdrN), (mFIXLENS, fixlensN),
   (mDHDR, dhdrN), (mSLEN, slenN), (mSNLEN, snlenN), (mSCOPY, scopyN), (mBUILD, buildN), (mLENS, lensN), (mSYM, symN),
   (mDECODE, decodeN), (mSYMD, symdN), (mLENX, lenxN), (mDSTD, dstdN), (mDSTX, dstxN), (mCOPY, copyN), (mDH2, dh2N),
   (mDH3, dh3N), (mDH4, dh4N), (mCLREAD, clreadN), (mCLPUT, clputN), (mLSYM, lsymN), (mLREP, lrepN), (mREP, repN)]

def stepN : NT := .op "md" tint .load [.v "w", .i cMODE] (dispN modes)
def stepT : Tm₂ := stepN.c ["w"]

/-- The dispatch's numbers are 0 … 27, each once (S-15's "a mode number in two branches" cannot occur). -/
theorem modes_keys : modes.map Prod.fst = (List.range 28).map (fun i => (i : Int)) := by
  simp [modes, mTABLE, mHDR, mREAD, mHDRB, mHDRD, mSHDR, mFIXLENS, mDHDR, mSLEN, mSNLEN, mSCOPY, mBUILD, mLENS, mSYM, mDECODE,
    mSYMD, mLENX, mDSTD, mDSTX, mCOPY, mDH2, mDH3, mDH4, mCLREAD, mCLPUT, mLSYM, mLREP, mREP, List.range, List.range.loop]

/-- Running the dispatch after both substitutions: the first branch whose number is m, or `ret ⟨p⟩` if none. -/
theorem disp_run (p m : Int) (σ : Store) : ∀ (ms : List (Int × NT)), (∀ kt ∈ ms, NT.ok "md" kt.2) →
    Steps₂ (Tm.subst 0 (ci m) (Tm.subst 1 (capA p) ((dispN ms).c ["md", "w"])), σ)
      (match ms.lookup m with
       | some t => (closeAt p (t.c ["w"]), σ)
       | none => (.ret (capA p), σ))
  | [], _ => by
    simp [dispN, NT.c, NA.c, List.idxOf, List.findIdx, List.findIdx.go, Tm.subst, Atom.subst, List.lookup]
    exact .refl _
  | (k, t) :: r, h => by
    have ht := carry_top p m t (h (k, t) (by simp))
    by_cases hk : m = k
    · subst hk
      have : Tm.subst 0 (ci m) (Tm.subst 1 (capA p) ((dispN ((m, t) :: r)).c ["md", "w"])) =
          Tm.ite (Atom.prim L1.Prim.eq [ci m, ci m]) (closeAt p (t.c ["w"]))
            (Tm.subst 0 (ci m) (Tm.subst 1 (capA p) ((dispN r).c ["md", "w"]))) := by
        rw [← ht]; simp [dispN, NT.c, NA.c, List.idxOf, List.findIdx, List.findIdx.go, Tm.subst, Atom.subst, Atom.substL]
      rw [this]
      simp only [List.lookup, beq_self_eq_true]
      exact steps_run 1 (by simp [run₂, stepFn₂, stepFn, Atom.eval, Atom.evalL, constsOf, S₂, pInterp, L1.Prim.interp,
        Const.toL1, Const.ofL1, Const.toBool])
    · have : Tm.subst 0 (ci m) (Tm.subst 1 (capA p) ((dispN ((k, t) :: r)).c ["md", "w"])) =
          Tm.ite (Atom.prim L1.Prim.eq [ci m, ci k]) (closeAt p (t.c ["w"]))
            (Tm.subst 0 (ci m) (Tm.subst 1 (capA p) ((dispN r).c ["md", "w"]))) := by
        rw [← ht]; simp [dispN, NT.c, NA.c, List.idxOf, List.findIdx, List.findIdx.go, Tm.subst, Atom.subst, Atom.substL]
      rw [this]
      have hb : (m == k) = false := by simp [hk]
      have hl : ((k, t) :: r).lookup m = r.lookup m := by simp [List.lookup, hb]
      rw [hl]
      refine Steps₂.trans (steps_run 1 (d := (Tm.subst 0 (ci m) (Tm.subst 1 (capA p) ((dispN r).c ["md", "w"])), σ)) (by simp [run₂, stepFn₂, stepFn, Atom.eval, Atom.evalL, constsOf, S₂, pInterp, L1.Prim.interp,
        Const.toL1, Const.ofL1, Const.toBool, hk])) ?_
      exact disp_run p m σ r (fun kt hkt => h kt (by simp [hkt]))

/-- Every mode term never names `md`, and its one closed atom (`BITc`) is closed. -/
theorem modes_ok : ∀ kt ∈ modes, NT.ok "md" kt.2 := by
  intro kt hkt
  simp only [modes, List.mem_cons, List.mem_nil_iff, or_false] at hkt
  rcases hkt with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
  subst h <;>
  simp [NT.ok, NA.ok, tableN, hdrN, readN, hdrbN, hdrdN, shdrN, fixlensN, dhdrN, slenN, snlenN, scopyN, buildN, lensN, symN,
    decodeN, symdN, lenxN, dstdN, dstxN, copyN, dh2N, dh3N, dh4N, clreadN, clputN, lsymN, lrepN, repN, reqN, reqDecN, reqKN,
    rejN, bZeroN, bCountN, bNextN, bRestN, bLeftN, bSymsN, BITc_subst]

/-- **The step, one load and the dispatch:** at mode m, the step reaches the mode term's own closed form, or `ret ⟨p⟩` when m
names no mode (DONE, REJECT, anything else). -/
theorem step_dispatch {σ : Store} {p : Int} {L : Nat} {f : Int → Int} (hw : World σ p L f) (hL : 0 < L) (m : Int)
    (hm : f cMODE = m) :
    Steps₂ (closeAt p stepT, σ)
      (match modes.lookup m with
       | some t => (closeAt p (t.c ["w"]), σ)
       | none => (.ret (capA p), σ)) := by
  simp only [cMODE] at hm
  have g0 := hw.get (i := 0) (by decide) (by omega) hm
  refine Steps₂.trans (steps_run 1 (d := (Tm.subst 0 (ci m) (Tm.subst 1 (capA p) ((dispN modes).c ["md", "w"])), σ)) ?_)
    (disp_run p m σ modes modes_ok)
  simp only [closeAt, stepT, stepN, NT.c, NA.c, List.idxOf, List.findIdx, List.findIdx.go, Tm.subst, Atom.subst,
    Atom.substL, run₂, stepFn₂, opStep, Store.load, hw.reg, g0, cMODE, capA]
  simp [NA.c, List.idxOf, List.findIdx, List.findIdx.go, Atom.substL, Atom.subst, Atom.eval, Atom.evalL, Store.load,
    hw.reg, hL, show (0 : Int) < L by omega, g0]

/-- **Every one-step mode lemma transfers to the step:** at mode k, where the dispatch maps k to t, whatever t's closed form
reaches, the step reaches. -/
theorem step_of_mode {σ : Store} {p : Int} {L : Nat} {f : Int → Int} (hw : World σ p L f) (hL : 0 < L) {k : Int} {t : NT}
    (hm : f cMODE = k) (hk : modes.lookup k = some t) {d : Config} (h : Steps₂ (closeAt p (t.c ["w"]), σ) d) :
    Steps₂ (closeAt p stepT, σ) d := by
  have := step_dispatch hw hL k hm
  rw [hk] at this
  exact Steps₂.trans this h

/-- **DONE and REJECT are fixed points of the step** (S-15): it returns the world, and the store is unchanged. -/
theorem step_fixed {σ : Store} {p : Int} {L : Nat} {f : Int → Int} (hw : World σ p L f) (hL : 0 < L) (m : Int)
    (hm : f cMODE = m) (h : m = mDONE ∨ m = mREJECT) :
    Steps₂ (closeAt p stepT, σ) (.ret (capA p), σ) := by
  have := step_dispatch hw hL m hm
  have hn : modes.lookup m = none := by
    rcases h with h | h <;> subst h <;> rfl
  rw [hn] at this
  exact this

/-- The lookups, one per mode, so a mode lemma transfers by `step_of_mode … rfl`. -/
example : modes.lookup mTABLE = some tableN := rfl
example : modes.lookup mREP = some repN := rfl

/-- Worked transfer: `TABLE`'s one-step lemma, at the step. -/
theorem step_table {σ : Store} {p : Int} {L : Nat} {f : Int → Int} (hw : World σ p L f) (hL : 2068 ≤ L)
    (tb ti : Nat) (hmode : f cMODE = mTABLE) (htb : f cTB = tb) (hti : f cTI = ti) (htb8 : tb < 256) (hti8 : ti ≤ 7) :
    Steps₂ (closeAt p stepT, σ)
      (.ret (.const (.cap p)),
        if (tblNext tb ti).1 = 256 then ⟨(tblH σ.H p tb ti).insert (p + 0) 1, σ.R⟩ else ⟨tblH σ.H p tb ti, σ.R⟩) :=
  step_of_mode hw (by omega) hmode rfl (table_step hw hL tb ti htb hti htb8 hti8)

end VIRDeflate.Step
