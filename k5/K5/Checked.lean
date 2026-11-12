/-
  O95, K5-2 (compiler/DECLARATIONS-K5.md addendum 3, written before this file), route A's generic half: a CHECKED runner.
  `stepFn₂C` is ⟶₂'s step function, refusing a configuration whose next-evaluated atoms are not in range (`headB`, a Bool
  check proved to imply `Tm.HeadInR`). `srcInRange_runC`: if the configuration where a checked run stops is in range from
  there on, so is its start (⟶₂ is deterministic, so the run's configurations ARE the reachable ones).
  The compiler and DEFLATE are imported by path and not edited.
-/
import VIRC.NoOvfSrc
import VIRDeflate.Statements

namespace K5
open VIRL1 VIRL2 VIRC

/-! ## The Bool check -/
def cInR : Option Atom₂ → Bool
  | some (.const (.int n)) => inRange n
  | _ => true

mutual
def aInR : Atom₂ → Bool
  | .prim p as => aInRL as && cInR (Atom.eval (.prim p as))
  | .pair a b => aInR a && aInR b
  | .fst a => aInR a
  | .snd a => aInR a
  | .inl _ a => aInR a
  | .inr _ a => aInR a
  | _ => true
def aInRL : List Atom₂ → Bool
  | [] => true
  | a :: as => aInR a && aInRL as
end

def headB : Tm₂ → Bool
  | .ret a => aInR a
  | .letE _ e₁ _ => headB e₁
  | .letOp _ as _ _ => aInRL as
  | .app a₁ a₂ => aInR a₁ && aInR a₂
  | .ite a _ _ => aInR a
  | .case a _ _ => aInR a

theorem cInR_sound {o : Option Atom₂} (h : cInR o = true) : ∀ v, o = some v → Atom.inR₂ v := by
  intro v hv; subst hv
  cases v with
  | const c => cases c <;> simp_all [cInR, Atom.inR₂]
  | _ => simp [Atom.inR₂]

mutual
theorem aInR_sound : ∀ (a : Atom₂), aInR a = true → Atom.InR₂ a
  | .var _, _ => trivial
  | .const _, _ => trivial
  | .lam _ _, _ => trivial
  | .fix _ _ _, _ => trivial
  | .prim p as, h => by
      simp only [aInR, Bool.and_eq_true] at h
      exact ⟨aInRL_sound as h.1, cInR_sound h.2⟩
  | .pair a b, h => by
      simp only [aInR, Bool.and_eq_true] at h
      exact ⟨aInR_sound a h.1, aInR_sound b h.2⟩
  | .fst a, h => aInR_sound a (by simpa [aInR] using h)
  | .snd a, h => aInR_sound a (by simpa [aInR] using h)
  | .inl _ a, h => aInR_sound a (by simpa [aInR] using h)
  | .inr _ a, h => aInR_sound a (by simpa [aInR] using h)
theorem aInRL_sound : ∀ (as : List Atom₂), aInRL as = true → Atom.InRL₂ as
  | [], _ => trivial
  | a :: as, h => by
      simp only [aInRL, Bool.and_eq_true] at h
      exact ⟨aInR_sound a h.1, aInRL_sound as h.2⟩
end

theorem headB_sound : ∀ (t : Tm₂), headB t = true → Tm.HeadInR t
  | .ret a, h => aInR_sound a h
  | .letE _ e₁ _, h => headB_sound e₁ h
  | .letOp _ as _ _, h => aInRL_sound as h
  | .app a₁ a₂, h => by
      simp only [headB, Bool.and_eq_true] at h
      exact ⟨aInR_sound a₁ h.1, aInR_sound a₂ h.2⟩
  | .ite a _ _, h => aInR_sound a h
  | .case a _ _, h => aInR_sound a h

/-! ## The checked runner -/
def stepFn₂C (t : Tm₂) (σ : Store) : Option Config := if headB t then stepFn₂ t σ else none

def run₂C : Nat → Config → Config
  | 0, c => c
  | n + 1, c => match stepFn₂C c.1 c.2 with
    | some c' => run₂C n c'
    | none => c

/-- A `ret` whose atom is in range is in range from there on: it has no step. -/
theorem srcInRange_ret {a : Atom₂} {σ : Store} (ha : Atom.InR₂ a) : SrcInRange (.ret a, σ) := by
  intro S hS
  cases hS with
  | refl => exact ha
  | step h _ => exact absurd h no_step_ret

/-- **The generic lemma.** If the configuration where a checked run stops is in range from there on, so is its start. -/
theorem srcInRange_runC : ∀ (k : Nat) (c : Config), SrcInRange (run₂C k c) → SrcInRange c
  | 0, _, h => h
  | k + 1, c, h => by
      simp only [run₂C] at h
      cases hc : stepFn₂C c.1 c.2 with
      | none => rw [hc] at h; exact h
      | some c' =>
        rw [hc] at h
        have ih := srcInRange_runC k c' h
        simp only [stepFn₂C] at hc
        split at hc
        · rename_i hb
          have hst : Step₂ c c' := stepFn₂_sound hc
          intro S hS
          cases hS with
          | refl => exact headB_sound _ hb
          | step h₁ h₂ =>
            rename_i c''
            have := step₂_det h₁ hst; subst this
            exact ih S h₂
        · cases hc


/-- One checked step at a time: the proof term of a walk built from this is a chain, never a 40-deep nested `match` (the
nested form overflows the kernel: k5p-004/005, probes 001–003). -/
theorem srcInRange_step {c : Config} (hb : headB c.1 = true) (hs : (stepFn₂ c.1 c.2).isSome = true)
    (h : SrcInRange ((stepFn₂ c.1 c.2).getD c)) : SrcInRange c := by
  obtain ⟨c', hc'⟩ := Option.isSome_iff_exists.mp hs
  rw [hc'] at h
  refine srcInRange_runC 1 c ?_
  simp only [run₂C, stepFn₂C, hb, if_true, hc']
  exact h

/-- The form a mode trace takes: a checked run that reaches `ret ⟨p⟩`. -/
theorem srcInRange_of_runC {k : Nat} {c : Config} {p : Int} {σ' : Store}
    (h : run₂C k c = (.ret (.const (.cap p)), σ')) : SrcInRange c :=
  srcInRange_runC k c (by rw [h]; exact srcInRange_ret trivial)

/-! ## Pilot: HDR (no arithmetic), by the same `simp` as its trace in Step.lean, on the checked runner. -/
open VIRDeflate.Step in
theorem hdr_inR {σ : Store} {p : Int} {L : Nat} {f : Int → Int} (hw : World σ p L f) (hL : 2080 ≤ L) :
    SrcInRange (closeAt p hdrT, σ) := by
  apply srcInRange_of_runC (k := 10) (p := p) (σ' := ⟨reqH σ.H p 1 3, σ.R⟩)
  simp [closeAt, hdrT, hdrN, reqN, reqH, NT.c, NA.c, List.idxOf, List.findIdx, List.findIdx.go, Tm.subst, Atom.subst,
    Atom.substL, run₂C, stepFn₂C, headB, aInR, aInRL, stepFn₂, stepFn, opStep, Store.store, hw.reg, Atom.eval, Atom.evalL,
    cK, cACC, cWT, cRET, cMODE, mREAD, mHDRB, show (2068 : Int) < L by omega, show (2069 : Int) < L by omega,
    show (2070 : Int) < L by omega, show (2071 : Int) < L by omega, show (0 : Int) < L by omega, show 0 < L by omega]

end K5
