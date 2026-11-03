/-
  O95 layer L1, Lean arm. The acceptance programs K1–K5 (inputs/L1-programs.md), in de Bruijn form, with per program:
  its typing, a ⟶* trace to its value (`run` by kernel reduction, then `run_steps`), and its denotation's value.
  K2 diverges: ¬ Dom, by the LEASTNESS of the fixed point (its approximation characterisation, `Part.Fix.mem_iff`).
-/
import VIRL1.L1

namespace VIRL1.L1
open VIRL1

abbrev tint : Ty₁ := .base BTy.int
abbrev tbool : Ty₁ := .base BTy.bool
abbrev ci (n : Int) : Atom S₁ := .const (Const.int n)
abbrev pr (p : Prim) (as : List (Atom S₁)) : Atom S₁ := .prim (S := S₁) p as

/-- K1: `let fact:int→int = ret (fix fact(n:int):int. if le(n,0) then ret 1 else let r:int = fact sub(n,1) in ret mul(n,r)) in fact 5` -/
def K1 : Tm₁ :=
  .letE (.arr tint tint)
    (.ret (.fix tint tint
      (.ite (pr .le [.var 0, ci 0]) (.ret (ci 1))
        (.letE tint (.app (.var 1) (pr .sub [.var 0, ci 1])) (.ret (pr .mul [.var 1, .var 0]))))))
    (.app (.var 0) (ci 5))

/-- K2: `(fix loop(x:int):int. loop x) 0` -/
def K2 : Tm₁ := .app (.fix tint tint (.app (.var 1) (.var 0))) (ci 0)

/-- K3: `let twice = ret (λ(f:int→int). ret (λ(x:int). let y:int = f x in f y)) in let g = twice (λ(z:int). ret add(z,1)) in g 40` -/
def K3 : Tm₁ :=
  .letE (.arr (.arr tint tint) (.arr tint tint))
    (.ret (.lam (.arr tint tint) (.ret (.lam tint (.letE tint (.app (.var 1) (.var 0)) (.app (.var 2) (.var 0)))))))
    (.letE (.arr tint tint) (.app (.var 0) (.lam tint (.ret (pr .add [.var 0, ci 1]))))
      (.app (.var 0) (ci 40)))

/-- K4: `if and(lt(1,2), not(eq(3,4))) then ret 7 else ret 8` -/
def K4 : Tm₁ := .ite (pr .and [pr .lt [ci 1, ci 2], pr .not [pr .eq [ci 3, ci 4]]]) (.ret (ci 7)) (.ret (ci 8))

/-- K5: `let sum = ret (fix sum(n:int):int→int. ret (λ(acc:int). if le(n,0) then ret acc else let k = sum sub(n,1) in k add(acc,n))) in let s = sum 10 in s 0` -/
def K5 : Tm₁ :=
  .letE (.arr tint (.arr tint tint))
    (.ret (.fix tint (.arr tint tint)
      (.ret (.lam tint
        (.ite (pr .le [.var 1, ci 0]) (.ret (.var 0))
          (.letE (.arr tint tint) (.app (.var 2) (pr .sub [.var 1, ci 1]))
            (.app (.var 0) (pr .add [.var 1, .var 2]))))))))
    (.letE (.arr tint tint) (.app (.var 0) (ci 10)) (.app (.var 0) (ci 0)))

/-! ## Typing -/
macro "typecheck" : tactic => `(tactic| repeat (first | rfl | constructor))

theorem K1_typed : HasType E₁ [] K1 tint := by unfold K1; typecheck
theorem K2_typed : HasType E₁ [] K2 tint := by unfold K2; typecheck
theorem K3_typed : HasType E₁ [] K3 tint := by unfold K3; typecheck
theorem K4_typed : HasType E₁ [] K4 tint := by unfold K4; typecheck
theorem K5_typed : HasType E₁ [] K5 tint := by unfold K5; typecheck

/-! ## Traces (kernel reduction of `run`) and meanings: e ⟶* ret a with ⟨a⟩ the value (OBJECT-L1 §6, soundness) -/
theorem K1_run : ∃ a, run 200 K1 = .ret a ∧ a.eval = some (ci 120) := ⟨_, rfl, rfl⟩
theorem K3_run : ∃ a, run 200 K3 = .ret a ∧ a.eval = some (ci 42) := ⟨_, rfl, rfl⟩
theorem K4_run : ∃ a, run 200 K4 = .ret a ∧ a.eval = some (ci 7) := ⟨_, rfl, rfl⟩
theorem K5_run : ∃ a, run 400 K5 = .ret a ∧ a.eval = some (ci 55) := ⟨_, rfl, rfl⟩

theorem trace_den {e : Tm₁} {n v} (h : ∃ a, run n e = .ret a ∧ a.eval = some v) :
    (∃ a, Steps e (.ret a) ∧ a.eval = some v) ∧ den e = Part.some v := by
  obtain ⟨a, hr, ha⟩ := h
  have hs : Steps e (.ret a) := hr ▸ run_steps n e
  exact ⟨⟨a, hs, ha⟩, den_of_steps hs ha⟩

theorem K1_meaning : (∃ a, Steps K1 (.ret a) ∧ a.eval = some (ci 120)) ∧ den K1 = Part.some (ci 120) := trace_den K1_run
theorem K3_meaning : (∃ a, Steps K3 (.ret a) ∧ a.eval = some (ci 42)) ∧ den K3 = Part.some (ci 42) := trace_den K3_run
theorem K4_meaning : (∃ a, Steps K4 (.ret a) ∧ a.eval = some (ci 7)) ∧ den K4 = Part.some (ci 7) := trace_den K4_run
theorem K5_meaning : (∃ a, Steps K5 (.ret a) ∧ a.eval = some (ci 55)) ∧ den K5 = Part.some (ci 55) := trace_den K5_run

/-! ## K2 diverges -/
theorem K2_head : head K2 = .go K2 := rfl

theorem K2_approx : ∀ i, Part.Fix.approx (Φo (S := S₁)) i K2 = Part.none
  | 0 => rfl
  | i + 1 => by
    change Φ _ K2 = Part.none
    show Head.run _ (head K2) = Part.none
    rw [K2_head]; exact K2_approx i

theorem K2_diverges : ¬ (den K2).Dom := by
  intro hd
  obtain ⟨i, hi⟩ := (Part.Fix.mem_iff (Φo (S := S₁)) K2 ((den K2).get hd)).mp (Part.get_mem hd)
  rw [K2_approx i] at hi
  exact Part.notMem_none _ hi

end VIRL1.L1
