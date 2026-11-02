/-
  O95 VIR program, Lean arm: n CALLS AT THE MEANING (council 2026-11-02 §C point 5: "calls and emits as inputs/outputs,
  so n-call theorems are trace properties"; STATUS-vir row 86). Each call: the caller puts a frame on the wire, ⟦F⟧ runs,
  and the store it returns (buckets) carries into the next call. RATE LIMITING OVER n CALLS is then an exact identity, by
  induction: sender p's tokens at the end + p's emits = p's tokens at the start. So p never emits more than it held.
  This is the abstract side. The machine side iterates paris's `reenter` + `sim_one` and is not built here.
-/
import VIRP.Router

namespace VIRP

/-- ⟦F⟧'s closed form as a function (F_closed's right-hand side). -/
def Fn (σ : Store) : Store × Label :=
  if (σ.wire.length : Int) ≥ 24 then
    (if rd32 σ.wire 0 = MAGIC ∧ σ.acl (rd32 σ.wire 4) (rd32 σ.wire 8) = true ∧ 1 ≤ σ.bucket (rd32 σ.wire 4)
     then (σ.dec (rd32 σ.wire 4), Label.emit 24) else (σ, Label.drop .unauthOrRate))
  else (σ, Label.drop .truncated)

theorem denote_F_eq (σ : Store) : denote F env0 σ = Part.some (Fn σ) := F_closed σ

/-- One call: the caller writes frame `w`, then ⟦F⟧ runs. -/
def call (σ : Store) (w : List Int) : Store × Label := Fn { σ with wire := w }

/-- The trace of n calls: the labels, and the store after the last. -/
def run : Store → List (List Int) → Store × List Label
  | σ, [] => (σ, [])
  | σ, w :: ws => let r := call σ w; let t := run r.1 ws; (t.1, r.2 :: t.2)

/-- Sender p's emits along the trace. -/
def emitsBy (p : Int) : Store → List (List Int) → Nat
  | _, [] => 0
  | σ, w :: ws =>
    let r := call σ w
    (match r.2 with | .emit _ => if rd32 w 4 = p then 1 else 0 | .drop _ => 0) + emitsBy p r.1 ws

/-- One call: p's tokens after + p's emit (0 or 1) = p's tokens before. -/
theorem call_tokens (σ : Store) (w : List Int) (p : Int) :
    (call σ w).1.bucket p + (match (call σ w).2 with | .emit _ => if rd32 w 4 = p then 1 else 0 | .drop _ => 0)
      = σ.bucket p := by
  unfold call Fn
  split_ifs with h1 h2 h3 <;> simp_all [Store.dec]
  all_goals omega

/-- RATE LIMITING OVER n CALLS, exactly. -/
theorem run_tokens (p : Int) : ∀ (ws : List (List Int)) (σ : Store),
    (run σ ws).1.bucket p + emitsBy p σ ws = σ.bucket p
  | [], σ => by simp [run, emitsBy]
  | w :: ws, σ => by
    have ih := run_tokens p ws (call σ w).1
    have h1 := call_tokens σ w p
    simp only [run, emitsBy]
    omega

theorem emits_le_tokens (p : Int) (ws : List (List Int)) (σ : Store) : emitsBy p σ ws ≤ σ.bucket p := by
  have := run_tokens p ws σ; omega

end VIRP
