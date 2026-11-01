/-
  STATUS-vir row 26: PROGRAM 3 (the A.1/A.2 safety theorem, inputs/program3-inputs.md K3, E10) on L-DEEP's denotation,
  from program 2's exit relation F2_exit. EXPLORATORY: no prediction is pinned for this embedding.
-/
import VIR.Exit2

namespace VIR.Deep2

open VIR.Deep (Val DOut)

variable (acl : Principal → TopicId → Bool)

/-- K3: a return, not a drop. -/
def IsRoutedD : DOut → Prop
  | .ret .. => True
  | .drop _ => False

/-- K3 on the deep denotation. There is no ValidFrame: amend-9 F2 measured that its refinement carries no load. -/
theorem route_acl_safe_deep (b0 st : Val) :
    IsRoutedD (den acl (F2 b0 st)) → acl (b0.rd 4).toP (b0.rd 8).toP = true := by
  rw [F2_exit]
  intro h
  split at h
  · split at h
    · next hc => exact hc.2.1
    · exact h.elim
  · exact h.elim

end VIR.Deep2
