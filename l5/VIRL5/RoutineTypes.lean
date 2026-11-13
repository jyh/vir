/-
  O95 layer L5, Lean arm (amend-24 LV7/LV8 groundwork): each routine is a CLOSED ⊢₅-typed value of its annotated arrow, so a typed
  program may call it (and LV8's re-expressed programs are typed through it). Derivations written out rule by rule.
-/
import VIRL5.CopyWithin

namespace VIRL5
open VIRL1 VIRL2

theorem mask_ff : Mask.empty [false, false] := by intro n; rcases n with _ | _ | n <;> simp
theorem mask_fff : Mask.empty [false, false, false] := by intro n; rcases n with _ | _ | _ | n <;> simp

theorem caps0 {Γ : Ctx₅} {Δ : List Bool} (hΓ : Γ[0]? = some t5cap) (hΔ : ∀ n, Δ[n]? = some true ↔ n = 0) :
    CapsExact Γ Δ [0] :=
  ⟨List.nodup_singleton 0, by simpa using hΓ, fun n => by simpa using hΔ n⟩

theorem caps10 {Γ : Ctx₅} {Δ : List Bool} (h1 : Γ[1]? = some t5cap) (h0 : Γ[0]? = some t5cap)
    (hΔ : ∀ n, Δ[n]? = some true ↔ n = 1 ∨ n = 0) : CapsExact Γ Δ [1, 0] :=
  ⟨by simp, by simp [h1, h0], fun n => by simpa using hΔ n⟩

theorem fillR_typed : HasTypeA₅ [] fillR (.arr τfill 1 t5unit) := by
  refine .fix (Δ₀ := [false, false]) rfl rfl mask_ff rfl ?_
  refine .ite (.prim (.cons (.fst (.snd (.var rfl rfl))) (.cons .int .nil))) ?_ ?_
  · exact .retK (ns := [0]) rfl .unit (caps0 rfl (fun n => by rcases n with _ | _ | _ | n <;> simp))
  · refine .store (n := 0) rfl rfl (.fst (.var rfl rfl)) (.snd (.snd (.var rfl rfl))) ?_
    exact .appK (ns := [0]) (.var rfl rfl)
      (.pair (.prim (.cons (.fst (.var rfl rfl)) (.cons .int .nil)))
        (.pair (.prim (.cons (.fst (.snd (.var rfl rfl))) (.cons .int .nil))) (.snd (.snd (.var rfl rfl)))))
      (caps0 rfl (fun n => by rcases n with _ | _ | _ | _ | n <;> simp))

theorem copyR_typed : HasTypeA₅ [] copyR (.arr τcopy 2 t5unit) := by
  refine .fix (Δ₀ := [false, false]) rfl rfl mask_ff rfl ?_
  refine .ite (.prim (.cons (.snd (.snd (.var rfl rfl))) (.cons .int .nil))) ?_ ?_
  · exact .retK (ns := [1, 0]) rfl .unit (caps10 rfl rfl (fun n => by rcases n with _ | _ | _ | _ | n <;> simp))
  · refine .load (n := 1) rfl rfl (.fst (.var rfl rfl)) ?_
    refine .store (n := 1) rfl rfl (.fst (.snd (.var rfl rfl))) (.var rfl rfl) ?_
    exact .appK (ns := [3, 0]) (.var rfl rfl)
      (.pair (.prim (.cons (.fst (.var rfl rfl)) (.cons .int .nil)))
        (.pair (.prim (.cons (.fst (.snd (.var rfl rfl))) (.cons .int .nil)))
          (.prim (.cons (.snd (.snd (.var rfl rfl))) (.cons .int .nil)))))
      ⟨by simp, by simp, fun n => by rcases n with _ | _ | _ | _ | _ | _ | _ | n <;> simp⟩

theorem cmpR_typed : HasTypeA₅ [] cmpR (.arr τcopy 2 t5bool) := by
  refine .fix (Δ₀ := [false, false]) rfl rfl mask_ff rfl ?_
  refine .ite (.prim (.cons (.snd (.snd (.var rfl rfl))) (.cons .int .nil))) ?_ ?_
  · exact .retK (ns := [1, 0]) rfl .bool (caps10 rfl rfl (fun n => by rcases n with _ | _ | _ | _ | n <;> simp))
  · refine .load (n := 1) rfl rfl (.fst (.var rfl rfl)) ?_
    refine .load (n := 1) rfl rfl (.fst (.snd (.var rfl rfl))) ?_
    refine .ite (.prim (.cons (.var rfl rfl) (.cons (.var rfl rfl) .nil))) ?_ ?_
    · exact .appK (ns := [3, 2]) (.var rfl rfl)
        (.pair (.prim (.cons (.fst (.var rfl rfl)) (.cons .int .nil)))
          (.pair (.prim (.cons (.fst (.snd (.var rfl rfl))) (.cons .int .nil)))
            (.prim (.cons (.snd (.snd (.var rfl rfl))) (.cons .int .nil)))))
        ⟨by simp, by simp, fun n => by rcases n with _ | _ | _ | _ | _ | _ | _ | n <;> simp⟩
    · exact .retK (ns := [3, 2]) rfl .bool
        ⟨by simp, by simp, fun n => by rcases n with _ | _ | _ | _ | _ | _ | _ | n <;> simp⟩

theorem scanR_typed : HasTypeA₅ [] scanR (.arr τfill 1 t5int) := by
  refine .fix (Δ₀ := [false, false]) rfl rfl mask_ff rfl ?_
  refine .ite (.prim (.cons (.fst (.snd (.var rfl rfl))) (.cons (.fst (.var rfl rfl)) .nil))) ?_ ?_
  · exact .retK (ns := [0]) rfl (.fst (.snd (.var rfl rfl))) (caps0 rfl (fun n => by rcases n with _ | _ | _ | n <;> simp))
  · refine .load (n := 0) rfl rfl (.fst (.var rfl rfl)) ?_
    refine .ite (.prim (.cons (.var rfl rfl) (.cons (.snd (.snd (.var rfl rfl))) .nil))) ?_ ?_
    · exact .retK (ns := [1]) rfl (.fst (.var rfl rfl))
        ⟨by simp, by simp, fun n => by rcases n with _ | _ | _ | _ | _ | n <;> simp⟩
    · exact .appK (ns := [1]) (.var rfl rfl)
        (.pair (.prim (.cons (.fst (.var rfl rfl)) (.cons .int .nil))) (.snd (.var rfl rfl)))
        ⟨by simp, by simp, fun n => by rcases n with _ | _ | _ | _ | _ | n <;> simp⟩

theorem copyWithinR_typed : HasTypeA₅ [] copyWithinR (.arr τcopy 1 t5unit) := by
  refine .fix (Δ₀ := [false, false]) rfl rfl mask_ff rfl ?_
  refine .ite (.prim (.cons (.snd (.snd (.var rfl rfl))) (.cons .int .nil))) ?_ ?_
  · exact .retK (ns := [0]) rfl .unit (caps0 rfl (fun n => by rcases n with _ | _ | _ | n <;> simp))
  · refine .load (n := 0) rfl rfl (.fst (.var rfl rfl)) ?_
    refine .store (n := 1) rfl rfl (.fst (.snd (.var rfl rfl))) (.var rfl rfl) ?_
    exact .appK (ns := [0]) (.var rfl rfl)
      (.pair (.prim (.cons (.fst (.var rfl rfl)) (.cons .int .nil)))
        (.pair (.prim (.cons (.fst (.snd (.var rfl rfl))) (.cons .int .nil)))
          (.prim (.cons (.snd (.snd (.var rfl rfl))) (.cons .int .nil)))))
      (caps0 rfl (fun n => by rcases n with _ | _ | _ | _ | _ | _ | n <;> simp))

end VIRL5
