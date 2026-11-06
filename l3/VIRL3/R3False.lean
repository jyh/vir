/-
  O95 layer L3, Lean arm. OBJECT-L3 §3.2 / inputs R3 as PINNED say `⟦U_tx⟧₂ σ = ⟦F⟧₂ σ` for EVERY σ. That is FALSE, twice,
  by runs on two concrete worlds (errata/ERRATA-L3.md L3-E1). Both are frames that G3 (a)'s layout precondition
  (sender < NS ∧ topic < NT) excludes; R3 is proved under it.
  (1) ORDER: a wrong magic with an out-of-range sender. U_tx checks the magic before it reads the sender and exits 2; F reads
      the ACL cell before its guard (ANF) and INDEX-FAULTS there. ⟦F⟧₂ = ⊥, ⟦U_tx⟧₂ = some.
  (2) ALIASING: sender 3, topic 7 puts the ACL cell A + 3·4 + 7 = 86 ON the bucket cell K + 3 = 86. With one token, F reads
      a = 1 and emits; U_tx decrements first, reads a = 0 from the decremented world, and refuses. The stores differ at cell 1.
-/
import VIRL3.Refusals

namespace VIRL3
open VIRL1 VIRL2

/-- (1): LEN 24, magic bytes all 0 (wrong), sender byte 0 = 200 (sender 200, ACL cell 67 + 800 out of the world). -/
def σE1 : Store := mkWorld [(0, 24), (7, 200)]
/-- (2): LEN 24, the magic, sender 3, topic 7, one token in bucket 3 (cell 86, which is also ACL cell (3, 7)). -/
def σE2 : Store := mkWorld [(0, 24), (3, 49), (4, 71), (5, 83), (6, 77), (7, 3), (11, 7), (86, 1)]

set_option maxRecDepth 100000 in
theorem E1_Utx_run : (run₂ 80 (closeW U_tx, σE1)).1 = .ret (.const (.cap 0)) := rfl
set_option maxRecDepth 100000 in
theorem E1_F_stuck : ∃ rest, (run₂ 80 (closeW F, σE1)).1 =
    .letOp .load [.const (.cap 0), .prim .add [.const (.int 67), .prim .add
      [.prim .mul [.const (.int 200), .const (.int 4)], .const (.int 0)]]] tint rest := ⟨_, rfl⟩

set_option maxRecDepth 100000 in
/-- L3-E1 (1): ⟦U_tx⟧₂ ≠ ⟦F⟧₂ at σE1 — F denotes ⊥ (an index fault), U_tx a value. -/
theorem R3_false_order : den₂ (closeW U_tx, σE1) ≠ den₂ (closeW F, σE1) := by
  rw [den_of_run E1_Utx_run rfl]
  obtain ⟨rest, hr⟩ := E1_F_stuck
  have he : run₂ 80 (closeW F, σE1) = ((run₂ 80 (closeW F, σE1)).1, (run₂ 80 (closeW F, σE1)).2) := rfl
  rw [soundness₂_steps (run₂_steps 80 (closeW F, σE1)), he, hr, den₂_fault rfl rfl]
  exact Part.some_ne_none _

set_option maxRecDepth 100000 in
theorem E2_F_run : (run₂ 80 (closeW F, σE2)).1 = .ret (.const (.cap 0)) := rfl
set_option maxRecDepth 100000 in
theorem E2_Utx_run : (run₂ 80 (closeW U_tx, σE2)).1 = .ret (.const (.cap 0)) := rfl
set_option maxRecDepth 100000 in
theorem E2_F_code : Store.load 0 1 (run₂ 80 (closeW F, σE2)).2 = some 0 := rfl
set_option maxRecDepth 100000 in
theorem E2_Utx_code : Store.load 0 1 (run₂ 80 (closeW U_tx, σE2)).2 = some 2 := rfl

/-- L3-E1 (2): ⟦U_tx⟧₂ ≠ ⟦F⟧₂ at σE2 — F emits (code 0), U_tx refuses (code 2). -/
theorem R3_false_alias : den₂ (closeW U_tx, σE2) ≠ den₂ (closeW F, σE2) := by
  rw [den_of_run E2_Utx_run rfl, den_of_run E2_F_run rfl]
  intro h
  have h' := congrArg (fun p : Atom₂ × Store => Store.load 0 1 p.2) (Part.some_injective h)
  simp only [E2_Utx_code, E2_F_code] at h'
  exact absurd h' (by decide)

end VIRL3
