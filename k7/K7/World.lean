/-
  O95, K7-b2 (compiler/DECLARATIONS-K7.md, Addendum 3): facts about L3's TEST-WORLD builder `mkWorld` (one 87-cell region at base 0),
  so concrete witness worlds are WF, Placed and CellsInR. Nothing here mentions the router F.
-/
import VIRL3.Inequality
import K5.Loader

namespace K7
open VIRL1 VIRL2 VIRL3 VIRC K5

/-- One region {0 ↦ 87}, the heap's domain [0, 87), every cell in range. -/
def W87 (σ : Store) : Prop :=
  (∀ p, σ.R.lookup p = if p = 0 then some 87 else none) ∧ (∀ a, a ∈ σ.H ↔ 0 ≤ a ∧ a < 87) ∧
    (∀ a v, σ.H.lookup a = some v → inRange v = true)

set_option maxRecDepth 20000 in
theorem w87_base : W87 (((Store.alloc 87 Store.empty).map Prod.snd).getD Store.empty) := by
  have hb : Store.nextBase Store.empty = 0 := rfl
  simp only [Store.alloc, show (0 : Int) < 87 by decide, if_true, hb, Option.map_some, Option.getD_some]
  refine ⟨fun p => ?_, fun a => ?_, fun a v h => ?_⟩
  · by_cases hp : p = 0
    · subst hp; simp
    · rw [Finmap.lookup_insert_of_ne _ hp]; simp [hp, Store.empty]
  · rw [Store.mem_fill]; simp [Store.empty]
    intro h; exact (Finmap.notMem_empty h).elim
  · rw [Store.lookup_fill] at h
    split_ifs at h with hc
    · cases h; simp [inRange]
    · simp [Store.empty] at h

theorem w87_store {σ : Store} (h : W87 σ) (c : Int × Int) (hv : inRange c.2 = true) :
    W87 ((Store.store 0 c.1 c.2 σ).getD σ) := by
  obtain ⟨hR, hD, hI⟩ := h
  have h0 : σ.R.lookup 0 = some 87 := by rw [hR]; simp
  simp only [Store.store, h0]
  by_cases hi : 0 ≤ c.1 ∧ c.1 < (87 : Nat)
  · rw [if_pos hi, Option.getD_some]
    refine ⟨hR, fun a => ?_, fun a v hl => ?_⟩
    · rw [Finmap.mem_insert, hD]; push_cast at hi; omega
    · by_cases ha : a = 0 + c.1
      · subst ha; rw [Finmap.lookup_insert] at hl; cases hl; exact hv
      · rw [Finmap.lookup_insert_of_ne _ ha] at hl; exact hI a v hl
  · rw [if_neg hi, Option.getD_none]; exact ⟨hR, hD, hI⟩

theorem w87_mkWorld : ∀ (cells : List (Int × Int)) (σ : Store), W87 σ → (∀ c ∈ cells, inRange c.2 = true) →
    W87 (cells.foldl (fun σ c => (Store.store 0 c.1 c.2 σ).getD σ) σ)
  | [], σ, h, _ => h
  | c :: cs, σ, h, hv => by
    simp only [List.foldl_cons]
    exact w87_mkWorld cs _ (w87_store h c (hv c (by simp))) (fun c' hc' => hv c' (by simp [hc']))

theorem mkWorld_w87 (cells : List (Int × Int)) (hv : ∀ c ∈ cells, inRange c.2 = true) : W87 (mkWorld cells) :=
  w87_mkWorld cells _ w87_base hv

theorem W87.R0 {σ : Store} (h : W87 σ) : σ.R.lookup 0 = some 87 := by rw [h.1]; simp

theorem W87.lk {σ : Store} (h : W87 σ) {p : Int} {n : Nat} (hp : σ.R.lookup p = some n) : p = 0 ∧ n = 87 := by
  rw [h.1] at hp
  by_cases h1 : p = 0
  · subst h1; simp at hp; exact ⟨rfl, hp.symm⟩
  · simp [h1] at hp

theorem W87.wf {σ : Store} (h : W87 σ) : σ.WF where
  pos p n hp := by obtain ⟨-, rfl⟩ := h.lk hp; decide
  disj p q n m hp hq hpq := by
    obtain ⟨rfl, -⟩ := h.lk hp; obtain ⟨rfl, -⟩ := h.lk hq; exact absurd rfl hpq
  domH a := by
    rw [h.2.1]
    constructor
    · intro ha; exact ⟨0, 87, h.R0, by simp only [Store.InRegion]; push_cast; omega⟩
    · rintro ⟨p, n, hp, hin⟩
      obtain ⟨rfl, rfl⟩ := h.lk hp
      simp only [Store.InRegion] at hin; push_cast at hin; omega

theorem W87.placed {σ : Store} (h : W87 σ) : Placed σ := by
  intro p n hp; obtain ⟨rfl, rfl⟩ := h.lk hp; constructor <;> omega

theorem W87.cellsInR {σ : Store} (h : W87 σ) : CellsInR σ := fun a v hl => h.2.2 a v hl

end K7
