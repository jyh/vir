/-
  O95, row 298 (compiler/DECLARATIONS-K5.md Addendum 7), D-1: DEFLATE's loader premise DISCHARGED. Every world the iteration reaches
  keeps ONE region {p ↦ L0 n om}, is WF, and holds in-range cells (L-2 over each step's run, its source run in range by
  `deflate_inrange`), so the scaled loader (L-1) satisfies `Layout`/`MemRel` there and `deflate_noovf` applies with no loader
  hypothesis. The premise on the caller is the region's placement p.
-/
import K5.RunShape
import K5.DeflateNoOvf

namespace K5
open VIRL1 VIRL2 VIRC VIRDeflate VIRDeflate.Step

set_option maxRecDepth 100000 in
theorem stepT_tmOk : tmOk stepT = true := by decide

theorem closeAt_tmOk (p : Int) : tmOk (closeAt p stepT) = true :=
  tm_subst_ok (by simp [atomOk]) stepT 0 stepT_tmOk

theorem arr_getD_lt (A : Array Nat) (K : Nat) (hK : 0 < K) (hA : ∀ x ∈ A, x < K) (j : Nat) : A.getD j 0 < K := by
  unfold Array.getD
  split
  · exact hA _ (Array.getElem_mem _)
  · exact hK

theorem list_getD_lt (K : Nat) (hK : 0 < K) : ∀ (l : List Nat), (∀ x ∈ l, x < K) → ∀ j, l.getD j 0 < K
  | [], _, j => by simpa using hK
  | a :: l, h, 0 => by simpa using h a (List.mem_cons_self ..)
  | a :: l, h, j + 1 => by
      simpa using list_getD_lt K hK l (fun x hx => h x (List.mem_cons_of_mem _ hx)) j

theorem LBASE_lt : ∀ x ∈ LBASE, x < 65536 := by decide
theorem LEXTRA_lt : ∀ x ∈ LEXTRA, x < 65536 := by decide
theorem DBASE_lt : ∀ x ∈ DBASE, x < 65536 := by decide
theorem DEXTRA_lt : ∀ x ∈ DEXTRA, x < 65536 := by decide
theorem ORDER_lt : ∀ x ∈ ORDER, x < 65536 := by decide

set_option maxHeartbeats 2000000 in
theorem initCell_inR {b : Array Nat} {om : Nat} {lit : Bool} (hb : ∀ x ∈ b, x < 256) (hn32 : b.size < 2 ^ 32)
    (hom32 : om < 2 ^ 32) (i : Int) : inRange (initCell b om lit i) = true := by
  have h1 := arr_getD_lt b 256 (by omega) hb
  have h2 := arr_getD_lt LBASE 65536 (by omega) LBASE_lt
  have h3 := arr_getD_lt LEXTRA 65536 (by omega) LEXTRA_lt
  have h4 := arr_getD_lt DBASE 65536 (by omega) DBASE_lt
  have h5 := arr_getD_lt DEXTRA 65536 (by omega) DEXTRA_lt
  have h6 := list_getD_lt 65536 (by omega) ORDER ORDER_lt
  simp only [inRange, decide_eq_true_eq]
  unfold initCell X0
  dsimp only
  split_ifs
  all_goals first
    | (constructor <;> omega)
    | (have := h1 (i - 2080).toNat; constructor <;> omega)
    | (have := h2 (i - (2080 + b.size + om + 1393) - 16).toNat; constructor <;> omega)
    | (have := h3 (i - (2080 + b.size + om + 1393) - 45).toNat; constructor <;> omega)
    | (have := h4 (i - (2080 + b.size + om + 1393) - 74).toNat; constructor <;> omega)
    | (have := h5 (i - (2080 + b.size + om + 1393) - 104).toNat; constructor <;> omega)
    | (have := h6 (i - (2080 + b.size + om + 1393) - 134).toNat; constructor <;> omega)
    | (split <;> constructor <;> omega)

theorem lookup_single {p q : Int} {L n : Nat} (h : (Finmap.singleton p L : Finmap (fun _ : Int => Nat)).lookup q = some n) : q = p ∧ n = L := by
  by_cases hq : q = p
  · subst hq; rw [Finmap.lookup_singleton_eq] at h; exact ⟨rfl, (Option.some.inj h).symm⟩
  · have : (Finmap.singleton p L : Finmap (fun _ : Int => Nat)).lookup q = none := Finmap.lookup_eq_none.mpr (by rw [Finmap.mem_singleton]; exact hq)
    rw [this] at h; cases h

set_option maxRecDepth 200000 in
theorem initStore_lookup (b : Array Nat) (om : Nat) (lit : Bool) (p a : Int) :
    (initStore b om lit p).H.lookup a =
      if p ≤ a ∧ a < p + ((L0 b.size om : Nat) : Int) then some (initCell b om lit (a - p)) else none := by
  simp only [initStore, lookup_fillF]
  split_ifs <;> simp

theorem initStore_R (b : Array Nat) (om : Nat) (lit : Bool) (p : Int) :
    (initStore b om lit p).R = Finmap.singleton p (L0 b.size om) := rfl

set_option maxRecDepth 200000 in
theorem initStore_shape {b : Array Nat} {om : Nat} {lit : Bool} (hb : ∀ x ∈ b, x < 256) (hn32 : b.size < 2 ^ 32)
    (hom32 : om < 2 ^ 32) (p : Int) : Shape (Finmap.singleton p (L0 b.size om)) (initStore b om lit p) := by
  refine ⟨initStore_R b om lit p, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro q n h
    rw [initStore_R] at h
    obtain ⟨-, rfl⟩ := lookup_single h
    unfold L0; omega
  · intro q r n m hq hr hne
    rw [initStore_R] at hq hr
    obtain ⟨rfl, -⟩ := lookup_single hq
    obtain ⟨rfl, -⟩ := lookup_single hr
    exact absurd rfl hne
  · intro a
    constructor
    · intro ha
      have hs := Finmap.lookup_isSome.mpr ha
      rw [initStore_lookup] at hs
      split_ifs at hs with hr
      · exact ⟨p, L0 b.size om, by rw [initStore_R]; exact Finmap.lookup_singleton_eq, hr⟩
      · simp at hs
    · rintro ⟨q, n, hq, hr⟩
      rw [initStore_R] at hq
      obtain ⟨rfl, rfl⟩ := lookup_single hq
      apply Finmap.lookup_isSome.mp
      simp only [Store.InRegion] at hr
      rw [initStore_lookup, if_pos hr]
      rfl
  · intro a v hv
    rw [initStore_lookup] at hv
    split_ifs at hv
    cases hv; exact initCell_inR hb hn32 hom32 _

theorem iterS_succ' (p : Int) : ∀ (k : Nat) (σ : Store), iterS p (k + 1) σ = (iterS p k σ).bind (stepS p)
  | 0, σ => by simp [iterS]
  | k + 1, σ => by
      rw [iterS]
      cases h : stepS p σ with
      | none => simp [iterS, h]
      | some σ₁ => simp only [Option.bind_some, iterS, h]; exact iterS_succ' p k σ₁

theorem stepS_steps {p : Int} {σ σ' : Store} (h : stepS p σ = some σ') :
    ∃ q, Steps₂ (closeAt p stepT, σ) (.ret (.const (.cap q)), σ') := by
  unfold stepS at h
  split at h
  · rename_i q σ'' hr
    split_ifs at h
    cases h
    exact ⟨q, steps_run KSTEP hr⟩
  · cases h

/-- Every world the iteration reaches keeps DEFLATE's one region, WF, and in-range cells. -/
theorem reach_shape {b : Array Nat} {om : Nat} {lit : Bool} {p : Int} (hb : ∀ x ∈ b, x < 256) (hn32 : b.size < 2 ^ 32)
    (hom32 : om < 2 ^ 32) : ∀ (k : Nat) (σ : Store), iterS p k (initStore b om lit p) = some σ →
      Shape (Finmap.singleton p (L0 b.size om)) σ := by
  intro k
  induction k with
  | zero => intro σ h; simp only [iterS, Option.some.injEq] at h; subst h; exact initStore_shape hb hn32 hom32 p
  | succ k ih =>
    intro σ h
    rw [iterS_succ'] at h
    cases h1 : iterS p k (initStore b om lit p) with
    | none => rw [h1] at h; cases h
    | some σ₁ =>
      rw [h1, Option.bind_some] at h
      obtain ⟨q, hs⟩ := stepS_steps h
      exact (run_shape hs (deflate_inrange hb hn32 hom32 k σ₁ h1) (closeAt_tmOk p) (ih σ₁ h1)).2

/-- **Row 298, D-1.** For bytes < 256, n, OUTMAX < 2³², either reading, a region placed in [0, 2⁶⁰), and every world σ the
iteration reaches: the scaled loader satisfies S2's layout premise at σ, and no word-machine run of the compiled step term from
it reaches the OVERFLOW exit. -/
theorem deflate_noovf_loaded {b : Array Nat} {om : Nat} {lit : Bool} {p : Int} (hb : ∀ x ∈ b, x < 256)
    (hn32 : b.size < 2 ^ 32) (hom32 : om < 2 ^ 32) (hp0 : 0 ≤ p) (hp1 : p + L0 b.size om ≤ 2 ^ 60) (k : Nat) (σ : Store)
    (h : iterS p k (initStore b om lit p) = some σ) :
    Layout σ scaleLay ∧ MemRel scaleLay σ (scaleMem σ) ∧
    ∀ j W', WN (lower2T [tcap] stepT []).2 j
      (.run (lower2T [tcap] stepT []).1 (capWords scaleLay p (L0 b.size om)) [], scaleMem σ) W' → W'.1 ≠ .ovf := by
  have hS := reach_shape hb hn32 hom32 k σ h
  have hpl : Placed σ := by
    intro q n hq
    rw [hS.reg] at hq
    obtain ⟨rfl, rfl⟩ := lookup_single hq
    exact ⟨hp0, hp1⟩
  obtain ⟨hl, hm⟩ := loader_ok hS.wf hpl hS.cells
  exact ⟨hl, hm, deflate_noovf hb hn32 hom32 k σ h hl hm⟩

end K5
