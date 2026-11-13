/-
  O95, DR-3 (compiler/DECLARATIONS-DRIVER.md Addendum 2; STATUS-vir 305): DEFLATE's k-step iteration through the driver's L2 half.
  The compiled step, run k times from the scaled loader's image of the initial store and fed each run's returned capability words,
  FINISHES every time, and the final memory is related to the store `iterS` reaches. Overflow is excluded by `deflate_noovf`.
-/
import K7.Driver
import K5.DeflateLoaded

namespace K7
open VIRL1 VIRL2 VIRC VIRDeflate VIRDeflate.Step K5

theorem stepS_steps_p {p : Int} {σ σ' : Store} (h : stepS p σ = some σ') :
    Steps₂ (closeAt p stepT, σ) (.ret (.const (.cap p)), σ') := by
  unfold stepS at h
  split at h
  · rename_i q σ'' hr
    split_ifs at h with hq
    cases h
    subst hq
    exact steps_run KSTEP hr
  · cases h

theorem envRel_cap_inv {T : Table} {lay : Int → W} {σ : Store} {p : Int} {ρw : List W}
    (h : EnvRel T lay σ [tcap] ([(Atom.const (.cap p) : Atom₂)].map valOf) ρw) :
    ∃ n, σ.R.lookup p = some n ∧ ρw = capWords lay p n := by
  simp only [List.map_cons, List.map_nil, valOf] at h
  cases h with
  | cons hv hs =>
    cases hs
    cases hv with
    | cap hR => exact ⟨_, hR, by simp [capWords]⟩

/-- **DR-3.** DEFLATE's k-step iteration, compiled and run by the driver loop from the scaled loader's image, finishes every call. -/
theorem deflate_driver {b : Array Nat} {om : Nat} {lit : Bool} {p : Int} (hb : ∀ x ∈ b, x < 256)
    (hn32 : b.size < 2 ^ 32) (hom32 : om < 2 ^ 32) (hp0 : 0 ≤ p) (hp1 : p + L0 b.size om ≤ 2 ^ 60) :
    ∀ (k : Nat) (σ : Store), iterS p k (initStore b om lit p) = some σ →
      ∃ ρw' m', WDone (lower2T [tcap] stepT []).2 (lower2T [tcap] stepT []).1 k (capWords scaleLay p (L0 b.size om))
          (scaleMem (initStore b om lit p)) ρw' m' ∧ MemRel scaleLay σ m' ∧
        EnvRel (lower2T [tcap] stepT []).2 scaleLay σ [tcap] ([(Atom.const (.cap p) : Atom₂)].map valOf) ρw' := by
  have hreg : ∀ k σ, iterS p k (initStore b om lit p) = some σ → σ.R.lookup p = some (L0 b.size om) := by
    intro k σ h
    rw [(reach_shape hb hn32 hom32 k σ h).reg]
    exact Finmap.lookup_singleton_eq
  intro k
  induction k with
  | zero =>
    intro σ h
    simp only [iterS, Option.some.injEq] at h
    subst h
    exact ⟨_, _, .zero _ _, (deflate_noovf_loaded hb hn32 hom32 hp0 hp1 0 _ rfl).2.1, K5.envRel_cap (hreg 0 _ rfl)⟩
  | succ k ih =>
    intro σ h
    rw [iterS_succ'] at h
    cases h1 : iterS p k (initStore b om lit p) with
    | none => rw [h1] at h; cases h
    | some σk =>
      rw [h1, Option.bind_some] at h
      obtain ⟨ρw', m', hD, hm', he'⟩ := ih σk h1
      have hl : Layout σk scaleLay := (deflate_noovf_loaded hb hn32 hom32 hp0 hp1 k σk h1).1
      have hs := stepS_steps_p h
      rw [← stepT_inst] at hs
      rcases compile_refines_mem [tcap] [true] stepT tcap [.const (.cap p)] ρw' stepT_typed stepT_wfB stepT_fnOk stepT_ok2
          rfl (good_cap1 p) stepT_table he' hl hm' _ σ _ hs rfl with ⟨j, ws, m₂, hWN, hv, -, hm₂⟩ | ⟨j, W', hWN, hov⟩
      · refine ⟨ws, m₂, hD.snoc hWN, hm₂, ?_⟩
        have := EnvRel.cons (ρw := []) hv .nil
        simpa using this
      · exfalso
        obtain ⟨n, hn, rfl⟩ := envRel_cap_inv he'
        rw [hreg k σk h1] at hn
        cases hn
        exact deflate_noovf hb hn32 hom32 k σk h1 hl hm' j W' hWN hov

end K7
