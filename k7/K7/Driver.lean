/-
  O95, the driver theorem's L2 half (compiler/DECLARATIONS-DRIVER.md; STATUS-vir 304). GENERIC: names no program.
  DR-1 `compile_refines_mem`: compile_refines (1) with the END-STATE memory relation (Layout and MemRel at the final store), which
  Sim2's `SRel.done` does not carry (finding DR-0). Route: the IR run's last step is S1's `ret` from a matched run state; there
  `SRel.run` carries Layout/MemRel, and the word machine's `ret` to `done` leaves memory unchanged. Sim2/S2/Compose are not edited.
-/
import VIRC.NoOvfSrc

namespace K7
open VIRL1 VIRL2 VIRC

theorem stepW_done_mem {T : Table} {s : WSt} {m m' : WMem} {ws : List W} (h : stepW T (s, m) = some (.done ws, m')) :
    m' = m := by
  cases s with
  | run c ρ k =>
    cases c with
    | ret o =>
      simp only [stepW] at h
      split at h <;> simp_all
    | _ => simp only [stepW] at h; (repeat' split at h) <;> simp_all
  | _ => simp [stepW] at h

theorem stepIR_done_store {c : Code} {ρ : List VIRC.Val} {k : List Frame} {σ σ' : Store} {v : VIRC.Val}
    (h : stepIR (.run c ρ k, σ) = some (.done v, σ')) : σ' = σ := by
  cases c <;> cases k <;> simp only [stepIR] at h <;> (repeat' split at h) <;> (try simp_all)
  all_goals (simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at h
             obtain ⟨_, _, _, _, h1, _⟩ := h; cases h1)

/-- **DR-1.** compile_refines (1) with the final store's layout and memory relation. -/
theorem compile_refines_mem {lay σ m} (Γ₀ : Ctx S₂) (Δ₀ : List Bool) (e : Tm₂) (τ : Ty₂) (vs : List Atom₂) (ρw₀ : List W)
    (hty : HasType₂ Γ₀ Δ₀ e τ) (hw : Tm.wfB Γ₀.length e = true) (hf : Tm.fnOk e = true) (hok : Tm.ok2 e = true)
    (hlen : vs.length = Γ₀.length) (hg : Good vs) (hT : (lower2T Γ₀ e []).2.length < 2 ^ 64)
    (he : EnvRel (lower2T Γ₀ e []).2 lay σ Γ₀ (vs.map valOf) ρw₀) (hl : Layout σ lay) (hm : MemRel lay σ m) :
    ∀ a σ' w, Steps₂ (instL 0 vs e, σ) (.ret a, σ') → Atom.eval a = some w →
      (∃ k ws m', WN (lower2T Γ₀ e []).2 k (.run (lower2T Γ₀ e []).1 ρw₀ [], m) (.done ws, m') ∧
        VRel (lower2T Γ₀ e []).2 lay σ' τ (valOf w) ws ∧ Layout σ' lay ∧ MemRel lay σ' m') ∨
      (∃ k W', WN (lower2T Γ₀ e []).2 k (.run (lower2T Γ₀ e []).1 ρw₀ [], m) W' ∧ W'.1 = .ovf) := by
  intro a σ' w hs hw'
  have hS1 : Match (.run (lowerT e) (vs.map valOf) [], σ) (instL 0 vs e, σ) := by
    have hr := lowerT_rel e (n := 0 + vs.length) (by rw [hlen]; simpa using hw) hf
    have := TRel.inst vs 0 (env := []) hg.closed (by simp [Closed]) hr
    rw [List.append_nil] at this
    exact Match.mk (k := []) (fs := []) (σ := σ) hg this .nil
  obtain ⟨n, hn⟩ := SrcN.of_steps hs
  obtain ⟨j, I, -, hI, hmI⟩ := sim_n hn hS1
  have hlast : stepIR I = some (.done (valOf w), σ') := match_ret hmI rfl hw'
  have h0 := s2_init Γ₀ Δ₀ e τ (vs.map valOf) ρw₀ hty hw hf hok he hl hm
  obtain ⟨j', W', hW', r⟩ := s2_run hT h0 hI
  rcases r with ⟨-, hrel⟩ | ⟨-, hov⟩
  · obtain ⟨st, σ₁⟩ := I
    cases st with
    | done v => simp [stepIR] at hlast
    | run c ρ k =>
      have hσ : σ' = σ₁ := stepIR_done_store hlast
      subst hσ
      have hLM : Layout σ' lay ∧ MemRel lay σ' W'.2 := by
        cases hrel with
        | run _ _ hl' hm' => exact ⟨hl', hm'⟩
      rcases sim2_step hT hrel with ⟨hn', -⟩ | ⟨I', hI', W'', hst, hr''⟩
      · rw [hlast] at hn'; cases hn'
      · rw [hlast] at hI'
        cases hI'
        rcases hr'' with hS | hov
        · cases hS with
          | done hv =>
            rename_i ws m''
            obtain ⟨st', mW⟩ := W'
            have hmeq : m'' = mW := stepW_done_mem hst
            subst hmeq
            exact .inl ⟨j' + 1, ws, _, by simpa using WN.trans hW' (.step hst (.refl _)), hv, hLM.1, hLM.2⟩
        · exact .inr ⟨j' + 1, W'', by simpa using WN.trans hW' (.step hst (.refl _)), hov⟩
  · exact .inr ⟨j', W', hW', hov⟩

/-- k ⟶₂ runs of a step-shaped program, each from the previous store, each returning the capability it was given. -/
inductive IterRel (e : Tm₂) (p : Int) : Nat → Store → Store → Prop where
  | zero (σ : Store) : IterRel e p 0 σ σ
  | succ {k : Nat} {σ σ₁ σ' : Store} : Steps₂ (instL 0 [(Atom.const (.cap p) : Atom₂)] e, σ) (.ret (.const (.cap p)), σ₁) →
      IterRel e p k σ₁ σ' → IterRel e p (k + 1) σ σ'

/-- k chained word runs of compiled code wc: each FINISHES, and its result words are the next call's argument words (the driver
loop: call, test the exit, jump back with the returned capability). -/
inductive WDone (T : Table) (wc : WCode) : Nat → List W → WMem → List W → WMem → Prop where
  | zero (ρw : List W) (m : WMem) : WDone T wc 0 ρw m ρw m
  | succ {k j : Nat} {ρw ws ρw' : List W} {m m₁ m' : WMem} : WN T j (.run wc ρw [], m) (.done ws, m₁) →
      WDone T wc k ws m₁ ρw' m' → WDone T wc (k + 1) ρw m ρw' m'

theorem good_cap1 (p : Int) : Good [(Atom.const (.cap p) : Atom₂)] := by
  intro w hw
  simp only [List.mem_singleton] at hw
  subst hw
  exact ⟨rfl, rfl, rfl⟩

/-- **DR-2, the driver's L2 half.** For a step-shaped program e (typed [tcap] ⊢ e : tcap, with the compiler's side conditions):
k chained ⟶₂ runs from σ to σ' are matched by k chained word runs of the compiled step that all FINISH, ending at a memory related
to σ' (Layout, MemRel), or by i < k finished runs followed by a run that reaches OVERFLOW. Names no program. -/
theorem driver_l2 (e : Tm₂) (hty : HasType₂ [tcap] [true] e tcap) (hw : Tm.wfB [tcap].length e = true)
    (hf : Tm.fnOk e = true) (hok : Tm.ok2 e = true) (hT : (lower2T [tcap] e []).2.length < 2 ^ 64) {p : Int} :
    ∀ {k σ σ'}, IterRel e p k σ σ' → ∀ {lay m ρw},
      EnvRel (lower2T [tcap] e []).2 lay σ [tcap] ([(Atom.const (.cap p) : Atom₂)].map valOf) ρw →
      Layout σ lay → MemRel lay σ m →
      (∃ ρw' m', WDone (lower2T [tcap] e []).2 (lower2T [tcap] e []).1 k ρw m ρw' m' ∧ Layout σ' lay ∧ MemRel lay σ' m') ∨
      (∃ i ρw₁ m₁ j W', i < k ∧ WDone (lower2T [tcap] e []).2 (lower2T [tcap] e []).1 i ρw m ρw₁ m₁ ∧
        WN (lower2T [tcap] e []).2 j (.run (lower2T [tcap] e []).1 ρw₁ [], m₁) W' ∧ W'.1 = .ovf)
  | _, _, _, .zero σ, _, m, ρw, _, hl, hm => .inl ⟨ρw, m, .zero ρw m, hl, hm⟩
  | _, _, _, .succ (k := k) (σ₁ := σ₁) hs hrest, lay, m, ρw, he, hl, hm => by
      rcases compile_refines_mem [tcap] [true] e tcap [.const (.cap p)] ρw hty hw hf hok rfl (good_cap1 p) hT he hl hm
        _ σ₁ _ hs rfl with ⟨j, ws, m₁, hWN, hv, hl₁, hm₁⟩ | ⟨j, W', hWN, hov⟩
      · have he₁ : EnvRel (lower2T [tcap] e []).2 lay σ₁ [tcap] ([(Atom.const (.cap p) : Atom₂)].map valOf) ws := by
          have := EnvRel.cons (ρw := []) hv .nil
          simpa using this
        rcases driver_l2 e hty hw hf hok hT hrest he₁ hl₁ hm₁ with ⟨ρw', m', hD, hl', hm'⟩ | ⟨i, ρw₁, m₂, j', W', hi, hD, hW, hov⟩
        · exact .inl ⟨ρw', m', .succ hWN hD, hl', hm'⟩
        · exact .inr ⟨i + 1, ρw₁, m₂, j', W', by omega, .succ hWN hD, hW, hov⟩
      · exact .inr ⟨0, ρw, m, j, W', by omega, .zero ρw m, hWN, hov⟩

end K7
