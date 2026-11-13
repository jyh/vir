/-
  O95 compiler: S1 ∘ S2, ONE statement about the SOURCE program (compiler/DECLARATIONS-S2.md, "Added"). A program e is typed
  under its caller's context Γ₀. The caller supplies parameter VALUES vs (e.g. the router's world capability), and the
  source program that ⟶₂ runs is e with them instantiated (`instL 0 vs e`). The IR runs `lowerT e` in the environment
  `vs.map valOf`, and the word machine runs `lower2T Γ₀ e []` in the caller's word environment.
-/
import VIRC.S2

namespace VIRC
open VIRL1 VIRL2

/-- Instantiate the locals m, m+1, … with vs, outermost first (the order ⟶₂'s substitutions would leave them in). -/
def instL : Nat → List Atom₂ → Tm₂ → Tm₂
  | _, [], e => e
  | m, v :: vs, e => (instL (m + 1) vs e).subst m v

theorem TRel.inst : ∀ (vs : List Atom₂) (m : Nat) {env : List Atom₂} {c : Code} {e : Tm₂}, Closed vs → Closed env →
    TRel (m + vs.length) env c e → TRel m (vs ++ env) c (instL m vs e)
  | [], _, _, _, _, _, _, h => by simpa [instL] using h
  | v :: vs, m, env, c, e, hv, he, h => by
      have hvs : Closed vs := fun w hw => hv w (List.mem_cons_of_mem _ hw)
      have h' : TRel ((m + 1) + vs.length) env c e := by simpa [Nat.add_assoc, Nat.add_comm 1] using h
      have ih := TRel.inst vs (m + 1) hvs he h'
      have hc : Closed (vs ++ env) := fun w hw => by
        rcases List.mem_append.mp hw with h | h
        · exact hvs w h
        · exact he w h
      simpa [instL] using TRel.subst ih v hc

/-- **The compiler so far, S1 ∘ S2, about the SOURCE program.** For a program e, typed under Γ₀, closed below it, C2 and S2's
predicate, with caller values vs (closed, C2, self-evaluating), their IR images related to the caller's words (`EnvRel`),
a code table under 2⁶⁴ entries, and a layout satisfying the premise:
(1) a ⟶₂ run of the instantiated program that FINISHES with `ret a`, where a evaluates to w, is matched by a word-machine run
    that finishes with words related to w's IR image, or that reaches OVERFLOW;
(2) a ⟶₂ run that FAULTS is matched by a word-machine run reaching the FAULT exit or the OVERFLOW exit;
(3) n ⟶₂ steps are matched by at least n word-machine steps, or by a stop at OVERFLOW. -/
theorem compile_refines {lay σ m} (Γ₀ : Ctx S₂) (Δ₀ : List Bool) (e : Tm₂) (τ : Ty₂) (vs : List Atom₂) (ρw₀ : List W)
    (hty : HasType₂ Γ₀ Δ₀ e τ) (hw : Tm.wfB Γ₀.length e = true) (hf : Tm.fnOk e = true) (hok : Tm.ok2 e = true)
    (hlen : vs.length = Γ₀.length) (hg : Good vs) (hT : (lower2T Γ₀ e []).2.length < 2 ^ 64)
    (he : EnvRel (lower2T Γ₀ e []).2 lay σ Γ₀ (vs.map valOf) ρw₀) (hl : Layout σ lay) (hm : MemRel lay σ m) :
    let T := (lower2T Γ₀ e []).2
    let W₀ : WSt × WMem := (.run (lower2T Γ₀ e []).1 ρw₀ [], m)
    let src : Tm₂ := instL 0 vs e
    (∀ a σ' w, Steps₂ (src, σ) (.ret a, σ') → Atom.eval a = some w →
      ∃ k W', WN T k W₀ W' ∧ ((∃ ws m', W' = (.done ws, m') ∧ VRel T lay σ' τ (valOf w) ws) ∨ W'.1 = .ovf)) ∧
    (∀ S, Steps₂ (src, σ) S → Faults S → ∃ k W', WN T k W₀ W' ∧ (W'.1 = .fault ∨ W'.1 = .ovf)) ∧
    (∀ n S, SrcN n (src, σ) S → ∃ k W', WN T k W₀ W' ∧ (n ≤ k ∨ W'.1 = .ovf)) := by
  intro T W₀ src
  have hS1 : Match (.run (lowerT e) (vs.map valOf) [], σ) (src, σ) := by
    have hr := lowerT_rel e (n := 0 + vs.length) (by rw [hlen]; simpa using hw) hf
    have := TRel.inst vs 0 (env := []) hg.closed (by simp [Closed]) hr
    rw [List.append_nil] at this
    exact Match.mk (k := []) (fs := []) (σ := σ) hg this .nil
  obtain ⟨h1, h2, h3⟩ := s2_refines Γ₀ Δ₀ e τ (vs.map valOf) ρw₀ hty hw hf hok hT he hl hm
  refine ⟨fun a σ' w hs hw' => ?_, fun S hs hf' => ?_, fun n S hn => ?_⟩
  · obtain ⟨n, hn⟩ := SrcN.of_steps hs
    obtain ⟨j, I, -, hI, hmI⟩ := sim_n hn hS1
    exact h1 (j + 1) (valOf w) σ' (by simpa using IRN.trans hI (.step (match_ret hmI rfl hw') (.refl _)))
  · obtain ⟨n, hn⟩ := SrcN.of_steps hs
    obtain ⟨j, I, -, hI, hmI⟩ := sim_n hn hS1
    obtain ⟨n', c, ρ, k, σ'', h', hst⟩ := match_fault hmI hf'
    exact h2 _ c ρ k σ'' (IRN.trans hI h') hst
  · obtain ⟨j, I, hle, hI, -⟩ := sim_n hn hS1
    obtain ⟨k, W', hW, r⟩ := h3 j I hI
    rcases r with rfl | r
    · exact ⟨k, W', hW, .inl hle⟩
    · exact ⟨k, W', hW, .inr r⟩

/-- S1's converse from ANY matched start (here: a program with caller parameters), the proof of `s1_converse` with its
start generalized. -/
theorem s1_converse_from {I₀ : St × Store} {S₀ : Config} (h0 : Match I₀ S₀) {n v σ'} (hI : IRN n I₀ (.done v, σ')) :
    ∃ a w, Steps₂ S₀ (.ret a, σ') ∧ Atom.eval a = some w ∧ valOf w = v := by
  have hdone : stepIR (.done v, σ') = none := rfl
  have no_stuck_run : ∀ p c ρ k σ₀, IRN p I₀ (.run c ρ k, σ₀) → stepIR (.run c ρ k, σ₀) = none → False := by
    intro p c ρ k σ₀ hp hst
    obtain ⟨-, hr⟩ := IRN.det_stuck hp hst hI
    obtain ⟨-, hu⟩ := IRN.from_done hr
    cases hu
  rcases src_classify S₀ (n + 1) with ⟨c', hc'⟩ | ⟨k, c', -, hc', hs⟩
  · obtain ⟨m, I, hle, hm, -⟩ := sim_n hc' h0
    obtain ⟨hle', -⟩ := IRN.det_stuck hI hdone hm
    omega
  · obtain ⟨m, I, -, hm, hmatch⟩ := sim_n hc' h0
    obtain ⟨t, σ₀⟩ := c'
    by_cases hret : ∃ a, t = .ret a
    · obtain ⟨a, rfl⟩ := hret
      cases hw : Atom.eval a with
      | some w =>
        have hstep := match_ret hmatch (a := a) rfl hw
        have hrun : IRN (m + 1) I₀ (.done (valOf w), σ₀) := by simpa using IRN.trans hm (.step hstep (.refl _))
        obtain ⟨-, hr⟩ := IRN.det_stuck hI hdone hrun
        obtain ⟨-, hu⟩ := IRN.from_done hr
        simp only [Prod.mk.injEq, St.done.injEq] at hu
        obtain ⟨rfl, rfl⟩ := hu
        exact ⟨a, w, SrcN.to_steps hc', hw, rfl⟩
      | none =>
        obtain ⟨c, ρ, k', σ₁, rfl, hst⟩ := match_ret_none hmatch (a := a) rfl hw
        exact (no_stuck_run m c ρ k' σ₁ hm hst).elim
    · have hf : Faults (t, σ₀) := ⟨by cases t <;> simp_all [Tm.IsTerminal], fun c'' h => hs c'' h⟩
      obtain ⟨n', c, ρ, k', σ₁, h', hst⟩ := match_fault hmatch hf
      exact (no_stuck_run (m + n') c ρ k' σ₁ (IRN.trans hm h') hst).elim

/-- **The converse, about the SOURCE.** Under `compile_refines`'s premises, if the word machine FINISHES with words ws, then the
instantiated source program FINISHES under ⟶₂ with `ret a`, ⟨a⟩ = w, and ws is related to w's image at the same final store.
So every answer the compiled code gives is an answer the source gives. -/
theorem compile_converse {lay σ m} (Γ₀ : Ctx S₂) (Δ₀ : List Bool) (e : Tm₂) (τ : Ty₂) (vs : List Atom₂) (ρw₀ : List W)
    (hty : HasType₂ Γ₀ Δ₀ e τ) (hw : Tm.wfB Γ₀.length e = true) (hf : Tm.fnOk e = true) (hok : Tm.ok2 e = true)
    (hlen : vs.length = Γ₀.length) (hg : Good vs) (hT : (lower2T Γ₀ e []).2.length < 2 ^ 64)
    (he : EnvRel (lower2T Γ₀ e []).2 lay σ Γ₀ (vs.map valOf) ρw₀) (hl : Layout σ lay) (hm : MemRel lay σ m)
    {k ws m'} (hW : WN (lower2T Γ₀ e []).2 k (.run (lower2T Γ₀ e []).1 ρw₀ [], m) (.done ws, m')) :
    ∃ a w σ', Steps₂ (instL 0 vs e, σ) (.ret a, σ') ∧ Atom.eval a = some w ∧
      VRel (lower2T Γ₀ e []).2 lay σ' τ (valOf w) ws := by
  have hS1 : Match (.run (lowerT e) (vs.map valOf) [], σ) (instL 0 vs e, σ) := by
    have hr := lowerT_rel e (n := 0 + vs.length) (by rw [hlen]; simpa using hw) hf
    have := TRel.inst vs 0 (env := []) hg.closed (by simp [Closed]) hr
    rw [List.append_nil] at this
    exact Match.mk (k := []) (fs := []) (σ := σ) hg this .nil
  obtain ⟨j, v, σ', hI, hv⟩ := s2_converse hT (s2_init Γ₀ Δ₀ e τ (vs.map valOf) ρw₀ hty hw hf hok he hl hm) hW
  obtain ⟨a, w, hs, hw', rfl⟩ := s1_converse_from hS1 hI
  exact ⟨a, w, σ', hs, hw', hv⟩

end VIRC
