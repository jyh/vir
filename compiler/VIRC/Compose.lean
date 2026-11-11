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

end VIRC
