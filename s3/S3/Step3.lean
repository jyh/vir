/-
  O95 compiler S3 (compiler/DECLARATIONS-S3.md, Addendum 12): one word step for every code form (`sim_step`), and word runs
  (`s3_run`): from an R3 state, the machine reaches R3 at the run's end in at least as many steps, or returns RES at a reached
  state whose `ResWhy` holds (ENV or STACK outgrown, a measure of that state).
-/
import S3.SimApp

namespace S3
open VIRC X86

/-- The per-step premises the simulation lemmas take (discharged from S2's `SRel` and `Fragment3.ok` at composition). -/
def StepOk (L : Lay3) : WSt → Prop
  | .run (.ret o) _ _ => need o ≤ L.bufN
  | .run (.letE _ _) _ _ => True
  | .run (.load off idx _) ρ _ => need idx ≤ L.bufN ∧ CapLive L ρ off
  | .run (.store off idx v _) ρ _ => need idx ≤ L.bufN ∧ 1 + need v ≤ L.bufN ∧ CapLive L ρ off ∧ evalW ρ idx ≠ .bad
  | .run (.app f x) ρ _ => need x + need f ≤ L.bufN ∧ evalW ρ f ≠ .bad
  | .run (.ite o _ _) _ _ => need o ≤ L.bufN
  | .run (.case o _ _ _ _) _ _ => need o ≤ L.bufN
  | _ => True

/-- A step's static prepend bound (Addendum 12). -/
def grow : WCode → Nat
  | .ret o => wid o
  | .letE _ _ => 0
  | .load _ _ _ => 1
  | .store _ _ _ _ => 2
  | .app _ x => wid x + 1
  | .ite _ _ _ => 0
  | .case o _ _ _ _ => wid o

/-- Why RES may be reached from a state: ENV outgrown with the step's prepend, or STACK outgrown with one more frame. -/
def ResWhy (L : Lay3) : WSt → Prop
  | .run c ρ k => EnvOver L ρ k (grow c) ∨ StkOver L ((c, ρ) :: k)
  | _ => False

theorem envOver_mono {L : Lay3} {ρ : List W} {k : List (WCode × List W)} {m m' : Nat} (h : EnvOver L ρ k m) (hm : m ≤ m') :
    EnvOver L ρ k m' := by
  simp only [EnvOver] at *; omega

theorem stepW_load_mem {tbl : Table} {off : Nat} {idx : WOpd} {c : WCode} {ρ : List W} {k : List (WCode × List W)} {wm : WMem}
    {W' : WSt × WMem} (h : stepW tbl (.run (.load off idx c) ρ k, wm) = some W') : W'.2 = wm := by
  simp only [stepW] at h
  split at h <;> (try split at h) <;> (try simp at h) <;> (try subst h) <;> rfl

theorem stepW_case_mem {tbl : Table} {o : WOpd} {n₁ n₂ : Nat} {c₁ c₂ : WCode} {ρ : List W} {k : List (WCode × List W)}
    {wm : WMem} {W' : WSt × WMem} (h : stepW tbl (.run (.case o n₁ n₂ c₁ c₂) ρ k, wm) = some W') : W'.2 = wm := by
  simp only [stepW] at h
  split at h <;> (try split at h) <;> (try split at h) <;> (try simp at h) <;> (try subst h) <;> rfl

theorem ret_resWhy {L : Lay3} {tbl : Table} {o : WOpd} {ρ : List W} {k : List (WCode × List W)} {wm : WMem}
    {W' : WSt × WMem} (hstep : stepW tbl (.run (.ret o) ρ k, wm) = some W') (h : RetOver L W'.1) : EnvOver L ρ k (wid o) := by
  simp only [stepW] at hstep
  cases ho : evalW ρ o with
  | bad => rw [ho] at hstep; cases k <;> simp at hstep
  | ovf => rw [ho] at hstep; cases k <;> simp at hstep <;> (subst hstep; simp [RetOver] at h)
  | ok ws =>
    rw [ho] at hstep
    have hl := evalW_length o ρ ws ho
    match k, hstep with
    | [], hstep => simp at hstep; subst hstep; simp [RetOver] at h
    | (c₂, ρ₂) :: k', hstep =>
      simp at hstep; subst hstep
      simp only [RetOver, EnvOver, kSize, List.length_append] at h ⊢; omega

theorem app_resWhy {L : Lay3} {tbl : Table} {f x : WOpd} {ρ : List W} {k : List (WCode × List W)} {wm : WMem}
    {W' : WSt × WMem} (hstep : stepW tbl (.run (.app f x) ρ k, wm) = some W') (h : RetOver L W'.1) :
    EnvOver L ρ k (wid x + 1) := by
  simp only [stepW] at hstep
  cases hf : evalW ρ f with
  | bad => cases hx : evalW ρ x <;> simp only [hf, hx] at hstep <;> (try simp at hstep) <;> (subst hstep; simp [RetOver] at h)
  | ovf => cases hx : evalW ρ x <;> simp only [hf, hx] at hstep <;> (try simp at hstep) <;> (subst hstep; simp [RetOver] at h)
  | ok fs =>
    cases hx : evalW ρ x with
    | bad => simp only [hf, hx] at hstep; rcases fs with _ | ⟨l, _ | ⟨_, _⟩⟩ <;> simp at hstep
    | ovf =>
      simp only [hf, hx] at hstep
      rcases fs with _ | ⟨l, _ | ⟨_, _⟩⟩ <;> simp at hstep <;> (subst hstep; simp [RetOver] at h)
    | ok ws =>
      simp only [hf, hx] at hstep
      have hl := evalW_length x ρ ws hx
      rcases fs with _ | ⟨l, _ | ⟨_, _⟩⟩
      · simp at hstep
      · cases ht : tbl[l.toNat]? with
        | none => simp [ht] at hstep
        | some e =>
          obtain ⟨fx, b⟩ := e
          cases fx <;> simp [ht] at hstep <;> subst hstep <;>
            simp only [RetOver, EnvOver, List.length_append, List.length_singleton] at h ⊢ <;> omega
      · simp at hstep

/-- **sim_step.** Every word step from an R3 state whose `StepOk` holds is simulated: the successor as an R3 state, or RES with
    `Common` at the successor's word memory and `ResWhy` of the state stepped from. -/
theorem sim_step {C : Ctx3} {p : Program} {L : Lay3} (E : StepEnv C p L) {tbl : Table} (hT : TblOk C p tbl)
    {W W' : WSt × WMem} {s : Cpu} (hR : R3 C p L W s) (hok : StepOk L W.1) (hstep : stepW tbl W = some W')
    (hnf : C.chk = false → W'.1 ≠ .fault) :
    ∃ n, 0 < n ∧ (R3 C p L W' (runP p n s) ∨ (ResExit L (runP p n s) ∧ Common L W'.2 (runP p n s) ∧ ResWhy L W.1)) := by
  obtain ⟨w, wm⟩ := W
  cases w with
  | done _ => simp [stepW] at hstep
  | fault => simp [stepW] at hstep
  | ovf => simp [stepW] at hstep
  | run c ρ k =>
    cases c with
    | ret o =>
      simp only [StepOk] at hok
      obtain ⟨n, hn, h | ⟨h1, h2, h3⟩⟩ := sim_ret E hR hok hstep
      · exact ⟨n, hn, Or.inl h⟩
      · exact ⟨n, hn, Or.inr ⟨h1, h2, Or.inl (ret_resWhy hstep h3)⟩⟩
    | letE c₁ c₂ =>
      obtain ⟨n, hn, h | ⟨h1, h2, h3⟩⟩ := sim_letE E hR hstep
      · exact ⟨n, hn, Or.inl h⟩
      · exact ⟨n, hn, Or.inr ⟨h1, h2, Or.inr (by simpa only [StkOver, List.length_cons] using h3)⟩⟩
    | load off idx c =>
      simp only [StepOk] at hok
      obtain ⟨n, hn, h | ⟨h1, h2, h3⟩⟩ := sim_load E hR hok.1 hok.2 hstep hnf
      · exact ⟨n, hn, Or.inl h⟩
      · exact ⟨n, hn, Or.inr ⟨h1, by rw [stepW_load_mem hstep]; exact h2, Or.inl h3⟩⟩
    | store off idx v c =>
      simp only [StepOk] at hok
      obtain ⟨n, hn, h | ⟨h1, h2, h3⟩⟩ := sim_store E hR hok.1 hok.2.1 hok.2.2.1 hok.2.2.2 hstep hnf
      · exact ⟨n, hn, Or.inl h⟩
      · exact ⟨n, hn, Or.inr ⟨h1, h2, Or.inl h3⟩⟩
    | app f x =>
      simp only [StepOk] at hok
      obtain ⟨n, hn, h | ⟨h1, h2, h3⟩⟩ := sim_app E hT hR hok.1 hok.2 hstep
      · exact ⟨n, hn, Or.inl h⟩
      · exact ⟨n, hn, Or.inr ⟨h1, h2, Or.inl (app_resWhy hstep h3)⟩⟩
    | ite o c₁ c₂ =>
      simp only [StepOk] at hok
      obtain ⟨n, hn, h⟩ := sim_ite E hR hok hstep
      exact ⟨n, hn, Or.inl h⟩
    | case o n₁ n₂ c₁ c₂ =>
      simp only [StepOk] at hok
      obtain ⟨n, hn, h | ⟨h1, h2, m, hm, h3⟩⟩ := sim_case E hR hok hstep
      · exact ⟨n, hn, Or.inl h⟩
      · exact ⟨n, hn, Or.inr ⟨h1, by rw [stepW_case_mem hstep]; exact h2, Or.inl (envOver_mono h3 hm)⟩⟩

/-- **s3_run.** A word run from an R3 state, with `StepOk` at every state it reaches, is matched: the machine reaches R3 at the
    run's end in at least as many steps, or returns RES at a reached state whose `ResWhy` holds. -/
theorem s3_run {C : Ctx3} {p : Program} {L : Lay3} (E : StepEnv C p L) {tbl : Table} (hT : TblOk C p tbl) :
    ∀ {n : Nat} {W Wf : WSt × WMem}, WN tbl n W Wf → ∀ s, R3 C p L W s → (∀ k W₁, WN tbl k W W₁ → StepOk L W₁.1) →
      (C.chk = false → ∀ k W₁, WN tbl k W W₁ → W₁.1 ≠ .fault) →
      ∃ m, (n ≤ m ∧ R3 C p L Wf (runP p m s)) ∨
        (∃ Wr Wr' k, WN tbl k W Wr ∧ stepW tbl Wr = some Wr' ∧ ResWhy L Wr.1 ∧ ResExit L (runP p m s) ∧
          Common L Wr'.2 (runP p m s)) := by
  intro n W Wf hWN
  induction hWN with
  | refl W => intro s hR _ _; exact ⟨0, Or.inl ⟨le_refl _, hR⟩⟩
  | step hst hrest ih =>
    intro s hR hok hnf
    obtain ⟨n₁, hn₁, h | ⟨h1, h2, h3⟩⟩ :=
      sim_step E hT hR (hok 0 _ (.refl _)) hst (fun hc => hnf hc 1 _ (.step hst (.refl _)))
    · obtain ⟨m, hm⟩ := ih _ h (fun k W₁ hk => hok (k + 1) W₁ (.step hst hk))
        (fun hc k W₁ hk => hnf hc (k + 1) W₁ (.step hst hk))
      refine ⟨n₁ + m, ?_⟩
      rcases hm with ⟨hle, hR'⟩ | ⟨Wr, Wr', k, hk, hs, hy, he, hc⟩
      · exact Or.inl ⟨by omega, by rw [runP_add]; exact hR'⟩
      · exact Or.inr ⟨Wr, Wr', k + 1, .step hst hk, hs, hy, by rw [runP_add]; exact he, by rw [runP_add]; exact hc⟩
    · exact ⟨n₁, Or.inr ⟨_, _, 0, .refl _, hst, h3, h1, h2⟩⟩

end S3
