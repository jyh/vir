/-
  O95 compiler S3 (compiler/DECLARATIONS-S3.md, Addendum 14): StepOk's static half. `needW c` bounds every BUF demand of c's
  steps; `NeedOk` (current and pending codes within |BUF|) is preserved by every word step, so a static check on main and the table
  bodies gives StepOk's `need` conjuncts at every reached state. `StepSem` is the half S2's relation supplies.
-/
import S3.Place3

namespace S3
open VIRC X86

def needW : WCode → Nat
  | .ret o => need o
  | .letE c₁ c₂ => max (needW c₁) (needW c₂)
  | .load _ idx k => max (need idx) (needW k)
  | .store _ idx v k => max (max (need idx) (1 + need v)) (needW k)
  | .app f x => need x + need f
  | .ite o c₁ c₂ => max (need o) (max (needW c₁) (needW c₂))
  | .case o _ _ c₁ c₂ => max (need o) (max (needW c₁) (needW c₂))

/-- The current code and every pending continuation's code demand at most N BUF slots. -/
def NeedOk (N : Nat) : WSt → Prop
  | .run c _ k => needW c ≤ N ∧ ∀ e ∈ k, needW e.1 ≤ N
  | _ => True

/-- StepOk's semantic half (from S2's `SRel`, Addendum 14). -/
def StepSem (L : Lay3) : WSt → Prop
  | .run (.load off _ _) ρ _ => CapLive L ρ off
  | .run (.store off idx _ _) ρ _ => CapLive L ρ off ∧ evalW ρ idx ≠ .bad
  | .run (.app f _) ρ _ => evalW ρ f ≠ .bad
  | _ => True

theorem stepOk_of {L : Lay3} {w : WSt} (hn : NeedOk L.bufN w) (hs : StepSem L w) : StepOk L w := by
  match w with
  | .done _ => trivial
  | .fault => trivial
  | .ovf => trivial
  | .run c ρ k =>
    obtain ⟨hc, _⟩ := hn
    cases c <;> simp only [StepOk, StepSem, needW] at hc hs ⊢ <;>
      first | omega | trivial | exact ⟨by omega, hs⟩ | exact ⟨by omega, by omega, hs.1, hs.2⟩

theorem needOk_step {tbl : Table} {N : Nat} (hT : ∀ e ∈ tbl, needW e.2 ≤ N) {W W' : WSt × WMem} (h : NeedOk N W.1)
    (hs : stepW tbl W = some W') : NeedOk N W'.1 := by
  obtain ⟨w, m⟩ := W
  cases w with
  | done _ => simp [stepW] at hs
  | fault => simp [stepW] at hs
  | ovf => simp [stepW] at hs
  | run c ρ k =>
    obtain ⟨hc, hk⟩ := h
    cases c with
    | app f x =>
      simp only [stepW] at hs
      cases hf : evalW ρ f <;> cases hx : evalW ρ x <;> simp only [hf, hx] at hs <;> (try simp at hs) <;>
        (try (subst hs; trivial))
      rename_i fs ws
      rcases fs with _ | ⟨l, _ | ⟨_, _⟩⟩ <;> simp at hs
      cases ht : tbl[l.toNat]? with
      | none => simp [ht] at hs
      | some e =>
        obtain ⟨fx, b⟩ := e
        have hb := hT _ (List.mem_of_getElem? ht)
        cases fx <;> simp [ht] at hs <;> subst hs <;> exact ⟨hb, hk⟩
    | _ =>
      simp only [stepW] at hs
      (try split at hs) <;> (try split at hs) <;> (try split at hs) <;> simp only [Option.some.injEq, reduceCtorEq] at hs <;>
        subst hs <;> simp_all +contextual [NeedOk, needW] <;> first | exact hk | exact hk.2

theorem needOk_run {tbl : Table} {N : Nat} (hT : ∀ e ∈ tbl, needW e.2 ≤ N) :
    ∀ {k : Nat} {W W₁ : WSt × WMem}, WN tbl k W W₁ → NeedOk N W.1 → NeedOk N W₁.1 := by
  intro k W W₁ h
  induction h with
  | refl => exact id
  | step hs _ ih => exact fun hn => ih (needOk_step hT hn hs)

/-- **s3_refines_lower3_static.** `s3_refines_lower3` with StepOk's BUF half discharged statically (Fragment3's BUF clause:
    main and every table body within |BUF|); StepSem along the run is what remains for S2's relation. -/
theorem s3_refines_lower3_static {ilen : Op → Nat} {tbl : Table} {main : WCode} {base : W} {C : Ctx3} {p : Program} {L : Lay3}
    (hCdef : C = ctxOf ilen tbl main base) (hp : p = lower3 ilen tbl main base) (hC : ∀ o, 1 ≤ ilen o)
    (hb : bytes C (allCode C tbl main) < 2 ^ 64) (hT64 : tbl.length < 2 ^ 64)
    (hNm : needW main ≤ L.bufN) (hNt : ∀ e ∈ tbl, needW e.2 ≤ L.bufN)
    (hL : L.Ok) (hcanon : ∀ a i, p.at? a = some i → canonical a = true) (hretc : canonical L.ret0 = true)
    (hstub : L.stubRet = base + BitVec.ofNat 64 (bytes C (stubHead C)))
    {ρ₀ : List W} {wm : WMem} {s : Cpu} (hD : DriverCall L ρ₀ wm s) (hrip : s.rip = base)
    {n : Nat} {Wf : WSt × WMem} (hrun : WN tbl n (.run main ρ₀ [], wm) Wf)
    (hsem : ∀ k W₁, WN tbl k (.run main ρ₀ [], wm) W₁ → StepSem L W₁.1) :
    ∃ m, (n + 3 ≤ m ∧ R3 C p L Wf (runP p m s)) ∨
      (∃ Wr Wr' k, WN tbl k (.run main ρ₀ [], wm) Wr ∧ stepW tbl Wr = some Wr' ∧ ResWhy L Wr.1 ∧ ResExit L (runP p m s) ∧
        Common L Wr'.2 (runP p m s)) :=
  s3_refines_lower3 (bc := true) hCdef hp hC hb hT64 hL hcanon hretc hstub hD hrip hrun
    (fun k W₁ hk => stepOk_of (needOk_run hNt hk ⟨hNm, by simp⟩) (hsem k W₁ hk))
    (fun h => by subst hCdef; simp [ctxOf, ctxOfB] at h)


/-- **s3_refines_lower3_staticB** (OBJECT-NOCHECK): `s3_refines_lower3_static` for `lower3B b`, given that no reached word state is FAULT when `b = false`. -/
theorem s3_refines_lower3_staticB {b : Bool} {ilen : Op → Nat} {tbl : Table} {main : WCode} {base : W} {C : Ctx3} {p : Program} {L : Lay3}
    (hCdef : C = ctxOfB b ilen tbl main base) (hp : p = lower3B b ilen tbl main base) (hC : ∀ o, 1 ≤ ilen o)
    (hb : bytes C (allCode C tbl main) < 2 ^ 64) (hT64 : tbl.length < 2 ^ 64)
    (hNm : needW main ≤ L.bufN) (hNt : ∀ e ∈ tbl, needW e.2 ≤ L.bufN)
    (hL : L.Ok) (hcanon : ∀ a i, p.at? a = some i → canonical a = true) (hretc : canonical L.ret0 = true)
    (hstub : L.stubRet = base + BitVec.ofNat 64 (bytes C (stubHead C)))
    {ρ₀ : List W} {wm : WMem} {s : Cpu} (hD : DriverCall L ρ₀ wm s) (hrip : s.rip = base)
    {n : Nat} {Wf : WSt × WMem} (hrun : WN tbl n (.run main ρ₀ [], wm) Wf)
    (hsem : ∀ k W₁, WN tbl k (.run main ρ₀ [], wm) W₁ → StepSem L W₁.1)
    (hnf : C.chk = false → ∀ k W₁, WN tbl k (.run main ρ₀ [], wm) W₁ → W₁.1 ≠ .fault) :
    ∃ m, (n + 3 ≤ m ∧ R3 C p L Wf (runP p m s)) ∨
      (∃ Wr Wr' k, WN tbl k (.run main ρ₀ [], wm) Wr ∧ stepW tbl Wr = some Wr' ∧ ResWhy L Wr.1 ∧ ResExit L (runP p m s) ∧
        Common L Wr'.2 (runP p m s)) :=
  s3_refines_lower3 hCdef hp hC hb hT64 hL hcanon hretc hstub hD hrip hrun
    (fun k W₁ hk => stepOk_of (needOk_run hNt hk ⟨hNm, by simp⟩) (hsem k W₁ hk)) hnf

end S3
