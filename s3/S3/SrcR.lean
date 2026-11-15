/-
  O95 compiler (compiler/DECLARATIONS-DRIVER.md, Addendum 6): σ.R is kept along an accepted program's run, carried through S2
  (`s2_run_R`, `compile_refines_mem_R`), so the driver needs L.live ⊇ Live σ lay at the START store only (`driver_x86_R`).
-/
import S3.Driver3

namespace S3
open VIRC VIRL1 VIRL2 X86

/-- **s2_run_R.** `s2_run` with the IR's region map kept on its SRel branch. -/
theorem s2_run_R {T lay τfin} (hT : T.length < 2 ^ 64) : ∀ {n I I' Wst}, SRel T lay τfin I Wst → IRN n I I' →
    ∃ m W', WN T m Wst W' ∧ ((m = n ∧ SRel T lay τfin I' W' ∧ I'.2.R = I.2.R) ∨ (m ≤ n ∧ W'.1 = .ovf))
  | _, _, _, Wst, h, .refl _ => ⟨0, Wst, .refl _, .inl ⟨rfl, h, rfl⟩⟩
  | _, I, _, Wst, h, .step hs hrest => by
      obtain ⟨st, σ⟩ := I
      cases st with
      | done v => simp [stepIR] at hs
      | run c ρ k =>
        rcases sim2_step hT h with ⟨hnone, _⟩ | ⟨I₁, h1, W₁, hW, rel⟩
        · rw [hnone] at hs; cases hs
        · rw [h1] at hs; cases hs
          have hR1 := stepIR_R (noAF_of_srel h) h1
          rcases rel with rel | ovf
          · obtain ⟨m, W', hw, r⟩ := s2_run_R hT rel hrest
            refine ⟨m + 1, W', .step hW hw, ?_⟩
            rcases r with ⟨rfl, r, hr⟩ | ⟨hle, r⟩
            · exact .inl ⟨rfl, r, hr.trans hR1⟩
            · exact .inr ⟨by omega, r⟩
          · exact ⟨1, W₁, .step hW (.refl _), .inr ⟨by omega, ovf⟩⟩

/-- **compile_refines_mem_R.** `compile_refines_mem` with σ'.R = σ.R on its finish branch. -/
theorem compile_refines_mem_R {lay σ m} (Γ₀ : Ctx S₂) (Δ₀ : List Bool) (e : Tm₂) (τ : Ty₂) (vs : List Atom₂) (ρw₀ : List W)
    (hty : HasType₂ Γ₀ Δ₀ e τ) (hw : Tm.wfB Γ₀.length e = true) (hf : Tm.fnOk e = true) (hok : Tm.ok2 e = true)
    (hlen : vs.length = Γ₀.length) (hg : Good vs) (hT : (lower2T Γ₀ e []).2.length < 2 ^ 64)
    (he : EnvRel (lower2T Γ₀ e []).2 lay σ Γ₀ (vs.map valOf) ρw₀) (hl : Layout σ lay) (hm : MemRel lay σ m) :
    ∀ a σ' w, Steps₂ (instL 0 vs e, σ) (.ret a, σ') → Atom.eval a = some w →
      (∃ k ws m', WN (lower2T Γ₀ e []).2 k (.run (lower2T Γ₀ e []).1 ρw₀ [], m) (.done ws, m') ∧
        VRel (lower2T Γ₀ e []).2 lay σ' τ (valOf w) ws ∧ Layout σ' lay ∧ MemRel lay σ' m' ∧ σ'.R = σ.R) ∨
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
  obtain ⟨j', W', hW', r⟩ := s2_run_R hT h0 hI
  rcases r with ⟨-, hrel, hRI⟩ | ⟨-, hov⟩
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
            exact .inl ⟨j' + 1, ws, _, by simpa using WN.trans hW' (.step hst (.refl _)), hv, hLM.1, hLM.2, hRI⟩
        · exact .inr ⟨j' + 1, W'', by simpa using WN.trans hW' (.step hst (.refl _)), hov⟩
  · exact .inr ⟨j', W', hW', hov⟩

set_option maxHeartbeats 1000000 in
open VIRL1 VIRL2 in
/-- **drv_iter_R.** `drv_iter` with σ₁.R = σ.R in its continue branch (Addendum 6). A ⟶₂ run of a step-shaped e from σ returning its capability, at a store related to the
    machine at the loop head: the machine reaches the head again with the returned words as the next arguments (related at σ₁),
    or leaves the loop at X with a status other than DONE. -/
theorem drv_iter_R (e : Tm₂) (hty : HasType₂ [tcap] [true] e tcap) (hw : Tm.wfB [tcap].length e = true)
    (hf : Tm.fnOk e = true) (hok : Tm.ok2 e = true) (hT : (lower2T [tcap] e []).2.length < 2 ^ 64) {p : Int} {σ σ₁ : Store}
    (hs : Steps₂ (instL 0 [(Atom.const (.cap p) : Atom₂)] e, σ) (.ret (.const (.cap p)), σ₁))
    {lay : Int → W} {m : WMem} {ρw : List W}
    (he : EnvRel (lower2T [tcap] e []).2 lay σ [tcap] ([(Atom.const (.cap p) : Atom₂)].map valOf) ρw)
    (hl : Layout σ lay) (hm : MemRel lay σ m)
    {ilen : X86.Op → Nat} {base : W} {C : Ctx3} {P : Program} {L : Lay3} {H X : W}
    (hCdef : C = ctxOf ilen (lower2T [tcap] e []).2 (lower2T [tcap] e []).1 base)
    (hP : P = lower3 ilen (lower2T [tcap] e []).2 (lower2T [tcap] e []).1 base) (hC : ∀ o, 1 ≤ ilen o)
    (hb : bytes C (allCode C (lower2T [tcap] e []).2 (lower2T [tcap] e []).1) < 2 ^ 64)
    (hNm : needW (lower2T [tcap] e []).1 ≤ L.bufN) (hNt : ∀ x ∈ (lower2T [tcap] e []).2, needW x.2 ≤ L.bufN)
    (hL : L.Ok) (hcanon : ∀ a i, P.at? a = some i → canonical a = true) (hretc : canonical L.ret0 = true)
    (hstub : L.stubRet = base + BitVec.ofNat 64 (bytes C (stubHead C)))
    (hcode : CodeAt C P H (loopCode base L.env0 X H)) (hbase : canonical base = true) (hX : canonical X = true)
    (hH : canonical H = true) (hret : L.ret0 = H + 5) (hN : 2 ≤ L.bufN) (hE : L.env0.toNat + 8 * 2 ≤ L.envTop.toNat)
    (hlive : ∀ a, VIRBridge.Live σ lay a → L.live a) {s : Cpu} (hA : AtHead L H ρw m s) :
    ∃ n, (∃ ρw' m', AtHead L H ρw' m' (runP P n s) ∧
        EnvRel (lower2T [tcap] e []).2 lay σ₁ [tcap] ([(Atom.const (.cap p) : Atom₂)].map valOf) ρw' ∧
        Layout σ₁ lay ∧ MemRel lay σ₁ m' ∧ σ₁.R = σ.R) ∨
      (∃ code, code ≠ 0 ∧ (runP P n s).rip = X ∧ (runP P n s).stopped = false ∧ rd (runP P n s).mem L.cb = code) := by
  obtain ⟨hDC, hrip1⟩ := head_call hL hA (by rw [hA.rip]; exact hcode) hbase hret
  have h0 := s2_init [tcap] [true] e tcap ([(Atom.const (.cap p) : Atom₂)].map valOf) ρw hty hw hf hok he hl hm
  have hcT : CodeAt C P L.ret0 (loopTail L.env0 X H) := by
    have h1 : CodeAt C P H (.callA base :: loopTail L.env0 X H) := hcode
    have h2 := codeAt_tail h1
    simp only [AI.size] at h2
    rw [hret]; exact h2
  have r1 : ∀ k, runP P (1 + k) s = runP P k (stepP P s) := fun k => by rw [Nat.add_comm]; rfl
  rcases compile_refines_mem_R [tcap] [true] e tcap [.const (.cap p)] ρw hty hw hf hok rfl (good_cap1 p) hT he hl hm
      _ σ₁ _ hs rfl with ⟨k, ws, m₁, hWN, hv, hl₁, hm₁, hR₁⟩ | ⟨k, W', hWN, hov⟩
  · have he₁ : EnvRel (lower2T [tcap] e []).2 lay σ₁ [tcap] ([(Atom.const (.cap p) : Atom₂)].map valOf) ws := by
      have := EnvRel.cons (ρw := []) hv .nil
      simpa using this
    obtain ⟨mm, ⟨-, hR3⟩ | ⟨Wr, Wr', j, -, -, -, hres, hcmr⟩⟩ :=
      s3_refines_from_s2 hCdef hP hC hb hT hNm hNt hL hcanon hretc hstub hDC hrip1 h0 hlive hWN
    · obtain ⟨hRet, hcm, -, hbuf⟩ := hR3
      cases hv with
      | cap hRp =>
        obtain ⟨w, hw', hAt⟩ := after_done hL hRet hcm hbuf (by rw [hRet.2.1]; exact hcT) hX hH hN hE hA.stk
        exact ⟨1 + mm + 10, .inl ⟨_, m₁, by rw [runP_add, r1, hw']; exact hAt, he₁, hl₁, hm₁, hR₁⟩⟩
    · obtain ⟨v, hv', hvs, hvrip, hvcb⟩ := after_exit hres hcmr (by rw [hres.2.1]; exact hcT) hX (by decide)
      exact ⟨1 + mm + 4, .inr ⟨stRes, by decide, by rw [runP_add, r1, hv']; exact hvrip, by rw [runP_add, r1, hv']; exact hvs,
        by rw [runP_add, r1, hv']; exact hvcb⟩⟩
  · obtain ⟨st, m'⟩ := W'
    simp only at hov; subst hov
    obtain ⟨mm, ⟨-, hR3⟩ | ⟨Wr, Wr', j, -, -, -, hres, hcmr⟩⟩ :=
      s3_refines_from_s2 hCdef hP hC hb hT hNm hNt hL hcanon hretc hstub hDC hrip1 h0 hlive hWN
    · obtain ⟨hRet, hcm⟩ := hR3
      obtain ⟨v, hv', hvs, hvrip, hvcb⟩ := after_exit hRet hcm (by rw [hRet.2.1]; exact hcT) hX (by decide)
      exact ⟨1 + mm + 4, .inr ⟨stOvf, by decide, by rw [runP_add, r1, hv']; exact hvrip, by rw [runP_add, r1, hv']; exact hvs,
        by rw [runP_add, r1, hv']; exact hvcb⟩⟩
    · obtain ⟨v, hv', hvs, hvrip, hvcb⟩ := after_exit hres hcmr (by rw [hres.2.1]; exact hcT) hX (by decide)
      exact ⟨1 + mm + 4, .inr ⟨stRes, by decide, by rw [runP_add, r1, hv']; exact hvrip, by rw [runP_add, r1, hv']; exact hvs,
        by rw [runP_add, r1, hv']; exact hvcb⟩⟩

set_option maxHeartbeats 1000000 in
open VIRL1 VIRL2 in
/-- **driver_x86_R.** `driver_x86` with L.live covering the START store only (DECLARATIONS-DRIVER Addendum 6). For a step-shaped e and k chained ⟶₂
    runs `IterRel e p k σ σ'`, from a machine at the loop head whose argument words and memory are related to σ: the machine reaches
    the head again after all k iterations with its memory related to σ', or some iteration leaves the loop at X with a status
    other than DONE (FAULT, OVF or RES). Premises: the compiler's on e, S3's on `lower3` and the layout, the loop's code at H, and
    L.live covering the live cells of every store the iteration reaches. Names no program. -/
theorem driver_x86_R (e : Tm₂) (hty : HasType₂ [tcap] [true] e tcap) (hw : Tm.wfB [tcap].length e = true)
    (hf : Tm.fnOk e = true) (hok : Tm.ok2 e = true) (hT : (lower2T [tcap] e []).2.length < 2 ^ 64) {p : Int}
    {lay : Int → W} {ilen : X86.Op → Nat} {base : W} {C : Ctx3} {P : Program} {L : Lay3} {H X : W}
    (hCdef : C = ctxOf ilen (lower2T [tcap] e []).2 (lower2T [tcap] e []).1 base)
    (hP : P = lower3 ilen (lower2T [tcap] e []).2 (lower2T [tcap] e []).1 base) (hC : ∀ o, 1 ≤ ilen o)
    (hb : bytes C (allCode C (lower2T [tcap] e []).2 (lower2T [tcap] e []).1) < 2 ^ 64)
    (hNm : needW (lower2T [tcap] e []).1 ≤ L.bufN) (hNt : ∀ x ∈ (lower2T [tcap] e []).2, needW x.2 ≤ L.bufN)
    (hL : L.Ok) (hcanon : ∀ a i, P.at? a = some i → canonical a = true) (hretc : canonical L.ret0 = true)
    (hstub : L.stubRet = base + BitVec.ofNat 64 (bytes C (stubHead C)))
    (hcode : CodeAt C P H (loopCode base L.env0 X H)) (hbase : canonical base = true) (hX : canonical X = true)
    (hH : canonical H = true) (hret : L.ret0 = H + 5) (hN : 2 ≤ L.bufN) (hE : L.env0.toNat + 8 * 2 ≤ L.envTop.toNat) :
    ∀ {k : Nat} {σ σ' : Store}, IterRel e p k σ σ' →
      (∀ a, VIRBridge.Live σ lay a → L.live a) →
      ∀ {m : WMem} {ρw : List W} {s : Cpu},
      EnvRel (lower2T [tcap] e []).2 lay σ [tcap] ([(Atom.const (.cap p) : Atom₂)].map valOf) ρw →
      Layout σ lay → MemRel lay σ m → AtHead L H ρw m s →
      ∃ n, (∃ ρw' m', AtHead L H ρw' m' (runP P n s) ∧ Layout σ' lay ∧ MemRel lay σ' m') ∨
        (∃ code, code ≠ 0 ∧ (runP P n s).rip = X ∧ (runP P n s).stopped = false ∧ rd (runP P n s).mem L.cb = code) := by
  intro k σ σ' hI
  induction hI with
  | zero σ =>
    intro _ m ρw s _ hl hm hA
    exact ⟨0, .inl ⟨ρw, m, hA, hl, hm⟩⟩
  | succ hs hrest ih =>
    rename_i k₀ σ₀ σ₁ σ₂
    intro hlv m ρw s he hl hm hA
    obtain ⟨n₁, ⟨ρw', m', hA', he', hl', hm', hR'⟩ | hx⟩ :=
      drv_iter_R e hty hw hf hok hT hs he hl hm hCdef hP hC hb hNm hNt hL hcanon hretc hstub hcode hbase hX hH hret hN hE
        hlv hA
    · obtain ⟨n₂, r⟩ := ih (fun a ha => hlv a (live_of_R hR' a ha)) he' hl' hm' hA'
      exact ⟨n₁ + n₂, by rw [runP_add]; exact r⟩
    · exact ⟨n₁, .inr hx⟩

end S3
