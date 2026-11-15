/-
  O95, STATUS-vir 374 (compiler/DECLARATIONS-K7.md, Addendum 6): the router SERVED k times at the x86 machine. One finishing call
  of F keeps `RInv` (W87, the wire bytes, R4's premises), so F's iteration exists for every k (`router_iter`), and the driver loop
  carries each call to the machine DONE-only (`drv_iter_D`: OVF by `router_inR`, RES by `resWhy_false`). A router result, beside K7.
-/
import K7.RouterR4
import K7.DriverD

namespace K7
open VIRL1 VIRL2 VIRL3 VIRC K5

/-- The router's invariant on a world: one 87-cell region at 0, wire bytes, and R4's premises (sender, topic < 4). -/
def RInv (σ : Store) : Prop := W87 σ ∧ WireB σ ∧ SvA (cells σ) 0 < 4 ∧ TvA (cells σ) 0 < 4

theorem cells_inR {σ : Store} (hW : W87 σ) (a : Int) : inRange (cells σ a) = true := by
  cases hl : σ.H.lookup a with
  | none => simp [cells, hl, inRange]
  | some v => simpa [cells, hl] using hW.2.2 a v hl

/-- `router_post` from a ⟶₂ run (the form IterRel carries). -/
theorem router_post_s {σ σ' : Store} (hI : RInv σ) (hs : Steps₂ (closeW F, σ) (.ret (.const (.cap 0)), σ')) :
    RegionAt 0 87 (postF (cells σ) 0) σ' := by
  obtain ⟨hW, hwire, hs4, ht4⟩ := hI
  have hb := wire_cells hW hwire
  have b7 := hb 7 (by decide) (by decide); have b8 := hb 8 (by decide) (by decide)
  have b9 := hb 9 (by decide) (by decide); have b10 := hb 10 (by decide) (by decide)
  have b11 := hb 11 (by decide) (by decide); have b12 := hb 12 (by decide) (by decide)
  have b13 := hb 13 (by decide) (by decide); have b14 := hb 14 (by decide) (by decide)
  have hs0 : 0 ≤ SvA (cells σ) 0 := by simp only [SvA, zero_add]; omega
  have ht0 : 0 ≤ TvA (cells σ) 0 := by simp only [TvA, zero_add]; omega
  have hdisj : Store.Disj σ Store.empty := ⟨(disj_empty_left σ).1.symm, (disj_empty_left σ).2.symm⟩
  obtain ⟨-, h2⟩ := R4 hs0 hs4 ht0 ht4 σ Store.empty (w87_regionAt hW) hdisj (by rw [store_empty_union_right]; exact hW.wf)
  have hs' : Steps₂ (closeAt 0 F, σ ⊎ Store.empty) (.ret (.const (.cap 0)), σ') := by
    rw [store_empty_union_right]; exact hs
  obtain ⟨v, σq, -, -, hσ', -, -, hq⟩ := h2 _ _ hs'
  rw [hσ', store_empty_union_right]; exact hq

theorem postF_inR {g : Int → Int} (hR : ∀ a, inRange (g a) = true) (a : Int) : inRange (postF g 0 a) = true := by
  unfold postF
  split_ifs with h1 h2
  · simp only [Function.update_apply]
    split_ifs
    · simp [inRange]
    · simp [inRange]
    · exact inR_sub1 h2.2.2.2 (hR _)
    · exact hR _
  · simp only [Function.update_apply]
    split_ifs
    · simp [inRange]
    · exact hR _
  · simp only [Function.update_apply]
    split_ifs
    · simp [inRange]
    · exact hR _

/-- **router_inv_step.** One finishing call of F keeps RInv. -/
theorem router_inv_step {σ σ' : Store} (hI : RInv σ) (hs : Steps₂ (closeW F, σ) (.ret (.const (.cap 0)), σ')) : RInv σ' := by
  have hp := router_post_s hI hs
  obtain ⟨hW, hwire, hs4, ht4⟩ := hI
  have hb := wire_cells hW hwire
  have hlk : ∀ a, 0 ≤ a → a < 87 → σ'.H.lookup a = some (postF (cells σ) 0 a) := fun a h0 h1 => by
    rw [hp.2 a, if_pos (by simp only [Store.InRegion]; push_cast; omega)]
  have hsv0 : 0 ≤ SvA (cells σ) 0 := by
    have b7 := hb 7 (by decide) (by decide); have b8 := hb 8 (by decide) (by decide)
    have b9 := hb 9 (by decide) (by decide); have b10 := hb 10 (by decide) (by decide)
    simp only [SvA, zero_add]; omega
  have hsame : ∀ i, 3 ≤ i → i < 67 → postF (cells σ) 0 i = cells σ i := fun i h0 h1 =>
    R5_contents (cells σ) 0 i (by simp only [bktA]; omega) (by omega) (by omega)
  have hcell : ∀ i, 3 ≤ i → i < 67 → cells σ' i = cells σ i := fun i h0 h1 => by
    simp only [cells] at *; rw [hlk i (by omega) (by omega), Option.getD_some]; exact hsame i h0 h1
  refine ⟨⟨fun p => ?_, fun a => ?_, fun a v hl => ?_⟩, fun i v h0 h1 hl => ?_, ?_, ?_⟩
  · rw [hp.1]
    by_cases hp0 : p = 0
    · subst hp0; simp
    · simp only [hp0, if_false]
      exact Finmap.lookup_eq_none.mpr (by rw [Finmap.mem_singleton]; exact hp0)
  · constructor
    · intro h
      obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (Finmap.lookup_isSome.mpr h)
      rw [hp.2 a] at hv
      split_ifs at hv with hin
      · simp only [Store.InRegion] at hin; push_cast at hin; omega
    · intro h
      exact Finmap.lookup_isSome.mp (by rw [hlk a h.1 h.2]; rfl)
  · rw [hp.2 a] at hl
    split_ifs at hl
    cases hl
    exact postF_inR (cells_inR hW) a
  · rw [hlk i (by omega) (by omega)] at hl
    cases hl
    rw [hsame i h0 h1]
    exact hb i h0 h1
  · simp only [SvA, zero_add] at hs4 ⊢
    rw [hcell 7 (by decide) (by decide), hcell 8 (by decide) (by decide), hcell 9 (by decide) (by decide),
      hcell 10 (by decide) (by decide)]
    exact hs4
  · simp only [TvA, zero_add] at ht4 ⊢
    rw [hcell 11 (by decide) (by decide), hcell 12 (by decide) (by decide), hcell 13 (by decide) (by decide),
      hcell 14 (by decide) (by decide)]
    exact ht4

/-- **router_iter.** From an RInv world, F's iteration exists for every k. -/
theorem router_iter : ∀ (k : Nat) (σ : Store), RInv σ → ∃ σ', IterRel F 0 k σ σ'
  | 0, σ, _ => ⟨σ, .zero σ⟩
  | k + 1, σ, hI => by
    obtain ⟨k0, σ1, hrun⟩ := router_halts hI.1 hI.2.1 hI.2.2.1 hI.2.2.2
    have hs : Steps₂ (closeW F, σ) (.ret (.const (.cap 0)), σ1) := by rw [← hrun]; exact run₂_steps k0 _
    obtain ⟨σ', hr⟩ := router_iter k σ1 (router_inv_step hI hs)
    exact ⟨σ', .succ hs hr⟩

set_option maxHeartbeats 1000000 in
open S3 X86 in
/-- **router_driver.** For F's iteration from an RInv world and a machine at the loop head related to it: after the k calls the
    machine is at the loop head again, related to the k-th store. DONE-only. -/
theorem router_driver
    {ilen : X86.Op → Nat} {base : W} {C : Ctx3} {P : Program} {L : Lay3} {H X : W}
    (hCdef : C = ctxOf ilen (lower2T [tcap] F []).2 (lower2T [tcap] F []).1 base)
    (hP : P = lower3 ilen (lower2T [tcap] F []).2 (lower2T [tcap] F []).1 base) (hC : ∀ o, 1 ≤ ilen o)
    (hb : bytes C (allCode C (lower2T [tcap] F []).2 (lower2T [tcap] F []).1) < 2 ^ 64)
    (hNm : needW (lower2T [tcap] F []).1 ≤ L.bufN) (hNt : ∀ x ∈ (lower2T [tcap] F []).2, needW x.2 ≤ L.bufN)
    (hL : L.Ok) (hcanon : ∀ a i, P.at? a = some i → canonical a = true) (hretc : canonical L.ret0 = true)
    (hstub : L.stubRet = base + BitVec.ofNat 64 (bytes C (stubHead C)))
    (hcode : CodeAt C P H (loopCode base L.env0 X H)) (hbase : canonical base = true) (hX : canonical X = true)
    (hH : canonical H = true) (hret : L.ret0 = H + 5) (hN : 2 ≤ L.bufN) (hE : L.env0.toNat + 8 * 2 ≤ L.envTop.toNat)
    (hEnv : 8 * envM (lower2T [tcap] F []).1 2 ≤ L.env0.toNat - L.envLo.toNat)
    (hStk : 16 * (frD (lower2T [tcap] F []).1 + 2) + 8 ≤ L.rsp0.toNat + 8 - L.stkLo.toNat) :
    ∀ {k : Nat} {σ σ' : Store}, IterRel F 0 k σ σ' → RInv σ →
      (∀ a, VIRBridge.Live σ scaleLay a → L.live a) →
      ∀ {m : WMem} {ρw : List W} {s : Cpu},
      EnvRel (lower2T [tcap] F []).2 scaleLay σ [tcap] ([(Atom.const (.cap 0) : Atom₂)].map valOf) ρw →
      Layout σ scaleLay → MemRel scaleLay σ m → AtHead L H ρw m s →
      ∃ n ρw' m', AtHead L H ρw' m' (runP P n s) ∧ Layout σ' scaleLay ∧ MemRel scaleLay σ' m' := by
  intro k σ σ' hI
  induction hI with
  | zero σ =>
    intro _ _ m ρw s _ hl hm hA
    exact ⟨0, ρw, m, hA, hl, hm⟩
  | succ hs hrest ih =>
    rename_i k₀ σ₀ σ₁ σ₂
    intro hinv hlv m ρw s he hl hm hA
    have hsrc : SrcInRange (instL 0 [(Atom.const (.cap 0) : Atom₂)] F, σ₀) := router_inR hinv.1 hinv.2.1
    obtain ⟨n₁, ρw', m', hA', he', hl', hm', hR'⟩ :=
      drv_iter_D F F_typed F_wfB F_fnOk F_ok2 F_table hs hsrc he hl hm hCdef hP hC hb hNm hNt hL hcanon hretc hstub hcode
        hbase hX hH hret hN hE hlv hA F_tbl_nil hEnv hStk
    obtain ⟨n₂, ρw'', m'', hA'', hl'', hm''⟩ :=
      ih (router_inv_step hinv hs) (fun a ha => hlv a (live_of_R hR' a ha)) he' hl' hm' hA'
    exact ⟨n₁ + n₂, ρw'', m'', by rw [runP_add]; exact hA'', hl'', hm''⟩

set_option maxHeartbeats 1000000 in
open S3 X86 in
/-- **router_served_x86.** From an RInv world's loader image at the loop head, for EVERY k the machine is at the loop head again
    after k calls of F, with its memory related to the k-th store of F's iteration. No OVF, no RES, no FAULT on any call. -/
theorem router_served_x86 {σ : Store} (hinv : RInv σ)
    {ilen : X86.Op → Nat} {base : W} {C : Ctx3} {P : Program} {L : Lay3} {H X : W}
    (hCdef : C = ctxOf ilen (lower2T [tcap] F []).2 (lower2T [tcap] F []).1 base)
    (hP : P = lower3 ilen (lower2T [tcap] F []).2 (lower2T [tcap] F []).1 base) (hC : ∀ o, 1 ≤ ilen o)
    (hb : bytes C (allCode C (lower2T [tcap] F []).2 (lower2T [tcap] F []).1) < 2 ^ 64)
    (hNm : needW (lower2T [tcap] F []).1 ≤ L.bufN) (hNt : ∀ x ∈ (lower2T [tcap] F []).2, needW x.2 ≤ L.bufN)
    (hL : L.Ok) (hcanon : ∀ a i, P.at? a = some i → canonical a = true) (hretc : canonical L.ret0 = true)
    (hstub : L.stubRet = base + BitVec.ofNat 64 (bytes C (stubHead C)))
    (hcode : CodeAt C P H (loopCode base L.env0 X H)) (hbase : canonical base = true) (hX : canonical X = true)
    (hH : canonical H = true) (hret : L.ret0 = H + 5) (hN : 2 ≤ L.bufN) (hE : L.env0.toNat + 8 * 2 ≤ L.envTop.toNat)
    (hEnv : 8 * envM (lower2T [tcap] F []).1 2 ≤ L.env0.toNat - L.envLo.toNat)
    (hStk : 16 * (frD (lower2T [tcap] F []).1 + 2) + 8 ≤ L.rsp0.toNat + 8 - L.stkLo.toNat)
    (hlive : ∀ a, VIRBridge.Live σ scaleLay a → L.live a)
    {s : Cpu} (hA : AtHead L H (capWords scaleLay 0 87) (scaleMem σ) s) (k : Nat) :
    ∃ σk n ρw' m', IterRel F 0 k σ σk ∧ AtHead L H ρw' m' (runP P n s) ∧ MemRel scaleLay σk m' := by
  obtain ⟨σk, hI⟩ := router_iter k σ hinv
  obtain ⟨hl, hm⟩ := loader_ok hinv.1.wf hinv.1.placed hinv.1.cellsInR
  have he := envRel_cap1 (T := (lower2T [tcap] F []).2) (lay := scaleLay) hinv.1.R0
  obtain ⟨n, ρw', m', hA', -, hm'⟩ := router_driver hCdef hP hC hb hNm hNt hL hcanon hretc hstub hcode hbase hX hH hret hN hE
    hEnv hStk hI hinv hlive he hl hm hA
  exact ⟨σk, n, ρw', m', hI, hA', hm'⟩

end K7
