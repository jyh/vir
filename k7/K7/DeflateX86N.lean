/-
  O95, STATUS-vir 371 (compiler/DECLARATIONS-DRIVER.md, Addendum 8): DEFLATE at the x86 machine with OVF EXCLUDED. Induction on k,
  `S3.drv_iter_N` at each step with SrcInRange from K5's `deflate_inrange`. The one non-DONE exit left is RES (not excluded).
-/
import K7.DeflateX86
import K5.DeflateInRange
import S3.DriverN

namespace K7
open VIRL1 VIRL2 VIRC VIRDeflate VIRDeflate.Step K5

set_option maxHeartbeats 1000000 in
open S3 X86 in
/-- **deflate_x86_N.** For DEFLATE's premises and the driver's S3 premises on stepT's lowering, from a machine at the loop head on the
    loader's image of `initStore b om lit p`: for every k with `iterS p k (initStore …) = some σ`, the machine reaches the head again
    with its memory related to σ, or it has left the loop at X with cb = stRes. OVF is excluded; RES is not. -/
theorem deflate_x86_N {b : Array Nat} {om : Nat} {lit : Bool} {p : Int} (hbyte : ∀ x ∈ b, x < 256)
    (hn32 : b.size < 2 ^ 32) (hom32 : om < 2 ^ 32) (hp0 : 0 ≤ p) (hp1 : p + L0 b.size om ≤ 2 ^ 60)
    {ilen : X86.Op → Nat} {base : W} {C : Ctx3} {P : Program} {L : Lay3} {H X : W}
    (hCdef : C = ctxOf ilen (lower2T [tcap] stepT []).2 (lower2T [tcap] stepT []).1 base)
    (hP : P = lower3 ilen (lower2T [tcap] stepT []).2 (lower2T [tcap] stepT []).1 base) (hC : ∀ o, 1 ≤ ilen o)
    (hb : bytes C (allCode C (lower2T [tcap] stepT []).2 (lower2T [tcap] stepT []).1) < 2 ^ 64)
    (hNm : needW (lower2T [tcap] stepT []).1 ≤ L.bufN) (hNt : ∀ x ∈ (lower2T [tcap] stepT []).2, needW x.2 ≤ L.bufN)
    (hL : L.Ok) (hcanon : ∀ a i, P.at? a = some i → canonical a = true) (hretc : canonical L.ret0 = true)
    (hstub : L.stubRet = base + BitVec.ofNat 64 (bytes C (stubHead C)))
    (hcode : CodeAt C P H (loopCode base L.env0 X H)) (hbase : canonical base = true) (hX : canonical X = true)
    (hH : canonical H = true) (hret : L.ret0 = H + 5) (hN : 2 ≤ L.bufN) (hE : L.env0.toNat + 8 * 2 ≤ L.envTop.toNat)
    (hlv : ∀ a, VIRBridge.Live (initStore b om lit p) scaleLay a → L.live a)
    {s : Cpu} (hA : AtHead L H (capWords scaleLay p (L0 b.size om)) (scaleMem (initStore b om lit p)) s) :
    ∀ (k : Nat) (σ : Store), iterS p k (initStore b om lit p) = some σ →
      ∃ n, (∃ ρw' m', AtHead L H ρw' m' (runP P n s) ∧
          EnvRel (lower2T [tcap] stepT []).2 scaleLay σ [tcap] ([(Atom.const (.cap p) : Atom₂)].map valOf) ρw' ∧
          Layout σ scaleLay ∧ MemRel scaleLay σ m' ∧ σ.R = (initStore b om lit p).R) ∨
        ((runP P n s).rip = X ∧ (runP P n s).stopped = false ∧ rd (runP P n s).mem L.cb = stRes) := by
  have h0 := deflate_noovf_loaded (lit := lit) hbyte hn32 hom32 hp0 hp1 0 (initStore b om lit p) rfl
  have hreg : (initStore b om lit p).R.lookup p = some (L0 b.size om) := by
    rw [(reach_shape (lit := lit) (p := p) hbyte hn32 hom32 0 (initStore b om lit p) rfl).reg]; exact Finmap.lookup_singleton_eq
  intro k
  induction k with
  | zero =>
    intro σ h
    simp only [iterS, Option.some.injEq] at h
    subst h
    exact ⟨0, .inl ⟨_, _, hA, envRel_cap hreg, h0.1, h0.2.1, rfl⟩⟩
  | succ k ih =>
    intro σ h
    rw [iterS_succ'] at h
    cases h1 : iterS p k (initStore b om lit p) with
    | none => rw [h1] at h; cases h
    | some σk =>
      rw [h1, Option.bind_some] at h
      obtain ⟨n₁, ⟨ρw', m', hA', he', hl', hm', hR'⟩ | hx⟩ := ih σk h1
      · have hs := stepS_steps_p h
        rw [← stepT_inst] at hs
        have hsrc : SrcInRange (instL 0 [(Atom.const (.cap p) : Atom₂)] stepT, σk) := by
          rw [stepT_inst]; exact deflate_inrange hbyte hn32 hom32 k σk h1
        obtain ⟨n₂, ⟨ρw'', m'', hA'', he'', hl'', hm'', hR''⟩ | hx₂⟩ :=
          drv_iter_N stepT stepT_typed stepT_wfB stepT_fnOk stepT_ok2 stepT_table hs hsrc he' hl' hm' hCdef hP hC hb hNm hNt hL
            hcanon hretc hstub hcode hbase hX hH hret hN hE (fun a ha => hlv a (live_of_R hR' a ha)) hA'
        · exact ⟨n₁ + n₂, .inl ⟨ρw'', m'', by rw [runP_add]; exact hA'', he'', hl'', hm'', hR''.trans hR'⟩⟩
        · exact ⟨n₁ + n₂, .inr (by rw [runP_add]; exact hx₂)⟩
      · exact ⟨n₁, .inr hx⟩

end K7
