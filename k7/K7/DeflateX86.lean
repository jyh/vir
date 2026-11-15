/-
  O95, STATUS-vir 369 (compiler/DECLARATIONS-DRIVER.md, Addendum 7): DEFLATE at the x86 machine. `driver_x86_R` instantiated at
  DEFLATE's step term from the loader's image of the initial store. The non-DONE exit disjunct is NOT excluded (declared limit).
-/
import K7.DeflateDriver
import S3.SrcR

namespace K7
open VIRL1 VIRL2 VIRC VIRDeflate VIRDeflate.Step K5

/-- **iterS_iterRel.** DEFLATE's k-step iteration is the driver's `IterRel` for stepT. -/
theorem iterS_iterRel (p : Int) : ∀ (k : Nat) (σ σ' : Store), iterS p k σ = some σ' → IterRel stepT p k σ σ'
  | 0, σ, σ', h => by simp only [iterS, Option.some.injEq] at h; subst h; exact .zero σ
  | k + 1, σ, σ', h => by
    simp only [iterS] at h
    cases h1 : stepS p σ with
    | none => rw [h1] at h; cases h
    | some σ₁ =>
      rw [h1, Option.bind_some] at h
      have hs := stepS_steps_p h1
      rw [← stepT_inst] at hs
      exact .succ hs (iterS_iterRel p k σ₁ σ' h)

set_option maxHeartbeats 1000000 in
open S3 X86 in
/-- **deflate_x86.** For DEFLATE's premises and the driver's S3 premises on stepT's lowering: from a machine at the loop head on the
    loader's image of `initStore b om lit p`, for every k with `iterS p k (initStore …) = some σ`, the machine reaches the head again
    with its memory related to σ, or some iteration leaves the loop at X with a non-DONE status. -/
theorem deflate_x86 {b : Array Nat} {om : Nat} {lit : Bool} {p : Int} (hbyte : ∀ x ∈ b, x < 256)
    (hn32 : b.size < 2 ^ 32) (hom32 : om < 2 ^ 32) (hp0 : 0 ≤ p) (hp1 : p + L0 b.size om ≤ 2 ^ 60)
    (hT : (lower2T [tcap] stepT []).2.length < 2 ^ 64)
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
    {s : Cpu} (hA : AtHead L H (capWords scaleLay p (L0 b.size om)) (scaleMem (initStore b om lit p)) s)
    {k : Nat} {σ : Store} (hk : iterS p k (initStore b om lit p) = some σ) :
    ∃ n, (∃ ρw' m', AtHead L H ρw' m' (runP P n s) ∧ Layout σ scaleLay ∧ MemRel scaleLay σ m') ∨
      (∃ code, code ≠ 0 ∧ (runP P n s).rip = X ∧ (runP P n s).stopped = false ∧ rd (runP P n s).mem L.cb = code) := by
  have h0 := deflate_noovf_loaded (lit := lit) hbyte hn32 hom32 hp0 hp1 0 (initStore b om lit p) rfl
  have hreg : (initStore b om lit p).R.lookup p = some (L0 b.size om) := by
    rw [(reach_shape (lit := lit) (p := p) hbyte hn32 hom32 0 (initStore b om lit p) rfl).reg]; exact Finmap.lookup_singleton_eq
  exact driver_x86_R stepT stepT_typed stepT_wfB stepT_fnOk stepT_ok2 hT hCdef hP hC hb hNm hNt hL hcanon hretc hstub hcode
    hbase hX hH hret hN hE (iterS_iterRel p k _ σ hk) hlv (envRel_cap hreg) h0.1 h0.2.1 hA

end K7
