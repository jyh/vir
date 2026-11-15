-- GOING RED (DECLARATIONS-K7 Addendum 6): drv_iter_D with the empty-table premise dropped; the RES branch must not close.
/-
  O95 (compiler/DECLARATIONS-K7.md, Addendum 6): a DONE-only driver step for a step term whose lowered table is empty. Generic: it
  names no program. Built from `S3.drv_iter_N`'s proof with the RES branch closed by `S3.resWhy_false`.
-/
import K7.DeflateDriver
import S3.DriverN
import S3.ResFree

namespace K7
open VIRC VIRL1 VIRL2 X86 S3 K5

set_option maxHeartbeats 1000000 in
open VIRL1 VIRL2 in
/-- **drv_iter_D.** `S3.drv_iter_N` for a step whose lowered table is empty, under ENV and STACK room for its main code
    (DECLARATIONS-K7 Addendum 6): the machine reaches the loop head again. RES is closed by `resWhy_false`. Names no program. -/
theorem drv_iter_D_mut (e : Tm₂) (hty : HasType₂ [tcap] [true] e tcap) (hw : Tm.wfB [tcap].length e = true)
    (hf : Tm.fnOk e = true) (hok : Tm.ok2 e = true) (hT : (lower2T [tcap] e []).2.length < 2 ^ 64) {p : Int} {σ σ₁ : Store}
    (hs : Steps₂ (instL 0 [(Atom.const (.cap p) : Atom₂)] e, σ) (.ret (.const (.cap p)), σ₁))
    (hsrc : SrcInRange (instL 0 [(Atom.const (.cap p) : Atom₂)] e, σ))
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
    (hlive : ∀ a, VIRBridge.Live σ lay a → L.live a) {s : Cpu} (hA : AtHead L H ρw m s)
    (hEnv : 8 * envM (lower2T [tcap] e []).1 2 ≤ L.env0.toNat - L.envLo.toNat)
    (hStk : 16 * (frD (lower2T [tcap] e []).1 + 2) + 8 ≤ L.rsp0.toNat + 8 - L.stkLo.toNat) :
    ∃ n ρw' m', AtHead L H ρw' m' (runP P n s) ∧
        EnvRel (lower2T [tcap] e []).2 lay σ₁ [tcap] ([(Atom.const (.cap p) : Atom₂)].map valOf) ρw' ∧
        Layout σ₁ lay ∧ MemRel lay σ₁ m' ∧ σ₁.R = σ.R := by
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
    obtain ⟨mm, ⟨-, hR3⟩ | ⟨Wr, Wr', j, hj, -, hwhy, -, -⟩⟩ :=
      s3_refines_from_s2 hCdef hP hC hb hT hNm hNt hL hcanon hretc hstub hDC hrip1 h0 hlive hWN
    · obtain ⟨hRet, hcm, -, hbuf⟩ := hR3
      cases hv with
      | cap hRp =>
        obtain ⟨w, hw', hAt⟩ := after_done hL hRet hcm hbuf (by rw [hRet.2.1]; exact hcT) hX hH hN hE hA.stk
        exact ⟨1 + mm + 10, _, m₁, by rw [runP_add, r1, hw']; exact hAt, he₁, hl₁, hm₁, hR₁⟩
    · exfalso
      rw [htbl] at hj
      obtain ⟨n, -, rfl⟩ := envRel_cap_inv he
      exact resWhy_false hj hEnv hStk hwhy
  · exact absurd hov (compile_noovf [tcap] [true] e tcap [.const (.cap p)] ρw hty hw hf hok rfl (good_cap1 p) hT he hl hm hsrc
      k W' hWN)

end K7
