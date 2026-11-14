/-
  O95 layer L5, Lean arm (STATUS 323, fork (T)): `Tab` survives one DEFLATE step in BUILD, phase by phase (ZERO, COUNT, NEXT,
  LEFT, SYMS), each branch through DEFLATE's own step lemma with Safety's premises (`safeB_*`). Every BUILD store is a control
  cell, a cell of the X area, or a cell of the table under build at tbase ≥ 2080 + n + om + 337, so the bit table [20, 2068)
  is as it was.
-/
import VIRL5.TabDec5

namespace VIRL5
open VIRL1 VIRL2 VIRDeflate.Step

theorem tab_build {b : Array Nat} {om : Nat} {lit : Bool} {p : Int} {σ σ' : Store} {f f' : Int → Int}
    (hw : World σ p (L0 b.size om) f) (hi : Inv b om lit f) (hm : f cMODE = mBUILD) (hT : Tab f)
    (hS : stepS p σ = some σ') (hw' : World σ' p (L0 b.size om) f') : Tab f' := by
  have hL : 2080 ≤ L0 b.size om := by unfold L0; omega
  have hX : X0 b.size om = 2080 + b.size + om + 1393 := rfl
  have hLB : LB0 b.size om = 2080 + b.size + om := rfl
  have hL0 : (L0 b.size om : Int) = b.size + om + 3626 := by unfold L0; push_cast; ring
  have hmem : (mBUILD, buildN) ∈ modes := by unfold modes; simp
  have hfit := modes_fit (mBUILD, buildN) hmem (by decide)
  have hnt : f cMODE ≠ mTABLE := by rw [hm]; decide
  have hr := hi.1.hdr_rng
  have hx := hi.1.x_eq
  have hb : buildInv b.size om f := by have h := hi.2.cur; rw [hm, facts_build] at h; exact h
  obtain ⟨ht0, ht2, htb, hsb0, hnn0, hsbn, hnn288⟩ := bp hb hr
  have hTB : f (X0 b.size om + 7) = LB0 b.size om + 337 + 352 * f cTGT := htb
  have hb' := hb
  obtain ⟨-, -, -, htg, h0, h1, h23, h4, hph⟩ := hb'
  have fin : ∀ {H : Finmap (fun _ : Int => Int)}, stepS p σ = some ⟨H, σ.R⟩ →
      (∀ c : Int, 20 ≤ c → c < 2068 → H.lookup (p + c) = σ.H.lookup (p + c)) → Tab f' :=
    fun hS0 hk => tab_of_stepH hw hS0 hS hw' hk hnt hT
  rcases hph with hph | hph | hph | hph | hph
  · -- ZERO
    obtain ⟨hj0, hj16, hz⟩ := h0 hph
    by_cases hlt : f cINDEX < 16
    · exact fin (stepS_of_mode hw (by omega) hm rfl hfit.1 hfit.2
        (build_zero_cell hw hL (f cINDEX) (X0 b.size om) (f (X0 b.size om + 7)) hph rfl hx rfl (by omega) (by omega) hj0 hlt
          (by omega) (by omega)))
        (fun c c0 c1 => by simp (disch := omega) only [Finmap.lookup_insert_of_ne])
    · exact fin (stepS_of_mode hw (by omega) hm rfl hfit.1 hfit.2
        (build_zero_end hw hL (f cINDEX) (X0 b.size om) (f (X0 b.size om + 7)) hph rfl hx rfl (by omega) (by omega) hlt))
        (fun c c0 c1 => by simp (disch := omega) only [Finmap.lookup_insert_of_ne])
  · -- COUNT
    obtain ⟨hj0, hjn, hc0, hcnt⟩ := h1 hph
    by_cases hlt : f cINDEX < f (X0 b.size om + 6)
    · have hlr := hi.1.lens (f (X0 b.size om + 5) + f cINDEX - (2080 + b.size + om)) (by omega) (by omega)
      rw [show (2080 : Int) + b.size + om + (f (X0 b.size om + 5) + f cINDEX - (2080 + b.size + om)) =
        f (X0 b.size om + 5) + f cINDEX by ring] at hlr
      have hS0 := stepS_of_mode hw (by omega) hm rfl hfit.1 hfit.2
        (build_count_cell hw hL (f cINDEX) (X0 b.size om) (f (X0 b.size om + 7)) (f (X0 b.size om + 5))
          (f (X0 b.size om + 6)) (f (f (X0 b.size om + 5) + f cINDEX))
          (f (f (X0 b.size om + 7) + f (f (X0 b.size om + 5) + f cINDEX)))
          hph rfl hx rfl rfl rfl (by omega) (by omega) hlt (by omega) (by omega) rfl (by omega) (by omega) hlr.1 hlr.2 rfl)
      split_ifs at hS0 <;> exact fin hS0 (fun c c0 c1 => by simp (disch := omega) only [Finmap.lookup_insert_of_ne])
    · exact fin (stepS_of_mode hw (by omega) hm rfl hfit.1 hfit.2
        (build_count_end hw hL (f cINDEX) (X0 b.size om) (f (X0 b.size om + 7)) (f (X0 b.size om + 5)) (f (X0 b.size om + 6))
          hph rfl hx rfl rfl rfl (by omega) (by omega) hlt (by omega) (by omega)))
        (fun c c0 c1 => by simp (disch := omega) only [Finmap.lookup_insert_of_ne])
  · -- NEXT
    obtain ⟨hj1, hj16, hc0, ho0, hcn, hoff⟩ := h23 (by omega) (by omega)
    by_cases hj15 : f cINDEX ≤ 15
    · exact fin (stepS_of_mode hw (by omega) hm rfl hfit.1 hfit.2
        (build_next_cell hw hL (f cINDEX) (X0 b.size om) (f (X0 b.size om + 7)) (f cCODE)
          (f (f (X0 b.size om + 7) + (f cINDEX - 1))) (f (f (X0 b.size om + 7) + 32 + (f cINDEX - 1))) hph rfl hx rfl
          (by omega) (by omega) hj1 hj15 (by omega) (by omega) rfl rfl rfl))
        (fun c c0 c1 => by simp (disch := omega) only [Finmap.lookup_insert_of_ne])
    · have hS0 := stepS_of_mode hw (by omega) hm rfl hfit.1 hfit.2
        (build_next_end hw hL (f cINDEX) (X0 b.size om) (f (X0 b.size om + 7)) (f cCHK) hph rfl hx rfl (by omega) (by omega)
          hj15 rfl)
      split_ifs at hS0 <;> exact fin hS0 (fun c c0 c1 => by simp (disch := omega) only [Finmap.lookup_insert_of_ne])
  · -- LEFT
    obtain ⟨hj1, hj16, hc0, ho0, hcn, hoff⟩ := h23 (by omega) (by omega)
    by_cases hj15 : f cINDEX ≤ 15
    · have hS0 := stepS_of_mode hw (by omega) hm rfl hfit.1 hfit.2
        (build_left_cell hw hL (f cINDEX) (X0 b.size om) (f (X0 b.size om + 7)) (f cLEFT) (f cREST) (f cTOTAL)
          (f (f (X0 b.size om + 7) + f cINDEX)) hph rfl hx rfl (by omega) (by omega) hj1 hj15 (by omega) (by omega)
          rfl rfl rfl rfl)
      split_ifs at hS0 <;> exact fin hS0 (fun c c0 c1 => by simp (disch := omega) only [Finmap.lookup_insert_of_ne])
    · have hS0 := stepS_of_mode hw (by omega) hm rfl hfit.1 hfit.2
        (build_left_end hw hL (f cINDEX) (X0 b.size om) (f (X0 b.size om + 7)) (f cLEFT) (f cREST) (f cTOTAL)
          (f (f (X0 b.size om + 7) + 1)) (f (X0 b.size om + 8)) hph rfl hx rfl (by omega) (by omega) hj15 (by omega)
          (by omega) rfl rfl rfl rfl rfl)
      split_ifs at hS0 <;> exact fin hS0 (fun c c0 c1 => by simp (disch := omega) only [Finmap.lookup_insert_of_ne])
  · -- SYMS
    obtain ⟨hj0, hjn, hsane, hslot⟩ := h4 hph
    have hjk : ((f cINDEX).toNat : Int) = f cINDEX := by omega
    by_cases hlt : f cINDEX < f (X0 b.size om + 6)
    · have hlr := hi.1.lens (f (X0 b.size om + 5) + f cINDEX - (2080 + b.size + om)) (by omega) (by omega)
      rw [show (2080 : Int) + b.size + om + (f (X0 b.size om + 5) + f cINDEX - (2080 + b.size + om)) =
        f (X0 b.size om + 5) + f cINDEX by ring] at hlr
      set T := f (X0 b.size om + 7) with hTd
      set sb := f (X0 b.size om + 5) with hsbd
      set nn := f (X0 b.size om + 6) with hnnd
      set j := f cINDEX with hjd
      set l := f (sb + j) with hld
      by_cases hl0 : l = 0
      · have hS0 := stepS_of_mode hw (by omega) hm rfl hfit.1 hfit.2
          (build_syms_cell hw hL j (X0 b.size om) T sb nn l (f (T + 48 + l)) hph rfl hx rfl rfl rfl (by omega) (by omega) hlt
            (by omega) (by omega) rfl (by omega) (by omega) hlr.1 hlr.2 rfl (fun h => absurd hl0 h) (fun h => absurd hl0 h))
        rw [if_pos hl0] at hS0
        exact fin hS0 (fun c c0 c1 => by simp (disch := omega) only [Finmap.lookup_insert_of_ne])
      · have hl1 : 1 ≤ l := by omega
        have hsl := hslot l hl1 hlr.2
        have hcm : cnt f sb l (j + 1).toNat ≤ cnt f sb l nn.toNat := cnt_mono f sb l (by omega)
        have hc1 : cnt f sb l (j + 1).toNat = cnt f sb l j.toNat + 1 := by
          rw [show (j + 1).toNat = j.toNat + 1 by omega]; simp only [cnt]; rw [hjk, if_pos rfl]
        have hsl288 : f (T + 48 + l) < 288 := by push_cast at hsl; omega
        have hS0 := stepS_of_mode hw (by omega) hm rfl hfit.1 hfit.2
          (build_syms_cell hw hL j (X0 b.size om) T sb nn l (f (T + 48 + l)) hph rfl hx rfl rfl rfl (by omega) (by omega) hlt
            (by omega) (by omega) rfl (by omega) (by omega) hlr.1 hlr.2 rfl (fun _ => hsl.1) (fun _ => hsl288))
        rw [if_neg hl0] at hS0
        exact fin hS0 (fun c c0 c1 => by simp (disch := omega) only [Finmap.lookup_insert_of_ne])
    · by_cases h0 : f cTGT = 0
      · exact fin (stepS_of_mode hw (by omega) hm rfl hfit.1 hfit.2
          (build_syms_end_cl hw hL (f cINDEX) (X0 b.size om) (f (X0 b.size om + 7)) (f (X0 b.size om + 5))
            (f (X0 b.size om + 6)) hph rfl hx rfl rfl rfl (by omega) (by omega) hlt h0))
          (fun c c0 c1 => by simp (disch := omega) only [Finmap.lookup_insert_of_ne])
      · by_cases h1 : f cTGT = 1
        · exact fin (stepS_of_mode hw (by omega) hm rfl hfit.1 hfit.2
            (build_syms_end_l hw hL (f cINDEX) (X0 b.size om) (f (X0 b.size om + 7)) (f (X0 b.size om + 5))
              (f (X0 b.size om + 6)) (f cHLIT) (f cHDIST) b.size om (f cDYN) hph rfl hx rfl rfl rfl (by omega) (by omega) hlt h1
              rfl rfl hi.1.n_eq hi.1.om_eq rfl))
            (fun c c0 c1 => by simp (disch := omega) only [Finmap.lookup_insert_of_ne])
        · have h2 : f cTGT = 2 := by omega
          exact fin (stepS_of_mode hw (by omega) hm rfl hfit.1 hfit.2
            (build_syms_end_d hw hL (f cINDEX) (X0 b.size om) (f (X0 b.size om + 7)) (f (X0 b.size om + 5))
              (f (X0 b.size om + 6)) hph rfl hx rfl rfl rfl (by omega) (by omega) hlt h2))
            (fun c c0 c1 => by simp (disch := omega) only [Finmap.lookup_insert_of_ne])

end VIRL5
