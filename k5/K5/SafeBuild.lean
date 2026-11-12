/-
  O95, K5-2b: BUILD in range from Inv (`buildInv`, `lens`, `hdr_rng`) and Mag (B1 code, B2 left/rest/total), n, OUTMAX < 2³².
  One theorem per phase, as Safety's `safeI_build` reads each phase's facts (counts by `cnt`, offsets by `off_cnt_le`,
  phase 4's slot bound by the `cnt` step at j); `build_inR` dispatches on the phase.
-/
import K5.Mag
import K5.BuildLeftEnd
import K5.BuildZero

namespace K5
open VIRL1 VIRL2 VIRC VIRDeflate VIRDeflate.Step

theorem cnt_le_self (f : Int → Int) (sb l : Int) : ∀ k : Nat, cnt f sb l k ≤ k
  | 0 => le_refl _
  | k + 1 => by simp only [cnt]; have := cnt_le_self f sb l k; split_ifs <;> omega

variable {b : Array Nat} {om : Nat} {lit : Bool} {σ : Store} {p : Int} {f : Int → Int}

/-- The facts every phase uses: the target's table base, and the source run [sb, sb + nn) inside the length area. -/
structure BFacts (n om : Nat) (f : Int → Int) (T sb nn : Int) : Prop where
  t0 : 2080 + n + om + 337 ≤ T
  tL : T + 352 ≤ X0 n om
  s0 : 2080 + n + om ≤ sb
  sL : sb + nn ≤ 2080 + n + om + 337
  n0 : 0 ≤ nn
  n318 : nn ≤ 318

theorem bfacts (hi : Inv b om lit f) (hb : buildInv b.size om f) :
    BFacts b.size om f (f (X0 b.size om + 7)) (f (X0 b.size om + 5)) (f (X0 b.size om + 6)) := by
  unfold buildInv at hb
  dsimp only at hb
  obtain ⟨ht0, ht2, htb, htg, -⟩ := hb
  have hh := hi.1.hdr_rng
  rw [htb]
  refine ⟨by unfold tbase LB0; omega, by unfold tbase LB0 X0; omega, ?_, ?_, ?_, ?_⟩ <;>
  rcases htg with ⟨_, h5, h6, _⟩ | ⟨_, h5, h6, h7, _⟩ | ⟨_, h5, h6, h7, h8, _⟩ <;> (try rw [h5]) <;> (try rw [h6]) <;> (try unfold LB0) <;> omega

/-- A source length: in [0, 15] (the length area, InvG.lens). -/
theorem src_len (hi : Inv b om lit f) {sb nn j : Int} (h0 : 2080 + b.size + om ≤ sb)
    (hL : sb + nn ≤ 2080 + b.size + om + 337) (hj0 : 0 ≤ j) (hjn : j < nn) : 0 ≤ f (sb + j) ∧ f (sb + j) ≤ 15 := by
  have := hi.1.lens (sb + j - (2080 + b.size + om)) (by omega) (by omega)
  rwa [show (2080 : Int) + b.size + om + (sb + j - (2080 + b.size + om)) = sb + j by ring] at this

theorem pow_le_32768 {k : Nat} (hk : k ≤ 15) : (2 : Int) ^ k ≤ 32768 := by
  calc (2 : Int) ^ k ≤ 2 ^ 15 := pow_le_pow_right₀ (by norm_num) hk
    _ = 32768 := by norm_num

theorem build0_inR (hn32 : b.size < 2 ^ 32) (hom32 : om < 2 ^ 32) (hw : World σ p (L0 b.size om) f)
    (hi : Inv b om lit f) (hb : buildInv b.size om f) (hph : f cPHASE = 0) : SrcInRange (closeAt p buildT, σ) := by
  have hB := bfacts hi hb
  have hx := hi.1.x_eq
  have hL0 : (L0 b.size om : Int) = b.size + om + 3626 := by unfold L0; push_cast; ring
  have hX0 : X0 b.size om = 2080 + b.size + om + 1393 := rfl
  unfold buildInv at hb
  dsimp only at hb
  obtain ⟨_, _, _, _, hp0, hp1, hp23, hp4, _⟩ := hb
  obtain ⟨t0, tL, s0, sL, n0, n318⟩ := hB
  have hj := hp0 hph
  by_cases h16 : f cINDEX < 16
  · apply build_zero_cell_inR hw (by unfold L0; omega) _ _ _ hph rfl hx rfl (by omega) (by omega) h16 (by omega) (by omega)
      (by omega)
    all_goals (try rw [hX0] at *)
    rclose
  · apply build_zero_end_inR hw (by unfold L0; omega) _ _ _ hph rfl hx rfl (by omega) (by omega) h16
    all_goals (try rw [hX0] at *)
    rclose

theorem build1_inR (hn32 : b.size < 2 ^ 32) (hom32 : om < 2 ^ 32) (hw : World σ p (L0 b.size om) f)
    (hi : Inv b om lit f) (hb : buildInv b.size om f) (hph : f cPHASE = 1) : SrcInRange (closeAt p buildT, σ) := by
  have hB := bfacts hi hb
  have hx := hi.1.x_eq
  have hL0 : (L0 b.size om : Int) = b.size + om + 3626 := by unfold L0; push_cast; ring
  have hX0 : X0 b.size om = 2080 + b.size + om + 1393 := rfl
  unfold buildInv at hb
  dsimp only at hb
  obtain ⟨_, _, _, _, hp0, hp1, hp23, hp4, _⟩ := hb
  obtain ⟨t0, tL, s0, sL, n0, n318⟩ := hB
  obtain ⟨hj0, hjn, hz, hcn⟩ := hp1 hph
  by_cases hlt : f cINDEX < f (X0 b.size om + 6)
  · have hl := src_len hi s0 sL hj0 hlt
    have hc : 0 ≤ f (f (X0 b.size om + 7) + f (f (X0 b.size om + 5) + f cINDEX)) ∧
        f (f (X0 b.size om + 7) + f (f (X0 b.size om + 5) + f cINDEX)) ≤ 318 := by
      by_cases h0 : f (f (X0 b.size om + 5) + f cINDEX) = 0
      · rw [h0, add_zero, hz]; omega
      · rw [hcn _ (by omega) (by omega)]
        have := cnt_le_self f (f (X0 b.size om + 5)) (f (f (X0 b.size om + 5) + f cINDEX)) (f cINDEX).toNat
        omega
    apply build_count_cell_inR hw (by unfold L0; omega) _ _ _ _ _ _ _ hph rfl hx rfl rfl rfl (by omega) (by omega) hlt
      (by omega) (by omega) rfl (by omega) (by omega) hl.1 hl.2 rfl
    all_goals (try rw [hX0] at *)
    rclose
  · apply build_count_end_inR hw (by unfold L0; omega) _ _ _ _ _ hph rfl hx rfl rfl rfl (by omega) (by omega) hlt
      (by omega) (by omega)
    all_goals (try rw [hX0] at *)
    rclose

theorem build2_inR (hn32 : b.size < 2 ^ 32) (hom32 : om < 2 ^ 32) (hw : World σ p (L0 b.size om) f)
    (hi : Inv b om lit f) (hg : Mag b.size om f) (hm : f cMODE = mBUILD) (hb : buildInv b.size om f) (hph : f cPHASE = 2) :
    SrcInRange (closeAt p buildT, σ) := by
  have hB := bfacts hi hb
  have hx := hi.1.x_eq
  have hL0 : (L0 b.size om : Int) = b.size + om + 3626 := by unfold L0; push_cast; ring
  have hX0 : X0 b.size om = 2080 + b.size + om + 1393 := rfl
  unfold buildInv at hb
  dsimp only at hb
  obtain ⟨_, _, _, _, hp0, hp1, hp23, hp4, _⟩ := hb
  obtain ⟨t0, tL, s0, sL, n0, n318⟩ := hB
  obtain ⟨hj1, hj16, hz, hz32, hcn, hoff⟩ := hp23 (by omega) (by omega)
  by_cases h15 : f cINDEX ≤ 15
  · have hcode := hg.b1 hm hph
    have hp := pow_le_32768 (k := (f cINDEX).toNat) (by omega)
    have hcp : 0 ≤ f (f (X0 b.size om + 7) + (f cINDEX - 1)) ∧ f (f (X0 b.size om + 7) + (f cINDEX - 1)) ≤ 318 := by
      by_cases h1 : f cINDEX = 1
      · rw [h1, show (1 : Int) - 1 = 0 by norm_num, add_zero, hz]; omega
      · rw [hcn _ (by omega) (by omega)]
        have := cnt_le_self f (f (X0 b.size om + 5)) (f cINDEX - 1) (f (X0 b.size om + 6)).toNat
        omega
    have hop : 0 ≤ f (f (X0 b.size om + 7) + 32 + (f cINDEX - 1)) ∧ f (f (X0 b.size om + 7) + 32 + (f cINDEX - 1)) ≤ 318 := by
      by_cases h1 : f cINDEX = 1
      · rw [h1, show (1 : Int) - 1 = 0 by norm_num, add_zero, hz32]; omega
      · rw [(hoff (f cINDEX - 1) (by omega) (by split_ifs <;> omega)).1]
        have e := off_cnt_le hcn (f cINDEX - 1) (by omega) (by omega)
        rw [offOf_sc hcn _ (by omega)] at e ⊢
        omega
    apply build_next_cell_inR hw (by unfold L0; omega) _ _ _ _ _ _ hph rfl hx rfl (by omega) (by omega) hj1 h15
      (by omega) (by omega) rfl rfl rfl
    all_goals (try rw [hX0] at *)
    rclose
  · apply build_next_end_inR hw (by unfold L0; omega) _ _ _ _ hph rfl hx rfl (by omega) (by omega) h15 rfl
    all_goals (try rw [hX0] at *)
    rclose

theorem build3_inR (hn32 : b.size < 2 ^ 32) (hom32 : om < 2 ^ 32) (hw : World σ p (L0 b.size om) f)
    (hi : Inv b om lit f) (hg : Mag b.size om f) (hm : f cMODE = mBUILD) (hb : buildInv b.size om f) (hph : f cPHASE = 3) :
    SrcInRange (closeAt p buildT, σ) := by
  have hB := bfacts hi hb
  have hx := hi.1.x_eq
  have hL0 : (L0 b.size om : Int) = b.size + om + 3626 := by unfold L0; push_cast; ring
  have hX0 : X0 b.size om = 2080 + b.size + om + 1393 := rfl
  unfold buildInv at hb
  dsimp only at hb
  obtain ⟨_, _, _, _, hp0, hp1, hp23, hp4, _⟩ := hb
  obtain ⟨t0, tL, s0, sL, n0, n318⟩ := hB
  obtain ⟨hj1, hj16, hz, hz32, hcn, hoff⟩ := hp23 (by omega) (by omega)
  have hlr := hg.b2 hm hph
  by_cases h15 : f cINDEX ≤ 15
  · have hp := pow_le_32768 (k := (f cINDEX).toNat) (by omega)
    have hc : 0 ≤ f (f (X0 b.size om + 7) + f cINDEX) ∧ f (f (X0 b.size om + 7) + f cINDEX) ≤ 318 := by
      rw [hcn _ (by omega) (by omega)]
      have := cnt_le_self f (f (X0 b.size om + 5)) (f cINDEX) (f (X0 b.size om + 6)).toNat
      omega
    apply build_left_cell_inR hw (by unfold L0; omega) _ _ _ _ _ _ _ hph rfl hx rfl (by omega) (by omega) hj1 h15
      (by omega) (by omega) rfl rfl rfl rfl
    all_goals (try rw [hX0] at *)
    rclose
  · apply build_left_end_inR hw (by unfold L0; omega) _ _ _ _ _ _ _ _ hph rfl hx rfl (by omega) (by omega) h15
      (by omega) (by omega) rfl rfl rfl rfl rfl
    all_goals (try rw [hX0] at *)
    rclose

theorem build4_inR (hn32 : b.size < 2 ^ 32) (hom32 : om < 2 ^ 32) (hw : World σ p (L0 b.size om) f)
    (hi : Inv b om lit f) (hb : buildInv b.size om f) (hph : f cPHASE = 4) : SrcInRange (closeAt p buildT, σ) := by
  have hbb := hb
  unfold buildInv at hbb
  dsimp only at hbb
  obtain ⟨htg0, htg2, _, _⟩ := hbb
  have hB := bfacts hi hb
  have hx := hi.1.x_eq
  have hL0 : (L0 b.size om : Int) = b.size + om + 3626 := by unfold L0; push_cast; ring
  have hX0 : X0 b.size om = 2080 + b.size + om + 1393 := rfl
  unfold buildInv at hb
  dsimp only at hb
  obtain ⟨_, _, _, _, hp0, hp1, hp23, hp4, _⟩ := hb
  obtain ⟨t0, tL, s0, sL, n0, n318⟩ := hB
  obtain ⟨hj0, hjn, _, hslot⟩ := hp4 hph
  have hh := hi.1.hdr_rng
  by_cases hlt : f cINDEX < f (X0 b.size om + 6)
  · have hl := src_len hi s0 sL hj0 hlt
    by_cases h0 : f (f (X0 b.size om + 5) + f cINDEX) = 0
    · apply build_syms_skip_inR hw (by unfold L0; omega) _ _ _ _ _ hph rfl hx rfl rfl rfl (by omega) (by omega) hlt
        (by omega) (by omega) h0
      all_goals (try rw [hX0] at *)
      rclose
    · set l := f (f (X0 b.size om + 5) + f cINDEX) with hld
      have hs := hslot l (by omega) (by omega)
      have hcm : cnt f (f (X0 b.size om + 5)) l (f cINDEX + 1).toNat ≤ cnt f (f (X0 b.size om + 5)) l (f (X0 b.size om + 6)).toNat :=
        cnt_mono _ _ _ (by omega)
      have hc1 : cnt f (f (X0 b.size om + 5)) l (f cINDEX + 1).toNat = cnt f (f (X0 b.size om + 5)) l (f cINDEX).toNat + 1 := by
        rw [show (f cINDEX + 1).toNat = (f cINDEX).toNat + 1 by omega]; simp only [cnt]
        rw [if_pos (by rw [show ((f cINDEX).toNat : Int) = f cINDEX by omega])]
      have hsl : 0 ≤ f (f (X0 b.size om + 7) + 48 + l) ∧ f (f (X0 b.size om + 7) + 48 + l) < 288 := by
        push_cast at hs; omega
      apply build_syms_cell_inR hw (by unfold L0; omega) _ _ _ _ _ _ _ hph rfl hx rfl rfl rfl (by omega) (by omega) hlt
        (by omega) (by omega) rfl (by omega) (by omega) hl.1 hl.2 rfl (fun _ => hsl.1) (fun _ => hsl.2)
      all_goals (try rw [hX0] at *)
      all_goals (try rw [← hld])
      rclose
  · have htg : f cTGT = 0 ∨ f cTGT = 1 ∨ f cTGT = 2 := by omega
    rcases htg with h | h | h
    · apply build_syms_end_cl_inR hw (by unfold L0; omega) _ _ _ _ _ hph rfl hx rfl rfl rfl (by omega) (by omega) hlt h
      all_goals (try rw [hX0] at *)
      rclose
    · apply build_syms_end_l_inR hw (by unfold L0; omega) _ _ _ _ _ _ _ _ _ _ hph rfl hx rfl rfl rfl (by omega) (by omega)
        hlt h rfl rfl hi.1.n_eq hi.1.om_eq rfl
      all_goals (try rw [hX0] at *)
      rclose
    · apply build_syms_end_d_inR hw (by unfold L0; omega) _ _ _ _ _ hph rfl hx rfl rfl rfl (by omega) (by omega) hlt h
      all_goals (try rw [hX0] at *)
      rclose

/-- **BUILD is in range** on every world satisfying Inv and Mag, n, OUTMAX < 2³². -/
theorem build_inR (hn32 : b.size < 2 ^ 32) (hom32 : om < 2 ^ 32) (hw : World σ p (L0 b.size om) f)
    (hi : Inv b om lit f) (hg : Mag b.size om f) (hm : f cMODE = mBUILD) : SrcInRange (closeAt p buildT, σ) := by
  have hb := hi.2.cur
  rw [hm, facts_build] at hb
  have hbb := hb
  unfold buildInv at hbb
  dsimp only at hbb
  obtain ⟨_, _, _, _, _, _, _, _, hph⟩ := hbb
  rcases hph with h | h | h | h | h
  · exact build0_inR hn32 hom32 hw hi hb h
  · exact build1_inR hn32 hom32 hw hi hb h
  · exact build2_inR hn32 hom32 hw hi hg hm hb h
  · exact build3_inR hn32 hom32 hw hi hg hm hb h
  · exact build4_inR hn32 hom32 hw hi hb h

end K5
