/-
  O95, K5-2b: `Mag_step` assembled — every step of DEFLATE's step program from a world with `Inv ∧ Mag` lands in a world
  with `Mag` (the 28 mode cases in MagStep.lean and MagBuild.lean), and `Mag_init`. With Safety's own preservation of `Inv`
  (`stepSafe_of`), `Inv ∧ Mag` holds on every world the run reaches; `step_inrange` then gives K5-2.
-/
import K5.MagBuild

namespace K5
open VIRL1 VIRL2 VIRC VIRDeflate VIRDeflate.Step

theorem Mag_step_build {b : Array Nat} {om : Nat} {lit : Bool} {σ σ' : Store} {p : Int} {f f' : Int → Int}
    (hw : World σ p (L0 b.size om) f) (hi : Inv b om lit f) (hg : Mag b.size om f) (hm : f cMODE = mBUILD)
    (hS : stepS p σ = some σ') (hw' : World σ' p (L0 b.size om) f') : Mag b.size om f' := by
  have hb := hi.2.cur
  rw [hm, facts_build] at hb
  unfold buildInv at hb
  dsimp only at hb
  obtain ⟨_, _, _, _, _, _, _, _, hph⟩ := hb
  rcases hph with h | h | h | h | h
  · exact Mag_step_build0 hw hi hg hm h hS hw'
  · exact Mag_step_build1 hw hi hg hm h hS hw'
  · exact Mag_step_build2 hw hi hg hm h hS hw'
  · exact Mag_step_build3 hw hi hg hm h hS hw'
  · exact Mag_step_build4 hw hi hg hm h hS hw'

/-- **`Mag_step`:** a step from a non-terminal world with `Inv ∧ Mag` keeps `Mag`. -/
theorem Mag_step {b : Array Nat} {om : Nat} {lit : Bool} {σ σ' : Store} {p : Int} {f f' : Int → Int}
    (hb : ∀ x ∈ b, x < 256) (hw : World σ p (L0 b.size om) f) (hi : Inv b om lit f) (hg : Mag b.size om f)
    (hd : f cMODE ≠ mDONE) (hr : f cMODE ≠ mREJECT) (hS : stepS p σ = some σ') (hw' : World σ' p (L0 b.size om) f') :
    Mag b.size om f' := by
  have hmode := hi.1.mode_ok
  simp only [validModes, List.mem_cons, List.mem_nil_iff, or_false] at hmode
  rcases hmode with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · first | exact Mag_step_table hw hi hg h hS hw' | exact Mag_step_table hb hw hi hg h hS hw' | exact Mag_step_table (lit := lit) hw hg h hS hw' | exact Mag_step_table hw hg h hS hw'
  · first | exact Mag_step_hdr hw hi hg h hS hw' | exact Mag_step_hdr hb hw hi hg h hS hw' | exact Mag_step_hdr (lit := lit) hw hg h hS hw' | exact Mag_step_hdr hw hg h hS hw'
  · first | exact Mag_step_read hw hi hg h hS hw' | exact Mag_step_read hb hw hi hg h hS hw' | exact Mag_step_read (lit := lit) hw hg h hS hw' | exact Mag_step_read hw hg h hS hw'
  · first | exact Mag_step_hdrb hw hi hg h hS hw' | exact Mag_step_hdrb hb hw hi hg h hS hw' | exact Mag_step_hdrb (lit := lit) hw hg h hS hw' | exact Mag_step_hdrb hw hg h hS hw'
  · first | exact Mag_step_hdrd hw hi hg h hS hw' | exact Mag_step_hdrd hb hw hi hg h hS hw' | exact Mag_step_hdrd (lit := lit) hw hg h hS hw' | exact Mag_step_hdrd hw hg h hS hw'
  · first | exact Mag_step_shdr hw hi hg h hS hw' | exact Mag_step_shdr hb hw hi hg h hS hw' | exact Mag_step_shdr (lit := lit) hw hg h hS hw' | exact Mag_step_shdr hw hg h hS hw'
  · first | exact Mag_step_fixlens hw hi hg h hS hw' | exact Mag_step_fixlens hb hw hi hg h hS hw' | exact Mag_step_fixlens (lit := lit) hw hg h hS hw' | exact Mag_step_fixlens hw hg h hS hw'
  · first | exact Mag_step_dhdr hw hi hg h hS hw' | exact Mag_step_dhdr hb hw hi hg h hS hw' | exact Mag_step_dhdr (lit := lit) hw hg h hS hw' | exact Mag_step_dhdr hw hg h hS hw'
  · first | exact Mag_step_slen hw hi hg h hS hw' | exact Mag_step_slen hb hw hi hg h hS hw' | exact Mag_step_slen (lit := lit) hw hg h hS hw' | exact Mag_step_slen hw hg h hS hw'
  · first | exact Mag_step_snlen hw hi hg h hS hw' | exact Mag_step_snlen hb hw hi hg h hS hw' | exact Mag_step_snlen (lit := lit) hw hg h hS hw' | exact Mag_step_snlen hw hg h hS hw'
  · first | exact Mag_step_scopy hw hi hg h hS hw' | exact Mag_step_scopy hb hw hi hg h hS hw' | exact Mag_step_scopy (lit := lit) hw hg h hS hw' | exact Mag_step_scopy hw hg h hS hw'
  · exact Mag_step_build hw hi hg h hS hw'
  · first | exact Mag_step_lens hw hi hg h hS hw' | exact Mag_step_lens hb hw hi hg h hS hw' | exact Mag_step_lens (lit := lit) hw hg h hS hw' | exact Mag_step_lens hw hg h hS hw'
  · first | exact Mag_step_sym hw hi hg h hS hw' | exact Mag_step_sym hb hw hi hg h hS hw' | exact Mag_step_sym (lit := lit) hw hg h hS hw' | exact Mag_step_sym hw hg h hS hw'
  · first | exact Mag_step_decode hw hi hg h hS hw' | exact Mag_step_decode hb hw hi hg h hS hw' | exact Mag_step_decode (lit := lit) hw hg h hS hw' | exact Mag_step_decode hw hg h hS hw'
  · first | exact Mag_step_symd hw hi hg h hS hw' | exact Mag_step_symd hb hw hi hg h hS hw' | exact Mag_step_symd (lit := lit) hw hg h hS hw' | exact Mag_step_symd hw hg h hS hw'
  · first | exact Mag_step_lenx hw hi hg h hS hw' | exact Mag_step_lenx hb hw hi hg h hS hw' | exact Mag_step_lenx (lit := lit) hw hg h hS hw' | exact Mag_step_lenx hw hg h hS hw'
  · first | exact Mag_step_dstd hw hi hg h hS hw' | exact Mag_step_dstd hb hw hi hg h hS hw' | exact Mag_step_dstd (lit := lit) hw hg h hS hw' | exact Mag_step_dstd hw hg h hS hw'
  · first | exact Mag_step_dstx hw hi hg h hS hw' | exact Mag_step_dstx hb hw hi hg h hS hw' | exact Mag_step_dstx (lit := lit) hw hg h hS hw' | exact Mag_step_dstx hw hg h hS hw'
  · first | exact Mag_step_copy hw hi hg h hS hw' | exact Mag_step_copy hb hw hi hg h hS hw' | exact Mag_step_copy (lit := lit) hw hg h hS hw' | exact Mag_step_copy hw hg h hS hw'
  · first | exact Mag_step_dh2 hw hi hg h hS hw' | exact Mag_step_dh2 hb hw hi hg h hS hw' | exact Mag_step_dh2 (lit := lit) hw hg h hS hw' | exact Mag_step_dh2 hw hg h hS hw'
  · first | exact Mag_step_dh3 hw hi hg h hS hw' | exact Mag_step_dh3 hb hw hi hg h hS hw' | exact Mag_step_dh3 (lit := lit) hw hg h hS hw' | exact Mag_step_dh3 hw hg h hS hw'
  · first | exact Mag_step_dh4 hw hi hg h hS hw' | exact Mag_step_dh4 hb hw hi hg h hS hw' | exact Mag_step_dh4 (lit := lit) hw hg h hS hw' | exact Mag_step_dh4 hw hg h hS hw'
  · first | exact Mag_step_clread hw hi hg h hS hw' | exact Mag_step_clread hb hw hi hg h hS hw' | exact Mag_step_clread (lit := lit) hw hg h hS hw' | exact Mag_step_clread hw hg h hS hw'
  · first | exact Mag_step_clput hw hi hg h hS hw' | exact Mag_step_clput hb hw hi hg h hS hw' | exact Mag_step_clput (lit := lit) hw hg h hS hw' | exact Mag_step_clput hw hg h hS hw'
  · first | exact Mag_step_lsym hw hi hg h hS hw' | exact Mag_step_lsym hb hw hi hg h hS hw' | exact Mag_step_lsym (lit := lit) hw hg h hS hw' | exact Mag_step_lsym hw hg h hS hw'
  · first | exact Mag_step_lrep hw hi hg h hS hw' | exact Mag_step_lrep hb hw hi hg h hS hw' | exact Mag_step_lrep (lit := lit) hw hg h hS hw' | exact Mag_step_lrep hw hg h hS hw'
  · first | exact Mag_step_rep hw hi hg h hS hw' | exact Mag_step_rep hb hw hi hg h hS hw' | exact Mag_step_rep (lit := lit) hw hg h hS hw' | exact Mag_step_rep hw hg h hS hw'
  · exact absurd h hd
  · exact absurd h hr

end K5
