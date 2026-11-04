/-
  O95 layer L3, Lean arm. R6, run_tokens (OBJECT-L3 §3.5): over n frames, the emits by sender s are at most s's initial
  tokens. It lives in the LOGIC (Z7, R-b): no L2 term loops; between calls the caller writes the next frame into the wire
  (cells [p, p + 67)), and each call's post-state is R4's `postF`. The bound is an induction over the list of frames.
-/
import VIRL3.RouterTriple

namespace VIRL3
open VIRL1 VIRL2 Classical

/-- The caller writes a frame: the wire cells [p, p + 67) take its contents; the ACL and the buckets persist. -/
def withFrame (p : Int) (f fr : Int → Int) : Int → Int := fun a => if p ≤ a ∧ a < p + 67 then fr a else f a

/-- The world after the calls, each call's post-state R4's. -/
noncomputable def after (p : Int) : (Int → Int) → List (Int → Int) → Int → Int
  | f, [] => f
  | f, fr :: frs => after p (postF (withFrame p f fr) p) frs

/-- The emits by sender s over the calls. -/
noncomputable def emitsBy (p s : Int) : (Int → Int) → List (Int → Int) → Nat
  | _, [] => 0
  | f, fr :: frs => (if Emits (withFrame p f fr) p ∧ SvA (withFrame p f fr) p = s then 1 else 0) +
      emitsBy p s (postF (withFrame p f fr) p) frs

/-- A frame's sender and topic in range. -/
def InRange (p : Int) (fr : Int → Int) : Prop := 0 ≤ SvA fr p ∧ SvA fr p < 4 ∧ 0 ≤ TvA fr p ∧ TvA fr p < 4

theorem SvA_withFrame (p : Int) (f fr : Int → Int) : SvA (withFrame p f fr) p = SvA fr p := by
  simp [SvA, withFrame]
theorem TvA_withFrame (p : Int) (f fr : Int → Int) : TvA (withFrame p f fr) p = TvA fr p := by
  simp [TvA, withFrame]

/-- Each call is an instance of R4 at the world the caller left. -/
theorem R6_call (p : Int) (f fr : Int → Int) (h : InRange p fr) :
    Triple (RegionAt p 87 (withFrame p f fr)) (closeAt p F)
      (fun v σ => v = .const (.cap p) ∧ RegionAt p 87 (postF (withFrame p f fr) p) σ) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact R4 (by rwa [SvA_withFrame]) (by rwa [SvA_withFrame]) (by rwa [TvA_withFrame]) (by rwa [TvA_withFrame])

/-- One call at sender s's bucket: decremented by one if it emits for s, unchanged otherwise. -/
theorem post_bucket (p s : Int) (f fr : Int → Int) (h : InRange p fr) (hs : 0 ≤ s) (hs4 : s < 4) :
    postF (withFrame p f fr) p (p + (83 + s)) =
      if Emits (withFrame p f fr) p ∧ SvA (withFrame p f fr) p = s then f (p + (83 + s)) - 1 else f (p + (83 + s)) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hw : withFrame p f fr (p + (83 + s)) = f (p + (83 + s)) := by simp [withFrame]; omega
  rw [SvA_withFrame]
  unfold postF bktA
  rw [SvA_withFrame]
  by_cases hn : 24 ≤ withFrame p f fr p <;> by_cases he : Emits (withFrame p f fr) p <;>
    by_cases hss : SvA fr p = s <;> simp [hn, he, hss, Function.update_apply, hw] <;>
    first | omega | exact absurd (by simpa using he.1) hn

/-- R6 (OBJECT-L3 §3.5): over any list of in-range frames, sender s's emits are at most its initial tokens. -/
theorem R6 (p s : Int) (hs : 0 ≤ s) (hs4 : s < 4) :
    ∀ (frs : List (Int → Int)) (f : Int → Int), (∀ fr ∈ frs, InRange p fr) → 0 ≤ f (p + (83 + s)) →
      (emitsBy p s f frs : Int) ≤ f (p + (83 + s))
  | [], _, _, h0 => by simp [emitsBy]; exact h0
  | fr :: frs, f, hr, h0 => by
    have hfr := hr fr (by simp)
    have ih := R6 p s hs hs4 frs (postF (withFrame p f fr) p) (fun x hx => hr x (by simp [hx]))
    have hb := post_bucket p s f fr hfr hs hs4
    simp only [emitsBy]
    by_cases he : Emits (withFrame p f fr) p ∧ SvA (withFrame p f fr) p = s
    · have ht : 0 < f (p + (83 + s)) := by
        obtain ⟨⟨-, -, -, h⟩, hss⟩ := he
        have : withFrame p f fr (bktA (withFrame p f fr) p) = f (p + (83 + s)) := by
          simp only [bktA, hss]; simp [withFrame]; omega
        rw [this] at h; exact h
      rw [hb, if_pos he] at ih
      rw [if_pos he]; push_cast; have := ih (by omega); omega
    · rw [hb, if_neg he] at ih
      rw [if_neg he]; push_cast; have := ih h0; omega

end VIRL3
