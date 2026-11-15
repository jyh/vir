/-
  O95 compiler, K7-b2 piece (1) (compiler/DECLARATIONS-K7.md, Addendum 2): RES excluded GENERICALLY for code with an empty
  function table. Static measures on `WCode` bound the ENV words and the frames along every word run from main. Names no program.
-/
import S3.SrcR

namespace S3M
open VIRC S3

/-- An upper bound on the width of the value a code returns. -/
def rW : WCode → Nat
  | .ret o => wid o
  | .letE _ c₂ => rW c₂
  | .load _ _ k => rW k
  | .store _ _ _ k => rW k
  | .app _ _ => 0
  | .ite _ c₁ c₂ => max (rW c₁) (rW c₂)
  | .case _ _ _ c₁ c₂ => max (rW c₁) (rW c₂)

/-- The most ENV words (with `grow`) while c runs from n words until it returns, frames it pushes included. -/
def envM : WCode → Nat → Nat
  | .ret o, n => n + wid o
  | .letE c₁ c₂, n => max n (max (n + envM c₁ n) (envM c₂ (rW c₁ + n)))
  | .load _ _ k, n => max (n + 1) (envM k (n + 1))
  | .store _ _ _ k, n => max (n + 2) (envM k (n + 2))
  | .app _ x, n => n + wid x + 1
  | .ite _ c₁ c₂, n => max n (max (envM c₁ n) (envM c₂ n))
  | .case o n₁ n₂ c₁ c₂, n => max (n + wid o) (max (envM c₁ (n + n₁)) (envM c₂ (n + n₂)))

/-- The most frames c pushes before it returns. -/
def frD : WCode → Nat
  | .letE c₁ c₂ => max (1 + frD c₁) (frD c₂)
  | .load _ _ k => frD k
  | .store _ _ _ k => frD k
  | .ite _ c₁ c₂ => max (frD c₁) (frD c₂)
  | .case _ _ _ c₁ c₂ => max (frD c₁) (frD c₂)
  | _ => 0

theorem envM_mono : ∀ (c : WCode) {n n' : Nat}, n ≤ n' → envM c n ≤ envM c n'
  | .ret o, n, n', h => by simp only [envM]; omega
  | .letE c₁ c₂, n, n', h => by
      have h1 := envM_mono c₁ h
      have h2 := envM_mono c₂ (show rW c₁ + n ≤ rW c₁ + n' by omega)
      simp only [envM]; omega
  | .load _ _ k, n, n', h => by
      have h1 := envM_mono k (show n + 1 ≤ n' + 1 by omega); simp only [envM]; omega
  | .store _ _ _ k, n, n', h => by
      have h1 := envM_mono k (show n + 2 ≤ n' + 2 by omega); simp only [envM]; omega
  | .app _ x, n, n', h => by simp only [envM]; omega
  | .ite _ c₁ c₂, n, n', h => by
      have h1 := envM_mono c₁ h; have h2 := envM_mono c₂ h; simp only [envM]; omega
  | .case o n₁ n₂ c₁ c₂, n, n', h => by
      have h1 := envM_mono c₁ (show n + n₁ ≤ n' + n₁ by omega)
      have h2 := envM_mono c₂ (show n + n₂ ≤ n' + n₂ by omega)
      simp only [envM]; omega

theorem grow_le (c : WCode) (n : Nat) : n + grow c ≤ envM c n := by
  cases c <;> simp only [envM, grow] <;> omega

/-- The potential over the pending frames: the current code's peak, then each frame's continuation from the returned width. -/
def topM : WCode → Nat → List (WCode × List W) → Nat
  | c, n, [] => envM c n
  | c, n, (c', ρ') :: k => max (ρ'.length + kSize k + envM c n) (topM c' (rW c + ρ'.length) k)

def tailM (r : Nat) : List (WCode × List W) → Nat
  | [] => 0
  | (c', ρ') :: k => topM c' (r + ρ'.length) k

theorem topM_eq (c : WCode) (n : Nat) (k : List (WCode × List W)) :
    topM c n k = max (kSize k + envM c n) (tailM (rW c) k) := by
  cases k with
  | nil => simp [topM, tailM, kSize]
  | cons f k => obtain ⟨c', ρ'⟩ := f; simp only [topM, tailM, kSize] <;> omega

theorem topM_mono (c : WCode) {n n' : Nat} (h : n ≤ n') (k : List (WCode × List W)) : topM c n k ≤ topM c n' k := by
  rw [topM_eq, topM_eq]; have := envM_mono c h; omega

theorem tailM_mono {r r' : Nat} (h : r ≤ r') (k : List (WCode × List W)) : tailM r k ≤ tailM r' k := by
  cases k with
  | nil => simp [tailM]
  | cons f k => obtain ⟨c', ρ'⟩ := f; exact topM_mono c' (by omega) k

def topF : WCode → List (WCode × List W) → Nat
  | c, [] => frD c
  | c, (c', _) :: k => max (k.length + 1 + frD c) (topF c' k)

def tailF : List (WCode × List W) → Nat
  | [] => 0
  | (c', _) :: k => topF c' k

theorem topF_eq (c : WCode) (k : List (WCode × List W)) : topF c k = max (k.length + frD c) (tailF k) := by
  cases k with
  | nil => simp [topF, tailF]
  | cons f k => obtain ⟨c', ρ'⟩ := f; simp only [topF, tailF, List.length_cons] <;> omega

theorem size_le_top (c : WCode) (ρ : List W) (k : List (WCode × List W)) :
    ρ.length + kSize k + grow c ≤ topM c ρ.length k ∧ k.length ≤ topF c k := by
  rw [topM_eq, topF_eq]; have := grow_le c ρ.length; omega

/-- From a successful run-to-run step equation, substitute the successor's parts (keeping the source's names). -/
macro "injrun " h:ident : tactic =>
  `(tactic| (simp only [Option.some.injEq, Prod.mk.injEq, WSt.run.injEq] at $h:ident
             obtain ⟨⟨e1, e2, e3⟩, e4⟩ := $h:ident; subst e1 e2 e3 e4))

/-- Same pending frames, a successor code c₁ that is a sub-code: both potentials drop when its peak and returned width do. -/
theorem top_same {c c₁ : WCode} {n n₁ : Nat} (k : List (WCode × List W)) (hm : envM c₁ n₁ ≤ envM c n) (hr : rW c₁ ≤ rW c)
    (hf : frD c₁ ≤ frD c) : topM c₁ n₁ k ≤ topM c n k ∧ topF c₁ k ≤ topF c k := by
  have := tailM_mono hr k
  rw [topM_eq, topM_eq, topF_eq, topF_eq]; constructor <;> omega

/-- The two potentials never increase under a word step with an EMPTY table. -/
theorem top_step {c : WCode} {ρ : List W} {k : List (WCode × List W)} {m : WMem} {c' : WCode} {ρ' : List W}
    {k' : List (WCode × List W)} {m' : WMem} (h : stepW [] (.run c ρ k, m) = some (.run c' ρ' k', m')) :
    topM c' ρ'.length k' ≤ topM c ρ.length k ∧ topF c' k' ≤ topF c k := by
  cases c with
  | ret o =>
    simp only [stepW] at h
    split at h
    · simp at h
    · rename_i ws c₂ ρ₂ k₂ hev
      injrun h
      have hw := evalW_length o ρ ws hev
      have t1 : topM (.ret o) ρ.length ((c₂, ρ₂) :: k₂) =
          max (ρ₂.length + kSize k₂ + envM (.ret o) ρ.length) (topM c₂ (wid o + ρ₂.length) k₂) := rfl
      have t2 : topF (.ret o) ((c₂, ρ₂) :: k₂) = max (k₂.length + 1 + frD (.ret o)) (topF c₂ k₂) := rfl
      rw [t1, t2, List.length_append, hw]; constructor <;> omega
    · simp at h
    · simp at h
  | letE c₁ c₂ =>
    simp only [stepW] at h
    injrun h
    have t1 : tailM (rW c₁) ((c₂, ρ) :: k) = topM c₂ (rW c₁ + ρ.length) k := rfl
    have t2 : tailF ((c₂, ρ) :: k) = topF c₂ k := rfl
    have ks : kSize ((c₂, ρ) :: k) = ρ.length + kSize k := rfl
    have hl : ((c₂, ρ) :: k).length = k.length + 1 := rfl
    have em : envM (.letE c₁ c₂) ρ.length = max ρ.length (max (ρ.length + envM c₁ ρ.length) (envM c₂ (rW c₁ + ρ.length))) := rfl
    have fm : frD (.letE c₁ c₂) = max (1 + frD c₁) (frD c₂) := rfl
    have rm : rW (.letE c₁ c₂) = rW c₂ := rfl
    rw [topM_eq c₁, topF_eq c₁, t1, t2, ks, hl, topM_eq c₂, topF_eq c₂, topM_eq (.letE c₁ c₂), topF_eq (.letE c₁ c₂), em, fm, rm]
    constructor <;> omega
  | load off idx kc =>
    simp only [stepW] at h
    split at h
    · split at h
      · injrun h
        apply top_same k
        · simp only [List.length_cons, envM]; omega
        · simp only [rW]; omega
        · simp only [frD]; omega
      · simp at h
    · simp at h
    · simp at h
  | store off idx v kc =>
    simp only [stepW] at h
    split at h
    · split at h
      · injrun h
        apply top_same k
        · simp only [List.length_cons, envM, Nat.add_assoc, Nat.reduceAdd]; omega
        · simp only [rW]; omega
        · simp only [frD]; omega
      · simp at h
    · simp at h
    · simp at h
    · simp at h
  | app f x =>
    simp only [stepW] at h
    split at h <;> (try split at h) <;> simp_all
  | ite o c₁ c₂ =>
    have m1 : envM c₁ ρ.length ≤ envM (.ite o c₁ c₂) ρ.length := by simp only [envM]; omega
    have m2 : envM c₂ ρ.length ≤ envM (.ite o c₁ c₂) ρ.length := by simp only [envM]; omega
    have r1 : rW c₁ ≤ rW (.ite o c₁ c₂) := by simp only [rW]; omega
    have r2 : rW c₂ ≤ rW (.ite o c₁ c₂) := by simp only [rW]; omega
    have f1 : frD c₁ ≤ frD (.ite o c₁ c₂) := by simp only [frD]; omega
    have f2 : frD c₂ ≤ frD (.ite o c₁ c₂) := by simp only [frD]; omega
    simp only [stepW] at h
    split at h
    · split at h
      · injrun h; exact top_same k m1 r1 f1
      · split at h
        · injrun h; exact top_same k m2 r2 f2
        · simp at h
    · simp at h
    · simp at h
  | case o n₁ n₂ c₁ c₂ =>
    have r1 : rW c₁ ≤ rW (.case o n₁ n₂ c₁ c₂) := by simp only [rW]; omega
    have r2 : rW c₂ ≤ rW (.case o n₁ n₂ c₁ c₂) := by simp only [rW]; omega
    have f1 : frD c₁ ≤ frD (.case o n₁ n₂ c₁ c₂) := by simp only [frD]; omega
    have f2 : frD c₂ ≤ frD (.case o n₁ n₂ c₁ c₂) := by simp only [frD]; omega
    simp only [stepW] at h
    split at h
    · rename_i t ws hev
      split at h
      · injrun h
        refine top_same k ?_ r1 f1
        have := envM_mono c₁ (show (List.take n₁ ws ++ ρ).length ≤ ρ.length + n₁ by simp; omega)
        simp only [envM]; omega
      · split at h
        · injrun h
          refine top_same k ?_ r2 f2
          have := envM_mono c₂ (show (List.take n₂ ws ++ ρ).length ≤ ρ.length + n₂ by simp; omega)
          simp only [envM]; omega
        · simp at h
    · simp at h
    · simp at h

/-- **res_free.** Along every word run with an empty table from `(run main ρ₀ [], m)`, every reached run state has ENV words
    (with `grow`) at most `envM main |ρ₀|` and at most `frD main` pending frames. -/
theorem res_free {main : WCode} {ρ₀ : List W} {m : WMem} :
    ∀ {n : Nat} {W₁ : WSt × WMem}, WN [] n (.run main ρ₀ [], m) W₁ →
      ∀ {c ρ k m'}, W₁ = (.run c ρ k, m') → ρ.length + kSize k + grow c ≤ envM main ρ₀.length ∧ k.length ≤ frD main := by
  suffices H : ∀ {n : Nat} {W W₁ : WSt × WMem}, WN [] n W W₁ → ∀ {c₀ ρ₀' k₀ m₀}, W = (.run c₀ ρ₀' k₀, m₀) →
      ∀ {c ρ k m'}, W₁ = (.run c ρ k, m') → topM c ρ.length k ≤ topM c₀ ρ₀'.length k₀ ∧ topF c k ≤ topF c₀ k₀ by
    intro n W₁ hrun c ρ k m' hW
    obtain ⟨h1, h2⟩ := H hrun rfl hW
    obtain ⟨s1, s2⟩ := size_le_top c ρ k
    have e1 : topM main ρ₀.length [] = envM main ρ₀.length := rfl
    have e2 : topF main [] = frD main := rfl
    rw [e1] at h1; rw [e2] at h2
    exact ⟨by omega, by omega⟩
  intro n W W₁ hrun
  induction hrun with
  | refl W => intro c₀ ρ₀' k₀ m₀ h0 c ρ k m' h1; rw [h0] at h1; cases h1; exact ⟨le_refl _, le_refl _⟩
  | step hs hrest ih =>
    rename_i n' Wa Wb Wc
    intro c₀ ρ₀' k₀ m₀ h0 c ρ k m' h1
    subst h0
    obtain ⟨st, mb⟩ := Wb
    cases st with
    | run cb ρb kb =>
      obtain ⟨a1, a2⟩ := top_step hs
      obtain ⟨b1, b2⟩ := ih rfl h1
      exact ⟨le_trans b1 a1, le_trans b2 a2⟩
    | done ws => cases hrest with
      | refl => cases h1
      | step hs' _ => simp [stepW] at hs'
    | fault => cases hrest with
      | refl => cases h1
      | step hs' _ => simp [stepW] at hs'
    | ovf => cases hrest with
      | refl => cases h1
      | step hs' _ => simp [stepW] at hs'

/-- **resWhy_false.** With an empty table, ENV of at least `8 · envM main |ρ₀|` bytes and STACK room for `frD main + 2` frames,
    no word state reached from `(run main ρ₀ [], m)` has a reason to return RES. -/
theorem resWhy_false {L : Lay3} {main : WCode} {ρ₀ : List W} {m : WMem} {n : Nat} {W₁ : WSt × WMem}
    (hrun : WN [] n (.run main ρ₀ [], m) W₁) (hE : 8 * envM main ρ₀.length ≤ L.env0.toNat - L.envLo.toNat)
    (hS : 16 * (frD main + 2) + 8 ≤ L.rsp0.toNat + 8 - L.stkLo.toNat) : ¬ ResWhy L W₁.1 := by
  obtain ⟨st, m'⟩ := W₁
  cases st with
  | run c ρ k =>
    obtain ⟨h1, h2⟩ := res_free hrun rfl
    simp only [ResWhy, EnvOver, StkOver, List.length_cons]
    omega
  | _ => simp [ResWhy]

end S3M
