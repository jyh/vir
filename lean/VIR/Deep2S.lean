/-
  STATUS-vir row 18, the DEEP STATEMENT CONTROL (predictions/PREDICTIONS-amend-8.md, pinned at vir 5c27056 BEFORE this
  file existed). Deep2's chain with `aux_le_len_adv` (side condition from the OUTER guard, via `Holds`) replaced by
  `aux_le_len_adv_own` (side condition `i < m` on literals; the guard's OWN conjunct `m ≤ y` carries the truncation case).
  `StepS` is Deep2's `Step` plus that one rule; Deep2.lean is not edited.
-/
import VIR.Deep2

namespace VIR.Deep2S

open VIR.Deep (Val DOut)
open VIR.Deep2 (Ix Cond Tm Holds Step den U2 F2 eU eP)

inductive StepS {V : Type} : List (Cond V) → Tm V → Tm V → Prop where
  | base {Γ a b} : Step Γ a b → StepS Γ a b
  -- AUX: the payload bound under advance{b; i}, discharged by the guard's own first conjunct (no context)
  | aux_le_len_adv_own {Γ} (b : V) (i m : Nat) (y z : Ix V) (k : V → Tm V) (e : Tm V) : i < m →
      StepS Γ (.advance b (.lit i) fun s => .guard (.and (.le (.lit m) y) (.le (.add y z) (.add (.len s) (.lit i)))) (k s) e)
              (.advance b (.lit i) fun s => .guard (.and (.le (.lit m) y) (.le (.add y z) (.len b))) (k s) e)
  | cg_guard_ok {Γ c ok ok' err} : StepS (c :: Γ) ok ok' → StepS Γ (.guard c ok err) (.guard c ok' err)
  | cg_read {Γ b j k k'} : (∀ v, StepS Γ (k v) (k' v)) → StepS Γ (.readU32 b j k) (.readU32 b j k')
  | cg_letlin {Γ st p k k'} : (∀ v, StepS Γ (k v) (k' v)) → StepS Γ (.letLinDec st p k) (.letLinDec st p k')
  | trans {Γ} {a b c : Tm V} : StepS Γ a b → StepS Γ b c → StepS Γ a c

variable (acl : Principal → TopicId → Bool)

theorem len_adv_sub (v : Val) (i : Nat) : (v.adv i).len = v.len - i := by
  cases v <;> simp [Val.adv, Val.len]

theorem own_bound (v : Val) (i m Y Z : Nat) (h : i < m) :
    (m ≤ Y ∧ Y + Z ≤ (v.adv i).len + i) ↔ (m ≤ Y ∧ Y + Z ≤ v.len) := by
  rw [len_adv_sub]; omega

theorem StepS.sound {Γ : List (Cond Val)} {a b : Tm Val} (h : StepS Γ a b) :
    (∀ d ∈ Γ, d.eval acl = true) → den acl a = den acl b := by
  induction h with
  | base h => exact h.sound acl
  | aux_le_len_adv_own b i m y z k e hi =>
      intro _
      simp only [den, VIR.Deep2.Cond.eval, VIR.Deep2.Ix.eval, Bool.and_eq_true, decide_eq_true_eq,
        own_bound b i m y.eval z.eval hi]
  | cg_guard_ok _ ih =>
      intro hΓ; simp only [den]
      split
      · next hc => rw [ih (by intro d hd; cases hd with | head => exact hc | tail _ hd => exact hΓ d hd)]
      · rfl
  | cg_read _ ih => intro hΓ; simp only [den]; exact ih _ hΓ
  | cg_letlin _ ih => intro hΓ; simp only [den]; exact ih _ hΓ
  | trans _ _ ih₁ ih₂ => intro hΓ; exact (ih₁ hΓ).trans (ih₂ hΓ)

/-- J5 on the deep embedding with the own-conjunct rule: the SCORED chain of the variant. -/
theorem router2s_fusion_deep_steps {V : Type} (b0 st : V) : StepS [] (U2 b0 st) (F2 b0 st) := by
  unfold U2 F2
  refine .cg_guard_ok (.cg_read fun magic => ?_)
  have inner : ∀ se to off n : V,
      StepS [.isMagic magic, .le (.lit 24) (.len b0)]
        (.advance b0 (.lit 12) fun s1 => .guard (.hasTok st se)
          (.letLinDec st se fun st' => .guard (.canAcc se to)
            (.guard (.and (.le (.lit 24) (.var off)) (.le (.add (.var off) (.var n)) (.add (.len s1) (.lit 12))))
              (.advance s1 (.sub (.var off) 12) fun p => .take p (.var n) fun q => .ret st' q) eP) eU) eU)
        (.guard (.and (.canAcc se to) (.hasTok st se))
          (.letLinDec st se fun st' =>
            .guard (.and (.le (.lit 24) (.var off)) (.le (.add (.var off) (.var n)) (.len b0)))
              (.advance b0 (.var off) fun p => .take p (.var n) fun q => .ret st' q) eP) eU) := by
    intro se to off n
    -- (a)-(c): Deep2's moves
    refine .trans (.base (.aux_advance_past_guard b0 (.lit 12) (.hasTok st se)
      (fun s1 => .letLinDec st se fun st' => .guard (.canAcc se to)
        (.guard (.and (.le (.lit 24) (.var off)) (.le (.add (.var off) (.var n)) (.add (.len s1) (.lit 12))))
          (.advance s1 (.sub (.var off) 12) fun p => .take p (.var n) fun q => .ret st' q) eP) eU) eU)) ?_
    refine .trans (.base (.cg_guard_ok (.aux_advance_past_letlin b0 (.lit 12) st se
      (fun s1 x => .guard (.canAcc se to)
        (.guard (.and (.le (.lit 24) (.var off)) (.le (.add (.var off) (.var n)) (.add (.len s1) (.lit 12))))
          (.advance s1 (.sub (.var off) 12) fun p => .take p (.var n) fun q => .ret x q) eP) eU)))) ?_
    refine .trans (.base (.cg_guard_ok (.cg_letlin fun x => .aux_advance_past_guard b0 (.lit 12) (.canAcc se to)
      (fun s1 => .guard (.and (.le (.lit 24) (.var off)) (.le (.add (.var off) (.var n)) (.add (.len s1) (.lit 12))))
          (.advance s1 (.sub (.var off) 12) fun p => .take p (.var n) fun q => .ret x q) eP) eU))) ?_
    -- (d), the variant: the payload bound from the guard's OWN conjunct 24 ≤ off (12 < 24), no context
    refine .trans (.cg_guard_ok (.cg_letlin fun x => .cg_guard_ok
      (.aux_le_len_adv_own b0 12 24 (.var off) (.var n)
        (fun s1 => .advance s1 (.sub (.var off) 12) fun p => .take p (.var n) fun q => .ret x q) eP (by decide)))) ?_
    -- (e)-(h): Deep2's moves
    refine .trans (.base (.cg_guard_ok (.cg_letlin fun x => .cg_guard_ok
      (.aux_advance_past_guard b0 (.lit 12) (.and (.le (.lit 24) (.var off)) (.le (.add (.var off) (.var n)) (.len b0)))
        (fun s1 => .advance s1 (.sub (.var off) 12) fun p => .take p (.var n) fun q => .ret x q) eP)))) ?_
    refine .trans (.base (.cg_guard_ok (.cg_letlin fun x => .cg_guard_ok (.cg_guard_ok
      (.trans (.slice_fuse b0 (.lit 12) (.sub (.var off) 12) (fun p => .take p (.var n) fun q => .ret x q))
        (.aux_advance_idx b0 24 12 (.var off) (fun p => .take p (.var n) fun q => .ret x q)
          (.andL (d := .le (.add (.var off) (.var n)) (.len b0)) (.mem (by simp))) (by decide))))))) ?_
    refine .trans (.base (.cg_guard_ok (.aux_letlin_past_guard st se (.canAcc se to)
      (fun x => .guard (.and (.le (.lit 24) (.var off)) (.le (.add (.var off) (.var n)) (.len b0)))
        (.advance b0 (.var off) fun p => .take p (.var n) fun q => .ret x q) eP) eU))) ?_
    refine .trans (.base (.aux_guard_swap (.hasTok st se) (.canAcc se to) _ eU)) ?_
    exact .base (.guard_merge _ _ _ eU)
  refine .trans (.base (.aux_read_past_guard (.isMagic magic) b0 4 _ eU)) ?_
  refine .trans (.base (.cg_read fun se => .aux_read_past_guard (.isMagic magic) b0 8 _ eU)) ?_
  refine .trans (.base (.cg_read fun se => .cg_read fun to => .aux_read_past_guard (.isMagic magic) b0 12 _ eU)) ?_
  refine .trans (.base (.cg_read fun se => .cg_read fun to => .cg_read fun off =>
    .aux_read_past_guard (.isMagic magic) b0 16 _ eU)) ?_
  refine .cg_read fun se => .cg_read fun to => .cg_read fun off => .cg_read fun n => ?_
  exact .trans (.cg_guard_ok (inner se to off n)) (.base (.guard_merge _ _ _ eU))

theorem router2s_fusion_deep (b0 st : Val) : den acl (U2 b0 st) = den acl (F2 b0 st) :=
  (router2s_fusion_deep_steps b0 st).sound acl (by simp)

end VIR.Deep2S
