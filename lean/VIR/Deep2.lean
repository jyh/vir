/-
  L-DEEP PROGRAM 2 (STATUS-vir row 13; inputs/program2-inputs.md J1-J5; scored by PREDICTIONS-program2 Q3).
  Program 1's `VIR.Deep.Step` has NO hypothesis context, so a rewrite whose side condition comes from an enclosing
  guard cannot be stated in it. This file is program 1's deep embedding plus exactly what program 2 needs:
  * offsets are INDEX EXPRESSIONS (`Ix`): a read value, a length, a literal, `+`, and truncated `−`;
  * `Step Γ a b` carries the conditions of the guards it is under (`cg_guard_ok` pushes the guard's condition);
  * `Holds Γ c` is the syntactic entailment the side conditions use (membership, and the two `∧` projections);
  * two AUX rules beyond program 1's five: `aux_advance_idx` (the context-dependent index rewrite J4 names) and
    `aux_le_len_adv` (len(s)+i = len(b) under advance{b; i; s. …}, given i ≤ len(b) from the context).
  Program 1's file is not edited; its rules are restated here over `Ix` under the same names.
-/
import VIR.Deep

namespace VIR.Deep2

open VIR.Deep (Val DOut)

/-- Index expressions: the offsets and lengths the payload arithmetic needs (A.2's relop atoms over read values). -/
inductive Ix (V : Type) where
  | lit (n : Nat)
  | var (v : V)          -- a read value (u32), as a natural
  | len (b : V)          -- len(b)
  | add (a b : Ix V)
  | sub (a : Ix V) (k : Nat)

inductive Cond (V : Type) where
  | le       (a b : Ix V)
  | isMagic  (v : V)
  | canAcc   (p t : V)
  | hasTok   (st p : V)
  | and      (c d : Cond V)

inductive Tm (V : Type) where
  | letLinDec (st p : V) (k : V → Tm V)
  | advance   (b : V) (i : Ix V) (k : V → Tm V)
  | take      (b : V) (n : Ix V) (k : V → Tm V)   -- J1 take{s; n; p. k}
  | readU32   (b : V) (j : Nat) (k : V → Tm V)
  | guard     (c : Cond V) (ok err : Tm V)
  | ret       (st p : V)
  | drop      (c : Code)

/-- Syntactic entailment from a context of guard conditions. -/
inductive Holds {V : Type} : List (Cond V) → Cond V → Prop where
  | mem  {Γ c} : c ∈ Γ → Holds Γ c
  | andL {Γ c d} : Holds Γ (.and c d) → Holds Γ c
  | andR {Γ c d} : Holds Γ (.and c d) → Holds Γ d

inductive Step {V : Type} : List (Cond V) → Tm V → Tm V → Prop where
  -- GIVEN (A.3)
  | slice_fuse {Γ} (b : V) (i j : Ix V) (k : V → Tm V) :
      Step Γ (.advance b i fun s => .advance s j k) (.advance b (.add i j) k)
  | guard_merge {Γ} (c₁ c₂ : Cond V) (ok err : Tm V) :
      Step Γ (.guard c₁ (.guard c₂ ok err) err) (.guard (.and c₁ c₂) ok err)
  -- AUX, program 1's five (E8), over Ix
  | aux_read_past_guard {Γ} (c : Cond V) (b : V) (j : Nat) (k : V → Tm V) (e : Tm V) :
      Step Γ (.guard c (.readU32 b j k) e) (.readU32 b j fun v => .guard c (k v) e)
  | aux_advance_past_guard {Γ} (b : V) (i : Ix V) (c : Cond V) (k : V → Tm V) (e : Tm V) :
      Step Γ (.advance b i fun s => .guard c (k s) e) (.guard c (.advance b i k) e)
  | aux_advance_past_letlin {Γ} (b : V) (i : Ix V) (st p : V) (k : V → V → Tm V) :
      Step Γ (.advance b i fun s => .letLinDec st p fun x => k s x) (.letLinDec st p fun x => .advance b i fun s => k s x)
  | aux_letlin_past_guard {Γ} (st p : V) (c : Cond V) (k : V → Tm V) (e : Tm V) :
      Step Γ (.letLinDec st p fun x => .guard c (k x) e) (.guard c (.letLinDec st p k) e)
  | aux_guard_swap {Γ} (a b : Cond V) (k e : Tm V) :
      Step Γ (.guard a (.guard b k e) e) (.guard b (.guard a k e) e)
  -- AUX, program 2 (Q3): side conditions discharged from the CONTEXT
  | aux_advance_idx {Γ} (b : V) (m k : Nat) (x : Ix V) (K : V → Tm V) :
      Holds Γ (.le (.lit m) x) → k ≤ m →
      Step Γ (.advance b (.add (.lit k) (.sub x k)) K) (.advance b x K)
  | aux_le_len_adv {Γ} (b : V) (i m : Nat) (c : Cond V) (x : Ix V) (k : V → Tm V) (e : Tm V) :
      Holds Γ (.le (.lit m) (.len b)) → i ≤ m →
      Step Γ (.advance b (.lit i) fun s => .guard (.and c (.le x (.add (.len s) (.lit i)))) (k s) e)
             (.advance b (.lit i) fun s => .guard (.and c (.le x (.len b))) (k s) e)
  -- congruence (free); the guard's ok-branch is rewritten UNDER its condition
  | cg_guard_ok {Γ c ok ok' err} : Step (c :: Γ) ok ok' → Step Γ (.guard c ok err) (.guard c ok' err)
  | cg_read {Γ b j k k'} : (∀ v, Step Γ (k v) (k' v)) → Step Γ (.readU32 b j k) (.readU32 b j k')
  | cg_advance {Γ b i k k'} : (∀ v, Step Γ (k v) (k' v)) → Step Γ (.advance b i k) (.advance b i k')
  | cg_letlin {Γ st p k k'} : (∀ v, Step Γ (k v) (k' v)) → Step Γ (.letLinDec st p k) (.letLinDec st p k')
  | refl {Γ} (t : Tm V) : Step Γ t t
  | trans {Γ} {a b c : Tm V} : Step Γ a b → Step Γ b c → Step Γ a c

/-! ## Denotation (program 1's `Val`, plus take) -/
def _root_.VIR.Deep.Val.toN : Val → Nat
  | .int i => i.toNat
  | _ => 0

def _root_.VIR.Deep.Val.take : Val → Nat → Val
  | .slice b o _, n => .slice b o n
  | v, _ => v

def Ix.eval : Ix Val → Nat
  | .lit n => n
  | .var v => v.toN
  | .len b => b.len
  | .add a b => a.eval + b.eval
  | .sub a k => a.eval - k

variable (acl : Principal → TopicId → Bool)

def Cond.eval : Cond Val → Bool
  | .le a b => decide (a.eval ≤ b.eval)
  | .isMagic v => decide (v.toP = MAGIC)
  | .canAcc p t => acl p.toP t.toP
  | .hasTok st p => decide (0 < st.st p.toP)
  | .and c d => c.eval && d.eval

def den : Tm Val → DOut
  | .letLinDec st p k => den (k (.state (decTokens st.st p.toP)))
  | .advance b i k => den (k (b.adv i.eval))
  | .take b n k => den (k (b.take n.eval))
  | .readU32 b j k => den (k (b.rd j))
  | .guard c ok err => if c.eval acl then den ok else den err
  | .ret st p => .ret st p
  | .drop c => .drop c

theorem Holds.sound {Γ : List (Cond Val)} {c : Cond Val} (h : Holds Γ c)
    (hΓ : ∀ d ∈ Γ, d.eval acl = true) : c.eval acl = true := by
  induction h with
  | mem hm => exact hΓ _ hm
  | andL _ ih => simp only [Cond.eval, Bool.and_eq_true] at ih; exact ih.1
  | andR _ ih => simp only [Cond.eval, Bool.and_eq_true] at ih; exact ih.2

theorem _root_.VIR.Deep.Val.len_adv (v : Val) (i : Nat) (h : i ≤ v.len) : (v.adv i).len + i = v.len := by
  cases v <;> simp_all [Val.adv, Val.len] <;> omega

/-- Every step preserves the denotation, in any valuation satisfying its context. -/
theorem Step.sound {Γ : List (Cond Val)} {a b : Tm Val} (h : Step Γ a b) :
    (∀ d ∈ Γ, d.eval acl = true) → den acl a = den acl b := by
  induction h with
  | slice_fuse b i j k => intro _; simp [den, Ix.eval, Val.adv_adv]
  | guard_merge c₁ c₂ ok err =>
      intro _; simp only [den, Cond.eval]
      by_cases h₁ : c₁.eval acl = true <;> by_cases h₂ : c₂.eval acl = true <;> simp [h₁, h₂]
  | aux_read_past_guard => intro _; simp [den]
  | aux_advance_past_guard => intro _; simp [den]
  | aux_advance_past_letlin => intro _; simp [den]
  | aux_letlin_past_guard => intro _; simp [den]
  | aux_guard_swap a b k e =>
      intro _; simp only [den]; cases h₁ : a.eval acl <;> cases h₂ : b.eval acl <;> simp
  | aux_advance_idx b m k x K hx hk =>
      intro hΓ
      have := hx.sound acl hΓ
      simp only [Cond.eval, Ix.eval, decide_eq_true_eq] at this
      have e : k + (x.eval - k) = x.eval := by omega
      simp only [den, Ix.eval, e]
  | aux_le_len_adv b i m c x k e hb hi =>
      intro hΓ
      have := hb.sound acl hΓ
      simp only [Cond.eval, Ix.eval, decide_eq_true_eq] at this
      have e' : (b.adv i).len + i = b.len := Val.len_adv b i (by omega)
      simp only [den, Cond.eval, Ix.eval, e']
      rfl
  | cg_guard_ok _ ih =>
      intro hΓ; simp only [den]
      split
      · next hc => rw [ih (by intro d hd; cases hd with | head => exact hc | tail _ hd => exact hΓ d hd)]
      · rfl
  | cg_read _ ih => intro hΓ; simp only [den]; exact ih _ hΓ
  | cg_advance _ ih => intro hΓ; simp only [den]; exact ih _ hΓ
  | cg_letlin _ ih => intro hΓ; simp only [den]; exact ih _ hΓ
  | refl => intro _; rfl
  | trans _ _ ih₁ ih₂ => intro hΓ; exact (ih₁ hΓ).trans (ih₂ hΓ)

/-! ## J3 (U2) and J4 (F2) as deep terms -/
def eU {V : Type} : Tm V := .drop .unauthOrRate
def eP {V : Type} : Tm V := .drop .badPayload

/-- J2's payload guard, read in U2 against s1 = b0 advanced by 12: `24 ≤ off ∧ off + n ≤ len(s1) + 12`. -/
def U2 {V : Type} (b0 st : V) : Tm V :=
  .guard (.le (.lit 24) (.len b0))
    (.readU32 b0 0 fun magic => .guard (.isMagic magic)
      (.readU32 b0 4 fun sender => .readU32 b0 8 fun topic => .readU32 b0 12 fun off => .readU32 b0 16 fun n =>
        .advance b0 (.lit 12) fun s1 =>
        .guard (.hasTok st sender)
          (.letLinDec st sender fun st' => .guard (.canAcc sender topic)
            (.guard (.and (.le (.lit 24) (.var off)) (.le (.add (.var off) (.var n)) (.add (.len s1) (.lit 12))))
              (.advance s1 (.sub (.var off) 12) fun p => .take p (.var n) fun q => .ret st' q)
              eP)
            eU)
          eU)
      eU)
    (.drop .truncated)

def F2 {V : Type} (b0 st : V) : Tm V :=
  .guard (.le (.lit 24) (.len b0))
    (.readU32 b0 0 fun magic => .readU32 b0 4 fun sender => .readU32 b0 8 fun topic =>
      .readU32 b0 12 fun off => .readU32 b0 16 fun n =>
      .guard (.and (.isMagic magic) (.and (.canAcc sender topic) (.hasTok st sender)))
        (.letLinDec st sender fun st' =>
          .guard (.and (.le (.lit 24) (.var off)) (.le (.add (.var off) (.var n)) (.len b0)))
            (.advance b0 (.var off) fun p => .take p (.var n) fun q => .ret st' q)
            eP)
        eU)
    (.drop .truncated)

/-- J5 on the deep embedding, the SCORED chain (I7): every step is a named rule, a congruence, or `trans`. -/
theorem router2_fusion_deep_steps {V : Type} (b0 st : V) : Step [] (U2 b0 st) (F2 b0 st) := by
  unfold U2 F2
  refine .cg_guard_ok (.cg_read fun magic => ?_)
  -- the inner block for fixed sender/topic/off/n, under the magic guard and the length guard
  have inner : ∀ se to off n : V,
      Step [.isMagic magic, .le (.lit 24) (.len b0)]
        (.advance b0 (.lit 12) fun s1 => .guard (.hasTok st se)
          (.letLinDec st se fun st' => .guard (.canAcc se to)
            (.guard (.and (.le (.lit 24) (.var off)) (.le (.add (.var off) (.var n)) (.add (.len s1) (.lit 12))))
              (.advance s1 (.sub (.var off) 12) fun p => .take p (.var n) fun q => .ret st' q) eP) eU) eU)
        (.guard (.and (.canAcc se to) (.hasTok st se))
          (.letLinDec st se fun st' =>
            .guard (.and (.le (.lit 24) (.var off)) (.le (.add (.var off) (.var n)) (.len b0)))
              (.advance b0 (.var off) fun p => .take p (.var n) fun q => .ret st' q) eP) eU) := by
    intro se to off n
    -- (a)-(c): sink advance{b0; 12} past the token guard, the let_lin and the ACL guard (program 1's moves)
    refine .trans (.aux_advance_past_guard b0 (.lit 12) (.hasTok st se)
      (fun s1 => .letLinDec st se fun st' => .guard (.canAcc se to)
        (.guard (.and (.le (.lit 24) (.var off)) (.le (.add (.var off) (.var n)) (.add (.len s1) (.lit 12))))
          (.advance s1 (.sub (.var off) 12) fun p => .take p (.var n) fun q => .ret st' q) eP) eU) eU) ?_
    refine .trans (.cg_guard_ok (.aux_advance_past_letlin b0 (.lit 12) st se
      (fun s1 x => .guard (.canAcc se to)
        (.guard (.and (.le (.lit 24) (.var off)) (.le (.add (.var off) (.var n)) (.add (.len s1) (.lit 12))))
          (.advance s1 (.sub (.var off) 12) fun p => .take p (.var n) fun q => .ret x q) eP) eU))) ?_
    refine .trans (.cg_guard_ok (.cg_letlin fun x => .aux_advance_past_guard b0 (.lit 12) (.canAcc se to)
      (fun s1 => .guard (.and (.le (.lit 24) (.var off)) (.le (.add (.var off) (.var n)) (.add (.len s1) (.lit 12))))
          (.advance s1 (.sub (.var off) 12) fun p => .take p (.var n) fun q => .ret x q) eP) eU)) ?_
    -- (d): the payload bound, len(s1)+12 = len(b0), from the OUTER length guard in the context
    refine .trans (.cg_guard_ok (.cg_letlin fun x => .cg_guard_ok
      (.aux_le_len_adv b0 12 24 (.le (.lit 24) (.var off)) (.add (.var off) (.var n))
        (fun s1 => .advance s1 (.sub (.var off) 12) fun p => .take p (.var n) fun q => .ret x q) eP
        (.mem (by simp)) (by decide)))) ?_
    -- (e): the payload guard no longer mentions s1, so advance{b0; 12} sinks past it
    refine .trans (.cg_guard_ok (.cg_letlin fun x => .cg_guard_ok
      (.aux_advance_past_guard b0 (.lit 12) (.and (.le (.lit 24) (.var off)) (.le (.add (.var off) (.var n)) (.len b0)))
        (fun s1 => .advance s1 (.sub (.var off) 12) fun p => .take p (.var n) fun q => .ret x q) eP))) ?_
    -- (f)-(g): slice_fuse, then 12 + (off − 12) = off from the payload guard's 24 ≤ off (the context-dependent rewrite)
    refine .trans (.cg_guard_ok (.cg_letlin fun x => .cg_guard_ok (.cg_guard_ok
      (.trans (.slice_fuse b0 (.lit 12) (.sub (.var off) 12) (fun p => .take p (.var n) fun q => .ret x q))
        (.aux_advance_idx b0 24 12 (.var off) (fun p => .take p (.var n) fun q => .ret x q)
          (.andL (d := .le (.add (.var off) (.var n)) (.len b0)) (.mem (by simp))) (by decide)))))) ?_
    -- (h): the ACL guard out past the let_lin, swap, merge (program 1's moves)
    refine .trans (.cg_guard_ok (.aux_letlin_past_guard st se (.canAcc se to)
      (fun x => .guard (.and (.le (.lit 24) (.var off)) (.le (.add (.var off) (.var n)) (.len b0)))
        (.advance b0 (.var off) fun p => .take p (.var n) fun q => .ret x q) eP) eU)) ?_
    refine .trans (.aux_guard_swap (.hasTok st se) (.canAcc se to) _ eU) ?_
    exact .guard_merge _ _ _ eU
  -- hoist the four reads out of the magic guard, rewrite the inner block, merge the magic guard
  refine .trans (.aux_read_past_guard (.isMagic magic) b0 4 _ eU) ?_
  refine .trans (.cg_read fun se => .aux_read_past_guard (.isMagic magic) b0 8 _ eU) ?_
  refine .trans (.cg_read fun se => .cg_read fun to => .aux_read_past_guard (.isMagic magic) b0 12 _ eU) ?_
  refine .trans (.cg_read fun se => .cg_read fun to => .cg_read fun off =>
    .aux_read_past_guard (.isMagic magic) b0 16 _ eU) ?_
  refine .cg_read fun se => .cg_read fun to => .cg_read fun off => .cg_read fun n => ?_
  exact .trans (.cg_guard_ok (inner se to off n)) (.guard_merge _ _ _ eU)

/-- J5's corollary on the deep embedding: equality of denotations, through the sound rules. -/
theorem router2_fusion_deep (b0 st : Val) : den acl (U2 b0 st) = den acl (F2 b0 st) :=
  (router2_fusion_deep_steps b0 st).sound acl (by simp)

end VIR.Deep2
