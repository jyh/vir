/-
  L-DEEP (STATUS-vir row 9, amend-2's queued variant): a DEEP, parametric-HOAS embedding of the A.2 grammar.
  The rules are constructors of a syntactic rewrite relation `Step`; each is proved SOUND against a denotation;
  I4 is a chain `Steps (U b0 st) (F b0 st)` and its corollary, equality of denotations.
  Values are untyped (CTT-like) and slices are FLAT inside them, so this variant measures C3 (rules), not C1.
-/
import VIR.Core

namespace VIR.Deep

/-- Guard conditions: the A.2 relop atoms plus the I1 constants and `∧`. -/
inductive Cond (V : Type) where
  | lenGe    (b : V) (k : Nat)
  | isMagic  (v : V)
  | canAcc   (p t : V)
  | hasTok   (st p : V)
  | and      (c d : Cond V)

inductive Tm (V : Type) where
  | letLinDec (st p : V) (k : V → Tm V)           -- let_lin{dec_tokens(st, p); st'. k}
  | advance   (b : V) (i : Nat) (k : V → Tm V)    -- advance{b; i; s. k}
  | readU32   (b : V) (j : Nat) (k : V → Tm V)    -- read_u32{b; j; v. k}
  | guard     (c : Cond V) (ok err : Tm V)        -- guard{c; ok; err}
  | ret       (st p : V)                          -- return{(st, p)}
  | drop      (c : Code)                          -- drop{code}


/-! ## The rewrite relation: the GIVEN rules used, the AUX rules (`aux_*`), and congruence (free, I7). -/
inductive Step {V : Type} : Tm V → Tm V → Prop where
  -- GIVEN (A.3)
  | slice_fuse (b : V) (i j : Nat) (k : V → Tm V) :
      Step (.advance b i fun s => .advance s j k) (.advance b (i + j) k)
  | guard_merge (c₁ c₂ : Cond V) (ok err : Tm V) :
      Step (.guard c₁ (.guard c₂ ok err) err) (.guard (.and c₁ c₂) ok err)
  -- AUX (E8)
  | aux_read_past_guard (c : Cond V) (b : V) (j : Nat) (k : V → Tm V) (e : Tm V) :
      Step (.guard c (.readU32 b j k) e) (.readU32 b j fun v => .guard c (k v) e)
  | aux_advance_past_guard (b : V) (i : Nat) (c : Cond V) (k : V → Tm V) (e : Tm V) :
      Step (.advance b i fun s => .guard c (k s) e) (.guard c (.advance b i k) e)
  | aux_advance_past_letlin (b : V) (i : Nat) (st p : V) (k : V → V → Tm V) :
      Step (.advance b i fun s => .letLinDec st p fun x => k s x) (.letLinDec st p fun x => .advance b i fun s => k s x)
  | aux_letlin_past_guard (st p : V) (c : Cond V) (k : V → Tm V) (e : Tm V) :
      Step (.letLinDec st p fun x => .guard c (k x) e) (.guard c (.letLinDec st p k) e)
  | aux_guard_swap (a b : Cond V) (k e : Tm V) :
      Step (.guard a (.guard b k e) e) (.guard b (.guard a k e) e)
  -- congruence (free)
  | cg_guard_ok {c ok ok' err} : Step ok ok' → Step (.guard c ok err) (.guard c ok' err)
  | cg_read {b j k k'} : (∀ v, Step (k v) (k' v)) → Step (.readU32 b j k) (.readU32 b j k')
  | cg_advance {b i k k'} : (∀ v, Step (k v) (k' v)) → Step (.advance b i k) (.advance b i k')
  | cg_letlin {st p k k'} : (∀ v, Step (k v) (k' v)) → Step (.letLinDec st p k) (.letLinDec st p k')
  | refl (t : Tm V) : Step t t
  | trans {a b c : Tm V} : Step a b → Step b c → Step a c

/-! ## Denotation (values untyped, slices flat) -/
inductive Val where
  | int   (i : Int)
  | slice (buf : ByteArray) (off len : Nat)
  | state (st : State)

def Val.adv : Val → Nat → Val
  | .slice b o l, i => .slice b (o + i) (l - i)
  | v, _ => v

def Val.rd : Val → Nat → Val
  | .slice b o _, j =>
      let g := fun k => (b.get! (o + j + k)).toUInt32
      .int (g 0 ||| (g 1 <<< 8) ||| (g 2 <<< 16) ||| (g 3 <<< 24)).toNat
  | _, _ => .int 0

def Val.len : Val → Nat
  | .slice _ _ l => l
  | _ => 0

def Val.toP : Val → UInt32
  | .int i => i.toNat.toUInt32
  | _ => 0

def Val.st : Val → State
  | .state s => s
  | _ => fun _ => 0

inductive DOut where
  | ret (st p : Val)
  | drop (c : Code)

variable (acl : Principal → TopicId → Bool)

def Cond.eval : Cond Val → Bool
  | .lenGe b k => decide (k ≤ b.len)
  | .isMagic v => decide (v.toP = MAGIC)
  | .canAcc p t => acl p.toP t.toP
  | .hasTok st p => decide (0 < st.st p.toP)
  | .and c d => c.eval && d.eval

def den : Tm Val → DOut
  | .letLinDec st p k => den (k (.state (decTokens st.st p.toP)))
  | .advance b i k => den (k (b.adv i))
  | .readU32 b j k => den (k (b.rd j))
  | .guard c ok err => if c.eval acl then den ok else den err
  | .ret st p => .ret st p
  | .drop c => .drop c

theorem Val.adv_adv (v : Val) (i j : Nat) : (v.adv i).adv j = v.adv (i + j) := by
  cases v <;> simp [Val.adv, Nat.add_assoc, Nat.sub_sub]

/-- Every step preserves the denotation. -/
theorem Step.sound {a b : Tm Val} (h : Step a b) : den acl a = den acl b := by
  induction h with
  | slice_fuse b i j k => simp [den, Val.adv_adv]
  | guard_merge c₁ c₂ ok err =>
      simp only [den, Cond.eval]
      by_cases h₁ : c₁.eval acl = true <;> by_cases h₂ : c₂.eval acl = true <;> simp [h₁, h₂]
  | aux_read_past_guard => simp [den]
  | aux_advance_past_guard => simp [den]
  | aux_advance_past_letlin => simp [den]
  | aux_letlin_past_guard => simp [den]
  | aux_guard_swap a b k e =>
      simp only [den]; cases h₁ : a.eval acl <;> cases h₂ : b.eval acl <;> simp
  | cg_guard_ok _ ih => simp only [den]; rw [ih]
  | cg_read _ ih => simp only [den]; exact ih _
  | cg_advance _ ih => simp only [den]; exact ih _
  | cg_letlin _ ih => simp only [den]; exact ih _
  | refl => rfl
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-! ## I2–I4 as deep terms -/
def eU {V : Type} : Tm V := .drop .unauthOrRate

def U {V : Type} (b0 st : V) : Tm V :=
  .guard (.lenGe b0 24)
    (.readU32 b0 0 fun magic => .guard (.isMagic magic)
      (.readU32 b0 4 fun sender => .readU32 b0 8 fun topic => .advance b0 12 fun s1 =>
        .guard (.hasTok st sender)
          (.letLinDec st sender fun st' => .guard (.canAcc sender topic) (.advance s1 12 fun p => .ret st' p) eU)
          eU)
      eU)
    (.drop .truncated)

def F {V : Type} (b0 st : V) : Tm V :=
  .guard (.lenGe b0 24)
    (.readU32 b0 0 fun magic => .readU32 b0 4 fun sender => .readU32 b0 8 fun topic =>
      .guard (.and (.isMagic magic) (.and (.canAcc sender topic) (.hasTok st sender)))
        (.letLinDec st sender fun st' => .advance b0 24 fun p => .ret st' p)
        eU)
    (.drop .truncated)

/-- I4 on the deep embedding, the SCORED chain (I7): every step is a named rule, a congruence, or `trans`. -/
theorem router_fusion_deep_steps {V : Type} (b0 st : V) : Step (U b0 st) (F b0 st) := by
  unfold U F
  refine .cg_guard_ok (.cg_read fun magic => ?_)
  -- the router's inner block, for fixed sender/topic: A0 ⟶ .guard (.canAcc ∧ hasTok) X eU
  have inner : ∀ se to : V,
      Step (.advance b0 12 fun s1 => .guard (.hasTok st se)
              (.letLinDec st se fun st' => .guard (.canAcc se to) (.advance s1 12 fun p => .ret st' p) eU) eU)
           (.guard (.and (.canAcc se to) (.hasTok st se))
              (.letLinDec st se fun st' => .advance b0 24 fun p => .ret st' p) eU) := by
    intro se to
    refine .trans (.aux_advance_past_guard b0 12 (.hasTok st se)
      (fun s1 => .letLinDec st se fun st' => .guard (.canAcc se to) (.advance s1 12 fun p => .ret st' p) eU) eU) ?_
    refine .trans (.cg_guard_ok (.aux_advance_past_letlin b0 12 st se
      (fun s1 x => .guard (.canAcc se to) (.advance s1 12 fun p => .ret x p) eU))) ?_
    refine .trans (.cg_guard_ok (.cg_letlin fun x => .aux_advance_past_guard b0 12 (.canAcc se to)
      (fun s1 => .advance s1 12 fun p => .ret x p) eU)) ?_
    refine .trans (.cg_guard_ok (.cg_letlin fun x => .cg_guard_ok
      (.slice_fuse b0 12 12 (fun p => .ret x p)))) ?_
    refine .trans (.cg_guard_ok (.aux_letlin_past_guard st se (.canAcc se to)
      (fun x => .advance b0 24 fun p => .ret x p) eU)) ?_
    refine .trans (.aux_guard_swap (.hasTok st se) (.canAcc se to) _ eU) ?_
    exact .guard_merge _ _ _ eU
  -- hoist the two reads out of the magic guard, then rewrite the inner block, then merge the magic .guard
  refine .trans (.aux_read_past_guard (.isMagic magic) b0 4 _ eU) ?_
  refine .trans (.cg_read fun se => .aux_read_past_guard (.isMagic magic) b0 8 _ eU) ?_
  refine .cg_read fun se => .cg_read fun to => ?_
  exact .trans (.cg_guard_ok (inner se to)) (.guard_merge _ _ _ eU)

/-- I4's corollary on the deep embedding: equality of denotations, through the sound rules. -/
theorem router_fusion_deep (b0 st : Val) : den acl (U b0 st) = den acl (F b0 st) :=
  (router_fusion_deep_steps b0 st).sound acl

end VIR.Deep
