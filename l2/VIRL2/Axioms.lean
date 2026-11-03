/-
  O95 layer L2, Lean arm. OBJECT-L2 §5: the small axioms of the four operations, and the `let x ← o(a⃗) in e` rule that
  sequences one with its continuation. An operation is specified by an OP TRIPLE: from a fragment σ ⊨ P with any disjoint
  frame σ_f, the operation succeeds and leaves σq ⊎ σ_f with σq ⊨ Q v, the frame untouched and the whole store well-formed.
  Each small axiom is proved by the operation's LOCALITY on Finmap (amend-16 Y4: one locality argument per operation).
-/
import VIRL2.Logic

namespace VIRL2
open VIRL1

def OpTriple (P : Assn) (o : Op) (vs : List Atom₂) (Q : Atom₂ → Assn) : Prop :=
  ∀ σ σf, P σ → Store.Disj σ σf → Store.WF (σ ⊎ σf) →
    ∃ v σq, opStep o vs (σ ⊎ σf) = some (v, σq ⊎ σf) ∧ Store.Disj σq σf ∧ Store.WF (σq ⊎ σf) ∧ Q v σq

theorem step₂_letOp_inv {o as τ e σ c'} (h : Step₂ (Tm.letOp o as τ e, σ) c') :
    ∃ vs v σ', Atom.evalL as = some vs ∧ opStep o vs σ = some (v, σ') ∧ c' = (e.subst 0 v, σ') := by
  cases h with
  | pure h => cases h
  | op h₁ h₂ => exact ⟨_, _, _, h₁, h₂, rfl⟩

/-- The `let x:τ ← o(a⃗) in e` rule. -/
theorem letOp_rule {P : Assn} {o : Op} {as : List Atom₂} {τ : Ty₂} {e : Tm₂} {R : Atom₂ → Assn} {vs : List Atom₂}
    {Q : Atom₂ → Assn} (hvs : Atom.evalL as = some vs) (ho : OpTriple P o vs Q)
    (hk : ∀ v, Triple (Q v) (e.subst 0 v) R) : Triple P (.letOp o as τ e) R := by
  intro σ σf hP hd hwf
  obtain ⟨v, σq, hop, hdq, hwfq, hQ⟩ := ho σ σf hP hd hwf
  obtain ⟨hs, hpost⟩ := hk v σq σf hQ hdq hwfq
  refine ⟨fun c hc => ?_, fun a σ' hc => ?_⟩
  · cases hc with
    | refl => exact fun hf => hf.2 _ (.op hvs hop)
    | step h₁ h₂ =>
      obtain ⟨vs', v', σ', h₁', h₂', rfl⟩ := step₂_letOp_inv h₁
      rw [hvs] at h₁'; cases h₁'; rw [hop] at h₂'; cases h₂'
      exact hs c h₂
  · cases hc with
    | step h₁ h₂ =>
      obtain ⟨vs', v', σ', h₁', h₂', rfl⟩ := step₂_letOp_inv h₁
      rw [hvs] at h₁'; cases h₁'; rw [hop] at h₂'; cases h₂'
      exact hpost a σ' h₂

/-! ## load and store: a fragment owning the region entry R(p) = n and the one cell p + i. -/

/-- The fragment `reg p n ∗ (p + i ↦ w)`. -/
def cellFrag (p : Int) (n : Nat) (i w : Int) : Store := ⟨Finmap.singleton (p + i) w, Finmap.singleton p n⟩

theorem load_axiom (p : Int) (n : Nat) (i w : Int) (hi : 0 ≤ i ∧ i < n) :
    OpTriple (fun σ => σ = cellFrag p n i w) .load [.const (.cap p), .const (.int i)]
      (fun v σ => v = .const (.int w) ∧ σ = cellFrag p n i w) := by
  rintro σ σf rfl hd hwf
  refine ⟨.const (.int w), cellFrag p n i w, ?_, hd, hwf, rfl, rfl⟩
  have hR : (cellFrag p n i w ⊎ σf).R.lookup p = some n := by
    simp [cellFrag, Store.union, Finmap.lookup_union_left, Finmap.mem_singleton, Finmap.lookup_singleton_eq]
  have hH : (cellFrag p n i w ⊎ σf).H.lookup (p + i) = some w := by
    simp [cellFrag, Store.union, Finmap.lookup_union_left, Finmap.mem_singleton, Finmap.lookup_singleton_eq]
  simp [opStep, Store.load, hR, hi, hH]

theorem wf_insert_mem {σ : Store} {k v : Int} (hk : k ∈ σ.H) (h : σ.WF) : Store.WF ⟨σ.H.insert k v, σ.R⟩ where
  pos := h.pos
  disj := h.disj
  domH a := by
    rw [Finmap.mem_insert, ← h.domH a]
    constructor
    · rintro (rfl | ha) <;> assumption
    · exact Or.inr

theorem store_axiom (p : Int) (n : Nat) (i w v : Int) (hi : 0 ≤ i ∧ i < n) :
    OpTriple (fun σ => σ = cellFrag p n i w) .store [.const (.cap p), .const (.int i), .const (.int v)]
      (fun c σ => c = .const (.cap p) ∧ σ = cellFrag p n i v) := by
  rintro σ σf rfl hd hwf
  have hR : (cellFrag p n i w ⊎ σf).R.lookup p = some n := by
    simp [cellFrag, Store.union, Finmap.lookup_union_left, Finmap.mem_singleton, Finmap.lookup_singleton_eq]
  have hins : (cellFrag p n i w ⊎ σf).H.insert (p + i) v = (cellFrag p n i v ⊎ σf).H := by
    simp [cellFrag, Store.union, Finmap.insert_union, Finmap.insert_singleton_eq]
  have hmem : p + i ∈ (cellFrag p n i w ⊎ σf).H := by
    simp [cellFrag, Store.union, Finmap.mem_union, Finmap.mem_singleton]
  refine ⟨.const (.cap p), cellFrag p n i v, ?_, ?_, ?_, rfl, rfl⟩
  · have hR' : Finmap.lookup p (Finmap.singleton p n ∪ σf.R) = some n := by simpa [cellFrag, Store.union] using hR
    have hI : Finmap.insert (p + i) v (Finmap.singleton (p + i) w ∪ σf.H) = Finmap.singleton (p + i) v ∪ σf.H := by
      rw [Finmap.insert_union, Finmap.insert_singleton_eq]
    simp [opStep, Store.store, cellFrag, Store.union, hR', hi, hI]
  · exact ⟨fun a ha => hd.1 a (by simpa [cellFrag, Finmap.mem_singleton] using ha), hd.2⟩
  · have := wf_insert_mem (v := v) hmem hwf
    rw [hins] at this
    simpa [Store.union, cellFrag] using this

/-! ## alloc and free: a fragment owning a WHOLE region, its entry and exactly its cells (contents unconstrained). -/

namespace Store

theorem le_fold_max (s : Multiset Int) : 0 ≤ s.fold max 0 ∧ ∀ x ∈ s, x ≤ s.fold max 0 := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.fold_cons_left]
    refine ⟨le_max_of_le_right ih.1, fun x hx => ?_⟩
    rcases Multiset.mem_cons.1 hx with rfl | hx
    · exact le_max_left _ _
    · exact le_max_of_le_right (ih.2 x hx)

theorem nextBase_nonneg (σ : Store) : 0 ≤ nextBase σ := (le_fold_max _).1

theorem end_le_nextBase {σ : Store} {q : Int} {m : Nat} (h : σ.R.lookup q = some m) : q + m ≤ nextBase σ :=
  (le_fold_max _).2 _ (Multiset.mem_map.2 ⟨⟨q, m⟩, Finmap.lookup_eq_some_iff.1 h, rfl⟩)

theorem mem_fill (h : Finmap (fun _ : Int => Int)) (p v : Int) :
    ∀ (k : Nat) (a : Int), a ∈ fill h p v k ↔ (p ≤ a ∧ a < p + k) ∨ a ∈ h
  | 0, a => by
    simp only [fill]
    constructor
    · exact Or.inr
    · rintro (⟨h₁, h₂⟩ | h)
      · omega
      · exact h
  | k + 1, a => by
    rw [fill, Finmap.mem_insert, mem_fill h p v k]
    by_cases ha : a ∈ h
    · simp [ha]
    · simp only [ha, or_false]; push_cast; omega

theorem fill_union (h : Finmap (fun _ : Int => Int)) (p v : Int) : ∀ k, fill h p v k = fill ∅ p v k ∪ h
  | 0 => by simp [fill, Finmap.empty_union]
  | k + 1 => by rw [fill, fill, fill_union h p v k, Finmap.insert_union]

theorem lookup_clear (h : Finmap (fun _ : Int => Int)) (p : Int) :
    ∀ (k : Nat) (a : Int), (clear h p k).lookup a = if p ≤ a ∧ a < p + k then none else h.lookup a
  | 0, a => by
    simp only [clear]
    split_ifs with hc
    · omega
    · rfl
  | k + 1, a => by
    rw [clear]
    by_cases ha : a = p + k
    · subst ha; rw [Finmap.lookup_erase]; split_ifs with hc
      · rfl
      · push_cast at hc; omega
    · rw [Finmap.lookup_erase_ne ha, lookup_clear h p k a]
      split_ifs with h₁ h₂ h₂ <;> first | rfl | (push_cast at *; omega)

theorem lookup_sing_union {β : Type} (p q : Int) (b : β) (R : Finmap (fun _ : Int => β)) :
    (Finmap.singleton p b ∪ R).lookup q = if q = p then some b else R.lookup q := by
  split_ifs with h
  · subst h; rw [Finmap.lookup_union_left (by simp [Finmap.mem_singleton]), Finmap.lookup_singleton_eq]
  · rw [Finmap.lookup_union_right (by simp [Finmap.mem_singleton, h])]

theorem empty_union (σ : Store) : Store.empty ⊎ σ = σ := by
  simp [Store.empty, Store.union, Finmap.empty_union]

end Store

/-- σ owns exactly the region at p of length n: its entry R(p) = n and every one of its cells (any contents). -/
def IsRegion (p : Int) (n : Nat) (σ : Store) : Prop :=
  σ.R = Finmap.singleton p n ∧ ∀ a, a ∈ σ.H ↔ Store.InRegion a p n

theorem alloc_axiom (n : Int) (hn : 0 < n) :
    OpTriple Assn.emp .alloc [.const (.int n)] (fun v σ => ∃ p, v = .const (.cap p) ∧ IsRegion p n.toNat σ) := by
  rintro σ σf rfl hd hwf
  rw [Store.empty_union] at hwf ⊢
  set p := Store.nextBase σf with hp
  set N := n.toNat with hN
  have hNpos : 0 < N := by omega
  have hNn : (N : Int) = n := by omega
  let σq : Store := ⟨Store.fill ∅ p 0 N, Finmap.singleton p N⟩
  have hpR : p ∉ σf.R := by
    intro hm
    obtain ⟨m, hm⟩ := Finmap.mem_iff.1 hm
    have := Store.end_le_nextBase hm
    have := hwf.pos _ _ hm
    omega
  have hRq : ∀ q, (σq ⊎ σf).R.lookup q = if q = p then some N else σf.R.lookup q := fun q =>
    Store.lookup_sing_union p q N σf.R
  have hdisjH : ∀ a, a ∈ Store.fill ∅ p 0 N → a ∉ σf.H := by
    intro a ha hf
    rw [Store.mem_fill] at ha
    obtain ⟨q, m, hqm, hin⟩ := (hwf.domH a).1 hf
    have := Store.end_le_nextBase hqm
    rcases ha with ⟨h₁, _⟩ | ha
    · unfold Store.InRegion at hin; omega
    · exact absurd ha Finmap.notMem_empty
  refine ⟨.const (.cap p), σq, ?_, ⟨hdisjH, fun a ha => ?_⟩, ?_, p, rfl, rfl, fun a => ?_⟩
  · show Option.map _ (Store.alloc n σf) = _
    unfold Store.alloc
    rw [if_pos hn]
    simp only [Option.map_some]
    congr 2
    show (⟨Store.fill σf.H p 0 N, σf.R.insert p N⟩ : Store) = ⟨Store.fill ∅ p 0 N ∪ σf.H, Finmap.singleton p N ∪ σf.R⟩
    rw [Store.fill_union]
    apply congrArg
    apply Finmap.ext_lookup; intro q
    rw [Store.lookup_sing_union]
    split_ifs with h
    · subst h; exact Finmap.lookup_insert _
    · exact Finmap.lookup_insert_of_ne _ h
  · rw [Finmap.mem_singleton] at ha; subst ha; exact hpR
  · refine ⟨fun q m h => ?_, fun q₁ q₂ m₁ m₂ h₁ h₂ hne a ha₁ ha₂ => ?_, fun a => ?_⟩
    · rw [hRq] at h; split_ifs at h with hq
      · cases h; exact hNpos
      · exact hwf.pos _ _ h
    · rw [hRq] at h₁ h₂
      unfold Store.InRegion at ha₁ ha₂
      split_ifs at h₁ h₂ with e₁ e₂ e₂
      · exact hne (e₁.trans e₂.symm)
      · cases h₁; have := Store.end_le_nextBase h₂; omega
      · cases h₂; have := Store.end_le_nextBase h₁; omega
      · exact hwf.disj _ _ _ _ h₁ h₂ hne a ha₁ ha₂
    · show a ∈ Store.fill ∅ p 0 N ∪ σf.H ↔ _
      rw [Finmap.mem_union, Store.mem_fill]
      constructor
      · rintro ((hin | hin) | hf)
        · exact ⟨p, N, by simp [hRq], hin⟩
        · exact absurd hin Finmap.notMem_empty
        · obtain ⟨q, m, hqm, hin⟩ := (hwf.domH a).1 hf
          refine ⟨q, m, ?_, hin⟩
          rw [hRq]; split_ifs with hq
          · subst hq; exact absurd (Finmap.mem_of_lookup_eq_some hqm) hpR
          · exact hqm
      · rintro ⟨q, m, hqm, hin⟩
        rw [hRq] at hqm; split_ifs at hqm with hq
        · cases hqm; subst hq; exact Or.inl (Or.inl hin)
        · exact Or.inr ((hwf.domH a).2 ⟨q, m, hqm, hin⟩)
  · show a ∈ Store.fill ∅ p 0 N ↔ _
    rw [Store.mem_fill]
    constructor
    · rintro (h | h)
      · exact h
      · exact absurd h Finmap.notMem_empty
    · exact Or.inl

theorem free_axiom (p : Int) (n : Nat) :
    OpTriple (IsRegion p n) .free [.const (.cap p)] (fun v σ => v = .const .unit ∧ σ = Store.empty) := by
  rintro σ σf ⟨hR, hH⟩ hd hwf
  have hpf : p ∉ σf.R := hd.2 p (by rw [hR]; simp [Finmap.mem_singleton])
  have hlook : (σ ⊎ σf).R.lookup p = some n := by
    show (σ.R ∪ σf.R).lookup p = some n
    rw [hR, Store.lookup_sing_union]; simp
  have hfrH : Store.clear (σ.H ∪ σf.H) p n = σf.H := by
    apply Finmap.ext_lookup; intro a
    rw [Store.lookup_clear]
    split_ifs with hin
    · have ha : a ∈ σ.H := (hH a).2 hin
      exact (Finmap.lookup_eq_none.2 (hd.1 a ha)).symm
    · exact Finmap.lookup_union_right (fun ha => hin ((hH a).1 ha))
  have hfrR : (σ.R ∪ σf.R).erase p = σf.R := by
    apply Finmap.ext_lookup; intro a
    by_cases ha : a = p
    · subst ha; rw [Finmap.lookup_erase]; exact (Finmap.lookup_eq_none.2 hpf).symm
    · rw [Finmap.lookup_erase_ne ha, hR, Store.lookup_sing_union, if_neg ha]
  refine ⟨.const .unit, Store.empty, ?_, ⟨Finmap.disjoint_empty _, Finmap.disjoint_empty _⟩, ?_, rfl, rfl⟩
  · simp only [opStep, Store.free, hlook, Option.map_some, Store.empty_union]
    congr 2
    show (⟨Store.clear (σ.H ∪ σf.H) p n, (σ.R ∪ σf.R).erase p⟩ : Store) = σf
    rw [hfrH, hfrR]
  · rw [Store.empty_union]
    have hRu : ∀ q, (σ ⊎ σf).R.lookup q = if q = p then some n else σf.R.lookup q := fun q => by
      show (σ.R ∪ σf.R).lookup q = _
      rw [hR, Store.lookup_sing_union]
    refine ⟨fun q m h => hwf.pos q m ?_, fun q₁ q₂ m₁ m₂ h₁ h₂ hne => hwf.disj q₁ q₂ m₁ m₂ ?_ ?_ hne, fun a => ?_⟩
    · rw [hRu, if_neg (fun (e : q = p) => hpf (e ▸ Finmap.mem_of_lookup_eq_some h))]; exact h
    · rw [hRu, if_neg (fun (e : q₁ = p) => hpf (e ▸ Finmap.mem_of_lookup_eq_some h₁))]; exact h₁
    · rw [hRu, if_neg (fun (e : q₂ = p) => hpf (e ▸ Finmap.mem_of_lookup_eq_some h₂))]; exact h₂
    · constructor
      · intro hf
        obtain ⟨q, m, hqm, hin⟩ := (hwf.domH a).1 (Finmap.mem_union.2 (Or.inr hf))
        rw [hRu] at hqm; split_ifs at hqm with hq
        · cases hqm; subst hq; exact absurd ((hH a).2 hin) (fun h => hd.1 a h hf)
        · exact ⟨q, m, hqm, hin⟩
      · rintro ⟨q, m, hqm, hin⟩
        have hq : q ≠ p := fun e => hpf (e ▸ Finmap.mem_of_lookup_eq_some hqm)
        have hu := (hwf.domH a).2 ⟨q, m, by rw [hRu, if_neg hq]; exact hqm, hin⟩
        rcases Finmap.mem_union.1 hu with hσ | hf
        · have hpin := (hH a).1 hσ
          exact absurd hpin (hwf.disj q p m n (by rw [hRu, if_neg hq]; exact hqm) hlook hq a hin)
        · exact hf

end VIRL2
