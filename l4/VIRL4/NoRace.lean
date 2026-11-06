/-
  O95 layer L4, Lean arm (amend-21 Q6; l4/DECLARATIONS-LEAN.md addendum 3). NO DATA RACE FROM TYPING, for a TYPED CONFIGURATION:
  `RT₄` is L2's runtime typing restated for Tm₄ (⊢₄'s rules plus the runtime operand forms ⟨p⟩, the owned regions Ω split across
  `let` and three ways across `par`), with a mutual atom typing that admits a lock constant. A `Race` is a `par`, reachable through
  evaluation contexts, whose two sides each have an enabled load/store through one ⟨p⟩. Theorem: a typed configuration whose store
  owns exactly Ω has no race. PRESERVATION (every reachable configuration of a typed program is typed) is OWED, not claimed here.
-/
import VIRL4.Values

namespace VIRL4
open VIRL1 VIRL2

mutual
inductive RTA₄ : Ctx₄ → Atom₄ → Ty₄ → Prop where
  | var {Γ n τ} : Γ[n]? = some τ → hasCap₄ τ = false → RTA₄ Γ (.var n) τ
  | int {Γ n} : RTA₄ Γ (.const (.c2 (.int n))) t4int
  | bool {Γ b} : RTA₄ Γ (.const (.c2 (.bool b))) t4bool
  | unit {Γ} : RTA₄ Γ (.const (.c2 .unit)) t4unit
  | lockC {Γ l} : RTA₄ Γ (.const (.lockv l)) t4lock
  | prim {Γ p as} : RTL₄ Γ as ((L1.Prim.args p).map fun b => .base (BTy₄.ofB2 (BTy.ofL1 b))) →
      RTA₄ Γ (.prim p as) (.base (BTy₄.ofB2 (BTy.ofL1 (L1.Prim.res p))))
  | lam {Γ τ₁ τ₂ e Δ} : hasCap₄ τ₁ = false → hasCap₄ τ₂ = false → Mask.empty Δ → Δ.length = Γ.length + 1 →
      RT₄ (τ₁ :: Γ) Δ [] e τ₂ → RTA₄ Γ (.lam τ₁ e) (.arr τ₁ τ₂)
  | fix {Γ τ₁ τ₂ e Δ} : hasCap₄ τ₁ = false → hasCap₄ τ₂ = false → Mask.empty Δ → Δ.length = Γ.length + 2 →
      RT₄ (τ₁ :: .arr τ₁ τ₂ :: Γ) Δ [] e τ₂ → RTA₄ Γ (.fix τ₁ τ₂ e) (.arr τ₁ τ₂)
  | pair {Γ a₁ a₂ τ₁ τ₂} : RTA₄ Γ a₁ τ₁ → RTA₄ Γ a₂ τ₂ → RTA₄ Γ (.pair a₁ a₂) (.prod τ₁ τ₂)
  | fst {Γ a τ₁ τ₂} : RTA₄ Γ a (.prod τ₁ τ₂) → RTA₄ Γ (.fst a) τ₁
  | snd {Γ a τ₁ τ₂} : RTA₄ Γ a (.prod τ₁ τ₂) → RTA₄ Γ (.snd a) τ₂
  | inl {Γ a τ₁ τ₂} : hasCap₄ τ₂ = false → RTA₄ Γ a τ₁ → RTA₄ Γ (.inl τ₂ a) (.sum τ₁ τ₂)
  | inr {Γ a τ₁ τ₂} : hasCap₄ τ₁ = false → RTA₄ Γ a τ₂ → RTA₄ Γ (.inr τ₁ a) (.sum τ₁ τ₂)
inductive RTL₄ : Ctx₄ → List Atom₄ → List Ty₄ → Prop where
  | nil {Γ} : RTL₄ Γ [] []
  | cons {Γ a as τ τs} : RTA₄ Γ a τ → RTL₄ Γ as τs → RTL₄ Γ (a :: as) (τ :: τs)
inductive RT₄ : Ctx₄ → List Bool → List Int → Tm₄ → Ty₄ → Prop where
  | ret {Γ Δ a τ} : Mask.empty Δ → RTA₄ Γ a τ → RT₄ Γ Δ [] (.ret a) τ
  | retCap {Γ Δ n} : Γ[n]? = some t4cap → Mask.only Δ n → RT₄ Γ Δ [] (.ret (.var n)) t4cap
  | retCapC {Γ Δ p} : Mask.empty Δ → RT₄ Γ Δ [p] (.ret (capv p)) t4cap
  | letE {Γ Δ Δ₁ Δ₂ Ω Ω₁ Ω₂ τ₁ τ₂ e₁ e₂} : Split Δ Δ₁ Δ₂ → Ω.Perm (Ω₁ ++ Ω₂) → (τ₁ = t4cap ∨ hasCap₄ τ₁ = false) →
      RT₄ Γ Δ₁ Ω₁ e₁ τ₁ → RT₄ (τ₁ :: Γ) (decide (τ₁ = t4cap) :: Δ₂) Ω₂ e₂ τ₂ → RT₄ Γ Δ Ω (.letE τ₁ e₁ e₂) τ₂
  | alloc {Γ Δ Ω a e τ} : RTA₄ Γ a t4int → RT₄ (t4cap :: Γ) (true :: Δ) Ω e τ →
      RT₄ Γ Δ Ω (.letOp (.o2 .alloc) [a] t4cap e) τ
  | load {Γ Δ Ω n a e τ} : Γ[n]? = some t4cap → Δ[n]? = some true → RTA₄ Γ a t4int →
      RT₄ (t4int :: Γ) (false :: Δ) Ω e τ → RT₄ Γ Δ Ω (.letOp (.o2 .load) [.var n, a] t4int e) τ
  | loadC {Γ Δ Ω p a e τ} : p ∈ Ω → RTA₄ Γ a t4int →
      RT₄ (t4int :: Γ) (false :: Δ) Ω e τ → RT₄ Γ Δ Ω (.letOp (.o2 .load) [capv p, a] t4int e) τ
  | store {Γ Δ Ω n a₁ a₂ e τ} : Γ[n]? = some t4cap → Δ[n]? = some true → RTA₄ Γ a₁ t4int → RTA₄ Γ a₂ t4int →
      RT₄ (t4cap :: Γ) (true :: Δ.set n false) Ω e τ → RT₄ Γ Δ Ω (.letOp (.o2 .store) [.var n, a₁, a₂] t4cap e) τ
  | storeC {Γ Δ Ω p a₁ a₂ e τ} : p ∈ Ω → RTA₄ Γ a₁ t4int → RTA₄ Γ a₂ t4int →
      RT₄ (t4cap :: Γ) (true :: Δ) (Ω.erase p) e τ → RT₄ Γ Δ Ω (.letOp (.o2 .store) [capv p, a₁, a₂] t4cap e) τ
  | free {Γ Δ Ω n e τ} : Γ[n]? = some t4cap → Δ[n]? = some true →
      RT₄ (t4unit :: Γ) (false :: Δ.set n false) Ω e τ → RT₄ Γ Δ Ω (.letOp (.o2 .free) [.var n] t4unit e) τ
  | freeC {Γ Δ Ω p e τ} : p ∈ Ω → RT₄ (t4unit :: Γ) (false :: Δ) (Ω.erase p) e τ →
      RT₄ Γ Δ Ω (.letOp (.o2 .free) [capv p] t4unit e) τ
  | app {Γ Δ a₁ a₂ τ₁ τ₂} : Mask.empty Δ → RTA₄ Γ a₁ (.arr τ₁ τ₂) → RTA₄ Γ a₂ τ₁ → RT₄ Γ Δ [] (.app a₁ a₂) τ₂
  | ite {Γ Δ Ω a e₁ e₂ τ} : RTA₄ Γ a t4bool → RT₄ Γ Δ Ω e₁ τ → RT₄ Γ Δ Ω e₂ τ → RT₄ Γ Δ Ω (.ite a e₁ e₂) τ
  | case {Γ Δ Ω a e₁ e₂ τ₁ τ₂ τ} : RTA₄ Γ a (.sum τ₁ τ₂) → RT₄ (τ₁ :: Γ) (false :: Δ) Ω e₁ τ →
      RT₄ (τ₂ :: Γ) (false :: Δ) Ω e₂ τ → RT₄ Γ Δ Ω (.case a e₁ e₂) τ
  | newlock {Γ Δ Ω n e τ} : Γ[n]? = some t4cap → Δ[n]? = some true →
      RT₄ (t4lock :: Γ) (false :: Δ.set n false) Ω e τ → RT₄ Γ Δ Ω (.letOp .newlock [.var n] t4lock e) τ
  | newlockC {Γ Δ Ω p e τ} : p ∈ Ω → RT₄ (t4lock :: Γ) (false :: Δ) (Ω.erase p) e τ →
      RT₄ Γ Δ Ω (.letOp .newlock [capv p] t4lock e) τ
  | acquire {Γ Δ Ω a e τ} : RTA₄ Γ a t4lock → RT₄ (t4cap :: Γ) (true :: Δ) Ω e τ →
      RT₄ Γ Δ Ω (.letOp .acquire [a] t4cap e) τ
  | release {Γ Δ Ω a n e τ} : RTA₄ Γ a t4lock → Γ[n]? = some t4cap → Δ[n]? = some true →
      RT₄ (t4unit :: Γ) (false :: Δ.set n false) Ω e τ → RT₄ Γ Δ Ω (.letOp .release [a, .var n] t4unit e) τ
  | releaseC {Γ Δ Ω a p e τ} : RTA₄ Γ a t4lock → p ∈ Ω → RT₄ (t4unit :: Γ) (false :: Δ) (Ω.erase p) e τ →
      RT₄ Γ Δ Ω (.letOp .release [a, capv p] t4unit e) τ
  | par {Γ Δ Δ₁ Δ' Δ₂ Δ₀ Ω Ω₁ Ω₂ Ω₀ τ₁ τ₂ e₁ e₂ e τ} : Split Δ Δ₁ Δ' → Split Δ' Δ₂ Δ₀ → Ω.Perm (Ω₁ ++ Ω₂ ++ Ω₀) →
      (τ₁ = t4cap ∨ hasCap₄ τ₁ = false) → (τ₂ = t4cap ∨ hasCap₄ τ₂ = false) →
      RT₄ Γ Δ₁ Ω₁ e₁ τ₁ → RT₄ Γ Δ₂ Ω₂ e₂ τ₂ →
      RT₄ (τ₂ :: τ₁ :: Γ) (decide (τ₂ = t4cap) :: decide (τ₁ = t4cap) :: Δ₀) Ω₀ e τ →
      RT₄ Γ Δ Ω (.par τ₁ τ₂ e₁ e₂ e) τ
end

/-- An ENABLED access through ⟨p⟩: a load/store at the head of a thread (under `let` heads and either `par` side). -/
inductive Acc : Tm₄ → Int → Prop where
  | load {p a τ e} : Acc (.letOp (.o2 .load) [capv p, a] τ e) p
  | store {p a₁ a₂ τ e} : Acc (.letOp (.o2 .store) [capv p, a₁, a₂] τ e) p
  | letE {τ e₁ e₂ p} : Acc e₁ p → Acc (.letE τ e₁ e₂) p
  | parL {τ₁ τ₂ e₁ e₂ e p} : Acc e₁ p → Acc (.par τ₁ τ₂ e₁ e₂ e) p
  | parR {τ₁ τ₂ e₁ e₂ e p} : Acc e₂ p → Acc (.par τ₁ τ₂ e₁ e₂ e) p

/-- A RACE on region p: a `par` reachable through evaluation contexts whose two sides each have an enabled access through ⟨p⟩. -/
inductive Race : Tm₄ → Int → Prop where
  | here {τ₁ τ₂ e₁ e₂ e p} : Acc e₁ p → Acc e₂ p → Race (.par τ₁ τ₂ e₁ e₂ e) p
  | letE {τ e₁ e₂ p} : Race e₁ p → Race (.letE τ e₁ e₂) p
  | parL {τ₁ τ₂ e₁ e₂ e p} : Race e₁ p → Race (.par τ₁ τ₂ e₁ e₂ e) p
  | parR {τ₁ τ₂ e₁ e₂ e p} : Race e₂ p → Race (.par τ₁ τ₂ e₁ e₂ e) p

/-- An enabled access through ⟨p⟩ is to a region the thread OWNS. -/
theorem acc_owned {e : Tm₄} {p : Int} (ha : Acc e p) : ∀ {Γ Δ Ω τ}, RT₄ Γ Δ Ω e τ → p ∈ Ω := by
  induction ha with
  | load =>
    intro Γ Δ Ω τ ht
    cases ht with
    | loadC hp _ _ => exact hp
  | store =>
    intro Γ Δ Ω τ ht
    cases ht with
    | storeC hp _ _ _ => exact hp
  | letE _ ih =>
    intro Γ Δ Ω τ ht
    cases ht with
    | letE _ hperm _ h₁ _ => exact hperm.mem_iff.2 (List.mem_append_left _ (ih h₁))
  | parL _ ih =>
    intro Γ Δ Ω τ ht
    cases ht with
    | par _ _ hperm _ _ h₁ _ _ => exact hperm.mem_iff.2 (List.mem_append_left _ (List.mem_append_left _ (ih h₁)))
  | parR _ ih =>
    intro Γ Δ Ω τ ht
    cases ht with
    | par _ _ hperm _ _ _ h₂ _ => exact hperm.mem_iff.2 (List.mem_append_left _ (List.mem_append_right _ (ih h₂)))

theorem no_race {e : Tm₄} {p : Int} (hr : Race e p) : ∀ {Γ Δ Ω τ}, RT₄ Γ Δ Ω e τ → Ω.Nodup → False := by
  induction hr with
  | here h₁ h₂ =>
    intro Γ Δ Ω τ ht hnd
    cases ht with
    | par _ _ hperm _ _ ht₁ ht₂ _ =>
      have hnd' := ((hperm.nodup_iff.1 hnd).sublist (List.sublist_append_left _ _))
      exact List.disjoint_of_nodup_append hnd' (acc_owned h₁ ht₁) (acc_owned h₂ ht₂)
  | letE _ ih =>
    intro Γ Δ Ω τ ht hnd
    cases ht with
    | letE _ hperm _ h₁ _ => exact ih h₁ ((hperm.nodup_iff.1 hnd).sublist (List.sublist_append_left _ _))
  | parL _ ih =>
    intro Γ Δ Ω τ ht hnd
    cases ht with
    | par _ _ hperm _ _ h₁ _ _ =>
      exact ih h₁ ((hperm.nodup_iff.1 hnd).sublist ((List.sublist_append_left _ _).trans (List.sublist_append_left _ _)))
  | parR _ ih =>
    intro Γ Δ Ω τ ht hnd
    cases ht with
    | par _ _ hperm _ _ _ h₂ _ =>
      exact ih h₂ ((hperm.nodup_iff.1 hnd).sublist ((List.sublist_append_right _ _).trans (List.sublist_append_left _ _)))

/-- A store owning exactly Ω's regions owns each at most once. -/
theorem ownAll_mem : ∀ (Ω : List Int) (σ : Store) (p : Int), OwnAll Ω σ → p ∈ Ω → p ∈ σ.R
  | [], _, _, _, hp => absurd hp (List.not_mem_nil)
  | q :: Ω, σ, p, ho, hp => by
    simp only [OwnAll] at ho
    obtain ⟨σ₁, σ₂, _, rfl, hq, hrest⟩ := ho
    rcases List.mem_cons.1 hp with rfl | hp'
    · exact Finmap.mem_union.2 (Or.inl (owns_mem hq))
    · exact Finmap.mem_union.2 (Or.inr (ownAll_mem Ω σ₂ p hrest hp'))

theorem ownAll_nodup : ∀ (Ω : List Int) (σ : Store), OwnAll Ω σ → Ω.Nodup
  | [], _, _ => List.nodup_nil
  | q :: Ω, σ, ho => by
    simp only [OwnAll] at ho
    obtain ⟨σ₁, σ₂, hd, rfl, hq, hrest⟩ := ho
    refine List.nodup_cons.2 ⟨fun hm => hd.2 q (owns_mem hq) (ownAll_mem Ω σ₂ q hrest hm), ownAll_nodup Ω σ₂ hrest⟩

/-- Q6, FOR A TYPED CONFIGURATION: a closed RT₄-typed term whose store owns exactly its Ω has no race on any region. -/
theorem Q6_no_race {Ω : List Int} {e : Tm₄} {τ : Ty₄} {σ : Store} (ht : RT₄ [] [] Ω e τ) (ho : OwnAll Ω σ) (p : Int) :
    ¬ Race e p :=
  fun hr => no_race hr ht (ownAll_nodup Ω σ ho)

/-! ## Controls, one per hypothesis: a race EXISTS (N2's two sides after its setup), and a `par` IS RT₄-typable. -/

/-- N2's sides with c1 = ⟨0⟩: both load through ⟨0⟩ at once. -/
theorem race_N2 : Race (.par t4cap t4cap
    (.letOp (.o2 .load) [capv 0, c4 0] t4int (.ret (capv 0)))
    (.letOp (.o2 .load) [capv 0, c4 0] t4int (.ret (capv 0))) (.ret unitv)) 0 :=
  Race.here Acc.load Acc.load

theorem par_typed : RT₄ [] [] [] (.par t4unit t4unit (.ret unitv) (.ret unitv) (.ret unitv)) t4unit := by
  refine RT₄.par (Δ₁ := []) (Δ' := []) (Δ₂ := []) (Δ₀ := []) (Ω₁ := []) (Ω₂ := []) (Ω₀ := []) Split.nil Split.nil
    (by simp) (Or.inr rfl) (Or.inr rfl) (RT₄.ret (fun n => by simp) RTA₄.unit) (RT₄.ret (fun n => by simp) RTA₄.unit) ?_
  refine RT₄.ret ?_ RTA₄.unit
  intro n
  simp [t4unit, t4cap]
  rcases n with _ | _ | n <;> simp

end VIRL4
