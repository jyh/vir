/-
S6's `dynamic` against the machine's DHDR … REP modes (S-18's `dynamic` row), and with it `CorrectStmt`.
Shape: the header (DHDR, DH2, DH3, DH4); the CL lengths (CLREAD, CLPUT, then the zero fill, S-14); the CL build (BUILD
target 0, strict); the lengths loop (LENS, LSYM, LREP, REP); the L build (target 1, normal) and the D build (target 2,
dist); then SYM and S7's `huff`.
-/
import VIRDeflate.Correct

namespace VIRDeflate.Step
open VIRL1 VIRL2

/-! ## Arrays -/

theorem getD_oob (a : Array Nat) (j : Nat) (h : a.size ≤ j) : a.getD j 0 = 0 := by
  unfold Array.getD; rw [dif_neg (by omega)]

theorem getD_set! (cl : Array Nat) (o x j : Nat) (ho : o < cl.size) :
    (cl.set! o x).getD j 0 = if j = o then x else cl.getD j 0 := by
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, show cl.set! o x = cl.setIfInBounds o x from rfl,
    Array.getElem?_setIfInBounds]
  by_cases h : j = o
  · subst h; simp [ho]
  · simp [Ne.symm h, h]

theorem size_set! (cl : Array Nat) (o x : Nat) : (cl.set! o x).size = cl.size := by simp [Array.set!]

theorem pushN_size (x : Nat) : ∀ k (a : Array Nat), (pushN x k a).size = a.size + k
  | 0, a => rfl
  | k + 1, a => by rw [pushN, pushN_size x k]; simp; omega

theorem pushN_getD (x : Nat) : ∀ k (a : Array Nat) (j : Nat), (pushN x k a).getD j 0 =
    if j < a.size then a.getD j 0 else if j < a.size + k then x else 0
  | 0, a, j => by
    simp only [pushN, Nat.add_zero]; split_ifs <;> first | rfl | omega | exact getD_oob a j (by omega)
  | k + 1, a, j => by
    rw [pushN, pushN_getD x k]
    simp only [Array.size_push, Array.getD_eq_getD_getElem?, Array.getElem?_push]
    split_ifs <;> first | omega | simp_all | skip

theorem push_getD (a : Array Nat) (x j : Nat) :
    (a.push x).getD j 0 = if j < a.size then a.getD j 0 else if j = a.size then x else 0 := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_push]
  split_ifs <;> first | omega | simp_all | skip

theorem extract_getD (a : Array Nat) (s e j : Nat) (he : e ≤ a.size) (hj : j < e - s) :
    (a.extract s e).getD j 0 = a.getD (s + j) 0 := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_extract]
  split_ifs <;> first | omega | simp_all | skip

/-! ## ORDER -/

theorem order_inj : ∀ k k' : Fin 19, ORDER.getD k 0 = ORDER.getD k' 0 → k = k' := by decide
theorem order_surj : ∀ j : Fin 19, ∃ k : Fin 19, ORDER.getD k 0 = j := by decide
theorem order_lt : ∀ k : Fin 19, ORDER.getD k 0 < 19 := by decide
theorem order_drop (i : Nat) (h : i < 19) : ORDER.drop i = ORDER.getD i 0 :: ORDER.drop (i + 1) := by
  interval_cases i <;> rfl

theorem order_ne {k k' : Nat} (hk : k < 19) (hk' : k' < 19) (h : k ≠ k') : ORDER.getD k 0 ≠ ORDER.getD k' 0 := fun e =>
  h (by have := order_inj ⟨k, hk⟩ ⟨k', hk'⟩ e; simpa using this)

/-- ORDER's cells (X + 134 …) hold ORDER, by the read-only area. -/
theorem order_cell {b : Array Nat} {om : Nat} {lit : Bool} {f : Int → Int} (hi : InvG b om lit f) (k : Nat) (hk : k < 19) :
    f (X0 b.size om + 134 + k) = ORDER.getD k 0 := by
  have hX : X0 b.size om = 2080 + b.size + om + 1393 := rfl
  rw [hi.ro _ (by omega) (by omega)]
  unfold initCell
  dsimp only
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos ⟨by omega, by omega⟩,
    show (X0 b.size om + 134 + (k : Int) - X0 b.size om - 134).toNat = k by omega]

/-! ## `dynamic`, unfolded -/

/-- S6 after the lengths: the L and D codes, then `huff`. -/
def dyn3 (lens : Array Nat) (hlit hdist : Nat) : M Unit :=
  code (lens.extract 0 hlit) >>= fun L => code (lens.extract hlit (hlit + hdist)) .dist >>= fun D => huff L D

/-- S6 after the header. -/
def dyn2 (hlit hdist hclen : Nat) : M Unit :=
  readCL ORDER hclen (Array.replicate 19 0) >>= fun cl => code cl .strict >>= fun CL => fuelNow >>= fun fu =>
    lensLoop CL (hlit + hdist) fu #[] >>= fun lens =>
      if lens.getD 256 0 = 0 then (reject "missing end-of-block" : M Unit) >>= fun _ => dyn3 lens hlit hdist
      else dyn3 lens hlit hdist

theorem dynamic_eq : dynamic = (bits 5 >>= fun a1 => bits 5 >>= fun a2 => bits 4 >>= fun a3 =>
    if a1 + 257 > 286 ∨ a2 + 1 > 30 then
      (reject "too many length or distance symbols" : M Unit) >>= fun _ => dyn2 (a1 + 257) (a2 + 1) (a3 + 4)
    else dyn2 (a1 + 257) (a2 + 1) (a3 + 4)) := rfl

theorem readCL_zero (os : List Nat) (cl : Array Nat) : readCL os 0 cl = pure cl := by
  cases os <;> rfl

theorem readCL_succ (o : Nat) (os : List Nat) (k : Nat) (cl : Array Nat) :
    readCL (o :: os) (k + 1) cl = (bits 3 >>= fun x => readCL os k (cl.set! o x)) := by
  simp only [readCL, Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel]

/-! ## Machine steps -/

theorem dhdr_mem : (mDHDR, dhdrN) ∈ modes := by unfold modes; simp
theorem dh2_mem : (mDH2, dh2N) ∈ modes := by unfold modes; simp
theorem dh3_mem : (mDH3, dh3N) ∈ modes := by unfold modes; simp
theorem dh4_mem : (mDH4, dh4N) ∈ modes := by unfold modes; simp
theorem clread_mem : (mCLREAD, clreadN) ∈ modes := by unfold modes; simp
theorem clput_mem : (mCLPUT, clputN) ∈ modes := by unfold modes; simp
theorem lens_mem : (mLENS, lensN) ∈ modes := by unfold modes; simp
theorem lsym_mem : (mLSYM, lsymN) ∈ modes := by unfold modes; simp
theorem lrep_mem : (mLREP, lrepN) ∈ modes := by unfold modes; simp
theorem rep_mem : (mREP, repN) ∈ modes := by unfold modes; simp

/-- Evaluate a cell of a chain of `Function.update`s at a named cell. -/
macro "updv" : tactic => `(tactic| (simp only [Function.update_apply, X0, LB0, tbase, cMODE, cFILL, cHCLEN, cDYN, cCHK, cTGT, cPHASE, cINDEX, cHLIT, cHDIST, cBF, cLAST, cPEND, cK, cACC, cWT, cRET, cREASON] <;> split_ifs <;> first | rfl | omega | (push_cast; ring)))

/-- A step that stores some cells and then makes a READ request: R carries over, and READ's cells are set. -/
theorem req_next {b : Array Nat} {om : Nat} {lit : Bool} {σ σ1 : Store} {p : Int} {f g : Int → Int} {st : St}
    {S : Int → Prop} (hb : ∀ x ∈ b, x < 256) (hw : World σ p (L0 b.size om) f) (hR : Rel b om lit f st)
    (hd : f cMODE ≠ mDONE) (hr : f cMODE ≠ mREJECT) (k rt : Int)
    (hS : stepS p σ = some ⟨reqH σ1.H p k rt, σ1.R⟩) (hg : World σ1 p (L0 b.size om) g)
    (hk : Keeps (L0 b.size om) f g S) (hSc : ∀ c, S c → ctl b.size om c) :
    ∃ f1, World ⟨reqH σ1.H p k rt, σ1.R⟩ p (L0 b.size om) f1 ∧ Rel b om lit f1 st ∧ f1 cMODE = mREAD ∧ f1 cK = k ∧
      f1 cACC = 0 ∧ f1 cWT = 1 ∧ f1 cRET = rt ∧
      Keeps (L0 b.size om) f f1 (fun c => S c ∨ c = 0 ∨ (2068 ≤ c ∧ c ≤ 2071)) ∧
      (∀ c : Int, 0 ≤ c → c < L0 b.size om → c ≠ 0 → (c < 2068 ∨ 2071 < c) → f1 c = g c) := by
  have hL : 2080 ≤ L0 b.size om := by unfold L0; omega
  have hk' : Keeps (L0 b.size om) f (reqF g k rt) (fun c => S c ∨ c = 0 ∨ (2068 ≤ c ∧ c ≤ 2071)) := fun c h0 h1 hc =>
    (reqF_keeps _ g k rt c h0 h1 (fun h => hc (Or.inr h))).trans (hk c h0 h1 (fun h => hc (Or.inl h)))
  obtain ⟨f1, hw1, hR1, hk1, ag⟩ := next_rel hb hw hR hd hr hS (hg.req (by omega) k rt) hk'
    (fun c hc => by
      rcases hc with h | h | h
      · exact hSc c h
      all_goals (unfold ctl IN; omega))
  obtain ⟨v1, v2, v3, v4, v5⟩ := reqF_vals g k rt
  refine ⟨f1, hw1, hR1, ?_, ?_, ?_, ?_, ?_, hk1, fun c h0 h1 hc0 hc => ?_⟩
  · rw [ag _ (by decide) (by unfold cMODE; omega)]; exact v1
  · rw [ag _ (by decide) (by unfold cK; omega)]; exact v2
  · rw [ag _ (by decide) (by unfold cACC; omega)]; exact v3
  · rw [ag _ (by decide) (by unfold cWT; omega)]; exact v4
  · rw [ag _ (by decide) (by unfold cRET; omega)]; exact v5
  · rw [ag c h0 h1]; exact reqF_eq g k rt c (by omega)

theorem dhdr_next {b : Array Nat} {om : Nat} {lit : Bool} {σ : Store} {p : Int} {f : Int → Int} {st : St}
    (hb : ∀ x ∈ b, x < 256) (hw : World σ p (L0 b.size om) f) (hR : Rel b om lit f st) (hm : f cMODE = mDHDR) :
    ∃ σ1 f1, stepS p σ = some σ1 ∧ World σ1 p (L0 b.size om) f1 ∧ Rel b om lit f1 st ∧ f1 cMODE = mREAD ∧ f1 cK = 5 ∧
      f1 cACC = 0 ∧ f1 cWT = 1 ∧ f1 cRET = mDH2 ∧ Keeps (L0 b.size om) f f1 (fun c => c = 0 ∨ (2068 ≤ c ∧ c ≤ 2071)) := by
  have hL : 2080 ≤ L0 b.size om := by unfold L0; omega
  have hS := stepS_fit hw (by omega) hm rfl dhdr_mem (by decide) (dhdr_step hw hL)
  obtain ⟨f1, hw1, hR1, h1, h2, h3, h4, h5, hk1, -⟩ := req_next (σ1 := σ) (S := fun _ => False) hb hw hR
    (by rw [hm]; decide) (by rw [hm]; decide) 5 20 hS hw (Keeps.refl _ f _) (fun _ h => h.elim)
  exact ⟨_, f1, hS, hw1, hR1, h1, h2, h3, h4, h5, fun c h0 h1 hc => hk1 c h0 h1 (fun h => hc (h.resolve_left id))⟩

theorem dh2_next {b : Array Nat} {om : Nat} {lit : Bool} {σ : Store} {p : Int} {f : Int → Int} {st : St}
    (hb : ∀ x ∈ b, x < 256) (hw : World σ p (L0 b.size om) f) (hR : Rel b om lit f st) (hm : f cMODE = mDH2) :
    ∃ σ1 f1, stepS p σ = some σ1 ∧ World σ1 p (L0 b.size om) f1 ∧ Rel b om lit f1 st ∧ f1 cMODE = mREAD ∧ f1 cK = 5 ∧
      f1 cACC = 0 ∧ f1 cWT = 1 ∧ f1 cRET = mDH3 ∧ f1 cHLIT = f cACC + 257 ∧
      Keeps (L0 b.size om) f f1 (fun c => c = 7 ∨ c = 0 ∨ (2068 ≤ c ∧ c ≤ 2071)) := by
  have hL : 2080 ≤ L0 b.size om := by unfold L0; omega
  have hS := stepS_fit hw (by omega) hm rfl dh2_mem (by decide) (dh2_step hw hL (f cACC) rfl)
  obtain ⟨f1, hw1, hR1, h1, h2, h3, h4, h5, hk1, ag⟩ := req_next (σ1 := ⟨σ.H.insert (p + 7) (f cACC + 257), σ.R⟩) (S := fun c => c = 7) hb hw hR
    (by rw [hm]; decide) (by rw [hm]; decide) 5 21 hS (hw.store (i := 7) (v := f cACC + 257) (by norm_num) (by omega))
    (fun c _ _ hc => upd_eq _ _ hc) (fun c hc => by unfold ctl; omega)
  refine ⟨_, f1, hS, hw1, hR1, h1, h2, h3, h4, h5, ?_, hk1⟩
  rw [ag _ (by decide) (by unfold cHLIT; omega) (by decide) (by decide)]; simp [cHLIT]

theorem dh3_next {b : Array Nat} {om : Nat} {lit : Bool} {σ : Store} {p : Int} {f : Int → Int} {st : St}
    (hb : ∀ x ∈ b, x < 256) (hw : World σ p (L0 b.size om) f) (hR : Rel b om lit f st) (hm : f cMODE = mDH3) :
    ∃ σ1 f1, stepS p σ = some σ1 ∧ World σ1 p (L0 b.size om) f1 ∧ Rel b om lit f1 st ∧ f1 cMODE = mREAD ∧ f1 cK = 4 ∧
      f1 cACC = 0 ∧ f1 cWT = 1 ∧ f1 cRET = mDH4 ∧ f1 cHDIST = f cACC + 1 ∧
      Keeps (L0 b.size om) f f1 (fun c => c = 8 ∨ c = 0 ∨ (2068 ≤ c ∧ c ≤ 2071)) := by
  have hL : 2080 ≤ L0 b.size om := by unfold L0; omega
  have hS := stepS_fit hw (by omega) hm rfl dh3_mem (by decide) (dh3_step hw hL (f cACC) rfl)
  obtain ⟨f1, hw1, hR1, h1, h2, h3, h4, h5, hk1, ag⟩ := req_next (σ1 := ⟨σ.H.insert (p + 8) (f cACC + 1), σ.R⟩) (S := fun c => c = 8) hb hw hR
    (by rw [hm]; decide) (by rw [hm]; decide) 4 22 hS (hw.store (i := 8) (v := f cACC + 1) (by norm_num) (by omega))
    (fun c _ _ hc => upd_eq _ _ hc) (fun c hc => by unfold ctl; omega)
  refine ⟨_, f1, hS, hw1, hR1, h1, h2, h3, h4, h5, ?_, hk1⟩
  rw [ag _ (by decide) (by unfold cHDIST; omega) (by decide) (by decide)]; simp [cHDIST]

/-- **DH4:** HCLEN, then S6's check (HLIT ≤ 286, HDIST ≤ 30) or REJECT; FILL 0, DYN 1, CHK 1, CLREAD. -/
theorem dh4_next {b : Array Nat} {om : Nat} {lit : Bool} {σ : Store} {p : Int} {f : Int → Int} {st : St}
    (hb : ∀ x ∈ b, x < 256) (hw : World σ p (L0 b.size om) f) (hR : Rel b om lit f st) (hm : f cMODE = mDH4) :
    (286 < f cHLIT ∨ 30 < f cHDIST → ∃ σ1 f1, stepS p σ = some σ1 ∧ World σ1 p (L0 b.size om) f1 ∧ f1 cMODE = mREJECT) ∧
    (¬ (286 < f cHLIT ∨ 30 < f cHDIST) → ∃ σ1 f1, stepS p σ = some σ1 ∧ World σ1 p (L0 b.size om) f1 ∧
      Rel b om lit f1 st ∧ f1 cMODE = mCLREAD ∧ f1 cHCLEN = f cACC + 4 ∧ f1 cFILL = 0 ∧ f1 cDYN = 1 ∧ f1 cCHK = 1 ∧
      Keeps (L0 b.size om) f f1 (fun c => c = 0 ∨ c = 9 ∨ c = 10 ∨ c = 2072 ∨ c = 2073)) := by
  have hL : 2080 ≤ L0 b.size om := by unfold L0; omega
  have hS := stepS_fit hw (by omega) hm rfl dh4_mem (by decide) (dh4_step hw hL (f cACC) (f cHLIT) (f cHDIST) rfl rfl rfl)
  refine ⟨fun hc => ?_, fun hc => ?_⟩
  · rw [if_pos hc] at hS
    have hg := ((hw.store (i := 9) (v := f cACC + 4) (by norm_num) (by omega)).store (i := 14) (v := 11) (by norm_num)
      (by omega)).store (i := 0) (v := 99) (by norm_num) (by omega)
    exact ⟨_, _, hS, hg, by simp [cMODE, mREJECT]⟩
  · rw [if_neg hc] at hS
    have hg := ((((hw.store (i := 9) (v := f cACC + 4) (by norm_num) (by omega)).store (i := 10) (v := 0) (by norm_num)
      (by omega)).store (i := 2073) (v := 1) (by norm_num) (by omega)).store (i := 2072) (v := 1) (by norm_num)
      (by omega)).store (i := 0) (v := 23) (by norm_num) (by omega)
    obtain ⟨f1, hw1, hR1, hk1, ag⟩ := next_rel hb hw hR (by rw [hm]; decide) (by rw [hm]; decide) hS hg
      (S := fun c => c = 0 ∨ c = 9 ∨ c = 10 ∨ c = 2072 ∨ c = 2073)
      (fun c _ _ hc => by simp only [Function.update_apply]; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega),
        if_neg (by omega), if_neg (by omega)])
      (fun c hc => by unfold ctl; omega)
    refine ⟨_, f1, hS, hw1, hR1, ?_, ?_, ?_, ?_, ?_, hk1⟩
    · rw [ag _ (by decide) (by unfold cMODE; omega)]; updv
    · rw [ag _ (by decide) (by unfold cHCLEN; omega)]; updv
    · rw [ag _ (by decide) (by unfold cFILL; omega)]; updv
    · rw [ag _ (by decide) (by unfold cDYN; omega)]; updv
    · rw [ag _ (by decide) (by unfold cCHK; omega)]; updv

/-- **CLREAD, a length still to read:** READ 3 bits, returning to CLPUT. -/
theorem clread_req_next {b : Array Nat} {om : Nat} {lit : Bool} {σ : Store} {p : Int} {f : Int → Int} {st : St}
    (hb : ∀ x ∈ b, x < 256) (hw : World σ p (L0 b.size om) f) (hR : Rel b om lit f st) (hm : f cMODE = mCLREAD)
    (hlt : f cFILL < f cHCLEN) :
    ∃ σ1 f1, stepS p σ = some σ1 ∧ World σ1 p (L0 b.size om) f1 ∧ Rel b om lit f1 st ∧ f1 cMODE = mREAD ∧ f1 cK = 3 ∧
      f1 cACC = 0 ∧ f1 cWT = 1 ∧ f1 cRET = mCLPUT ∧ Keeps (L0 b.size om) f f1 (fun c => c = 0 ∨ (2068 ≤ c ∧ c ≤ 2071)) := by
  have hL : 2080 ≤ L0 b.size om := by unfold L0; omega
  have hS := stepS_fit hw (by omega) hm rfl clread_mem (by decide)
    (clread_req hw hL (f cFILL) (f cHCLEN) (X0 b.size om) b.size om rfl rfl hR.inv.1.x_eq hR.inv.1.n_eq hR.inv.1.om_eq hlt)
  obtain ⟨f1, hw1, hR1, h1, h2, h3, h4, h5, hk1, -⟩ := req_next (σ1 := σ) (S := fun _ => False) hb hw hR
    (by rw [hm]; decide) (by rw [hm]; decide) 3 24 hS hw (Keeps.refl _ f _) (fun _ h => h.elim)
  exact ⟨_, f1, hS, hw1, hR1, h1, h2, h3, h4, h5, fun c h0 h1 hc => hk1 c h0 h1 (fun h => hc (h.resolve_left id))⟩

/-- **CLPUT:** cl[ORDER[i]] := acc, FILL + 1, CLREAD. -/
theorem clput_next {b : Array Nat} {om : Nat} {lit : Bool} {σ : Store} {p : Int} {f : Int → Int} {st : St}
    (hb : ∀ x ∈ b, x < 256) (hw : World σ p (L0 b.size om) f) (hR : Rel b om lit f st) (hm : f cMODE = mCLPUT)
    (i : Nat) (hi : f cFILL = i) (h19 : i < 19) :
    ∃ σ1 f1, stepS p σ = some σ1 ∧ World σ1 p (L0 b.size om) f1 ∧ Rel b om lit f1 st ∧ f1 cMODE = mCLREAD ∧
      f1 cFILL = i + 1 ∧ f1 (LB0 b.size om + 318 + ORDER.getD i 0) = f cACC ∧
      Keeps (L0 b.size om) f f1 (fun c => c = 0 ∨ c = 10 ∨ c = LB0 b.size om + 318 + ORDER.getD i 0) := by
  have hL : 2080 ≤ L0 b.size om := by unfold L0; omega
  have ho := order_cell hR.inv.1 i h19
  have hol := order_lt ⟨i, h19⟩
  simp only at hol
  have hS := stepS_fit hw (by omega) hm rfl clput_mem (by decide)
    (clput_step hw hL i (X0 b.size om) b.size om (f cACC) (ORDER.getD i 0) hi hR.inv.1.x_eq hR.inv.1.n_eq
      hR.inv.1.om_eq rfl (by omega) (by omega) (by unfold X0; omega) (by unfold X0 L0; omega) ho (by omega)
      (by unfold L0; omega))
  have hg := ((hw.store (i := LB0 b.size om + 318 + ORDER.getD i 0) (v := f cACC) (by unfold LB0; omega)
    (by unfold LB0 L0; omega)).store (i := 10) (v := (i : Int) + 1) (by norm_num) (by omega)).store (i := 0) (v := 23)
    (by norm_num) (by omega)
  obtain ⟨f1, hw1, hR1, hk1, ag⟩ := next_rel hb hw hR (by rw [hm]; decide) (by rw [hm]; decide) hS hg
    (S := fun c => c = 0 ∨ c = 10 ∨ c = LB0 b.size om + 318 + ORDER.getD i 0)
    (fun c _ _ hc => by simp only [Function.update_apply]; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)])
    (fun c hc => by unfold ctl LB0 IN at *; omega)
  refine ⟨_, f1, hS, hw1, hR1, ?_, ?_, ?_, hk1⟩
  · rw [ag _ (by decide) (by unfold cMODE; omega)]; updv
  · rw [ag _ (by decide) (by unfold cFILL; omega)]; updv
  · rw [ag _ (by unfold LB0; omega) (by unfold LB0 L0; omega)]; updv

/-- **CLREAD past HCLEN:** cl[ORDER[i]] := 0, FILL + 1 (S-14's zero fill). -/
theorem clread_zero_next {b : Array Nat} {om : Nat} {lit : Bool} {σ : Store} {p : Int} {f : Int → Int} {st : St}
    (hb : ∀ x ∈ b, x < 256) (hw : World σ p (L0 b.size om) f) (hR : Rel b om lit f st) (hm : f cMODE = mCLREAD)
    (i : Nat) (hi : f cFILL = i) (hlt : ¬ f cFILL < f cHCLEN) (h19 : i < 19) :
    ∃ σ1 f1, stepS p σ = some σ1 ∧ World σ1 p (L0 b.size om) f1 ∧ Rel b om lit f1 st ∧ f1 cMODE = mCLREAD ∧
      f1 cFILL = i + 1 ∧ f1 (LB0 b.size om + 318 + ORDER.getD i 0) = 0 ∧
      Keeps (L0 b.size om) f f1 (fun c => c = 10 ∨ c = LB0 b.size om + 318 + ORDER.getD i 0) := by
  have hL : 2080 ≤ L0 b.size om := by unfold L0; omega
  have ho := order_cell hR.inv.1 i h19
  have hol := order_lt ⟨i, h19⟩
  simp only at hol
  have hS := stepS_fit hw (by omega) hm rfl clread_mem (by decide)
    (clread_zero hw hL i (f cHCLEN) (X0 b.size om) b.size om (ORDER.getD i 0) hi rfl hR.inv.1.x_eq hR.inv.1.n_eq
      hR.inv.1.om_eq (by rw [← hi]; exact hlt) (by omega) (by omega) (by unfold X0; omega) (by unfold X0 L0; omega) ho
      (by omega) (by unfold L0; omega))
  have hg := (hw.store (i := LB0 b.size om + 318 + ORDER.getD i 0) (v := 0) (by unfold LB0; omega)
    (by unfold LB0 L0; omega)).store (i := 10) (v := (i : Int) + 1) (by norm_num) (by omega)
  obtain ⟨f1, hw1, hR1, hk1, ag⟩ := next_rel hb hw hR (by rw [hm]; decide) (by rw [hm]; decide) hS hg
    (S := fun c => c = 10 ∨ c = LB0 b.size om + 318 + ORDER.getD i 0)
    (fun c _ _ hc => by simp only [Function.update_apply]; rw [if_neg (by omega), if_neg (by omega)])
    (fun c hc => by unfold ctl LB0 IN at *; omega)
  refine ⟨_, f1, hS, hw1, hR1, ?_, ?_, ?_, hk1⟩
  · rw [hk1 _ (by decide) (by unfold cMODE; omega) (by unfold cMODE LB0; omega)]; exact hm
  · rw [ag _ (by decide) (by unfold cFILL; omega)]; updv
  · rw [ag _ (by unfold LB0; omega) (by unfold LB0 L0; omega)]; updv

/-- **CLREAD at 19:** the CL build's start (target 0, strict). -/
theorem clread_end_next {b : Array Nat} {om : Nat} {lit : Bool} {σ : Store} {p : Int} {f : Int → Int} {st : St}
    (hb : ∀ x ∈ b, x < 256) (hw : World σ p (L0 b.size om) f) (hR : Rel b om lit f st) (hm : f cMODE = mCLREAD)
    (hi : f cFILL = 19) (hlt : ¬ f cFILL < f cHCLEN) :
    ∃ σ1 f1, stepS p σ = some σ1 ∧ World σ1 p (L0 b.size om) f1 ∧ Rel b om lit f1 st ∧ f1 cMODE = mBUILD ∧
      f1 cTGT = 0 ∧ f1 (X0 b.size om + 5) = LB0 b.size om + 318 ∧ f1 (X0 b.size om + 6) = 19 ∧
      f1 (X0 b.size om + 7) = tbase b.size om 0 ∧ f1 (X0 b.size om + 8) = 1 ∧ f1 cPHASE = 0 ∧ f1 cINDEX = 0 ∧
      f1 cFILL = 0 ∧
      Keeps (L0 b.size om) f f1 (fun c => c = 0 ∨ c = 10 ∨ c = 12 ∨ c = 13 ∨ c = 2074 ∨
        (X0 b.size om + 5 ≤ c ∧ c ≤ X0 b.size om + 8)) := by
  have hL : 2080 ≤ L0 b.size om := by unfold L0; omega
  have hXL : X0 b.size om + 8 < L0 b.size om := by unfold X0 L0; omega
  have hXL' : X0 b.size om + 5 < L0 b.size om := by unfold X0 L0; omega
  have hS := stepS_fit hw (by omega) hm rfl clread_mem (by decide)
    (clread_end hw hL (f cFILL) (f cHCLEN) (X0 b.size om) b.size om rfl rfl hR.inv.1.x_eq hR.inv.1.n_eq
      hR.inv.1.om_eq hlt (by omega) (by unfold X0; omega) (by unfold X0 L0; omega))
  have hg := ((((((((hw.store (i := 2074) (v := 0) (by norm_num) (by omega)).store (i := X0 b.size om + 5)
    (v := 2080 + b.size + om + 318) (by unfold X0; omega) hXL').store (i := X0 b.size om + 6) (v := 19)
    (by unfold X0; omega) (by unfold X0 L0; omega)).store (i := X0 b.size om + 7) (v := 2080 + b.size + om + 337)
    (by unfold X0; omega) (by unfold X0 L0; omega)).store (i := X0 b.size om + 8) (v := 1) (by unfold X0; omega)
    hXL).store (i := 12) (v := 0) (by norm_num) (by omega)).store (i := 13) (v := 0) (by norm_num) (by omega)).store
    (i := 10) (v := 0) (by norm_num) (by omega)).store (i := 0) (v := 11) (by norm_num) (by omega)
  obtain ⟨f1, hw1, hR1, hk1, ag⟩ := next_rel hb hw hR (by rw [hm]; decide) (by rw [hm]; decide) hS hg
    (S := fun c => c = 0 ∨ c = 10 ∨ c = 12 ∨ c = 13 ∨ c = 2074 ∨ (X0 b.size om + 5 ≤ c ∧ c ≤ X0 b.size om + 8))
    (fun c _ _ hc => by
      simp only [Function.update_apply]
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
        if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)])
    (fun c hc => by unfold ctl IN X0 at *; omega)
  refine ⟨_, f1, hS, hw1, hR1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hk1⟩
  · rw [ag _ (by decide) (by unfold cMODE; omega)]; updv
  · rw [ag _ (by decide) (by unfold cTGT; omega)]; updv
  · rw [ag _ (by unfold X0; omega) hXL']; updv
  · rw [ag _ (by unfold X0; omega) (by unfold X0 L0; omega)]; updv
  · rw [ag _ (by unfold X0; omega) (by unfold X0 L0; omega)]; updv
  · rw [ag _ (by unfold X0; omega) hXL]; updv
  · rw [ag _ (by decide) (by unfold cPHASE; omega)]; updv
  · rw [ag _ (by decide) (by unfold cINDEX; omega)]; updv
  · rw [ag _ (by decide) (by unfold cFILL; omega)]
    exact (upd_eq _ _ (by decide)).trans (Function.update_self _ _ _)

/-! ## The CL lengths (S6's `readCL`, then S-14's zero fill) -/

/-- What the CL loop keeps besides R, the mode and FILL: the header cells, the cells written so far (k < i) against the
spec's array, and the spec's array still 0 at the positions not yet read. -/
def ClFrame (b : Array Nat) (om : Nat) (bf : Int) (hl hd hc i : Nat) (cl : Array Nat) (f : Int → Int) : Prop :=
  f cHCLEN = hc ∧ f cBF = bf ∧ f cHLIT = hl ∧ f cHDIST = hd ∧ f cDYN = 1 ∧ f cCHK = 1 ∧ cl.size = 19 ∧
    (∀ k : Nat, k < i → f (LB0 b.size om + 318 + ORDER.getD k 0) = cl.getD (ORDER.getD k 0) 0) ∧
    (∀ k : Nat, i ≤ k → k < 19 → cl.getD (ORDER.getD k 0) 0 = 0) ∧ (∀ j : Nat, cl.getD j 0 < 8) ∧ i ≤ 19

def ClInv (b : Array Nat) (om : Nat) (lit : Bool) (bf : Int) (hl hd hc i : Nat) (cl : Array Nat) (f : Int → Int)
    (st : St) : Prop :=
  (Rel b om lit f st ∧ f cMODE = mCLREAD ∧ f cFILL = i) ∧ ClFrame b om bf hl hd hc i cl f

/-- The frame survives a change that avoids the header cells and the CL lengths. -/
theorem ClFrame.keep {b : Array Nat} {om : Nat} {bf : Int} {hl hd hc i : Nat} {cl : Array Nat} {f f' : Int → Int}
    {S : Int → Prop} (h : ClFrame b om bf hl hd hc i cl f) (hk : Keeps (L0 b.size om) f f' S)
    (hS : ∀ c, S c → c ≠ 4 ∧ c ≠ 7 ∧ c ≠ 8 ∧ c ≠ 9 ∧ c ≠ 2072 ∧ c ≠ 2073 ∧
      (c < LB0 b.size om + 318 ∨ LB0 b.size om + 337 ≤ c)) : ClFrame b om bf hl hd hc i cl f' := by
  have hL : 2080 ≤ L0 b.size om := by unfold L0; omega
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  have kc : ∀ c : Int, (c = 4 ∨ c = 7 ∨ c = 8 ∨ c = 9 ∨ c = 2072 ∨ c = 2073) → f' c = f c := fun c hc' =>
    hk c (by omega) (by omega) (fun hs => by have := hS c hs; omega)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, h7, fun k hk' => ?_, h9, h10, h11⟩
  · rw [kc cHCLEN (by unfold cHCLEN; omega)]; exact h1
  · rw [kc cBF (by unfold cBF; omega)]; exact h2
  · rw [kc cHLIT (by unfold cHLIT; omega)]; exact h3
  · rw [kc cHDIST (by unfold cHDIST; omega)]; exact h4
  · rw [kc cDYN (by unfold cDYN; omega)]; exact h5
  · rw [kc cCHK (by unfold cCHK; omega)]; exact h6
  · have hol := order_lt ⟨k, by omega⟩
    simp only at hol
    rw [← h8 k hk']
    exact hk _ (by unfold LB0; omega) (by unfold LB0 L0; omega) (fun hs => by
      have := (hS _ hs).2.2.2.2.2.2; omega)

theorem getD_rep19 (j : Nat) : (Array.replicate 19 0).getD j 0 = 0 := by
  unfold Array.getD; split_ifs <;> simp

/-- **S6's `readCL` against CLREAD/CLPUT:** each length below HCLEN is a READ of 3 bits and a CLPUT. -/
theorem readcl_sim {b : Array Nat} {om : Nat} {lit : Bool} {p : Int} (hb : ∀ x ∈ b, x < 256) (bf : Int) (hl hd hc : Nat)
    (hc19 : hc ≤ 19) : ∀ r i (cl : Array Nat), i + r = hc →
    Sim b om p (readCL (ORDER.drop i) (hc - i) cl) (ClInv b om lit bf hl hd hc i cl)
      (fun cl' f st => ClInv b om lit bf hl hd hc hc cl' f st) := by
  have hL : 2080 ≤ L0 b.size om := by unfold L0; omega
  intro r
  induction r with
  | zero =>
    intro i cl h
    obtain rfl : i = hc := by omega
    rw [Nat.sub_self, readCL_zero]
    exact Sim.pure (fun f st h => h)
  | succ r ih =>
    intro i cl h
    have hi19 : i < 19 := by omega
    rw [order_drop i hi19, show hc - i = (hc - (i + 1)) + 1 by omega, readCL_succ]
    refine Sim.step (pre' := fun f st => (Rel b om lit f st ∧ f cMODE = mREAD ∧ f cK = (2 : Nat) + 1 ∧ f cACC = 0 ∧
      f cWT = 1 ∧ f cRET = mCLPUT) ∧ (f cFILL = i ∧ ClFrame b om bf hl hd hc i cl f)) ?_ ?_
    · rintro σ f st hw ⟨⟨hR, hm, hfi⟩, hF⟩
      obtain ⟨σ1, f1, hS, hw1, hR1, h1, h2, h3, h4, h5, hk1⟩ :=
        clread_req_next hb hw hR hm (by rw [hfi, hF.1]; exact_mod_cast (show i < hc by omega))
      refine ⟨σ1, f1, hS, hw1, ⟨hR1, h1, by rw [h2]; norm_num, h3, h4, h5⟩, ?_,
        hF.keep hk1 (fun c hc' => by unfold LB0; omega)⟩
      rw [hk1 _ (by decide) (by unfold cFILL; omega) (by unfold cFILL; omega)]; exact hfi
    refine Sim.bind (bits_sim' hb 2 mCLPUT (fun f _ => f cFILL = i ∧ ClFrame b om bf hl hd hc i cl f)
      (fun f _ => f cFILL = i ∧ ClFrame b om bf hl hd hc i cl f) (fun f st f' st' hq hk _ _ _ =>
        ⟨by rw [hk _ (by decide) (by unfold cFILL L0; omega) (by unfold rdSet cFILL; omega)]; exact hq.1,
          hq.2.keep hk (fun c hc' => by unfold rdSet at hc'; unfold LB0; omega)⟩)) (fun x => ?_)
    refine Sim.step (pre' := ClInv b om lit bf hl hd hc (i + 1) (cl.set! (ORDER.getD i 0) x)) ?_ (ih (i + 1) _ (by omega))
    rintro σ f st hw ⟨hR, hm, hacc, hfi, hF⟩
    have hx := hR.inv.2.ret (by rw [hm]; decide)
    rw [hm, hacc, show kcap mCLPUT = 8 by decide] at hx
    obtain ⟨σ1, f1, hS, hw1, hR1, h1, h2, h3, hk1⟩ := clput_next hb hw hR hm i hfi hi19
    obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11⟩ := hF
    have hol := order_lt ⟨i, hi19⟩
    simp only at hol
    have ho : ORDER.getD i 0 < cl.size := by omega
    have kk : ∀ c : Int, 0 ≤ c → c < 2080 → c ≠ 0 → c ≠ 10 → f1 c = f c := fun c a0 a1 a2 a3 =>
      hk1 c a0 (by omega) (by unfold LB0; omega)
    refine ⟨σ1, f1, hS, hw1, ⟨hR1, h1, by rw [h2]; push_cast; ring⟩, ?_, ?_, ?_, ?_, ?_, ?_, by rw [size_set!]; exact g7,
      fun k hk => ?_, fun k hk1' hk2 => ?_, fun j => ?_, by omega⟩
    · rw [kk _ (by decide) (by decide) (by decide) (by decide)]; exact g1
    · rw [kk _ (by decide) (by decide) (by decide) (by decide)]; exact g2
    · rw [kk _ (by decide) (by decide) (by decide) (by decide)]; exact g3
    · rw [kk _ (by decide) (by decide) (by decide) (by decide)]; exact g4
    · rw [hk1 _ (by decide) (by unfold cDYN; omega) (by unfold cDYN LB0; omega)]; exact g5
    · rw [hk1 _ (by decide) (by unfold cCHK; omega) (by unfold cCHK LB0; omega)]; exact g6
    · rw [getD_set! _ _ _ _ ho]
      by_cases hki : k = i
      · subst hki; rw [h3, hacc, if_pos rfl]
      · have hne := order_ne (show k < 19 by omega) hi19 hki
        have hol' := order_lt ⟨k, by omega⟩
        simp only at hol'
        rw [if_neg hne, hk1 _ (by unfold LB0; omega) (by unfold LB0 L0; omega) (fun hc' => by
          rcases hc' with hc' | hc' | hc'
          · unfold LB0 at hc'; omega
          · unfold LB0 at hc'; omega
          · exact hne (by unfold LB0 at hc'; omega))]
        exact g8 k (by omega)
    · rw [getD_set! _ _ _ _ ho, if_neg (order_ne hk2 hi19 (by omega))]; exact g9 k (by omega) hk2
    · rw [getD_set! _ _ _ _ ho]; split_ifs
      · omega
      · exact g10 j

/-- What the CL build starts from: BUILD for target 0 (strict) with the 19 CL lengths at LB0 + 318. -/
def ClStart (b : Array Nat) (om : Nat) (lit : Bool) (bf : Int) (hl hd : Nat) (cl : Array Nat) (f : Int → Int) (st : St) :
    Prop :=
  Rel b om lit f st ∧ f cMODE = mBUILD ∧ f cTGT = 0 ∧ f (X0 b.size om + 5) = LB0 b.size om + 318 ∧
    f (X0 b.size om + 6) = 19 ∧ f (X0 b.size om + 7) = tbase b.size om 0 ∧ f (X0 b.size om + 8) = 1 ∧ f cPHASE = 0 ∧
    f cINDEX = 0 ∧ f cFILL = 0 ∧ f cBF = bf ∧ f cHLIT = hl ∧ f cHDIST = hd ∧ f cDYN = 1 ∧ f cCHK = 1 ∧ cl.size = 19 ∧
    (∀ j : Nat, cl.getD j 0 < 8) ∧ (∀ j : Nat, j < 19 → f (LB0 b.size om + 318 + j) = cl.getD j 0)

/-- **S-14's zero fill, then CLREAD's end:** the cells past HCLEN are zeroed (the spec's array is 0 there already). -/
theorem clzero_run {b : Array Nat} {om : Nat} {lit : Bool} {p : Int} (hb : ∀ x ∈ b, x < 256) (bf : Int) (hl hd hc : Nat)
    (cl : Array Nat) : ∀ r (i : Nat) (σ : Store) (f : Int → Int) (st : St), i + r = 19 → hc ≤ i →
      World σ p (L0 b.size om) f → ClInv b om lit bf hl hd hc i cl f st →
      ∃ σ' f', Reach p σ σ' ∧ World σ' p (L0 b.size om) f' ∧ ClStart b om lit bf hl hd cl f' st := by
  have hL : 2080 ≤ L0 b.size om := by unfold L0; omega
  intro r
  induction r with
  | zero =>
    intro i σ f st h hci hw ⟨⟨hR, hm, hfi⟩, hF⟩
    obtain rfl : i = 19 := by omega
    obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, -⟩ := hF
    have hlt : ¬ f cFILL < f cHCLEN := by rw [hfi, g1]; exact_mod_cast (show ¬ 19 < hc by omega)
    obtain ⟨σ1, f1, hS, hw1, hR1, h1, h2, h3, h4, h5, h6, h7, h8, h9, hk1⟩ :=
      clread_end_next hb hw hR hm (by rw [hfi]; rfl) hlt
    refine ⟨σ1, f1, Reach.step hS, hw1, hR1, h1, h2, h3, h4, h5, h6, h7, h8, h9, ?_, ?_, ?_, ?_, ?_, g7, g10,
      fun j hj => ?_⟩
    · rw [hk1 _ (by decide) (by unfold cBF; omega) (by unfold cBF X0; omega)]; exact g2
    · rw [hk1 _ (by decide) (by unfold cHLIT; omega) (by unfold cHLIT X0; omega)]; exact g3
    · rw [hk1 _ (by decide) (by unfold cHDIST; omega) (by unfold cHDIST X0; omega)]; exact g4
    · rw [hk1 _ (by decide) (by unfold cDYN; omega) (by unfold cDYN X0; omega)]; exact g5
    · rw [hk1 _ (by decide) (by unfold cCHK; omega) (by unfold cCHK X0; omega)]; exact g6
    · obtain ⟨⟨k, hk⟩, hkj⟩ := order_surj ⟨j, hj⟩
      simp only at hkj
      have := g8 k hk
      rw [hkj] at this
      rw [hk1 _ (by unfold LB0; omega) (by unfold LB0 L0; omega) (by unfold LB0 X0; omega)]; exact this
  | succ r ih =>
    intro i σ f st h hci hw ⟨⟨hR, hm, hfi⟩, hF⟩
    have hi19 : i < 19 := by omega
    obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11⟩ := hF
    have hlt : ¬ f cFILL < f cHCLEN := by rw [hfi, g1]; exact_mod_cast (show ¬ i < hc by omega)
    obtain ⟨σ1, f1, hS, hw1, hR1, h1, h2, h3, hk1⟩ := clread_zero_next hb hw hR hm i hfi hlt hi19
    have hol := order_lt ⟨i, hi19⟩
    simp only at hol
    have kk : ∀ c : Int, 0 ≤ c → c < 2080 → c ≠ 10 → f1 c = f c := fun c a0 a1 a2 =>
      hk1 c a0 (by omega) (by unfold LB0; omega)
    have hF1 : ClFrame b om bf hl hd hc (i + 1) cl f1 := by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, g7, fun k hk => ?_, fun k hk1' hk2 => g9 k (by omega) hk2, g10, by omega⟩
      · rw [kk _ (by decide) (by decide) (by decide)]; exact g1
      · rw [kk _ (by decide) (by decide) (by decide)]; exact g2
      · rw [kk _ (by decide) (by decide) (by decide)]; exact g3
      · rw [kk _ (by decide) (by decide) (by decide)]; exact g4
      · rw [hk1 _ (by decide) (by unfold cDYN; omega) (by unfold cDYN LB0; omega)]; exact g5
      · rw [hk1 _ (by decide) (by unfold cCHK; omega) (by unfold cCHK LB0; omega)]; exact g6
      · by_cases hki : k = i
        · subst hki; rw [h3, g9 k (le_refl _) hi19]; rfl
        · have hne := order_ne (show k < 19 by omega) hi19 hki
          have hol' := order_lt ⟨k, by omega⟩
          simp only at hol'
          rw [hk1 _ (by unfold LB0; omega) (by unfold LB0 L0; omega) (fun hc' => by
            rcases hc' with hc' | hc'
            · unfold LB0 at hc'; omega
            · exact hne (by unfold LB0 at hc'; omega))]
          exact g8 k (by omega)
    obtain ⟨σ', f', hR', hw', hst⟩ := ih (i + 1) σ1 f1 st (by omega) (by omega) hw1
      ⟨⟨hR1, h1, by rw [h2]; push_cast; ring⟩, hF1⟩
    exact ⟨σ', f', (Reach.step hS).trans hR', hw', hst⟩

/-! ## The lengths loop, machine side: LENS, LSYM, LREP, REP -/

/-- **LENS, a length still owed:** a decode request in table 0, returning to LSYM. -/
theorem lens_req_next {b : Array Nat} {om : Nat} {lit : Bool} {σ : Store} {p : Int} {f : Int → Int} {st : St}
    (hb : ∀ x ∈ b, x < 256) (hw : World σ p (L0 b.size om) f) (hR : Rel b om lit f st) (hm : f cMODE = mLENS)
    (hlt : f cFILL < f cHLIT + f cHDIST) :
    ∃ σ1 f1, stepS p σ = some σ1 ∧ World σ1 p (L0 b.size om) f1 ∧ DecReady b om lit f1 st 0 mLSYM ∧
      Keeps (L0 b.size om) f f1 (decReqSet b.size om) := by
  have hL : 2080 ≤ L0 b.size om := by unfold L0; omega
  have hX4 : X0 b.size om + 4 < L0 b.size om := by unfold X0 L0; omega
  have hS := stepS_fit hw (by omega) hm rfl lens_mem (by decide)
    (lens_req hw hL (f cFILL) (f cHLIT) (f cHDIST) (X0 b.size om) b.size om rfl rfl rfl hR.inv.1.x_eq hR.inv.1.n_eq
      hR.inv.1.om_eq hlt (by unfold X0; omega) (by unfold X0 L0; omega))
  obtain ⟨f1, hw1, hR1, hk1, ag⟩ := next_rel hb hw hR (by rw [hm]; decide) (by rw [hm]; decide) hS
    (hw.reqDec (by unfold X0; omega) hX4 0 25) (reqDecF_keeps _ b.size om f 0 25)
    (fun c hc => by unfold decReqSet at hc; unfold ctl IN X0 at *; omega)
  obtain ⟨v1, v2, v3, v4, v5⟩ := reqDecF_vals f (X0 b.size om) 0 25 (by unfold X0; omega)
  refine ⟨_, f1, hS, hw1, ⟨hR1, ?_, ?_, ?_, ?_, ?_⟩, hk1⟩
  · rw [ag _ (by decide) (by unfold cMODE; omega)]; exact v1
  · rw [ag _ (by unfold X0; omega) (by unfold X0 L0; omega)]; simpa using v2
  · rw [ag _ (by unfold X0; omega) (by unfold X0 L0; omega)]; simpa using v3
  · rw [ag _ (by unfold X0; omega) (by unfold X0 L0; omega)]; exact v4
  · rw [ag _ (by unfold X0; omega) (by unfold X0 L0; omega)]; exact v5

/-- **LSYM:** by the decoded symbol s — a length (≤ 15) written at FILL; 16 with FILL 0 REJECTs; 16 / 17 / 18 set LAST and
PENDING and READ 2 / 3 / 7 bits, returning to LREP. -/
theorem lsym_next {b : Array Nat} {om : Nat} {lit : Bool} {σ : Store} {p : Int} {f : Int → Int} {st : St}
    (hb : ∀ x ∈ b, x < 256) (hw : World σ p (L0 b.size om) f) (hR : Rel b om lit f st) (hm : f cMODE = mLSYM)
    (s fl : Nat) (hs : f (X0 b.size om + 4) = s) (hfl : f cFILL = fl) (hfl3 : fl < 318) :
    (s ≤ 15 → ∃ σ1 f1, stepS p σ = some σ1 ∧ World σ1 p (L0 b.size om) f1 ∧ Rel b om lit f1 st ∧ f1 cMODE = mLENS ∧
      f1 cFILL = fl + 1 ∧ f1 (LB0 b.size om + fl) = s ∧
      Keeps (L0 b.size om) f f1 (fun c => c = 0 ∨ c = 10 ∨ c = LB0 b.size om + fl)) ∧
    (s = 16 → fl = 0 → ∃ σ1 f1, stepS p σ = some σ1 ∧ World σ1 p (L0 b.size om) f1 ∧ f1 cMODE = mREJECT) ∧
    (16 ≤ s → (s = 16 → fl ≠ 0) → ∃ σ1 f1, stepS p σ = some σ1 ∧ World σ1 p (L0 b.size om) f1 ∧ Rel b om lit f1 st ∧
      f1 cMODE = mREAD ∧ f1 cACC = 0 ∧ f1 cWT = 1 ∧ f1 cRET = mLREP ∧
      f1 cK = (if s = 16 then 2 else if s = 17 then 3 else 7) ∧ f1 cPEND = (if s = 18 ∨ 18 < s then 11 else 3) ∧
      f1 cLAST = (if s = 16 then f (LB0 b.size om + (fl - 1 : Int)) else 0) ∧
      Keeps (L0 b.size om) f f1 (fun c => c = 5 ∨ c = 11 ∨ c = 0 ∨ (2068 ≤ c ∧ c ≤ 2071))) := by
  have hL : 2080 ≤ L0 b.size om := by unfold L0; omega
  have hXL : X0 b.size om + 8 < L0 b.size om := by unfold X0 L0; omega
  have hS := stepS_fit hw (by omega) hm rfl lsym_mem (by decide)
    (lsym_step hw hL (X0 b.size om) s fl b.size om (f (LB0 b.size om + (fl - 1 : Int))) hR.inv.1.x_eq
      (by unfold X0; omega) hXL hs hfl hR.inv.1.n_eq hR.inv.1.om_eq (fun _ => ⟨by omega, by unfold L0; omega⟩)
      (fun _ h0 => ⟨by omega, by unfold L0; omega⟩) rfl)
  refine ⟨fun h15 => ?_, fun h16 h0 => ?_, fun h16 hne => ?_⟩
  · rw [show lsymH σ.H p s fl b.size om (f (LB0 b.size om + (fl - 1 : Int))) =
      ((σ.H.insert (p + (2080 + b.size + om + fl)) s).insert (p + 10) ((fl : Int) + 1)).insert (p + 0) 12 by
        unfold lsymH; rw [if_pos (by exact_mod_cast h15)]] at hS
    have hg := ((hw.store (i := LB0 b.size om + fl) (v := s) (by unfold LB0; omega) (by unfold LB0 L0; omega)).store
      (i := 10) (v := (fl : Int) + 1) (by norm_num) (by omega)).store (i := 0) (v := 12) (by norm_num) (by omega)
    obtain ⟨f1, hw1, hR1, hk1, ag⟩ := next_rel hb hw hR (by rw [hm]; decide) (by rw [hm]; decide) hS hg
      (S := fun c => c = 0 ∨ c = 10 ∨ c = LB0 b.size om + fl)
      (fun c _ _ hc => by simp only [Function.update_apply]; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)])
      (fun c hc => by unfold ctl LB0 IN at *; omega)
    refine ⟨_, f1, hS, hw1, hR1, ?_, ?_, ?_, hk1⟩
    · rw [ag _ (by decide) (by unfold cMODE; omega)]; updv
    · rw [ag _ (by decide) (by unfold cFILL; omega)]; updv
    · rw [ag _ (by unfold LB0; omega) (by unfold LB0 L0; omega)]; updv
  · subst h16; subst h0
    rw [show lsymH σ.H p ((16 : Nat) : Int) ((0 : Nat) : Int) b.size om (f (LB0 b.size om + ((0 : Nat) - 1 : Int))) =
      (σ.H.insert (p + 14) 13).insert (p + 0) 99 by unfold lsymH; simp] at hS
    exact ⟨_, _, hS, (hw.store (i := 14) (v := 13) (by norm_num) (by omega)).store (i := 0) (v := 99) (by norm_num)
      (by omega), by simp [cMODE, mREJECT]⟩
  · set pv := f (LB0 b.size om + (fl - 1 : Int)) with hpv
    have key : ∀ (K Pd La : Int), lsymH σ.H p s fl b.size om pv = reqH ((σ.H.insert (p + 11) La).insert (p + 5) Pd) p K 26 →
        K = (if s = 16 then 2 else if s = 17 then 3 else 7) → Pd = (if s = 18 ∨ 18 < s then 11 else 3) →
        La = (if s = 16 then pv else 0) →
        ∃ σ1 f1, stepS p σ = some σ1 ∧ World σ1 p (L0 b.size om) f1 ∧ Rel b om lit f1 st ∧
          f1 cMODE = mREAD ∧ f1 cACC = 0 ∧ f1 cWT = 1 ∧ f1 cRET = mLREP ∧
          f1 cK = (if s = 16 then 2 else if s = 17 then 3 else 7) ∧ f1 cPEND = (if s = 18 ∨ 18 < s then 11 else 3) ∧
          f1 cLAST = (if s = 16 then pv else 0) ∧
          Keeps (L0 b.size om) f f1 (fun c => c = 5 ∨ c = 11 ∨ c = 0 ∨ (2068 ≤ c ∧ c ≤ 2071)) := by
      intro K Pd La e eK ePd eLa
      rw [e] at hS
      obtain ⟨f1, hw1, hR1, h1, h2, h3, h4, h5, hk1, ag⟩ :=
        req_next (σ1 := ⟨(σ.H.insert (p + 11) La).insert (p + 5) Pd, σ.R⟩) (S := fun c => c = 5 ∨ c = 11) hb hw hR
          (by rw [hm]; decide) (by rw [hm]; decide) K 26 hS
          ((hw.store (i := 11) (v := La) (by norm_num) (by omega)).store (i := 5) (v := Pd) (by norm_num) (by omega))
          (fun c _ _ hc => by simp only [Function.update_apply]; rw [if_neg (by omega), if_neg (by omega)])
          (fun c hc => by unfold ctl; omega)
      refine ⟨_, f1, hS, hw1, hR1, h1, h3, h4, h5, by rw [h2, eK], ?_, ?_,
        fun c h0 h1 hc => hk1 c h0 h1 (fun h => hc (or_assoc.mp h))⟩
      · rw [ag _ (by decide) (by unfold cPEND; omega) (by decide) (by decide), ← ePd]; updv
      · rw [ag _ (by decide) (by unfold cLAST; omega) (by decide) (by decide), ← eLa]; updv
    by_cases e16 : s = 16
    · subst e16
      exact key 2 3 pv (by unfold lsymH; rw [if_neg (by decide), if_pos (by norm_num), if_neg (by exact_mod_cast hne rfl)]) (by simp)
        (by simp) (by simp)
    · by_cases e17 : s = 17
      · subst e17
        exact key 3 3 0 (by unfold lsymH; simp) (by simp) (by simp) (by simp)
      · exact key 7 11 0 (by
          unfold lsymH
          rw [if_neg (by omega), if_neg (by exact_mod_cast e16), if_neg (by exact_mod_cast e17)])
          (by rw [if_neg e16, if_neg e17]) (by rw [if_pos (by omega)]) (by rw [if_neg e16])

/-- **LREP:** FILL + PENDING + acc past HLIT + HDIST REJECTs; else PENDING += acc, REP. -/
theorem lrep_next {b : Array Nat} {om : Nat} {lit : Bool} {σ : Store} {p : Int} {f : Int → Int} {st : St}
    (hb : ∀ x ∈ b, x < 256) (hw : World σ p (L0 b.size om) f) (hR : Rel b om lit f st) (hm : f cMODE = mLREP) :
    (f cHLIT + f cHDIST < f cFILL + (f cPEND + f cACC) →
      ∃ σ1 f1, stepS p σ = some σ1 ∧ World σ1 p (L0 b.size om) f1 ∧ f1 cMODE = mREJECT) ∧
    (¬ f cHLIT + f cHDIST < f cFILL + (f cPEND + f cACC) →
      ∃ σ1 f1, stepS p σ = some σ1 ∧ World σ1 p (L0 b.size om) f1 ∧ Rel b om lit f1 st ∧ f1 cMODE = mREP ∧
        f1 cPEND = f cPEND + f cACC ∧ Keeps (L0 b.size om) f f1 (fun c => c = 0 ∨ c = 5)) := by
  have hL : 2080 ≤ L0 b.size om := by unfold L0; omega
  have hS := stepS_fit hw (by omega) hm rfl lrep_mem (by decide)
    (lrep_step hw hL (f cPEND) (f cACC) (f cFILL) (f cHLIT) (f cHDIST) rfl rfl rfl rfl rfl)
  refine ⟨fun hc => ?_, fun hc => ?_⟩
  · rw [if_pos hc] at hS
    exact ⟨_, _, hS, (hw.store (i := 14) (v := 14) (by norm_num) (by omega)).store (i := 0) (v := 99) (by norm_num)
      (by omega), by simp [cMODE, mREJECT]⟩
  · rw [if_neg hc] at hS
    have hg := (hw.store (i := 5) (v := f cPEND + f cACC) (by norm_num) (by omega)).store (i := 0) (v := 27) (by norm_num)
      (by omega)
    obtain ⟨f1, hw1, hR1, hk1, ag⟩ := next_rel hb hw hR (by rw [hm]; decide) (by rw [hm]; decide) hS hg
      (S := fun c => c = 0 ∨ c = 5)
      (fun c _ _ hc => by simp only [Function.update_apply]; rw [if_neg (by omega), if_neg (by omega)])
      (fun c hc => by unfold ctl; omega)
    refine ⟨_, f1, hS, hw1, hR1, ?_, ?_, hk1⟩
    · rw [ag _ (by decide) (by unfold cMODE; omega)]; updv
    · rw [ag _ (by decide) (by unfold cPEND; omega)]; updv

/-- **REP, run to its end:** PENDING copies of LAST written from FILL on, then LENS. -/
theorem rep_run {b : Array Nat} {om : Nat} {lit : Bool} {p : Int} (hb : ∀ x ∈ b, x < 256) :
    ∀ (k : Nat) (σ : Store) (f : Int → Int) (st : St) (fl : Nat), World σ p (L0 b.size om) f → Rel b om lit f st →
      f cMODE = mREP → f cPEND = k → f cFILL = fl → fl + k ≤ 318 →
      ∃ σ' f', Reach p σ σ' ∧ World σ' p (L0 b.size om) f' ∧ Rel b om lit f' st ∧ f' cMODE = mLENS ∧
        f' cFILL = fl + k ∧ (∀ j : Nat, j < k → f' (LB0 b.size om + (fl + j : Nat)) = f cLAST) ∧
        Keeps (L0 b.size om) f f' (fun c => c = 0 ∨ c = 5 ∨ c = 10 ∨
          (LB0 b.size om + fl ≤ c ∧ c < LB0 b.size om + fl + k)) := by
  have hL : 2080 ≤ L0 b.size om := by unfold L0; omega
  intro k
  induction k with
  | zero =>
    intro σ f st fl hw hR hm hpd hfl _
    have hS := stepS_fit hw (by omega) hm rfl rep_mem (by decide) (rep_end hw hL (by rw [hpd]; rfl))
    have hg := hw.store (i := 0) (v := 12) (by norm_num) (by omega)
    obtain ⟨f1, hw1, hR1, hk1, ag⟩ := next_rel hb hw hR (by rw [hm]; decide) (by rw [hm]; decide) hS hg
      (S := fun c => c = 0) (fun c _ _ hc => upd_eq _ _ hc) (fun c hc => by unfold ctl; omega)
    refine ⟨_, f1, Reach.step hS, hw1, hR1, ?_, ?_, fun j hj => by omega, fun c h0 h1 hc => hk1 c h0 h1 (fun h => hc (Or.inl h))⟩
    · rw [ag _ (by decide) (by unfold cMODE; omega)]; updv
    · rw [hk1 _ (by decide) (by unfold cFILL; omega) (by unfold cFILL; omega), hfl]; simp
  | succ k ih =>
    intro σ f st fl hw hR hm hpd hfl hk
    have hS := stepS_fit hw (by omega) hm rfl rep_mem (by decide)
      (rep_byte hw hL (k + 1 : Nat) fl (f cLAST) b.size om hpd (by omega) hfl rfl hR.inv.1.n_eq hR.inv.1.om_eq
        (by omega) (by unfold L0; omega))
    have hg := ((hw.store (i := LB0 b.size om + fl) (v := f cLAST) (by unfold LB0; omega) (by unfold LB0 L0; omega)).store
      (i := 10) (v := (fl : Int) + 1) (by norm_num) (by omega)).store (i := 5) (v := ((k + 1 : Nat) : Int) - 1)
      (by norm_num) (by omega)
    obtain ⟨f1, hw1, hR1, hk1, ag⟩ := next_rel hb hw hR (by rw [hm]; decide) (by rw [hm]; decide) hS hg
      (S := fun c => c = 5 ∨ c = 10 ∨ c = LB0 b.size om + fl)
      (fun c _ _ hc => by simp only [Function.update_apply]; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)])
      (fun c hc => by unfold ctl LB0 IN at *; omega)
    have e1 : f1 (LB0 b.size om + fl) = f cLAST := by rw [ag _ (by unfold LB0; omega) (by unfold LB0 L0; omega)]; updv
    have eL : f1 cLAST = f cLAST := hk1 _ (by decide) (by unfold cLAST; omega) (by unfold cLAST LB0; omega)
    obtain ⟨σ', f', hR', hw', hR'', hm', hfl', hc', hk'⟩ := ih _ f1 st (fl + 1) hw1 hR1
      (by rw [hk1 _ (by decide) (by unfold cMODE; omega) (by unfold cMODE LB0; omega)]; exact hm)
      (by rw [ag _ (by decide) (by unfold cPEND; omega)]; updv)
      (by rw [ag _ (by decide) (by unfold cFILL; omega)]; updv) (by omega)
    refine ⟨σ', f', (Reach.step hS).trans hR', hw', hR'', hm', by rw [hfl']; omega, fun j hj => ?_, fun c h0 h1 hc => ?_⟩
    · by_cases hj0 : j = 0
      · subst hj0
        rw [hk' _ (by unfold LB0; omega) (by unfold LB0 L0; omega) (by unfold LB0; push_cast; omega)]
        simpa using e1
      · have := hc' (j - 1) (by omega)
        rw [show fl + 1 + (j - 1) = fl + j by omega, eL] at this
        exact this
    · rw [hk' c h0 h1 (by push_cast at hc ⊢; omega), hk1 c h0 h1 (by push_cast at hc ⊢; omega)]

/-- **LENS, the lengths complete:** lengths[256] = 0 REJECTs; else BUILD for L (target 1) from LB0, HLIT symbols. -/
theorem lens_end_next {b : Array Nat} {om : Nat} {lit : Bool} {σ : Store} {p : Int} {f : Int → Int} {st : St}
    (hb : ∀ x ∈ b, x < 256) (hw : World σ p (L0 b.size om) f) (hR : Rel b om lit f st) (hm : f cMODE = mLENS)
    (hge : ¬ f cFILL < f cHLIT + f cHDIST) :
    (f (LB0 b.size om + 256) = 0 → ∃ σ1 f1, stepS p σ = some σ1 ∧ World σ1 p (L0 b.size om) f1 ∧ f1 cMODE = mREJECT) ∧
    (f (LB0 b.size om + 256) ≠ 0 → ∃ σ1 f1, stepS p σ = some σ1 ∧ World σ1 p (L0 b.size om) f1 ∧ Rel b om lit f1 st ∧
      f1 cMODE = mBUILD ∧ f1 cTGT = 1 ∧ f1 (X0 b.size om + 5) = LB0 b.size om ∧ f1 (X0 b.size om + 6) = f cHLIT ∧
      f1 (X0 b.size om + 7) = tbase b.size om 1 ∧ f1 (X0 b.size om + 8) = 0 ∧ f1 cPHASE = 0 ∧ f1 cINDEX = 0 ∧
      Keeps (L0 b.size om) f f1 (fun c => c = 0 ∨ c = 12 ∨ c = 13 ∨ c = 2074 ∨
        (X0 b.size om + 5 ≤ c ∧ c ≤ X0 b.size om + 8))) := by
  have hL : 2080 ≤ L0 b.size om := by unfold L0; omega
  have hXL : X0 b.size om + 8 < L0 b.size om := by unfold X0 L0; omega
  have hXL' : X0 b.size om + 5 < L0 b.size om := by unfold X0 L0; omega
  have hS := stepS_fit hw (by omega) hm rfl lens_mem (by decide)
    (lens_end hw hL (f cFILL) (f cHLIT) (f cHDIST) (X0 b.size om) b.size om (f (LB0 b.size om + 256)) rfl rfl rfl
      hR.inv.1.x_eq hR.inv.1.n_eq hR.inv.1.om_eq hge (by unfold X0; omega) hXL (by omega) (by unfold L0; omega) rfl)
  refine ⟨fun hz => ?_, fun hz => ?_⟩
  · rw [if_pos hz] at hS
    exact ⟨_, _, hS, (hw.store (i := 14) (v := 12) (by norm_num) (by omega)).store (i := 0) (v := 99) (by norm_num)
      (by omega), by simp [cMODE, mREJECT]⟩
  · rw [if_neg hz] at hS
    have hg := (((((((hw.store (i := 2074) (v := 1) (by norm_num) (by omega)).store (i := X0 b.size om + 5)
      (v := 2080 + b.size + om) (by unfold X0; omega) hXL').store (i := X0 b.size om + 6) (v := f cHLIT)
      (by unfold X0; omega) (by unfold X0 L0; omega)).store (i := X0 b.size om + 7) (v := 2080 + b.size + om + 689)
      (by unfold X0; omega) (by unfold X0 L0; omega)).store (i := X0 b.size om + 8) (v := 0) (by unfold X0; omega)
      hXL).store (i := 12) (v := 0) (by norm_num) (by omega)).store (i := 13) (v := 0) (by norm_num) (by omega)).store
      (i := 0) (v := 11) (by norm_num) (by omega)
    obtain ⟨f1, hw1, hR1, hk1, ag⟩ := next_rel hb hw hR (by rw [hm]; decide) (by rw [hm]; decide) hS hg
      (S := fun c => c = 0 ∨ c = 12 ∨ c = 13 ∨ c = 2074 ∨ (X0 b.size om + 5 ≤ c ∧ c ≤ X0 b.size om + 8))
      (fun c _ _ hc => by
        simp only [Function.update_apply]
        rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
          if_neg (by omega), if_neg (by omega), if_neg (by omega)])
      (fun c hc => by unfold ctl IN X0 at *; omega)
    refine ⟨_, f1, hS, hw1, hR1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hk1⟩
    · rw [ag _ (by decide) (by unfold cMODE; omega)]; updv
    · rw [ag _ (by decide) (by unfold cTGT; omega)]; updv
    · rw [ag _ (by unfold X0; omega) hXL']; updv
    · rw [ag _ (by unfold X0; omega) (by unfold X0 L0; omega)]; updv
    · rw [ag _ (by unfold X0; omega) (by unfold X0 L0; omega)]; updv
    · rw [ag _ (by unfold X0; omega) hXL]; updv
    · rw [ag _ (by decide) (by unfold cPHASE; omega)]; updv
    · rw [ag _ (by decide) (by unfold cINDEX; omega)]; updv

/-! ## The lengths loop against S6's `lensLoop` -/

def lnext (CL : Code) (total fuel : Nat) (lens' : Array Nat) : M (Array Nat) :=
  if lens'.size > total then (reject "invalid bit length repeat" : M Unit) >>= fun _ => lensLoop CL total fuel lens'
  else lensLoop CL total fuel lens'

/-- One `lensLoop` body after the decode, as the do-notation elaborates it (the continuation in every branch). -/
def lbody (CL : Code) (total fuel : Nat) (lens : Array Nat) (s : Nat) : M (Array Nat) :=
  if s ≤ 15 then pure (lens.push s) >>= fun lens' => lnext CL total fuel lens'
  else if s = 16 then
    (if lens.size = 0 then (reject "repeat with no first length" : M Unit) >>= fun _ =>
        (bits 2 >>= fun r => pure (pushN (lens.getD (lens.size - 1) 0) (3 + r) lens) >>= fun lens' =>
          lnext CL total fuel lens')
     else bits 2 >>= fun r => pure (pushN (lens.getD (lens.size - 1) 0) (3 + r) lens) >>= fun lens' =>
          lnext CL total fuel lens')
  else if s = 17 then bits 3 >>= fun r => pure (pushN 0 (3 + r) lens) >>= fun lens' => lnext CL total fuel lens'
  else bits 7 >>= fun r => pure (pushN 0 (11 + r) lens) >>= fun lens' => lnext CL total fuel lens'

theorem lensLoop_succ (CL : Code) (total fuel : Nat) (lens : Array Nat) :
    lensLoop CL total (fuel + 1) lens = if lens.size < total then
      (decode CL >>= fun s => lbody CL total fuel lens s) else pure lens := rfl

/-- What the lengths loop keeps: the header cells, CHK and DYN, the CL table, and the lengths so far in the lengths area. -/
def LFrame (b : Array Nat) (om : Nat) (bf : Int) (hl hd : Nat) (cl lens : Array Nat) (f : Int → Int) : Prop :=
  f cHLIT = hl ∧ f cHDIST = hd ∧ f cBF = bf ∧ f cDYN = 1 ∧ f cCHK = 1 ∧ TblRel b.size om f 0 cl ∧
    lens.size ≤ hl + hd ∧ (∀ i : Nat, i < lens.size → f (LB0 b.size om + i) = lens.getD i 0) ∧
    (∀ i : Nat, i < lens.size → lens.getD i 0 ≤ 15)

theorem LFrame.keep {b : Array Nat} {om : Nat} {bf : Int} {hl hd : Nat} {cl lens : Array Nat} {f f' : Int → Int}
    {S : Int → Prop} (h : LFrame b om bf hl hd cl lens f) (hk : Keeps (L0 b.size om) f f' S) (htot : hl + hd ≤ 318)
    (hS : ∀ c, S c → c ≠ 4 ∧ c ≠ 7 ∧ c ≠ 8 ∧ c ≠ 2072 ∧ c ≠ 2073 ∧ (c < LB0 b.size om ∨ LB0 b.size om + lens.size ≤ c) ∧
      (c < tbase b.size om 0 ∨ tbase b.size om 0 + 352 ≤ c)) : LFrame b om bf hl hd cl lens f' := by
  have hL : 2080 ≤ L0 b.size om := by unfold L0; omega
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  have kc : ∀ c : Int, (c = 4 ∨ c = 7 ∨ c = 8 ∨ c = 2072 ∨ c = 2073) → f' c = f c := fun c hc' =>
    hk c (by omega) (by omega) (fun hs => by have := hS c hs; omega)
  refine ⟨?_, ?_, ?_, ?_, ?_, h6.keep' (by norm_num) hk (fun c hc => (hS c hc).2.2.2.2.2.2), h7, fun i hi => ?_, h9⟩
  · rw [kc cHLIT (by unfold cHLIT; omega)]; exact h1
  · rw [kc cHDIST (by unfold cHDIST; omega)]; exact h2
  · rw [kc cBF (by unfold cBF; omega)]; exact h3
  · rw [kc cDYN (by unfold cDYN; omega)]; exact h4
  · rw [kc cCHK (by unfold cCHK; omega)]; exact h5
  · rw [← h8 i hi]
    exact hk _ (by unfold LB0; omega) (by unfold LB0 L0; omega) (fun hs => by
      have := (hS _ hs).2.2.2.2.2.1; omega)

theorem LFrame.pushN {b : Array Nat} {om : Nat} {bf : Int} {hl hd : Nat} {cl lens : Array Nat} {f : Int → Int}
    (h : LFrame b om bf hl hd cl lens f) (v k : Nat) (hv : v ≤ 15) (hk : lens.size + k ≤ hl + hd)
    (hc : ∀ j : Nat, j < k → f (LB0 b.size om + (lens.size + j : Nat)) = v) :
    LFrame b om bf hl hd cl (pushN v k lens) f := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  have hs := pushN_size v k lens
  refine ⟨h1, h2, h3, h4, h5, h6, by rw [hs]; exact hk, fun i hi => ?_, fun i hi => ?_⟩
  · rw [pushN_getD]
    by_cases a1 : i < lens.size
    · rw [if_pos a1]; exact h8 i a1
    · rw [if_neg a1, if_pos (by omega)]
      have := hc (i - lens.size) (by omega)
      rw [show lens.size + (i - lens.size) = i by omega] at this
      exact this
  · rw [pushN_getD]
    by_cases a1 : i < lens.size
    · rw [if_pos a1]; exact h9 i a1
    · rw [if_neg a1, if_pos (by omega)]; exact hv

def LPre (b : Array Nat) (om : Nat) (lit : Bool) (bf : Int) (hl hd : Nat) (cl lens : Array Nat) (F : Nat)
    (f : Int → Int) (st : St) : Prop :=
  ((Rel b om lit f st ∧ f cMODE = mLENS ∧ f cFILL = lens.size) ∧ LFrame b om bf hl hd cl lens f) ∧ 8 * b.size - st.pos < F

def LPost (b : Array Nat) (om : Nat) (lit : Bool) (bf : Int) (hl hd : Nat) (cl : Array Nat) (lens : Array Nat)
    (f : Int → Int) (st : St) : Prop :=
  ((Rel b om lit f st ∧ f cMODE = mLENS ∧ f cFILL = lens.size) ∧ LFrame b om bf hl hd cl lens f) ∧ lens.size = hl + hd

/-- After a repeat's extra bits: LREP, then REP's copies, then the loop again. -/
theorem rep_tail {b : Array Nat} {om : Nat} {lit : Bool} {p : Int} (hb : ∀ x ∈ b, x < 256) (bf : Int) (hl hd : Nat)
    (htot : hl + hd ≤ 316) (cl : Array Nat) (fuel : Nat)
    (ih : ∀ lens, Sim b om p (lensLoop (assign cl) (hl + hd) fuel lens) (LPre b om lit bf hl hd cl lens fuel)
      (LPost b om lit bf hl hd cl))
    (lens : Array Nat) (v q r : Nat) (hv15 : v ≤ 15) :
    Sim b om p (pure (pushN v (q + r) lens) >>= fun lens' => lnext (assign cl) (hl + hd) fuel lens')
      (fun f st => Rel b om lit f st ∧ f cMODE = mLREP ∧ f cACC = r ∧ (f cPEND = q ∧ f cLAST = v ∧
        f cFILL = lens.size ∧ LFrame b om bf hl hd cl lens f ∧ 8 * b.size - st.pos < fuel))
      (LPost b om lit bf hl hd cl) := by
  have hL : 2080 ≤ L0 b.size om := by unfold L0; omega
  refine Sim.bind (mid := fun lens' f st => lens' = pushN v (q + r) lens ∧ (Rel b om lit f st ∧ f cMODE = mLREP ∧
    f cACC = r ∧ (f cPEND = q ∧ f cLAST = v ∧ f cFILL = lens.size ∧ LFrame b om bf hl hd cl lens f ∧
      8 * b.size - st.pos < fuel))) (Sim.pure fun f st h => ⟨rfl, h⟩) (fun lens' => ?_)
  unfold lnext
  refine Sim.ite (fun hc => Sim.reject_bind ?_) (fun hc => Sim.reach ?_ (ih lens'))
  · rintro σ f st hw ⟨rfl, hR, hm, ha, hpd, hla, hfl, hF, hfu⟩
    rw [pushN_size] at hc
    obtain ⟨σ1, f1, hS, hw1, hm1⟩ := (lrep_next hb hw hR hm).1 (by rw [hF.1, hF.2.1, hfl, hpd, ha]; push_cast; omega)
    exact ⟨σ1, f1, Reach.step hS, hw1, hm1⟩
  · rintro σ f st hw ⟨rfl, hR, hm, ha, hpd, hla, hfl, hF, hfu⟩
    rw [pushN_size] at hc
    obtain ⟨σ1, f1, hS, hw1, hR1, h1, h2, hk1⟩ := (lrep_next hb hw hR hm).2
      (by rw [hF.1, hF.2.1, hfl, hpd, ha]; push_cast; omega)
    have hF1 := hF.keep hk1 (by omega) (fun c hc' => by unfold tbase LB0; omega)
    obtain ⟨σ2, f2, hR2, hw2, hRe2, hm2, hfl2, hc2, hk2⟩ := rep_run hb (q + r) σ1 f1 st lens.size hw1 hR1 h1
      (by rw [h2, hpd, ha]; push_cast; ring)
      (by rw [hk1 _ (by decide) (by unfold cFILL; omega) (by unfold cFILL; omega)]; exact hfl) (by omega)
    have eL : f1 cLAST = v := by rw [hk1 _ (by decide) (by unfold cLAST; omega) (by unfold cLAST; omega)]; exact hla
    have hF2 := hF1.keep hk2 (by omega) (fun c hc' => by unfold tbase LB0 at *; push_cast at hc'; omega)
    refine ⟨σ2, f2, (Reach.step hS).trans hR2, hw2, ⟨⟨hRe2, hm2, by rw [hfl2, pushN_size]; push_cast; ring⟩,
      hF2.pushN v (q + r) hv15 (by omega) (fun j hj => by rw [hc2 j hj, eL])⟩, hfu⟩

/-- A repeat code (16, 17, 18): LSYM's request, READ of the extra bits, then `rep_tail`. -/
theorem rep_req {b : Array Nat} {om : Nat} {lit : Bool} {p : Int} (hb : ∀ x ∈ b, x < 256) (bf : Int) (hl hd : Nat)
    (htot : hl + hd ≤ 316) (cl : Array Nat) (fuel : Nat)
    (ih : ∀ lens, Sim b om p (lensLoop (assign cl) (hl + hd) fuel lens) (LPre b om lit bf hl hd cl lens fuel)
      (LPost b om lit bf hl hd cl))
    (lens : Array Nat) (hlt : lens.size < hl + hd) (s K q v : Nat) (hs16 : 16 ≤ s) (hne : s = 16 → lens.size ≠ 0)
    (hK : (if s = 16 then (2 : Int) else if s = 17 then 3 else 7) = (K : Int) + 1)
    (hq : (if s = 18 ∨ 18 < s then (11 : Int) else 3) = q)
    (hv : (s = 16 → v = lens.getD (lens.size - 1) 0) ∧ (s ≠ 16 → v = 0)) :
    Sim b om p (bits (K + 1) >>= fun r => pure (pushN v (q + r) lens) >>= fun lens' => lnext (assign cl) (hl + hd) fuel lens')
      (fun f st => Rel b om lit f st ∧ f cMODE = mLSYM ∧ f (X0 b.size om + 4) = s ∧
        (f cFILL = lens.size ∧ LFrame b om bf hl hd cl lens f ∧ 8 * b.size - st.pos < fuel))
      (LPost b om lit bf hl hd cl) := by
  have hL : 2080 ≤ L0 b.size om := by unfold L0; omega
  intro σ0 f0 st0 hw0 hpre0
  have hv15 : v ≤ 15 := by
    obtain ⟨-, -, -, -, hF, -⟩ := hpre0
    by_cases h : s = 16
    · rw [hv.1 h]; exact hF.2.2.2.2.2.2.2.2 _ (by have := hne h; omega)
    · rw [hv.2 h]; omega
  let Q : (Int → Int) → St → Prop := fun f st => f cPEND = q ∧ f cLAST = v ∧ f cFILL = lens.size ∧
    LFrame b om bf hl hd cl lens f ∧ 8 * b.size - st.pos < fuel
  refine (Sim.step (pre := fun f st => Rel b om lit f st ∧ f cMODE = mLSYM ∧ f (X0 b.size om + 4) = s ∧
    (f cFILL = lens.size ∧ LFrame b om bf hl hd cl lens f ∧ 8 * b.size - st.pos < fuel))
    (pre' := fun f st => (Rel b om lit f st ∧ f cMODE = mREAD ∧ f cK = K + 1 ∧ f cACC = 0 ∧ f cWT = 1 ∧
    f cRET = mLREP) ∧ Q f st) ?_ (Sim.bind (bits_sim' hb K mLREP Q Q (fun f st f' st' hq' hk _ hlt' _ =>
      ⟨by rw [hk _ (by decide) (by unfold cPEND L0; omega) (by unfold rdSet cPEND; omega)]; exact hq'.1,
       by rw [hk _ (by decide) (by unfold cLAST L0; omega) (by unfold rdSet cLAST; omega)]; exact hq'.2.1,
       by rw [hk _ (by decide) (by unfold cFILL L0; omega) (by unfold rdSet cFILL; omega)]; exact hq'.2.2.1,
       hq'.2.2.2.1.keep hk (by omega) (fun c hc => by unfold rdSet at hc; unfold tbase LB0; omega),
       by have := hq'.2.2.2.2; omega⟩))
      (fun r => rep_tail hb bf hl hd htot cl fuel ih lens v q r hv15))) σ0 f0 st0 hw0 hpre0
  rintro σ f st hw ⟨hR, hm, hs, hfl, hF, hfu⟩
  obtain ⟨-, -, hreq⟩ := lsym_next hb hw hR hm s lens.size hs hfl (by omega)
  obtain ⟨σ1, f1, hS, hw1, hR1, h1, h2, h3, h4, hK1, hq1, hv1, hk1⟩ := hreq (by exact_mod_cast hs16) (fun h => hne (by exact_mod_cast h))
  have hF1 := hF.keep hk1 (by omega) (fun c hc => by unfold tbase LB0; omega)
  refine ⟨σ1, f1, hS, hw1, ⟨hR1, h1, by rw [hK1]; push_cast; exact hK, h2, h3, h4⟩, by rw [hq1]; push_cast; exact hq, ?_,
    by rw [hk1 _ (by decide) (by unfold cFILL; omega) (by unfold cFILL; omega)]; exact hfl, hF1, hfu⟩
  rw [hv1]
  by_cases h : s = 16
  · rw [if_pos h, hv.1 h, show (lens.size : Int) - 1 = ((lens.size - 1 : Nat) : Int) by have := hne h; omega]
    exact hF.2.2.2.2.2.2.2.1 _ (by have := hne h; omega)
  · rw [if_neg h, hv.2 h]; rfl

/-- **S6's `lensLoop` is simulated** (LENS … REP), from LENS with the lengths so far in the lengths area. -/
theorem lens_sim {b : Array Nat} {om : Nat} {lit : Bool} {p : Int} (hb : ∀ x ∈ b, x < 256) (bf : Int) (hl hd : Nat)
    (htot : hl + hd ≤ 316) (cl : Array Nat) :
    ∀ fuel (lens : Array Nat), Sim b om p (lensLoop (assign cl) (hl + hd) fuel lens)
      (LPre b om lit bf hl hd cl lens fuel) (LPost b om lit bf hl hd cl) := by
  have hL : 2080 ≤ L0 b.size om := by unfold L0; omega
  intro fuel
  induction fuel with
  | zero => intro lens; rintro σ f st hw ⟨_, h⟩; omega
  | succ fuel ih =>
    intro lens
    rw [lensLoop_succ]
    refine Sim.ite (fun hlt => ?_) (fun hge => Sim.pure (fun f st ⟨⟨hRm, hF⟩, _⟩ =>
      ⟨⟨hRm, hF⟩, by have := hF.2.2.2.2.2.2.1; omega⟩))
    refine Sim.step (pre' := fun f st => (DecReady b om lit f st 0 mLSYM ∧ TblRel b.size om f 0 cl) ∧
      (f cFILL = lens.size ∧ LFrame b om bf hl hd cl lens f ∧ 8 * b.size - st.pos < fuel + 1)) ?_ ?_
    · rintro σ f st hw ⟨⟨⟨hR, hm, hfl⟩, hF⟩, hfu⟩
      obtain ⟨σ1, f1, hS, hw1, hD, hk1⟩ := lens_req_next hb hw hR hm (by rw [hfl, hF.1, hF.2.1]; exact_mod_cast hlt)
      have hF1 := hF.keep hk1 (by omega) (fun c hc => by unfold decReqSet at hc; unfold tbase LB0 X0 at *; omega)
      exact ⟨σ1, f1, hS, hw1, ⟨hD, hF1.2.2.2.2.2.1⟩,
        by rw [hk1 _ (by decide) (by unfold cFILL; omega) (by unfold decReqSet cFILL X0; omega)]; exact hfl, hF1, hfu⟩
    refine Sim.bind (decode_Sim hb cl 0 mLSYM
      (fun f st => f cFILL = lens.size ∧ LFrame b om bf hl hd cl lens f ∧ 8 * b.size - st.pos < fuel + 1)
      (fun f st => f cFILL = lens.size ∧ LFrame b om bf hl hd cl lens f ∧ 8 * b.size - st.pos < fuel)
      (fun f st f' st' hq hk hlt' hin =>
        ⟨by rw [hk _ (by decide) (by unfold cFILL L0; omega) (by unfold decSet cFILL X0; omega)]; exact hq.1,
          hq.2.1.keep hk (by omega) (fun c hc => by unfold decSet at hc; unfold tbase LB0 X0 at *; omega),
          by have := hq.2.2; omega⟩)) (fun s => ?_)
    unfold lbody
    refine Sim.ite (fun h15 => ?_) (fun h15 => Sim.ite (fun h16 => ?_) (fun h16 => Sim.ite (fun h17 => ?_) (fun h17 => ?_)))
    · refine Sim.step (pre' := LPre b om lit bf hl hd cl (lens.push s) fuel) ?_ ?_
      · rintro σ f st hw ⟨hR, hm, hs, hfl, hF, hfu⟩
        obtain ⟨hl15, -, -⟩ := lsym_next hb hw hR hm s lens.size hs hfl (by omega)
        obtain ⟨σ1, f1, hS, hw1, hR1, h1, h2, h3, hk1⟩ := hl15 h15
        have hF1 := hF.keep hk1 (by omega) (fun c hc => by unfold tbase LB0 at *; omega)
        refine ⟨σ1, f1, hS, hw1, ⟨⟨hR1, h1, by rw [h2, Array.size_push]; push_cast; ring⟩, ?_⟩, hfu⟩
        exact hF1.pushN s 1 (by omega) (by omega) (fun j hj => by rw [show j = 0 by omega]; simpa using h3)
      refine Sim.bind (mid := fun lens' f st => lens' = lens.push s ∧ LPre b om lit bf hl hd cl (lens.push s) fuel f st)
        (Sim.pure fun f st h => ⟨rfl, h⟩) (fun lens' => ?_)
      unfold lnext
      refine Sim.ite (fun hc => Sim.reject_bind ?_) (fun hc => (ih lens').mono (fun f st ⟨e, h⟩ => e ▸ h) (fun _ _ _ h => h))
      rintro σ f st hw ⟨e, _⟩
      subst e
      simp at hc
      omega
    · refine Sim.ite (fun h0 => Sim.reject_bind ?_) (fun h0 => ?_)
      · rintro σ f st hw ⟨hR, hm, hs, hfl, hF, hfu⟩
        obtain ⟨-, hrej, -⟩ := lsym_next hb hw hR hm s lens.size hs hfl (by omega)
        obtain ⟨σ1, f1, hS, hw1, hm1⟩ := hrej h16 h0
        exact ⟨σ1, f1, Reach.step hS, hw1, hm1⟩
      · exact rep_req hb bf hl hd htot cl fuel ih lens hlt s 1 3 (lens.getD (lens.size - 1) 0) (by omega) (fun _ => h0)
          (by rw [if_pos h16]; norm_num) (by rw [if_neg (by omega)]; norm_num) ⟨fun _ => rfl, fun h => absurd h16 h⟩
    · exact rep_req hb bf hl hd htot cl fuel ih lens hlt s 2 3 0 (by omega) (fun h => absurd h h16)
        (by rw [if_neg h16, if_pos h17]; norm_num) (by rw [if_neg (by omega)]; norm_num) ⟨fun h => absurd h h16, fun _ => rfl⟩
    · exact rep_req hb bf hl hd htot cl fuel ih lens hlt s 6 11 0 (by omega) (fun h => absurd h h16)
        (by rw [if_neg h16, if_neg h17]; norm_num) (by rw [if_pos (by omega)]; norm_num) ⟨fun h => absurd h h16, fun _ => rfl⟩

/-- `fuelNow` binds the unread bits plus one, and touches nothing. -/
theorem Sim.fuel {b : Array Nat} {om : Nat} {p : Int} {α : Type} {k : Nat → M α} {pre : (Int → Int) → St → Prop}
    {post : α → (Int → Int) → St → Prop}
    (h : ∀ s : St, Sim b om p (k (8 * b.size - s.pos + 1)) (fun f st => pre f st ∧ st = s) post) :
    Sim b om p (fuelNow >>= k) pre post := by
  intro σ f st hw hp
  have := h st σ f st hw ⟨hp, rfl⟩
  refine ⟨fun a st' h' => this.1 a st' ?_, fun r h' => this.2 r ?_⟩ <;> rw [go_bind, go_fuelNow] at h' <;> exact h'

/-- **The CL build** (S6's `code cl .strict`, BUILD target 0), then BUILD's end: LENS with no lengths yet. -/
theorem cl_build_sim {b : Array Nat} {om : Nat} {lit : Bool} {p : Int} (hb : ∀ x ∈ b, x < 256) (bf : Int) (hl hd : Nat)
    (htot : hl + hd ≤ 316) (cl : Array Nat) :
    Sim b om p (code cl .strict) (ClStart b om lit bf hl hd cl)
      (fun C f st => C = assign cl ∧ (Rel b om lit f st ∧ f cMODE = mLENS ∧ f cFILL = (#[] : Array Nat).size) ∧
        LFrame b om bf hl hd cl #[] f) := by
  have hL : 2080 ≤ L0 b.size om := by unfold L0; omega
  intro σ f st hw h0
  obtain ⟨hR, hm, htg, h5, h6, h7, h8, hph, hj, hfl, hbf, hhl, hhd, hdy, hchk, hsz, h8b, hcl⟩ := h0
  have h15 : ∀ i, i < cl.size → cl.getD i 0 ≤ 15 := fun i _ => by have := h8b i; omega
  obtain ⟨hok, herr⟩ := code_Sim (lit := lit) hb cl .strict f st h15 σ f st hw
    ⟨rfl, rfl, hR, hm, hph, hj, by rw [h6, hsz]; rfl, fun i hi => by rw [h5]; exact hcl i (by omega), hchk,
      by rw [h8]; rfl⟩
  refine ⟨fun C st' h => ?_, herr⟩
  obtain ⟨σ1, f1, hR1, hw1, hC, rfl, hB⟩ := hok C st' h
  obtain ⟨hRb, hmb, hphb, hjb, hT, hk⟩ := hB
  rw [htg] at hT; rw [h7] at hk
  have kk : ∀ c : Int, 0 ≤ c → c < L0 b.size om → ¬ bset (tbase b.size om 0) c → f1 c = f c := hk
  have e6 : f1 (X0 b.size om + 6) = 19 := by
    rw [kk _ (by unfold X0; omega) (by unfold X0 L0; omega) (by unfold bset tbase LB0 X0; omega)]; exact h6
  have etg : f1 cTGT = 0 := by
    rw [kk _ (by decide) (by unfold cTGT; omega) (by unfold bset tbase LB0 cTGT; omega)]; exact htg
  obtain ⟨σ2, f2, hS, hw2, hR2, hL2, -, -⟩ := build_end_next hb hw1 hRb hmb hphb (by rw [hjb, e6, hsz]; rfl)
  obtain ⟨hm2, hk2⟩ := hL2 etg
  have kc : ∀ c : Int, 0 ≤ c → c < 2075 → c ≠ 0 → c ≠ 12 → c ≠ 13 → c ≠ 14 → f2 c = f c := fun c a0 a1 a2 a3 a4 a5 => by
    rw [hk2 c a0 (by omega) a2, kk c a0 (by omega) (by unfold bset tbase LB0; omega)]
  refine ⟨σ2, f2, hR1.trans (Reach.step hS), hw2, hC, ⟨hR2, hm2, ?_⟩, ?_, ?_, ?_, ?_, ?_,
    hT.keep (by norm_num) hk2 (fun c hc => by unfold tbase LB0; omega), by simp, fun i hi => by simp at hi,
    fun i hi => by simp at hi⟩
  · rw [kc _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hfl]; rfl
  · rw [kc _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hhl
  · rw [kc _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hhd
  · rw [kc _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hbf
  · rw [hk2 _ (by decide) (by unfold cDYN; omega) (by unfold cDYN; omega),
      kk _ (by decide) (by unfold cDYN; omega) (by unfold bset tbase LB0 cDYN; omega)]; exact hdy
  · rw [hk2 _ (by decide) (by unfold cCHK; omega) (by unfold cCHK; omega),
      kk _ (by decide) (by unfold cCHK; omega) (by unfold bset tbase LB0 cCHK; omega)]; exact hchk

end VIRDeflate.Step
