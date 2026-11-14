/-
  O95 compiler S3 (compiler/DECLARATIONS-S3.md, Addendum 13): where `lower3` puts each piece. Sizes do not depend on targets
  (erasure, `gen_er`), so `ctxOf`'s first-pass contexts measure what the final context generates; then the entry stub, the
  exits, main and every table body are found at the addresses `ctxOf` assigns.
-/
import S3.Top3

namespace S3
open VIRC X86

/-! ## Erasure: every jump target to 0 -/

def AI.er : AI → AI
  | .op o => .op o
  | .jccA c _ => .jccA c 0
  | .jmpA _ => .jmpA 0
  | .callA _ => .callA 0

@[simp] theorem er_op (o : Op) : AI.er (.op o) = .op o := rfl
@[simp] theorem er_jcc (c : Cc) (a : W) : AI.er (.jccA c a) = .jccA c 0 := rfl
@[simp] theorem er_jmp (a : W) : AI.er (.jmpA a) = .jmpA 0 := rfl
@[simp] theorem er_call (a : W) : AI.er (.callA a) = .callA 0 := rfl

theorem bytes_er (C : Ctx3) (l : List AI) : bytes C (l.map AI.er) = bytes C l := by
  induction l with
  | nil => rfl
  | cons i l ih => rw [List.map_cons, bytes_cons, bytes_cons, ih]; cases i <;> rfl

theorem bytes_ilen {C C' : Ctx3} (h : C.ilen = C'.ilen) (l : List AI) : bytes C l = bytes C' l := by
  induction l with
  | nil => rfl
  | cons i l ih => rw [bytes_cons, bytes_cons, ih]; cases i <;> simp [AI.size, blen, h]

section
variable {C C' : Ctx3}

theorem evalTo_er (hv : True) : ∀ (t : Nat) (o : WOpd), (evalTo C t o).map AI.er = (evalTo C' t o).map AI.er
  | _, .slice _ _ => by simp only [evalTo]
  | _, .imm _ => by simp only [evalTo]
  | t, .arith op a b => by
      simp only [evalTo, List.map_append, evalTo_er hv t a, evalTo_er hv (t + 1) b]
      cases op <;> simp [arithCode, ld, st, movi]
  | t, .bnot a => by simp only [evalTo, List.map_append, evalTo_er hv t a]
  | t, .cat a b => by simp only [evalTo, List.map_append, evalTo_er hv t a, evalTo_er hv (t + wid a) b]
  | t, .take _ a => by simp only [evalTo, evalTo_er hv t a]
  | t, .drop _ a => by simp only [evalTo, List.map_append, evalTo_er hv t a]
  | t, .tag _ _ a => by simp only [evalTo, List.map_append, evalTo_er hv (t + 1) a]

theorem envRoom_er (n : Nat) : (envRoom C n).map AI.er = (envRoom C' n).map AI.er := by simp [envRoom, ld]
theorem stackRoom_er : (stackRoom C).map AI.er = (stackRoom C').map AI.er := by simp [stackRoom, ld]
theorem prependLoop_er (pc pc' : W) : (prependLoop C pc).map AI.er = (prependLoop C' pc').map AI.er := by
  simp [prependLoop, ld, movi]
theorem prependBuf_er (s n : Nat) : (prependBuf C s n).map AI.er = (prependBuf C' s n).map AI.er := by
  simp only [prependBuf, List.map_append, envRoom_er (C := C) (C' := C')]

theorem dispatch_er (hf : C.fix = C'.fix) (wx : Nat) :
    ∀ (fuel i : Nat) (pc pc' : W), (dispatch C wx pc fuel i).map AI.er = (dispatch C' wx pc' fuel i).map AI.er
  | 0, _, _, _ => by simp [dispatch]
  | fuel + 1, i, pc, pc' => by
      simp only [dispatch, List.map_append]
      congr 1
      · simp [dispatchEntry, envRoom, ld, st, hf]
      · exact dispatch_er hf wx fuel (i + 1) _ _

theorem gen_er (hf : C.fix = C'.fix) (ht : C.tblLen = C'.tblLen) :
    ∀ (c : WCode) (pc pc' : W), (gen C pc c).map AI.er = (gen C' pc' c).map AI.er
  | .ret o, pc, pc' => by
      simp only [gen, List.map_append, List.append_assoc]
      repeat' (first | (refine congrArg₂ (· ++ ·) ?_ ?_) | exact gen_er hf ht _ _ _ | exact evalTo_er trivial _ _ |
        exact prependLoop_er _ _ | exact prependBuf_er _ _ | (rw [ht]; exact dispatch_er hf _ _ _ _ _) |
        (simp [stackRoom, envRoom, ld, st, movi]; done))
  | .letE c₁ c₂, pc, pc' => by
      simp only [gen, List.map_append, List.append_assoc]
      repeat' (first | (refine congrArg₂ (· ++ ·) ?_ ?_) | exact gen_er hf ht _ _ _ | exact evalTo_er trivial _ _ |
        exact prependLoop_er _ _ | exact prependBuf_er _ _ | (rw [ht]; exact dispatch_er hf _ _ _ _ _) |
        (simp [stackRoom, envRoom, ld, st, movi]; done))
  | .load off idx k, pc, pc' => by
      simp only [gen, List.map_append, List.append_assoc]
      repeat' (first | (refine congrArg₂ (· ++ ·) ?_ ?_) | exact gen_er hf ht _ _ _ | exact evalTo_er trivial _ _ |
        exact prependLoop_er _ _ | exact prependBuf_er _ _ | (rw [ht]; exact dispatch_er hf _ _ _ _ _) |
        (simp [stackRoom, envRoom, ld, st, movi]; done))
  | .store off idx v k, pc, pc' => by
      simp only [gen, List.map_append, List.append_assoc]
      repeat' (first | (refine congrArg₂ (· ++ ·) ?_ ?_) | exact gen_er hf ht _ _ _ | exact evalTo_er trivial _ _ |
        exact prependLoop_er _ _ | exact prependBuf_er _ _ | (rw [ht]; exact dispatch_er hf _ _ _ _ _) |
        (simp [stackRoom, envRoom, ld, st, movi]; done))
  | .app f x, pc, pc' => by
      simp only [gen, List.map_append, List.append_assoc]
      repeat' (first | (refine congrArg₂ (· ++ ·) ?_ ?_) | exact gen_er hf ht _ _ _ | exact evalTo_er trivial _ _ |
        exact prependLoop_er _ _ | exact prependBuf_er _ _ | (rw [ht]; exact dispatch_er hf _ _ _ _ _) |
        (simp [stackRoom, envRoom, ld, st, movi]; done))
  | .ite o c₁ c₂, pc, pc' => by
      simp only [gen, List.map_append, List.append_assoc]
      repeat' (first | (refine congrArg₂ (· ++ ·) ?_ ?_) | exact gen_er hf ht _ _ _ | exact evalTo_er trivial _ _ |
        exact prependLoop_er _ _ | exact prependBuf_er _ _ | (rw [ht]; exact dispatch_er hf _ _ _ _ _) |
        (simp [stackRoom, envRoom, ld, st, movi]; done))
  | .case o n₁ n₂ c₁ c₂, pc, pc' => by
      simp only [gen, List.map_append, List.append_assoc]
      repeat' (first | (refine congrArg₂ (· ++ ·) ?_ ?_) | exact gen_er hf ht _ _ _ | exact evalTo_er trivial _ _ |
        exact prependLoop_er _ _ | exact prependBuf_er _ _ | (rw [ht]; exact dispatch_er hf _ _ _ _ _) |
        (simp [stackRoom, envRoom, ld, st, movi]; done))

/-- **gsz_congr.** Code size depends on the context only through `ilen`, the fix flags and the table length. -/
theorem gsz_congr (hi : C.ilen = C'.ilen) (hf : C.fix = C'.fix) (ht : C.tblLen = C'.tblLen) (c : WCode) : gsz C c = gsz C' c := by
  rw [← bytes_gen C c 0, ← bytes_gen C' c 0, ← bytes_er C, gen_er hf ht c 0 0, bytes_er, bytes_ilen hi]
end

/-! ## The table's bodies -/

def addrs (C : Ctx3) : W → Table → List W
  | _, [] => []
  | a, e :: t => a :: addrs C (a + BitVec.ofNat 64 (bytes C (gen C a e.2))) t

theorem foldl_addrs (C : Ctx3) : ∀ (t : Table) (acc : List W) (a : W),
    (t.foldl (fun (acc : List W × W) (e : Bool × WCode) => (acc.1 ++ [acc.2], acc.2 + BitVec.ofNat 64 (bytes C (gen C acc.2 e.2))))
      (acc, a)).1 = acc ++ addrs C a t
  | [], acc, a => by simp [addrs]
  | e :: t, acc, a => by simp only [List.foldl_cons]; rw [foldl_addrs C t]; simp [addrs]

theorem bodyAddrs_eq (C : Ctx3) (t : Table) (a : W) : bodyAddrs C t a = addrs C a t := by
  simp only [bodyAddrs]; rw [foldl_addrs]; simp

/-- **place_bodies.** Bodies laid out back to back from `a`, with `C.body (k + j)` the j-th address measured in C1 (sizes equal to
    C's): body j is at its address. -/
theorem place_bodies {C C1 : Ctx3} {p : Program} (hsz : ∀ c a, bytes C1 (gen C1 a c) = bytes C (gen C a c)) :
    ∀ (t : Table) (k : Nat) (a : W), (∀ j, j < t.length → C.body (k + j) = (addrs C1 a t).getD j 0) →
      CodeAt C p a ((t.zipIdx k).flatMap fun q => gen C (C.body q.2) q.1.2) →
      ∀ j (h : j < t.length), CodeAt C p (C.body (k + j)) (gen C (C.body (k + j)) t[j].2)
  | [], _, _, _, _, j, h => absurd h (Nat.not_lt_zero j)
  | e :: t, k, a, hb, hc, j, h => by
    simp only [List.zipIdx_cons, List.flatMap_cons] at hc
    have hk : C.body k = a := by have := hb 0 (by simp); simpa [addrs] using this
    rw [hk] at hc
    cases j with
    | zero => simp only [Nat.add_zero, List.getElem_cons_zero, hk]; exact codeAt_left hc
    | succ j =>
      have hc' := codeAt_right hc
      rw [← hsz e.2 a] at hc'
      have := place_bodies hsz t (k + 1) _ (fun j hj => by
        have := hb (j + 1) (by simp; omega); rw [show k + (j + 1) = k + 1 + j by omega] at this
        simpa [addrs] using this) hc' j (by simp at h; omega)
      rw [show k + (j + 1) = k + 1 + j by omega]; simpa using this

/-- **lower3_placed.** In `lower3`, with every instruction at least one byte and the whole code under 2⁶⁴ bytes: the entry stub
    is at `base`, FAULT/OVF/RES at `C.fault`/`C.ovf`/`C.res`, main at `mainAddr C`, and table body i at `C.body i` with
    `C.fix i` its flag (TblOk's body clause). -/
theorem lower3_placed {ilen : Op → Nat} {tbl : Table} {main : WCode} {base : W} {C : Ctx3} {p : Program}
    (hCdef : C = ctxOf ilen tbl main base) (hp : p = lower3 ilen tbl main base) (hC : ∀ o, 1 ≤ ilen o)
    (hb : bytes C (allCode C tbl main) < 2 ^ 64) :
    CodeAt C p base (entryStub (mainAddr C)) ∧ CodeAt C p C.fault (exitCode stFault) ∧ CodeAt C p C.ovf (exitCode stOvf) ∧
      CodeAt C p C.res (exitCode stRes) ∧ CodeAt C p (mainAddr C) (gen C (mainAddr C) main) ∧
      (∀ i fx b, tbl[i]? = some (fx, b) → C.fix i = fx ∧ CodeAt C p (C.body i) (gen C (C.body i) b)) := by
  subst hp
  have hall : CodeAt C (lower3 ilen tbl main base) base (allCode C tbl main) := by
    subst hCdef; exact codeAt_asm (C := ctxOf ilen tbl main base) hC base _ hb
  have h1 : CodeAt C (lower3 ilen tbl main base) base (entryStub (mainAddr C) ++ (exitCode stFault ++ (exitCode stOvf ++
      (exitCode stRes ++ (gen C (mainAddr C) main ++ tbl.zipIdx.flatMap fun q => gen C (C.body q.2) q.1.2))))) := by
    simpa only [allCode, List.append_assoc] using hall
  have eF : base + BitVec.ofNat 64 (bytes C (entryStub (mainAddr C))) = C.fault := by
    subst hCdef; simp [ctxOf, entryStub, bytes_cons, bytes_nil, AI.size, st, movi]
  have eO : C.fault + BitVec.ofNat 64 (bytes C (exitCode stFault)) = C.ovf := by
    subst hCdef; simp [ctxOf, exitCode, bytes_cons, bytes_nil, AI.size, st, ld, movi]
  have eR : C.ovf + BitVec.ofNat 64 (bytes C (exitCode stOvf)) = C.res := by
    subst hCdef; simp [ctxOf, exitCode, bytes_cons, bytes_nil, AI.size, st, ld, movi]
  have c1 := codeAt_right h1; rw [eF] at c1
  have c2 := codeAt_right c1; rw [eO] at c2
  have c3 := codeAt_right c2; rw [eR] at c3
  have c4 := codeAt_right c3
  rw [show C.res + BitVec.ofNat 64 (bytes C (exitCode stRes)) = mainAddr C from rfl] at c4
  have c5 := codeAt_right c4
  refine ⟨codeAt_left h1, codeAt_left c1, codeAt_left c2, codeAt_left c3, codeAt_left c4, ?_⟩
  -- the table: ctxOf's first-pass context C1 measures what C generates
  obtain ⟨C1, pB, hbody, hi1, hf1, ht1, hpB⟩ : ∃ C1 pB, (∀ i, C.body i = (bodyAddrs C1 tbl pB).getD i 0) ∧ C1.ilen = C.ilen ∧
      C1.fix = C.fix ∧ C1.tblLen = C.tblLen ∧ pB = mainAddr C + BitVec.ofNat 64 (bytes C (gen C (mainAddr C) main)) := by
    subst hCdef
    refine ⟨_, _, fun i => rfl, rfl, rfl, rfl, ?_⟩
    rw [bytes_gen, bytes_gen]
    congr 2
    apply gsz_congr <;> rfl
  have hsz : ∀ c a, bytes C1 (gen C1 a c) = bytes C (gen C a c) := fun c a => by
    rw [bytes_gen, bytes_gen]; exact gsz_congr hi1 hf1 ht1 c
  rw [← hpB] at c5
  intro i fx b hib
  have hlt : i < tbl.length := (List.getElem?_eq_some_iff.mp hib).1
  have hget : tbl[i] = (fx, b) := (List.getElem?_eq_some_iff.mp hib).2
  have hpl := place_bodies (p := lower3 ilen tbl main base) hsz tbl 0 pB
    (fun j _ => by rw [Nat.zero_add, hbody, bodyAddrs_eq]) c5 i hlt
  rw [Nat.zero_add, hget] at hpl
  refine ⟨?_, hpl⟩
  subst hCdef; simp [ctxOf, hib]

end S3
