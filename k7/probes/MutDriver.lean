import K7
open VIRL1 VIRL2 VIRC K7
-- mutant: the end-state clause at the INITIAL memory m instead of the final m' must be refused (one error expected, line 12)
theorem mut_mem {lay σ m} (e : Tm₂) (hty : HasType₂ [tcap] [true] e tcap) (hw : Tm.wfB [tcap].length e = true)
    (hf : Tm.fnOk e = true) (hok : Tm.ok2 e = true) (hT : (lower2T [tcap] e []).2.length < 2 ^ 64) (p : Int) (ρw : List W)
    (he : EnvRel (lower2T [tcap] e []).2 lay σ [tcap] ([(Atom.const (.cap p) : Atom₂)].map valOf) ρw)
    (hl : Layout σ lay) (hm : MemRel lay σ m) (a : Atom₂) (σ' : Store) (w : Atom₂)
    (hs : Steps₂ (instL 0 [(Atom.const (.cap p) : Atom₂)] e, σ) (.ret a, σ')) (hw' : Atom.eval a = some w) :
    MemRel lay σ' m ∨ True := by
  rcases compile_refines_mem [tcap] [true] e tcap [.const (.cap p)] ρw hty hw hf hok rfl (good_cap1 p) hT he hl hm a σ' w hs hw' with ⟨k, ws, m', -, -, -, hm'⟩ | -
  · exact .inl hm'
  · exact .inr trivial
