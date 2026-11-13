import VIRDeflate.Spec
namespace VIRDeflate

theorem getD_oob (a : Array Nat) (j : Nat) (h : a.size ≤ j) : a.getD j 0 = 0 := by
  unfold Array.getD; rw [dif_neg (by omega)]

theorem getD_set! (cl : Array Nat) (o x j : Nat) (ho : o < cl.size) :
    (cl.set! o x).getD j 0 = if j = o then x else cl.getD j 0 := by
  have hs : (cl.set! o x).size = cl.size := Array.size_setIfInBounds
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, show cl.set! o x = cl.setIfInBounds o x from rfl,
    Array.getElem?_setIfInBounds]
  by_cases h : j = o
  · subst h; simp [ho]
  · simp [Ne.symm h, h]

theorem pushN_getD (x : Nat) : ∀ k (a : Array Nat) (j : Nat), (pushN x k a).getD j 0 =
    if j < a.size then a.getD j 0 else if j < a.size + k then x else 0
  | 0, a, j => by
    simp only [pushN, Nat.add_zero]; split_ifs <;> first | rfl | omega | exact getD_oob a j (by omega)
  | k + 1, a, j => by
    rw [pushN, pushN_getD x k]
    simp only [Array.size_push, Array.getD_eq_getD_getElem?, Array.getElem?_push]
    split_ifs <;> first | omega | simp_all | skip

def dyn3 (lens : Array Nat) (hlit hdist : Nat) : M Unit :=
  code (lens.extract 0 hlit) >>= fun L => code (lens.extract hlit (hlit + hdist)) .dist >>= fun D => huff L D

def dyn2 (hlit hdist hclen : Nat) : M Unit :=
  readCL ORDER hclen (Array.replicate 19 0) >>= fun cl => code cl .strict >>= fun CL => fuelNow >>= fun fu =>
    lensLoop CL (hlit + hdist) fu #[] >>= fun lens =>
      if lens.getD 256 0 = 0 then (reject "missing end-of-block" : M Unit) >>= fun _ => dyn3 lens hlit hdist else dyn3 lens hlit hdist

theorem dynamic_eq : dynamic = (bits 5 >>= fun a1 => bits 5 >>= fun a2 => bits 4 >>= fun a3 =>
    if a1 + 257 > 286 ∨ a2 + 1 > 30 then (reject "too many length or distance symbols" : M Unit) >>= fun _ => dyn2 (a1 + 257) (a2 + 1) (a3 + 4)
    else dyn2 (a1 + 257) (a2 + 1) (a3 + 4)) := rfl
