import VIRDeflate.Spec
namespace VIRDeflate

set_option pp.proofs false in
#print dynamic

theorem getD_set! (cl : Array Nat) (o x j : Nat) (ho : o < cl.size) :
    (cl.set! o x).getD j 0 = if j = o then x else cl.getD j 0 := by
  simp only [Array.getD_eq_getD_getElem?, Array.set!, Array.getElem?_setIfInBounds]
  split_ifs <;> simp_all

theorem size_set! (cl : Array Nat) (o x : Nat) : (cl.set! o x).size = cl.size := by simp [Array.set!]

theorem pushN_size (x : Nat) : ∀ k (a : Array Nat), (pushN x k a).size = a.size + k
  | 0, a => rfl
  | k + 1, a => by rw [pushN, pushN_size x k]; simp; omega

theorem pushN_getD (x : Nat) : ∀ k (a : Array Nat) (j : Nat), (pushN x k a).getD j 0 =
    if j < a.size then a.getD j 0 else if j < a.size + k then x else 0
  | 0, a, j => by simp [pushN, Array.getD_eq_getD_getElem?]; intro h; rw [Array.getElem?_eq_none (by omega)]; rfl
  | k + 1, a, j => by
    rw [pushN, pushN_getD x k]
    simp only [Array.size_push, Array.getD_eq_getD_getElem?, Array.getElem?_push]
    split_ifs <;> first | omega | simp_all | skip

theorem push_getD (a : Array Nat) (x j : Nat) : (a.push x).getD j 0 = if j < a.size then a.getD j 0 else if j = a.size then x else 0 := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_push]
  split_ifs <;> first | omega | simp_all | skip

theorem extract_getD (a : Array Nat) (s e j : Nat) (he : e ≤ a.size) (hj : j < e - s) :
    (a.extract s e).getD j 0 = a.getD (s + j) 0 := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_extract]
  split_ifs <;> first | omega | simp_all | skip

theorem extract_size (a : Array Nat) (s e : Nat) : (a.extract s e).size = min e a.size - s := by simp

theorem order_inj : ∀ k k' : Fin 19, ORDER.getD k 0 = ORDER.getD k' 0 → k = k' := by decide
theorem order_surj : ∀ j : Fin 19, ∃ k : Fin 19, ORDER.getD k 0 = j := by decide
theorem order_lt : ∀ k : Fin 19, ORDER.getD k 0 < 19 := by decide
theorem order_drop (i : Nat) (h : i < 19) : ORDER.drop i = ORDER.getD i 0 :: ORDER.drop (i + 1) := by
  interval_cases i <;> rfl
theorem order_drop19 : ORDER.drop 19 = [] := rfl
