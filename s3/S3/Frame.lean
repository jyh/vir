/-
  O95 compiler S3 (compiler/DECLARATIONS-S3.md, S3-F): frame bounds. S2's environment ρ grows at the FRONT (a `ret` into a
  continuation prepends its words, a load prepends one word, a store prepends the capability's two), so a `slice off len` names
  words counted from the newest one. A frame with static slot addresses needs ρ's length to be static at every program point, and
  its first fact is that an operand's WIDTH is static: `wid o`, with `evalW_length` saying an operand that evaluates yields
  exactly `wid o` words.
-/
import VIRC.Word

namespace S3
open VIRC

/-- An operand's static width, in words. -/
def wid : WOpd → Nat
  | .slice _ len => len
  | .imm ws => ws.length
  | .arith _ _ _ => 1
  | .bnot _ => 1
  | .cat a b => wid a + wid b
  | .take n a => min n (wid a)
  | .drop n a => wid a - n
  | .tag _ pad a => 1 + wid a + pad

theorem chk_length {n : Int} {ws : List W} (h : chk n = .ok ws) : ws.length = 1 := by
  unfold chk at h; split at h <;> cases h; rfl

theorem apply_length {op : AOp} {x y : W} {ws : List W} (h : op.apply x y = .ok ws) : ws.length = 1 := by
  cases op <;> simp only [AOp.apply] at h <;> first | exact chk_length h | (cases h; rfl)

/-- **evalW_length.** An operand that evaluates yields exactly `wid o` words, whatever ρ is. -/
theorem evalW_length : ∀ (o : WOpd) (ρ : List W) (ws : List W), evalW ρ o = .ok ws → ws.length = wid o
  | .slice off len, ρ, ws, h => by
      simp only [evalW] at h; split at h
      · cases h; simp only [wid, List.length_take, List.length_drop]; omega
      · cases h
  | .imm vs, ρ, ws, h => by simp only [evalW] at h; cases h; rfl
  | .arith op a b, ρ, ws, h => by
      simp only [evalW] at h
      cases ha : evalW ρ a with
      | ovf => simp [ha, WRes.bind] at h
      | bad => simp [ha, WRes.bind] at h
      | ok xs =>
        cases hb : evalW ρ b with
        | ovf => simp [ha, hb, WRes.bind] at h
        | bad => simp [ha, hb, WRes.bind] at h
        | ok ys =>
          simp only [ha, hb, WRes.bind] at h
          match xs, ys, h with
          | [x], [y], h => exact apply_length h
  | .bnot a, ρ, ws, h => by
      simp only [evalW] at h
      cases ha : evalW ρ a with
      | ovf => simp [ha, WRes.bind] at h
      | bad => simp [ha, WRes.bind] at h
      | ok xs =>
        simp only [ha, WRes.bind] at h
        match xs, h with
        | [x], h => cases h; rfl
  | .cat a b, ρ, ws, h => by
      simp only [evalW] at h
      cases ha : evalW ρ a with
      | ovf => simp [ha, WRes.bind] at h
      | bad => simp [ha, WRes.bind] at h
      | ok xs =>
        cases hb : evalW ρ b with
        | ovf => simp [ha, hb, WRes.bind] at h
        | bad => simp [ha, hb, WRes.bind] at h
        | ok ys =>
          simp only [ha, hb, WRes.bind] at h; cases h
          simp only [List.length_append, wid, evalW_length a ρ xs ha, evalW_length b ρ ys hb]
  | .take n a, ρ, ws, h => by
      simp only [evalW] at h
      cases ha : evalW ρ a with
      | ovf => simp [ha, WRes.bind] at h
      | bad => simp [ha, WRes.bind] at h
      | ok xs =>
        simp only [ha, WRes.bind] at h; cases h
        simp only [List.length_take, wid, evalW_length a ρ xs ha]
  | .drop n a, ρ, ws, h => by
      simp only [evalW] at h
      cases ha : evalW ρ a with
      | ovf => simp [ha, WRes.bind] at h
      | bad => simp [ha, WRes.bind] at h
      | ok xs =>
        simp only [ha, WRes.bind] at h; cases h
        simp only [List.length_drop, wid, evalW_length a ρ xs ha]
  | .tag t pad a, ρ, ws, h => by
      simp only [evalW] at h
      cases ha : evalW ρ a with
      | ovf => simp [ha, WRes.bind] at h
      | bad => simp [ha, WRes.bind] at h
      | ok xs =>
        simp only [ha, WRes.bind] at h; cases h
        simp only [List.length_cons, List.length_append, List.length_replicate, wid, evalW_length a ρ xs ha]; omega

end S3
