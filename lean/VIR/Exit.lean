/-
  STATUS-vir row 11: the MEANING OF F as a closed-form exit relation (the four outcomes),
  for paris's step 3 (the A.4 refinement against F under I6). Stated on L-DEEP's denotation.
-/
import VIR.Deep

namespace VIR.Deep

variable (acl : Principal → TopicId → Bool)

/-- F's four outcomes. TRUNCATED iff len < 24; UNAUTHORIZED_OR_RATE_LIMITED iff magic ≠ MAGIC, or the
    ACL bit is clear, or the sender has no token; otherwise OK with the bucket decremented for the
    sender and the payload slice = b0 advanced by 24 (pointer b0+24, length len−24). -/
theorem F_exit (b0 st : Val) :
    den acl (F b0 st) =
      if 24 ≤ b0.len then
        if (b0.rd 0).toP = MAGIC ∧ acl (b0.rd 4).toP (b0.rd 8).toP = true ∧ 0 < st.st (b0.rd 4).toP then
          .ret (.state (decTokens st.st (b0.rd 4).toP)) (b0.adv 24)
        else .drop .unauthOrRate
      else .drop .truncated := by
  simp only [F, den, Cond.eval, eU]
  by_cases h : 24 ≤ b0.len <;> simp [h]

/-- The same relation for the UNFUSED term, by the deep chain: the spec composition has F's exits. -/
theorem U_exit (b0 st : Val) :
    den acl (U b0 st) =
      if 24 ≤ b0.len then
        if (b0.rd 0).toP = MAGIC ∧ acl (b0.rd 4).toP (b0.rd 8).toP = true ∧ 0 < st.st (b0.rd 4).toP then
          .ret (.state (decTokens st.st (b0.rd 4).toP)) (b0.adv 24)
        else .drop .unauthOrRate
      else .drop .truncated :=
  (router_fusion_deep acl b0 st).trans (F_exit acl b0 st)

end VIR.Deep
