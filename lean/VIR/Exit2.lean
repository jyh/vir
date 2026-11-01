/-
  STATUS-vir row 17: the MEANING OF F2 (program 2, the dynamic payload) as a closed-form exit relation, for paris's
  lowering spike. It is the program-2 twin of Exit.lean's F_exit, stated on L-DEEP program 2's denotation (Deep2.lean).
-/
import VIR.Deep2

namespace VIR.Deep2

open VIR.Deep (Val DOut)

variable (acl : Principal → TopicId → Bool)

/-- F2's FOUR outcomes:
    TRUNCATED iff len < 24;
    UNAUTHORIZED_OR_RATE_LIMITED iff magic ≠ MAGIC, or the ACL bit is clear, or the sender has no token;
    BAD_PAYLOAD iff (the header is accepted and) off < 24 or off + n > len, where off = u32 at 12 and n = u32 at 16;
    otherwise OK, with the bucket decremented for the sender and the payload = b0 advanced by off, taken to n bytes. -/
theorem F2_exit (b0 st : Val) :
    den acl (F2 b0 st) =
      if 24 ≤ b0.len then
        if (b0.rd 0).toP = MAGIC ∧ acl (b0.rd 4).toP (b0.rd 8).toP = true ∧ 0 < st.st (b0.rd 4).toP then
          if 24 ≤ (b0.rd 12).toN ∧ (b0.rd 12).toN + (b0.rd 16).toN ≤ b0.len then
            .ret (.state (decTokens st.st (b0.rd 4).toP)) ((b0.adv (b0.rd 12).toN).take (b0.rd 16).toN)
          else .drop .badPayload
        else .drop .unauthOrRate
      else .drop .truncated := by
  simp only [F2, den, Cond.eval, Ix.eval, eU, eP]
  by_cases h : 24 ≤ b0.len <;> simp [h]

/-- The same relation for the UNFUSED term U2, by the deep chain: B.1's composition has F2's exits. -/
theorem U2_exit (b0 st : Val) :
    den acl (U2 b0 st) =
      if 24 ≤ b0.len then
        if (b0.rd 0).toP = MAGIC ∧ acl (b0.rd 4).toP (b0.rd 8).toP = true ∧ 0 < st.st (b0.rd 4).toP then
          if 24 ≤ (b0.rd 12).toN ∧ (b0.rd 12).toN + (b0.rd 16).toN ≤ b0.len then
            .ret (.state (decTokens st.st (b0.rd 4).toP)) ((b0.adv (b0.rd 12).toN).take (b0.rd 16).toN)
          else .drop .badPayload
        else .drop .unauthOrRate
      else .drop .truncated :=
  (router2_fusion_deep acl b0 st).trans (F2_exit acl b0 st)

end VIR.Deep2
