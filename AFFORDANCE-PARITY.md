# Affordance parity: did both arms start from the SAME goal? (STATUS-vir row 21, 2026-11-01, the 2nd vir head)

The design requires that both arms receive the same affordances, or the comparison is not fair. This file puts the goal each arm actually proved side by side. The goals are read from the artifacts, never from either arm's description:
- **Lean:** the elaborated statement in `lean/out/terms.txt` (audit-010).
- **MetaPRL:** the goal mpdrive displays at the chain's first `refine` (mojave vir-arm-tools adef670: `runs-c2-router.txt` and `runs-c2-router2.txt`, step 2).

| program | Lean | MetaPRL |
|---|---|---|
| 1 (I4) | `∀ acl {n} (b0 : Slice n) (st : State), U acl b0 st = F acl b0 st` | `<Γ> ⊢ vir_U{b0; st} ≡ vir_F{b0; st}`, with hyps `b0 ∈ (Top ╳ int)` · `∀x k. wire_u32{x;k} ∈ int` · `∀x y. can_access{x;y} ∈ Bool` · `∀x. has_tokens{st;x} ∈ Bool` |
| 2 (J5) | `∀ acl {n} (b0 : Slice n) (st : State), U2 acl b0 st = F2 acl b0 st` | `<Γ> ⊢ vir_U2{b0; st} ≡ vir_F2{b0; st}`, with the same hyps except `b0 ∈ (List ╳ int)` |

## Verdict: SAME GOAL, the unfused term equal to the fused one, with SIX named differences
- **D1 · the token predicates are INTERPRETED in Lean and UNINTERPRETED in MetaPRL.** Lean defines `hasTokens st p := 0 < st p` and `decTokens` (Core.lean). MetaPRL gives `has_tokens` only a typing hypothesis. ⇒ MetaPRL's theorem is MORE GENERAL. Neither Lean scored chain unfolds `hasTokens` or `decTokens` by name: they appear only as arguments to `aux_guard_swap`/`guard_merge` and inside `Out.ret`. ⚠️ **Limit:** a grep cannot exclude a DEFINITIONAL use inside `rw`/`simp only`. ~~The test that would settle it … has NOT been run.~~ **RUN (row 22):** in a scratch copy, Core.lean ends with `attribute [irreducible] hasTokens decTokens canAccess Slice.rd`, and Core · Rules · Router · Router2 build GREEN (`lean/logs/build-ctl-d1.log`, `saltbuild EXIT=0`). The positive control, `hasTokens st p = (0 < st p) := rfl` added under the same attribute, is RED (`build-ctl-d1-pos.log`, EXIT=1), so the attribute does block definitional use. ⇒ **Neither scored Lean chain uses the four definitions, by name or definitionally (at the elaborator's default transparency).** D1 and D3 are closed.
- **D2 · the ACL is a parameter in Lean** (`acl : Principal → TopicId → Bool`) **and an uninterpreted constant in MetaPRL** (`can_access`, typed Bool). The two are equally general.
- **D3 · the wire read is a total DEFINED function in Lean** (`Slice.rd`, via `ByteArray.get!`) **and an uninterpreted constant in MetaPRL** (`wire_u32`, typed int). Neither chain unfolds it by name, and D1's limit applies here too.
- **D4 · the buffer's representation differs by design:** Lean's is length-INDEXED (`Slice n`, so the length guard is on a type index; PREDICTIONS L-IDX), and MetaPRL's is a pair (model B). This difference is the comparison's own subject, not an unfairness.
- **D5 · MetaPRL's b0 type changes between its own programs:** `Top ╳ int` in program 1 and `List ╳ int` in program 2. It is within one arm and is reported for mojave. It is not a parity defect between the arms, and vir has not measured whether it changes any count.
- **D6 · equality:** Lean proves `=` on `Out`, and MetaPRL proves `≡`. Each is its logic's native equality of terms.
⇒ **No difference gives either arm a step the other lacks on the scored chain** (D1's limit is closed by row 22). The one place where generality differs, the token predicates (D1), points AGAINST MetaPRL: its statement is the stronger one.
