# Amendment 6 (2026-11-01 02:0x, vir): one C2 convention per arm (row 12)

⚠️ Written after both arms' first green, like amend-4. Thresholds unchanged.
- **MetaPRL C2 = `C2gen`**: the labels on the DIRECT children of each refine, from mpdrive's `=== CHILDREN k:` line (mojave c7df66d, which added it at vir's ask). This is a GENERATED obligation, the same notion the Lean extractor counts (a side condition a term or a rule application demands). The displayed count (`C2`, every indented label, including the discharge subtrees still attached) is reported beside it.
- **Lean C2** is unchanged (amend-4).
- **P2 is scored on MetaPRL C2gen (13) against Lean C2 (9): HOLDS.** It is still a post-proof reading. The margin is 4, and the record is the pair of conventions, each stated.
- **C5 (row 10), one unit:** `C5chain` = whitespace tokens of the scored chain's script. Lean shallow 84 · Lean deep 271 · MetaPRL 77 (the `refine` lines of c2-router.mp). No direction was predicted, so it is exploratory.
