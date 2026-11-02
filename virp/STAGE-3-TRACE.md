# VIR program, Lean arm — stage 3: n calls at the meaning (rate limiting as a trace property)

O95, council 2026-11-02 §C point 5: *"exits as labelled values; calls and emits as inputs/outputs, so n-call theorems are
trace properties."* File: `virp/VIRP/Trace.lean`.

- `Fn` is ⟦F⟧'s closed form as a function, and `denote_F_eq` is `F_closed` restated through it.
- `call σ w`: the caller puts frame `w` on the wire and ⟦F⟧ runs. `run` threads the returned store through a list of frames.
  `emitsBy p` counts sender p's emits along the trace.
- **`run_tokens`: p's tokens at the end + p's emits = p's tokens at the start, for EVERY list of frames.** It is exact, by
  induction on the list, from the one-call identity `call_tokens`.
- **`emits_le_tokens`: a sender never emits more often than it held tokens, over ANY number of calls.**

Checked: build-015 + audit-005 `saltbuild EXIT=0` (32 theorems, no `sorryAx`). **Mutant `mutant-006-twotokens`** (one emit
charged two tokens) is RED at `omega`.

Limits: the abstract side only. The machine side iterates paris's `reenter` + `sim_one` (paris's `sim_two` is built and n
calls is not). The caller's only write is the new frame, and tokens are never refilled between calls.
