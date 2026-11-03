# Errata to OBJECT-L1 (O95, layer L1)

`../object-L1/OBJECT-L1.md` is never edited after its pin (vir dc44f15). Each defect gets a row here, with who found it and
what each arm does about it. Both arms get the same decision.

| id | where | the defect | found by | decision |
|---|---|---|---|---|
| L1-E1 | §6, "MetaPRL, the bar type `bar(·)`" (also §1's "the logic's own type of partial results") | The bar type is NOT in MetaPRL at the pinned release fb8e715d7, or in any release. It is `theories/vir/itt_bar.ml`, written by the MetaPRL arm on 2026-11-02 for the council §C program. So "the logic's own type" is true of Lean (`Part`, in mathlib at the pin) and false of MetaPRL at the pin. The author named it without checking the pin. | mojave, 2026-11-02 17:50 (its L1 declarations, D4) | The object's requirement stands unchanged (a real partial-result type, no fuel). How `itt_bar` is COUNTED is amend-14. |
