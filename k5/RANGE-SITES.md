# K5-2b work list: every range hypothesis the mode traces carry (generated from k5/K5/*.lean at the commit beside it)

Each row is an arithmetic site a mode's ⟶₂ run passes through whose range the trace could NOT read off its own local facts.
K5-2b discharges each from the mode's Safety-level facts (Inv) and, where Inv has no upper bound (finding K5-2-0), from `Mag`.

| file | trace | hypotheses (expression in the trace's own variables) |
|---|---|---|
| Read.lean | `inRange_of` | none |
| Read.lean | `readbit_inR` | `(t * wt)` · `(acc + t * wt)` · `(2 * wt)` · `(k - 1)` |
| Modes1.lean | `hdrb_step_inR` | none |
| Modes1.lean | `hdrd_step_inR` | none |
| Modes1.lean | `shdr_step_inR` | `(bx + 1)` |
| Modes1.lean | `slen_step_inR` | none |
| Modes1.lean | `snlen_step_inR` | `(a + len)` · `(bx + len)` · `(m + len)` |
| Modes1.lean | `fixlens_step_inR` | `(2080 + (n : Int))` · `(2080 + (n : Int) + (om : Int))` · `(2080 + (n : Int) + (om : Int) + (i : Int))` · `((i : Int) + 1)` |
| Modes1.lean | `fixlens_end_inR` | `(X + 5)` · `(2080 + n)` · `(2080 + n + om)` · `(X + 6)` · `(X + 7)` · `(2080 + n + om + 689)` · `(X + 8)` |
| Modes1.lean | `dhdr_step_inR` | none |
| Modes1.lean | `dh2_step_inR` | `(a + 257)` |
| Modes1.lean | `dh3_step_inR` | `(a + 1)` |
| Modes1.lean | `dh4_step_inR` | `(a + 4)` |
| Modes1.lean | `clput_step_inR` | `(X + 134)` · `(X + 134 + i)` · `(2080 + n)` · `(2080 + n + om)` · `(2080 + n + om + 318)` · `(2080 + n + om + 318 + o)` · `(i + 1)` |
| Modes2.lean | `readbit_trunc_inR` | none |
| Modes2.lean | `scopy_end_inR` | none |
| Modes2.lean | `scopy_byte_inR` | `(2080 + (bx : Int))` · `(2080 + (n : Int))` · `(2080 + (n : Int) + (m : Int))` · `((bx : Int) + 1)` · `((m : Int) + 1)` · `(k - 1)` |
| Modes2.lean | `decode_trunc_inR` | none |
| Modes2.lean | `sym_step_inR` | `(X + 1)` · `(X + 2)` · `(X + 3)` |
| Modes2.lean | `symd_step_inR` | `(X + 4)` · `(2080 + n)` · `(2080 + n + m)` · `(X + 16)` · `(s - 257)` · `(X + 16 + (s - 257))` · `(m + 1)` · `(X + 45)` · `(X + 45 + (s - 257))` |
| Modes2.lean | `lenx_step_inR` | `(pd + a)` · `(X + 1)` · `(X + 2)` · `(X + 3)` |
| Modes2.lean | `dstd_step_inR` | `(X + 4)` · `(X + 74)` · `(X + 74 + d)` · `(X + 104)` · `(X + 104 + d)` |
| Modes2.lean | `dstx_step_inR` | `(ds + a)` · `(m + pd)` |
| Modes2.lean | `copy_end_inR` | none |
| Modes2.lean | `copy_byte_inR` | `(2080 + n)` · `(m - ds)` · `(2080 + n + (m - ds))` · `(2080 + n + m)` · `(m + 1)` · `(pd - 1)` |
| Modes2.lean | `clread_req_inR` | none |
| Modes2.lean | `clread_zero_inR` | `(X + 134)` · `(X + 134 + i)` · `(2080 + n)` · `(2080 + n + om)` · `(2080 + n + om + 318)` · `(2080 + n + om + 318 + o)` · `(i + 1)` |
| Modes2.lean | `clread_end_inR` | `(X + 5)` · `(2080 + n)` · `(2080 + n + om)` · `(2080 + n + om + 318)` · `(X + 6)` · `(X + 7)` · `(2080 + n + om + 337)` · `(X + 8)` |
| Modes2.lean | `lens_req_inR` | `(hl + hd)` · `(X + 1)` · `(X + 2)` · `(X + 3)` |
| Modes2.lean | `lens_end_inR` | `(hl + hd)` · `(2080 + n)` · `(2080 + n + om)` · `(2080 + n + om + 256)` · `(X + 5)` · `(X + 6)` · `(X + 7)` · `(2080 + n + om + 689)` · `(X + 8)` |
| Modes2.lean | `lsym_step_inR` | `(X + 4)` · `(2080 + n)` · `(2080 + n + om)` · `(2080 + n + om + fl)` · `(fl - 1)` · `(2080 + n + om + (fl - 1))` · `(fl + 1)` |
| Modes2.lean | `lrep_step_inR` | `(hl + hd)` · `(pd + a)` · `(fl + (pd + a))` |
| Modes2.lean | `rep_end_inR` | none |
| Modes2.lean | `rep_byte_inR` | `(2080 + n)` · `(2080 + n + om)` · `(2080 + n + om + fl)` · `(fl + 1)` · `(pd - 1)` |
| Modes3.lean | `build_zero_end_inR` | `(X + 7)` |
| Modes3.lean | `build_count_cell_inR` | `(X + 7)` · `(X + 5)` · `(X + 6)` · `(sb + j)` · `(j + 1)` · `(tbb + l)` · `(c + 1)` |
| Modes3.lean | `build_count_end_inR` | `(X + 7)` · `(X + 5)` · `(X + 6)` · `(tbb + 16)` · `(tbb + 32)` |
| Modes3.lean | `build_next_cell_inR` | `(X + 7)` · `(j - 1)` · `(tbb + (j - 1))` · `(tbb + 32)` · `(tbb + 32 + (j - 1))` · `(code + cp)` · `(2 * (code + cp))` · `(tbb + 16)` · `(tbb + 16 + j)` · `(tbb + 32 + j)` · `(op + cp)` · `(tbb + 48)` · `(tbb + 48 + j)` · `(j + 1)` |
| Modes3.lean | `build_next_end_inR` | `(X + 7)` |
| Modes3.lean | `build_left_cell_inR` | `(X + 7)` · `(tbb + j)` · `(2 * left)` · `(2 * left - c)` · `(rest + c)` · `(tot + c)` · `(j + 1)` |
| Modes3.lean | `build_syms_cell_inR` | `(X + 7)` · `(X + 5)` · `(X + 6)` · `(sb + j)` · `(j + 1)` · `(tbb + 48)` · `(tbb + 48 + l)` · `(tbb + 64)` · `(tbb + 64 + sl)` · `(sl + 1)` |
| Modes3.lean | `build_syms_end_cl_inR` | `(X + 7)` · `(X + 5)` · `(X + 6)` |
| Modes3.lean | `build_syms_end_l_inR` | `(X + 7)` · `(X + 5)` · `(X + 6)` · `(2080 + n)` · `(2080 + n + om)` · `(2080 + n + om + hl)` · `(2080 + n + om + 1041)` · `(X + 8)` |
| Modes3.lean | `build_syms_end_d_inR` | `(X + 7)` · `(X + 5)` · `(X + 6)` |
| Modes4.lean | `decode_step_inR` | `(2080 + (bx : Int))` · `(8 * (v : Int))` · `(8 * (v : Int) + 7)` · `(20 + (8 * (v : Int) + 7))` · `(8 * (v : Int) + (bi : Int))` · `(20 + (8 * (v : Int) + (bi : Int)))` · `(X + 1)` · `(8 * (v : Int) + (7 : Int))` · `(20 + (8 * (v : Int) + (7 : Int)))` · `(X + 2)` · `(X + 3)` · `(2080 + (n : Int))` · `(2080 + (n : Int) + om)` · `(2080 + (n : Int) + om + 337)` · `(352 * t)` · `(2080 + (n : Int) + om + 337 + 352 * t)` · `(2080 + (n : Int) + om + 337 + 352 * t + 16)` · `(2080 + (n : Int) + om + 337 + 352 * t + 16 + l)` · `(2080 + (n : Int) + om + 337 + 352 * t + 16 + 15)` · `(2080 + (n : Int) + om + 337 + 352 * t + l)` · `(2080 + (n : Int) + om + 337 + 352 * t + 15)` · `((bx : Int) + 1)` · `((bi : Int) + 1)` · `(2 * cv)` · `(2 * cv + b)` · `((7 : Int) + 1)` · `(fs + c)` · `(7 + 1)` · `(l + 1)` · `(2080 + (n : Int) + om + 337 + 352 * t + 32)` · `(2080 + (n : Int) + om + 337 + 352 * t + 32 + l)` · `(2080 + (n : Int) + om + 337 + 352 * t + 64)` · `(2080 + (n : Int) + om + 337 + 352 * t + 64 + o)` · `(2 * cv + b - fs)` · `(2080 + (n : Int) + om + 337 + 352 * t + 64 + o + (2 * cv + b - fs))` · `(X + 4)` |

**202 distinct (trace, expression) range obligations.** Open traces not listed: `build_left_end` (WIP), `table_step` (BITc).
