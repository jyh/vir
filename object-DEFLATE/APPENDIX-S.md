# OBJECT-DEFLATE — APPENDIX S, the spec as pseudo-code (PINNED 2026-11-11 with OBJECT-DEFLATE.md; fork X4 (a))

**Pinned in the same commit as `OBJECT-DEFLATE.md`, on the same word.** He had not read these bytes when he gave it (see that
file). From the next line down this is the 11-06 draft byte for byte. Its "DRAFT, UNPINNED" title is kept as the record of what was
read, and this header supersedes it. **Nothing here is edited after the pin.** A disagreement with zlib under X5 is an erratum
in `errata/ERRATA-DEFLATE.md`, recorded before any repair.

# OBJECT-DEFLATE — APPENDIX S, the spec as pseudo-code (DRAFT, UNPINNED; fork X4 (a) of the companion draft)

Transcribed 2026-11-06 by the 25th vir head from RFC 1951 §3.2, for his read BEFORE the pin. Under X4 (a) these bytes are frozen with
the object and each arm formalizes THEM. Clauses marked **[zlib]** are where the RFC is silent or permissive and zlib's raw `inflate`
decides. Each one is ADOPTED so that X5's accept/reject agreement is well-posed, and each is a candidate for his veto. Clauses marked
**[X6]** come from the OUTMAX bound. Nothing here was checked against zlib yet. That check is X5's, and it runs after the pin.

## S1. Values and the bit reader
```
input  : bytes b[0 .. n-1]        output : bytes o[0 .. m-1], m ≤ OUTMAX          state: (pos_bit, o)
bit()        = (b[pos_bit / 8] >> (pos_bit mod 8)) & 1 ; pos_bit += 1      -- REJECT "truncated" if pos_bit/8 ≥ n
bits(k)      = Σ_{i<k} bit_i · 2^i                  -- data fields: LEAST-significant bit first (§3.1.1)
align()      = pos_bit := 8 · ⌈pos_bit / 8⌉
```
A Huffman code is read one `bit()` at a time, the code's MOST-significant bit first (§3.1.1, "packed starting with the MSB").

## S2. The stream
```
inflate(b):
  repeat
    BFINAL := bits(1) ; BTYPE := bits(2)
    case BTYPE of 0 → stored()  | 1 → huff(FIXED_L, FIXED_D)  | 2 → dynamic()  | 3 → REJECT "invalid block type"
  until BFINAL = 1
  ACCEPT o          -- bits after the final block, and bytes after it, are IGNORED [zlib: raw inflate stops at the final block]
```

## S3. Stored blocks (BTYPE 00)
```
stored(): align() ; LEN := bits(16) ; NLEN := bits(16)
  if NLEN ≠ LEN xor 0xFFFF then REJECT "invalid stored block lengths"
  copy the next LEN input bytes to o            -- REJECT "truncated" if fewer remain ; REJECT "overflow" if m + LEN > OUTMAX [X6]
```

## S4. Canonical Huffman codes (§3.2.2)
```
code(lens[0 .. N-1]):                        -- lens[i] ∈ 0..15, 0 = symbol unused
  bl_count[ℓ] := #{ i : lens[i] = ℓ } for ℓ ≥ 1 ;  code := 0 ; bl_count[0] := 0
  for ℓ in 1..15: code := (code + bl_count[ℓ-1]) << 1 ; next_code[ℓ] := code
  for i in 0..N-1 with lens[i] ≠ 0: assign i the ℓ-bit code next_code[lens[i]]++, ℓ = lens[i]
  left := 1 ; for ℓ in 1..15: left := 2·left − bl_count[ℓ] ; if left < 0 then REJECT "over-subscribed"      [zlib]
  if left > 0 and not (the code has exactly one symbol, of length 1) then REJECT "incomplete"               [zlib]
decode(C) = read bits MSB-first until they form a code of C ; that code's symbol      -- REJECT "invalid code" if none can
```
**[zlib] the empty distance code:** a dynamic block whose distance lengths are ALL zero is ACCEPTED. It REJECTS only when a length
symbol then needs a distance. The "incomplete" clause above is not applied to an empty distance code.

## S5. Fixed codes (BTYPE 01, §3.2.6)
```
FIXED_L = code(lens) with lens[0..143]=8, lens[144..255]=9, lens[256..279]=7, lens[280..287]=8
FIXED_D = code(lens) with lens[0..29]=5          -- 30 symbols; the RFC lists 32 and says 30, 31 never occur.
           -- [zlib] reading 30 or 31 REJECTS "invalid distance code" ; reading literal/length 286 or 287 REJECTS "invalid literal/length code"
```

## S6. Dynamic codes (BTYPE 10, §3.2.7)
```
dynamic(): HLIT := bits(5) + 257 ; HDIST := bits(5) + 1 ; HCLEN := bits(4) + 4
  if HLIT > 286 or HDIST > 30 then REJECT "too many length or distance symbols"              [zlib]
  ORDER = 16 17 18 0 8 7 9 6 10 5 11 4 12 3 13 2 14 1 15
  cl[ORDER[i]] := bits(3) for i < HCLEN ; cl[ORDER[i]] := 0 for HCLEN ≤ i < 19
  CL := code(cl)                                -- an incomplete code-length code REJECTS (S4, no exception)  [zlib]
  lens := [] ; while |lens| < HLIT + HDIST:
    s := decode(CL)
    s ≤ 15 → append s
    s = 16 → if lens = [] then REJECT "repeat with no first length" ; append last(lens) × (3 + bits(2))
    s = 17 → append 0 × (3 + bits(3))
    s = 18 → append 0 × (11 + bits(7))
    if |lens| > HLIT + HDIST then REJECT "invalid bit length repeat"                          -- a repeat may cross HLIT into HDIST
  if lens[256] = 0 then REJECT "missing end-of-block"                                          [zlib]
  huff(code(lens[0 .. HLIT-1]), code(lens[HLIT .. HLIT+HDIST-1]))
```

## S7. Compressed data (§3.2.5)
```
huff(L, D): loop
  s := decode(L)
  s < 256  → append byte s to o                                   -- REJECT "overflow" if m = OUTMAX [X6]
  s = 256  → return                                                -- end of block
  s ≤ 285  → len  := LBASE[s-257] + bits(LEXTRA[s-257])
             d    := decode(D) ; if d ≥ 30 then REJECT "invalid distance code"
             dist := DBASE[d] + bits(DEXTRA[d])
             if dist > m then REJECT "distance too far back"      -- [zlib] no preset dictionary, so ≤ the bytes produced so far
             for k in 0 .. len-1: append o[m - dist] to o         -- ONE BYTE AT A TIME: overlap (dist < len) repeats, §3.2.3
                                                                   -- REJECT "overflow" if the result would exceed OUTMAX [X6]
  else     → REJECT "invalid literal/length code"                 -- 286, 287
LBASE  = 3 4 5 6 7 8 9 10 11 13 15 17 19 23 27 31 35 43 51 59 67 83 99 115 131 163 195 227 258
LEXTRA = 0 0 0 0 0 0 0 0  1  1  1  1  2  2  2  2  3  3  3  3  4  4  4   4   5   5   5   5   0
DBASE  = 1 2 3 4 5 7 9 13 17 25 33 49 65 97 129 193 257 385 513 769 1025 1537 2049 3073 4097 6145 8193 12289 16385 24577
DEXTRA = 0 0 0 0 1 1 2  2  3  3  4  4  5  5   6   6   7   7   8   8    9    9   10   10   11   11   12    12    13    13
```
The window is the last 32,768 bytes of o. With no dictionary, `dist ≤ m` and `dist ≤ 32,768` (DBASE's maximum plus its extra bits) together
are exactly the RFC's constraint, so the spec keeps all of o and needs no separate window clause.

## S8. What the spec's REJECT means
Each REJECT names a reason string, and the spec returns `reject(reason)`. X3 (a) and X5 compare ACCEPT/REJECT only, never the reason.
Reasons are reported, because a disagreement in REASON with zlib on a rejected input is a finding about the spec's ORDER of checks.
