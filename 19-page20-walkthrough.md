# 19 — Page 20 of the Paper, Walked Through With Numbers

**What is actually on p.20** (§3.4, lines 827–866 of `_source/paper-extracted-text.txt`):

1. **Remark 1** — assume `pi` is constant size
2. **"Accumulator."** — the data structure: `acc.x` and `acc.w`
3. **"Accumulation prover."** — its *inputs*, then "works as in **Figure 3**"
4. **"Accumulation verifier."** — its *inputs*, then "works as in **Figure 4**"
5. **"Decider."** — its *inputs*, then "the checks described in **Figure 5**"
6. **Remark 2** — the folding-scheme reading

So page 20 defines **the data structure and the three interfaces**; the algorithm
*bodies* are Figures 3, 4, 5 on pp. 21–22. This file does both: first the page-20
structures with real values, then the figures executed step by step.

Everything in **`F_101`**. Every number verified.

---

## The toy commitment (read this first)

To show actual numbers for `Commit`, this file uses a **linear toy commitment**:

```
ck = (1, 2, 3, …, n)          Commit(ck, m) := Σ_i  ck_i · m_i   mod 101
```

> ⚠️ **This is homomorphic but NOT binding** — it is a stand-in used only so the
> homomorphism (`Commit(αm + m') = α·Commit(m) + Commit(m')`) can be *seen* with
> real integers. A real deployment uses **Pedersen** over a prime-order elliptic
> curve group, where binding rests on discrete log (Def. 6, §2.3). Every
> homomorphism identity demonstrated below holds verbatim for Pedersen; only the
> binding property differs.

---

## The setting (continuing file 17)

4 multiplication gates, `a_i·b_i = c_i`. So `k = 1`, `d = 2`, `ℓ = 4`.

```
Object A — the new proof π          Object B — the accumulator acc
  a  = (2, 3, 5, 7)                   a' = (1, 1, 2, 2)
  b  = (4, 6, 8, 9)                   b' = (3, 2, 1, 4)
  c  = (8,18,40,63)                   c' = (1, 1, 1, 1)
  pi = 1                              pi' = 3
  μ  = 1                              μ' = 2
```

---

## PART 1 — "Accumulator." (p.20) — the data structure, filled in

The paper says:

> "**Accumulator instance** `acc.x := {pi, [C_i]_{i=1}^{k}, [r_i]_{i=1}^{k−1}, E, μ}`,
> where `pi ∈ M_in` is the accumulated public input, `[C_i] ∈ C^k` are the
> accumulated commitments, `[r_i] ∈ F^{k−1}` are the accumulated challenges,
> `E ∈ C` is the accumulated commitment to the error terms, and `μ ∈ F` is a slack
> variable.
> **Accumulator witness** `acc.w := {[m_i]_{i=1}^{k}}`, where `[m_i]` are the
> accumulated prover messages."

Fill it in for our two objects. With `k = 1` there is **one** commitment and
**zero** challenges (`[r_i]_{i=1}^{0}` is empty).

### Object B — the accumulator `acc`

```
acc.w  =  { m'_1 }                                          <- the WITNESS, 12 numbers
          m'_1 = (1,1,2,2 , 3,2,1,4 , 1,1,1,1)

          C'_1 = Commit(ck, m'_1)
               = 1·1 + 2·1 + 3·2 + 4·2 + 5·3 + 6·2 + 7·1 + 8·4 + 9·1 + 10·1 + 11·1 + 12·1
               = 125  =  24                mod 101

          e'   = a'∘b' − μ'·c'  =  (3,2,2,8) − (2,2,2,2)  =  (1, 0, 0, 6)
          E'   = Commit(ck_E, e')  =  1·1 + 2·0 + 3·0 + 4·6  =  25

acc.x  =  { pi'=3 ,  C'_1=24 ,  (no challenges) ,  E'=25 ,  μ'=2 }    <- the INSTANCE
```

**The instance is 4 numbers. The witness is 12.** That ratio is the whole point,
and at realistic sizes it is 4 numbers versus millions.

### Object A — the proof `π`

Page 20 gives `π := (π.x = [C_i], π.w = [m_i])` — note it has **no** `E` or `μ`
field. Remark 2 supplies them:

```
π.w  =  { m_1 = (2,3,5,7 , 4,6,8,9 , 8,18,40,63) }

        C_1 = Commit(ck, m_1)
            = 1·2 + 2·3 + 3·5 + 4·7 + 5·4 + 6·6 + 7·8 + 8·9 + 9·8 + 10·18 + 11·40 + 12·63
            = 1683  =  67                mod 101

π.x  =  { C_1 = 67 }        and implicitly   μ = 1,  E = 0        <- Remark 2
```

---

## PART 2 — "Accumulation prover." (p.20) → Figure 3 (p.21), executed

Page 20 states only the **inputs**:

> "On input commitment key `ck` (which can be hardwired in the prover's algorithm),
> accumulator `acc`, an instance-proof pair `(pi, π)` … the accumulation prover
> `P_acc` works as in Figure 3."

Now Figure 3, step by step.

### Step 1 — recompute the challenges

```
r_i ← ρ_NARK(r_{i−1}, C_i)   for i ∈ [k−1]
```

`k = 1`, so `[k−1]` is empty. **Nothing to do.**

### Step 2 — compute the `d−1` cross terms

```
e_1 = a∘b' + a'∘b − μ'·c − c'

  a∘b'  = (2·3, 3·2, 5·1, 7·4)  = ( 6,  6,  5, 28)
  a'∘b  = (1·4, 1·6, 2·8, 2·9)  = ( 4,  6, 16, 18)
  μ'·c  = 2·(8,18,40,63)        = (16, 36, 80,126)
  c'                             = ( 1,  1,  1,  1)

e_1 = (6+4−16−1, 6+6−36−1, 5+16−80−1, 28+18−126−1)
    = (−7, −25, −60, −81)  =  (94, 76, 41, 20)      mod 101
```

`d − 1 = 1` cross term, and it is a **vector in `F^ℓ = F^4`** — exactly as
Figure 3 writes it: `[e_j]_{j=1}^{d−1} ∈ (F^ℓ)^{d−1}`.

### Step 3 — commit to the cross terms

```
E_1 = Commit(ck_E, e_1) = 1·94 + 2·76 + 3·41 + 4·20 = 449 = 45    mod 101
```

**This is the group operation that `CV` (§3.5) exists to eliminate.** With `d = 2`
there is only one; with `d = 10` there would be nine.

### Step 4 — derive the folding challenge

```
α ← ρ_acc(acc.x, pi, π.x, [E_j])
```

Say it returns **`α = 5`**. Note it is computed **after** `E_1` is fixed — the
prover cannot choose `e_1` knowing `α`.

### Step 5 — set the two vectors

```
v  := ( 1,  pi,  [r_i], [C_i], [m_i] )  =  ( 1, 1, —, 67, m_1 )      <- the proof; leading 1 is its μ
v' := ( μ', pi', [r'_i],[C'_i],[m'_i])  =  ( 2, 3, —, 24, m'_1 )     <- the accumulator
```

**Two vectors. This is the whole "we fold 2 instances" fact, in one line of the
paper.**

### Step 6 — the fold

```
v''  ←  α · v + v'

  μ''   = 5·1  + 2   = 7
  pi''  = 5·1  + 3   = 8
  C''_1 = 5·67 + 24  = 359  =  56           mod 101
  m''_1 = 5·m_1 + m'_1
        = (11,16,27,37 , 23,32,41,49 , 41,91,100,13)      mod 101
```

**Check the homomorphism** — commit the folded message directly:

```
Commit(ck, m''_1) = 1·11 + 2·16 + 3·27 + 4·37 + 5·23 + 6·32
                  + 7·41 + 8·49 + 9·41 + 10·91 + 11·100 + 12·13
                  = 3793  =  56              mod 101
```

`56 = 56` ✓ — the commitment of the fold equals the fold of the commitments. This
is the property the completeness proof of Theorem 2 leans on, twice.

### Step 7 — accumulate the error

```
E''  =  E' + Σ_{j=1}^{d−1} α^j · E_j  =  25 + 5·45  =  250  =  48      mod 101
```

**Check** against the true folded error vector `e'' = e' + α·e_1`:

```
e'' = (1,0,0,6) + 5·(94,76,41,20) = (471,380,205,106) = (67, 77, 3, 5)   mod 101

Commit(ck_E, e'') = 1·67 + 2·77 + 3·3 + 4·5 = 250 = 48                   mod 101
```

`48 = 48` ✓ — homomorphism holds for the error terms too.

### Steps 8–9 — package the output

```
acc''.x := { pi''=8, C''_1=56, —, E''=48, μ''=7 }
acc''.w := { m''_1 }
pf      := [E_1] = [45]
```

---

## PART 3 — "Accumulation verifier." (p.20) → Figure 4 (p.21), executed

Page 20 states the inputs:

> "On input public input `pi`, NARK proof instance `π.x`, accumulator instance
> `acc.x`, accumulation proof `pf`, and the updated accumulator instance `acc'.x`
> … the accumulation verifier `V_acc` works as in Figure 4."

**Every input is an instance or `pf`. No witness anywhere.** This is what becomes
the recursive circuit.

```
1.  r_i ← ρ_NARK(...)                    k = 1, nothing to do
2.  α ← ρ_acc(acc.x, pi, π.x, pf)        = 5
3.  v  := (1,  pi,  [r_i], [C_i])  = (1, 1, —, 67)
    v' := (μ', pi', [r'_i],[C'_i]) = (2, 3, —, 24)
4.  Check (μ'', pi'', [r''_i], [C''_i]) =? α·v + v'
        (7, 8, —, 56)  =?  5·(1,1,—,67) + (2,3,—,24)
                        =  (7, 8, —, 359 = 56)              ✓
5.  Check acc''.x.E =? acc'.x.E + Σ α^j·E_j
        48  =?  25 + 5·45  =  250  =  48                    ✓
```

**Accepts.** Now count what it touched:

```
numbers used:  1, 67, 2, 3, 24, 7, 8, 56, 25, 45, 48, and α
NOT used:      the 12 witness values of either object
               the 4-entry vectors e', e_1, e''
```

The verifier folded **one** commitment (`C_1`) and **one** error commitment (`E`).
It never saw `ℓ = 4` coordinates or `|m| = 12` witness values. That is what
"`V_acc` sublinear in its input" (Theorem 1) means in practice.

---

## PART 4 — "Decider." (p.20) → Figure 5 (p.22), executed

Page 20:

> "On input the commitment key `ck` … and an accumulator `acc = (acc.x = {…},
> acc.w = {…})`, the decider does the checks described in Figure 5."

**Note this one takes `acc.w`** — the decider is the only algorithm that sees the
witness, and it runs **once**, at the very end.

```
1.  C''_1 =? Commit(ck, m''_1)
        56  =?  56                                          ✓

2.  e ← Σ_{j=0}^{d} μ''^{d−j} · f_j(...)     i.e.  a''∘b'' − μ''·c''

        a''∘b'' = (11·23, 16·32, 27·41, 37·49)
                = (253, 512, 1107, 1813)  =  (51,  7, 97, 96)     mod 101
        μ''·c'' = 7·(41, 91, 100, 13)
                = (287, 637, 700, 91)     =  (85, 31, 94, 91)     mod 101

        e       = (51−85, 7−31, 97−94, 96−91)
                = (−34, −24, 3, 5)        =  (67, 77, 3, 5)       mod 101

3.  E'' =? Commit(ck_E, e)
        48  =?  1·67 + 2·77 + 3·3 + 4·5  =  250  =  48            ✓
```

**Decider accepts.** The folded accumulator is valid — which, by Theorem 2, means
both the proof `π` and the old accumulator `acc` were valid.

---

## PART 5 — Remark 2 (p.20), the three folding modes

> "A NARK proof `π` is an accumulator with `μ = 1` and `E = 0 ∈ G`. We can use the
> same accumulation scheme to fold two accumulators `(acc, acc')` into a new
> accumulator `acc''`. The scheme is identical to the one presented above but with
> non-trivial `μ, e, E` terms for `acc'`. **The verifier performs one additional
> group scalar multiplication.** In the language of folding schemes, we can fold
> two NARK instances into an accumulator; or fold a NARK instance and an
> accumulator into an updated accumulator; or fold two accumulators into an updated
> accumulator."

| Mode | Left operand | Right operand | Extra cost |
|---|---|---|---|
| proof + accumulator | `μ=1, E=0` | `μ'≠1, E'≠0` | — (what we just did) |
| proof + proof | `μ=1, E=0` | `μ=1, E=0` | — |
| accumulator + accumulator | `μ≠1, E≠0` | `μ'≠1, E'≠0` | **+1 group scalar mult** |

**Three modes, all of them two-into-one.** The extra group multiplication in the
third mode is because `E ≠ 0` on *both* sides, so the verifier must scale the left
`E` too instead of dropping it.

---

## What page 20 is doing, in one paragraph

Page 20 is the **interface page**. It declares the accumulator type
(`acc.x` short, `acc.w` long), then declares three algorithms by their *inputs
only*, deferring every body to a figure:

| Algorithm | Sees `acc.w`? | Runs | Becomes |
|---|---|---|---|
| `P_acc` | yes | every step | native prover work |
| `V_acc` | **no** | every step | **the recursive circuit** |
| `D` | yes | **once, at the end** | the IVC verifier's final check |

The middle row is the entire economic argument of the paper: because page 20
declares `V_acc` to take only `(pi, π.x, acc.x, pf, acc'.x)` — instances, never
witnesses — the recursive circuit costs `k + d − 1` group operations regardless of
how big the witness, the circuit, or `ℓ` is.

---

## Every number in one table

| Quantity | Proof `π` | Accumulator `acc` | Folded `acc''` |
|---|---|---|---|
| `pi` | 1 | 3 | 8 |
| `μ` | 1 | 2 | 7 |
| `C_1` | 67 | 24 | 56 |
| `E` | 0 | 25 | 48 |
| error vector | `(0,0,0,0)` | `(1,0,0,6)` | `(67,77,3,5)` |
| witness `m_1` | 12 values | 12 values | 12 values |

with `α = 5`, `e_1 = (94,76,41,20)`, `E_1 = 45`, `pf = [45]`.

Verified identities:

```
Commit(α·m_1 + m'_1)  =  α·C_1 + C'_1        56 = 56    ✓
Commit(e' + α·e_1)    =  E' + α·E_1          48 = 48    ✓
a''∘b'' − μ''·c''     =  e''                 (67,77,3,5) ✓
```
