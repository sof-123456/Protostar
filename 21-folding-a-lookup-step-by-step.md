# 21 — Folding a Lookup, Step by Step

**What this file is:** the complete path from "here is a lookup table" to "here is
a folded accumulator", with every number worked out in `F_101` and every step
verified. It answers, in order:

1. What is the lookup relation and what is `Π_LK`?
2. Why can it be fed into Protostar's compiler at all?
3. What does an *accumulated* lookup even mean — what are `μ` and `e`?
4. **What exactly happens when you fold, and where do the error terms come from?**
5. What if you have 3 instances instead of 2?
6. Why does none of it depend on the table size?

File [20-lookup-tables-explained.md](20-lookup-tables-explained.md) covers the
lookup argument in isolation. **This file is about what the folding machinery does
to it.** Read 20 first if `Σ 1/(X+w_i) = Σ m_i/(X+t_i)` is unfamiliar.

Running example throughout: `F_101`, table `t = [0, 1, 2, 3]`, `T = 4`, `ℓ = 4`.
Every number below was recomputed and checked.

---

# Part 1 — The starting point: `Π_LK`

## 1.1 The relation

`R_LK` = the witnesses `w ∈ F^ℓ` such that **every `w_i` appears in the public
table `t ∈ F^T`**. The table is preprocessed public data; the witness is the list
of values being looked up.

## 1.2 The protocol (Def. 12 + §4.3)

```
Prover P(C_LK, w ∈ F^ℓ)                             Verifier V(C_LK)

m_i := Σ_{j∈[ℓ]} 1(w_j = t_i)   ∀i ∈ [T]
                        --- w, m --->
                        <--- r ---                   r ←$ F
h_i := 1/(w_i + r)    ∀i ∈ [ℓ]
g_i := m_i/(t_i + r)  ∀i ∈ [T]
                        --- h, g --->
                                            (1)  Σ_{i∈[ℓ]} h_i =? Σ_{i∈[T]} g_i
                                            (2)  h_i·(w_i + r) =? 1     ∀i ∈ [ℓ]
                                            (3)  g_i·(t_i + r) =? m_i   ∀i ∈ [T]
```

Check (1) is Haböck's log-derivative identity evaluated at `r`; checks (2) and (3)
force `h` and `g` to really be the inverse vectors.

## 1.3 Three valid instances — our raw material

These three lookup proofs are used for the rest of the file. All are honest.

```
π_1 :  w = [1,1,3,0]   m = [1,2,0,1]   r = 9
       h = [91,91,59,45]              g = [45,81, 0,59]      Σh = Σg = 84  ✓

π_2 :  w = [2,0,2,3]   m = [1,0,2,1]   r = 5
       h = [29,81,29,38]              g = [81, 0,58,38]      Σh = Σg = 76  ✓

π_3 :  w = [3,3,1,2]   m = [0,1,1,2]   r = 11
       h = [65,65,59,70]              g = [ 0,59,70,29]      Σh = Σg = 57  ✓
```

Spot-check `π_2`, entry 1: `h_1·(w_1+r) = 29·(2+5) = 203 = 2·101 + 1 ≡ 1` ✓.
Spot-check `π_2`, check (3) entry 3: `g_3·(t_3+r) = 58·(2+5) = 406 ≡ 2 = m_3` ✓.

---

# Part 2 — Why `Π_LK` is a legal input to the compiler

Protostar's compiler (report [04](04-step1-compiler-pipeline.md)) accepts any
special-sound protocol whose verifier is **algebraic** and **decomposes into
homogeneous parts**. Three parameters characterise it:

| parameter | meaning | value for `Π_LK` |
|---|---|---|
| `k` | number of prover messages | **2** — `(w,m)` then `(h,g)` |
| `d` | verifier degree | **2** |
| output length | number of equations checked | `1 + ℓ + T` |

## 2.1 The homogeneous decomposition — the load-bearing step

The compiler needs `V_sps = f_0 + f_1 + f_2`, where each `f_j` is homogeneous of
degree **exactly** `j`.

**Critical: what counts as a variable.** The folded vector is
`v = (μ, pi, [r_i], [m_i])`. So:

* `w, m, h, g` are **variables** (witness) — degree 1 each.
* `r` is a **variable** (challenge) — degree 1. *This surprises people.*
* `t` is a **constant** (public preprocessed table) — degree 0. It never folds.

With that, the three check families decompose as:

| check | `f_0` (deg 0) | `f_1` (deg 1) | `f_2` (deg 2) |
|---|---|---|---|
| (1) `Σh − Σg` | — | `Σh − Σg` | — |
| (2) `h_i(w_i+r) − 1` | `−1` | — | `h_i·w_i + h_i·r` |
| (3) `g_i(t_i+r) − m_i` | — | `g_i·t_i − m_i` | `g_i·r` |

Note `g_i·t_i` is degree **1** (only `g_i` is a variable) but `g_i·r` is degree
**2** (both are). That asymmetry is why check (3)'s relaxed form looks lopsided.

**`d = 2`.** A lookup is exactly as hard to fold as an R1CS multiplication gate.

---

# Part 3 — What an accumulated lookup means

## 3.1 The relaxed predicate

The compiler replaces `V_sps = 0` with the **relaxed** check
`Σ_{j=0}^{d} μ^{d−j}·f_j = e`. For `d = 2` that is `μ²f_0 + μf_1 + f_2 = e`:

```
(1)   μ·( Σ h_i − Σ g_i )                = e⁽¹⁾    ∈ F
(2)   h ∘ (w + r·1)  −  μ²·1             = e⁽²⁾    ∈ F^ℓ
(3)   g ∘ (μ·t + r·1)  −  μ·m            = e⁽³⁾    ∈ F^T
```

An honest proof has `μ = 1`, `e = 0`, and these collapse back to Part 1.3's
checks. Verify on `π_2`: `μ=1`, so (2) gives `29·7 − 1 = 0` ✓.

## 3.2 What `μ` is for

`μ` is a **slack variable** that makes the whole predicate a single homogeneous
form of degree exactly `d`. Its job is to make the degree-0 constant `−1` scale at
the same rate as the degree-2 product `h·(w+r)` when you fold. Part 5.3 shows
precisely what breaks without it.

## 3.3 What `e` is for

`e` is the **noise bin**. Folding two solutions of a degree-2 equation does not
give a solution — it gives something off by a cross term. `e` absorbs that. Only
its commitment `E` is carried in the instance.

## 3.4 The accumulator

```
acc.x = { pi, C_1, C_2, r, E, μ }        ← instance,  SHORT
acc.w = { (w,m), (h,g) }                 ← witness,   LONG
```

**A NARK proof is already an accumulator** with `μ = 1`, `E = 0` (Remark 2). That
is how the chain gets started.

---

# Part 4 — Commit and Fiat–Shamir

Before folding, two compiler stages run:

**Commit (§3.2).** The prover sends commitments instead of messages:
```
C_1 = Commit(ck, w ‖ m)          C_2 = Commit(ck, h ‖ g)
```
`m` and `g` have length `T` but at most `ℓ` non-zeros, so both cost `O(ℓ)` group
operations — **not** `O(T)`.

**Fiat–Shamir (§3.3).** The lookup challenge `r` *is* the FS challenge:
```
r_0 = ρ_NARK(pi)            r = ρ_NARK(r_0, C_1)
```
This is what makes "the prover must fix `m` before seeing `r`" enforceable, and
therefore what makes the soundness argument of file 20 §6 bite.

---

# Part 5 — The fold, one number at a time

**This is the core of the file.** Everything else is repetition of what happens
here.

## 5.1 The problem, in one line

Folding means `new := old + α·(new proof)`. That works perfectly for anything
**linear**. It breaks for anything with a **product**, because

```
(a + b)·(c + d)  ≠  a·c  +  b·d
```

The leftover is `a·d + b·c`. **That leftover is the error term.** Nothing more.

## 5.2 Watch it happen on a single entry

Fold `acc := π_1` with `π := π_2`. Look only at **entry 1 of check (2)**, i.e.
`h_1·(w_1 + r) = 1`.

Both operands pass it:

```
π_1 :  91 · (1 + 9)  =  91 · 10  =  910  =  9·101 + 1  ≡  1   ✓
π_2 :  29 · (2 + 5)  =  29 ·  7  =  203  =  2·101 + 1  ≡  1   ✓
```

Now fold — but instead of plugging in `α` immediately, use a **symbol `X`**. Every
folded coordinate becomes `old + X·new`:

```
h_1(X) = 91 + 29X          w_1(X) = 1 + 2X
r(X)   =  9 +  5X          μ(X)   = 1 +  1X
```

Multiply out the check:

```
h_1(X)·( w_1(X) + r(X) )  =  (91 + 29X) · (10 + 7X)

                          =  910  +  (637 + 290)·X  +  203·X²

                          =    1  +        18 ·X   +    1·X²      (mod 101)
```

Subtract the relaxed right-hand side `μ(X)² = (1 + X)² = 1 + 2X + X²`:

```
       1  +  18X  +  X²
    − (1  +   2X  +  X²)
    ─────────────────────
       0  +  16X  +  0
```

**Read the coefficients:**

| coeff | value | what it is |
|---|---|---|
| `X⁰` | **0** | the old accumulator's check — it passed, so 0 (`= e'`) |
| `X²` | **0** | the new proof's check — it passed, so 0 (`= V_NARK`) |
| `X¹` | **16** | nobody could predict this. **This is `e_1⁽²⁾_1`.** |

That `16` is the first entry of `e_1⁽²⁾ = [16, 51, 52, 94]`. It is the
cross-multiplication leftover `637 + 290 ≡ 18`, minus the `2` from `(1+X)²`.

## 5.3 Why `μ²` and not just `1`

Keep the original `−1` instead of `−μ²` and redo the subtraction:

```
       1  +  18X  +  X²
    −  1
    ─────────────────────
       0  +  18X  +  X²        ← the X² coefficient is 1, NOT 0
```

The top coefficient is no longer "the new proof's check", so the whole structure
collapses — the prover would have to publish a `d`-th correction too, and the
extractor's argument would fail. **`μ` exists solely so the constant term scales
in step with the quadratic term.** This one line is the entire justification for
the slack variable.

---

# Part 6 — The general formula, and how the example instantiates it

## 6.1 The formula (Figure 3, step 2)

```
Σ_{j=0}^{d} (X + μ)^{d−j} · f_j^{V_sps}( X·pi + pi', [X·m_i + m'_i], [X·r_i + r'_i] )

   =   Σ_{j=0}^{d} μ^{d−j} f_j^{V_sps}(pi', [m'_i], [r'_i])     ←  e'   (old error)
   +   X^d · V_NARK(pi, [m_i], [r_i])                           ←  0    (new proof valid)
   +   Σ_{j=1}^{d−1} e_j X^j                                    ←  PUBLISH THESE
```

Convention: **`X·π + acc`** — the new proof is scaled by `X`, the accumulator is
the constant term.

## 6.2 Why the two outer coefficients are automatic

**Constant term.** Set `X = 0`: the argument becomes `acc`, and `(X+μ)^{d−j}`
becomes `μ'^{d−j}`. The sum is the relaxed check evaluated on the accumulator,
which is `e'` by definition.

**Top term.** `f_j` is homogeneous of degree `j`, so `f_j(X·π + acc)` has leading
coefficient `X^j·f_j(π)`. Multiply by `(X+μ)^{d−j}`, whose leading term is
`X^{d−j}`:

```
X^{d−j} · X^j · f_j(π)  =  X^d · f_j(π)
```

Every `j` lands on `X^d`. Summing over `j`:

```
X^d · Σ_j f_j(π)  =  X^d · V_sps(π)  =  X^d · 0  =  0
```

**This is why homogeneity is a hard requirement.** Without it the degrees don't
line up and the top coefficient isn't `V_NARK`.

Check it against Part 5.2: the `X²` coefficient was `203 − 1 ≡ 1 − 1 = 0`, and the
`203` is literally `π_2`'s own check value `h_1(w_1+r)`.

## 6.3 The formula written out for the lookup, `d = 2`

Substituting the `f_j` table from Part 2.1 and writing `μ(X) = X + μ'`:

```
(1)   μ(X)·( Σh(X) − Σg(X) )                                    = e⁽¹⁾(X)

(2)   h(X) ∘ ( w(X) + r(X)·1 )   −  μ(X)²·1                     = e⁽²⁾(X)

(3)   μ(X)·( g(X)∘t − m(X) )  +  r(X)·g(X)                      = e⁽³⁾(X)
      ≡  g(X) ∘ ( μ(X)·t + r(X)·1 )  −  μ(X)·m(X)
```

These are exactly the three expressions in Appendix B
([07-step4-error-term-algorithms.md](07-step4-error-term-algorithms.md) §"Worked
application"). Since `d = 2`, there is **exactly one** unknown coefficient — `e_1`
— hence `pf = [E_1]`, one commitment per fold.

---

# Part 7 — All the cross terms, computed

Fold `acc = π_1` with `π = π_2`. Reading the `X¹` coefficient of each expression
in 6.3:

## 7.1 Component (1) — always zero

```
X¹ coeff  =  μ'·(Σh − Σg)  +  μ·(Σh' − Σg')
          =   1·(76 − 76)  +   1·(84 − 84)
          =   0
```

Both brackets vanish because **each proof individually** satisfies `Σh = Σg`. And
since `Σacc.h − Σacc.g = acc.e⁽¹⁾/acc.μ`, which IVC initialises to 0, this stays
zero at every future fold. **The log-derivative sum check is free to accumulate,
forever.**

## 7.2 Component (2)

```
e_1⁽²⁾_i  =  h'_i·(w_i + r)  +  h_i·(w'_i + r')  −  2μ'μ
```

| i | `h'_i·(w_i+5)` | `h_i·(w'_i+9)` | sum | `−2` | `e_1⁽²⁾_i` |
|---|---|---|---|---|---|
| 1 | `91·7  = 637 ≡ 31` | `29·10 = 290 ≡ 88` | `119 ≡ 18` | −2 | **16** |
| 2 | `91·5  = 455 ≡ 51` | `81·10 = 810 ≡  2` | `53` | −2 | **51** |
| 3 | `59·7  = 413 ≡  9` | `29·12 = 348 ≡ 45` | `54` | −2 | **52** |
| 4 | `45·8  = 360 ≡ 57` | `38·9  = 342 ≡ 39` | `96` | −2 | **94** |

```
e_1⁽²⁾ = [16, 51, 52, 94]
```

## 7.3 Component (3)

```
e_1⁽³⁾_i  =  g'_i·(μ·t_i + r)  +  g_i·(μ'·t_i + r')  −  μ'·m_i  −  μ·m'_i
```
With `μ = μ' = 1` this is `g'_i·(t_i + r) + g_i·(t_i + r') − m_i − m'_i`:

| i | `g'_i·(t_i+5)` | `g_i·(t_i+9)` | `−m_i −m'_i` | `e_1⁽³⁾_i` |
|---|---|---|---|---|
| 1 | `45·5 = 225 ≡ 23` | `81·9  = 729 ≡ 22` | `−1 −1` | **43** |
| 2 | `81·6 = 486 ≡ 82` | `0·10  =   0` | `−0 −2` | **80** |
| 3 | `0·7  =   0` | `58·11 = 638 ≡ 32` | `−2 −0` | **30** |
| 4 | `59·8 = 472 ≡ 68` | `38·12 = 456 ≡ 52` | `−1 −1` | `118 ≡` **17** |

```
e_1⁽³⁾ = [43, 80, 30, 17]
```

**Cross-check by the polynomial method** (entry 1, `t_1 = 0`):
```
g_1(X) = 45 + 81X          μ(X)·t_1 + r(X) = 0 + (9 + 5X) = 9 + 5X
μ(X)·m_1(X) = (1+X)(1+X)   = 1 + 2X + X²

(45 + 81X)(9 + 5X) = 405 + 954X + 405X² ≡ 1 + 45X + X²

     (1 + 45X + X²) − (1 + 2X + X²)  =  43X        ✓  matches the table
```

---

# Part 8 — Applying the fold

## 8.1 The prover's moves (Figure 3, steps 3–9)

```
3.  E_1 ← Commit(ck, e_1)
4.  α   ← ρ_acc(acc.x, pi, π.x, [E_1])            (here: α = 3)
6.  v'' ← α·v + v'                                 (one linear combination)
7.  E'' ← E' + α·E_1
9.  pf  := [E_1]
```

## 8.2 Every coordinate, with `α = 3`

```
μ''  =  1 + 3·1  =  4
r''  =  9 + 3·5  =  24

w''  =  [1,1,3,0]     + 3·[2,0,2,3]     =  [1+6, 1+0, 3+6, 0+9]  =  [ 7,  1,  9,  9]
m''  =  [1,2,0,1]     + 3·[1,0,2,1]     =  [1+3, 2+0, 0+6, 1+3]  =  [ 4,  2,  6,  4]
h''  =  [91,91,59,45] + 3·[29,81,29,38] =  [178, 334, 146, 159]  ≡  [77, 31, 45, 58]
g''  =  [45,81,0,59]  + 3·[81,0,58,38]  =  [288,  81, 174, 173]  ≡  [86, 81, 73, 72]
```

## 8.3 The new error is the same polynomial at `X = α`

```
e''  =  e'  +  α·e_1  +  α²·0   =   3·e_1

e''⁽¹⁾ = 0
e''⁽²⁾ = 3·[16,51,52,94] = [48, 153, 156, 282] ≡ [48, 52, 55, 80]
e''⁽³⁾ = 3·[43,80,30,17] = [129, 240,  90,  51] ≡ [28, 38, 90, 51]
```

## 8.4 Verify the folded accumulator from scratch

Run the relaxed predicate of Part 3.1 on `acc_2` and compare:

```
(1)  μ''·(Σh'' − Σg'')       Σh'' = 77+31+45+58 = 211 ≡ 9
                             Σg'' = 86+81+73+72 = 312 ≡ 9
                             4·(9−9) = 0            = e''⁽¹⁾   ✓

(2)  h''∘(w'' + r''·1) − μ''²
     entry 1:  77·(7+24) − 16 = 77·31 − 16 = 2387 − 16 ≡ 64 − 16 = 48
                             [48,52,55,80]          = e''⁽²⁾   ✓

(3)  g''∘(μ''·t + r''·1) − μ''·m''
     entry 1:  86·(4·0+24) − 4·4 = 86·24 − 16 = 2064 − 16 ≡ 44 − 16 = 28
                             [28,38,90,51]          = e''⁽³⁾   ✓
```

## 8.5 What the folded object actually is

```
acc_2 :  μ = 4    r = 24    w = [7,1,9,9]    m = [4,2,6,4]
                            h = [77,31,45,58]  g = [86,81,73,72]
```

Look at `w'' = [7,1,9,9]`. **Not one of those values is in `t = [0,1,2,3]`.**
`h''_1·(w''_1+r'') = 64`, not `1`. The accumulator asserts **no lookup statement
at all** — it is a relaxed object whose validity, via Theorem 2's extractor,
implies both originals were valid. That is the conceptual heart of folding: you
stop proving the statement and start proving *a thing from which the statement can
be extracted*.

---

# Part 9 — Three instances: the chain

## 9.1 The shape

**The folding arity is always 2.** Never 3 at once — `P_acc` step 6 is literally
`v'' := α·v + v'`, a two-term combination
([14-how-many-instances-do-we-fold.md](14-how-many-instances-do-we-fold.md)).

With 3 instances you do **2 folds, sequentially**:

```
π_1  ─────────► acc_1                 bootstrap: a proof IS an accumulator (μ=1, E=0)
                 │
        π_2 ─────┤ α_1 = 3            fold #1 :  acc_2 := acc_1 + α_1·π_2
                 ▼
               acc_2
                 │
        π_3 ─────┤ α_2 = 7            fold #2 :  acc_3 := acc_2 + α_2·π_3
                 ▼
               acc_3
```

There is **no "fold 1 then 3"**. In IVC the order is forced: `π_2` does not exist
until step 2 has run, and the accumulator is what step 2 carries forward.

> **PCD variant.** Protostar also folds accumulator+accumulator (Remark 2), so a
> tree is possible: `(π_1,π_2) → A`, `(π_3,π_4) → B`, then `A + B`. With an odd
> count you still end with a chain step. Either way every node is **binary** —
> this is why the paper only claims PCD for *DAGs of degree two*.

## 9.2 Fold #2 in full — the general case

Fold #1 had two `μ = 1` operands. Fold #2 is the real thing: the left operand now
has `μ = 4` and **non-zero error**.

```
acc_2 :  μ = 4   r = 24   w=[7,1,9,9]      m=[4,2,6,4]
                          h=[77,31,45,58]  g=[86,81,73,72]
                          e⁽²⁾=[48,52,55,80]   e⁽³⁾=[28,38,90,51]

π_3   :  μ = 1   r = 11   w=[3,3,1,2]      m=[0,1,1,2]
                          h=[65,65,59,70]  g=[0,59,70,29]
```

Cross terms (same formulas, now with `μ' = 4`):

```
e_1⁽¹⁾ = 0
e_1⁽²⁾ = [55, 31, 55, 26]
e_1⁽³⁾ = [33, 93, 48, 20]
```

Fold with `α_2 = 7`:

```
acc_3 :  μ = 7·1 + 4 = 11        r = 7·11 + 24 = 101 ≡ 0
         w = [28,22,16,23]       m = [4,9,13,18]
         h = [27,82,54,43]       g = [86,90,58,73]
         e⁽²⁾ = e⁽²⁾_2 + 7·[55,31,55,26] = [29,67,36,60]
         e⁽³⁾ = e⁽³⁾_2 + 7·[33,93,48,20] = [57,83,22,90]
```

Decider on `acc_3` — all three families check out:

```
μ·(Σh − Σg)       = 11·(Σh − Σg) = 0        = e⁽¹⁾   ✓
h∘(w + r) − μ²    = [29,67,36,60]           = e⁽²⁾   ✓
g∘(μt + r) − μ·m  = [57,83,22,90]           = e⁽³⁾   ✓
```

Note `r'' = 0` after fold #2. A folded challenge is just a field element — it is
no longer any hash of anything, and `V_acc` only checks that it equals
`α·r + r'`.

## 9.3 What changed across the chain

| | `acc_1` | `acc_2` | `acc_3` |
|---|---|---|---|
| `μ` | 1 | 4 | 11 |
| `r` | 9 | 24 | 0 |
| `e⁽¹⁾` | 0 | 0 | **0** — always |
| `e⁽²⁾` | `[0,0,0,0]` | `[48,52,55,80]` | `[29,67,36,60]` |
| `m` sparsity | 3/4 non-zero | 4/4 | 4/4 — **dense** |
| cost of the fold | — | `O(ℓ)` | `O(ℓ)` |

The table `t = [0,1,2,3]` is **identical at every step**. Three instances, three
different challenges `r_i`, one shared table, never folded.

---

# Part 10 — Why none of this depends on `T`

## 10.1 The problem

Look at the `m` row in 9.3: after two folds, `acc.m = [4,9,13,18]` and
`acc.g = [86,90,58,73]` are **fully dense**. A fresh proof's `m` and `g` are
`ℓ`-sparse, but the accumulator's are not. With a `2^16`-row table, touching
`acc.g` would cost `2^16` per folding step, destroying the entire point.

## 10.2 The escape

The prover never needs the error **vector** `e_1⁽³⁾ ∈ F^T` — only its
**commitment**. And because `μ'`, `r`, `r'` are scalars, that commitment is a
**linear** function of six commitments:

```
E_1⁽³⁾  =  GT'  +  π.r·G'  +  acc.μ·GT  +  acc.r·G  −  acc.μ·M  −  M'

    G  = Commit(π.g)        G'  = Commit(acc.g)
    M  = Commit(π.m)        M'  = Commit(acc.m)
    GT = Commit(π.g ∘ t)    GT' = Commit(acc.g ∘ t)
```

`G`, `M`, `GT` commit to **`ℓ`-sparse** vectors → `O(ℓ)`.
`G'`, `M'`, `GT'` are **cached** and updated in place, never recomputed:

```
G' ← G' + α·G          M' ← M' + α·M          GT' ← GT' + α·GT
```

## 10.3 Verified numerically

Toy linear commitment `ck = (1,2,3,4)`, `Commit(x) = Σ i·x_i mod 101` (the
stand-in from [19-page20-walkthrough.md](19-page20-walkthrough.md) — homomorphic
but not binding).

**Fold #1:**
```
cached (from π_1):   G' = 39     M' =  9     GT' = 62
fresh  (from π_2):   G  =  3     M  = 11     GT  = 97          α = 3

E_1⁽³⁾ = 62 + 5·39 + 1·97 + 9·3 − 1·11 − 9  =  361 ≡ 58
direct : Commit([43,80,30,17]) = 43+160+90+68 = 361 ≡ 58        ✓ identical

cache update →  G' = 48    M' = 42    GT' = 50
```

**Fold #2:**
```
fresh  (from π_3):   G  = 40     M  = 13     GT  = 78          α = 7

E_1⁽³⁾ = 50 + 11·48 + 4·78 + 24·40 − 4·13 − 42  =  1756 ≡ 39
direct : Commit([33,93,48,20]) = 33+186+144+80 =   443 ≡ 39     ✓ identical

cache update →  G' = 25    M' = 32    GT' = 91
```

**The cache is exact:**
```
Commit(acc_3.g)     = Commit([86,90,58,73])  = 25    = G'    ✓
Commit(acc_3.m)     = Commit([4,9,13,18])    = 32    = M'    ✓
Commit(acc_3.g ∘ t) = 91                             = GT'   ✓
```

The prover tracked three dense length-`T` vectors through two folds **without ever
reading one**, paying only `O(ℓ)` per step. This is the paper's claim
"independent of the table size in the lookup", and §4.3's "most efficient lookup
protocol today".

---

# Part 11 — Where this sits in real Protostar

## 11.1 Inside `Π_mplkup`

In the assembled protocol
([09-protostar-and-ccs.md](09-protostar-and-ccs.md)) the lookup is round 3 of a
3-move protocol, with two changes:

* `m` is sent in the **first** message, alongside the branch selector `b` and the
  sparse witness `w̃`;
* the per-lookup check becomes branch-selected:
  `Σ_j b_j · h_i · (w^{(j)}_{L_j[i]} + r) = 1`, pushing the verifier degree from
  `d` to `d+1` — the same `+1` every check pays for non-uniformity.

`Π_mplkup` is `2(T + lk)`-special-sound (Lemma 8), and that `(T+lk)` comes
**entirely** from the lookup round — Lemma 5's degree-`(ℓ+T−1)` polynomial
argument, unchanged.

## 11.2 The one place it conflicts with `CV`

`CV[·]` (§3.5) compresses many verifier equations into one so error terms become
scalars. The paper states it is **not composable** with the sparse-lookup
optimisation of Part 10. So Protostar applies `CV` **only to the gate part**:

```
 n   +   lk + T + c·n
 ↑       └──────┬────┘
deg d         deg ≤ 2
CV here       CV must NOT touch these — Part 10 depends on it
```

See [06-step3-cv-compression.md](06-step3-cv-compression.md) §"Scope check".

## 11.3 The bottom line

Corollary 1's recursive-circuit row is `3G`, `d+4` field ops, `d+O(1)` hashes.
**It contains no `T` and no `lk`.** Adding lookups to Protostar costs the IVC
verifier nothing, and costs the folding prover `O(lk)` per step.

---

# Part 12 — The whole thing in one page

```
1.  Write the dumbest protocol for the statement.          Π_LK: send (w,m), get r, send (h,g)

2.  Count k, d, and decompose V into homogeneous f_j.      k=2, d=2
                                                           f_0 = −1
                                                           f_1 = Σh−Σg,  g∘t − m
                                                           f_2 = h∘(w+r), r·g

3.  Relax it with a slack variable μ and an error e.       h∘(w+r) − μ²   = e⁽²⁾
                                                           g∘(μt+r) − μm  = e⁽³⁾

4.  To fold, substitute old + X·new and expand.            (91+29X)(10+7X) − (1+X)²
                                                             = 0 + 16X + 0

5.  X⁰ coefficient  = old error       (known)
    X^d coefficient = new proof check (zero, by homogeneity)
    middle coefficients = e_1 … e_{d−1}     ← PUBLISH.     d=2 ⟹ exactly one: e_1

6.  Commit them, hash for α, take ONE linear combination.  α = 3
    acc'' = acc + α·π,   e'' = e' + α·e_1                  μ''=4, e''⁽²⁾=[48,52,55,80]

7.  For n instances, repeat step 6 n−1 times, in a chain.  3 instances → 2 folds

8.  Never touch the dense accumulator: keep 3 cached
    commitments and update them homomorphically.           G' ← G' + α·G   ⟹  O(ℓ), not O(T)
```

**The one sentence:** replace `α` with a symbol `X`, multiply out the check, and
you get a polynomial whose bottom coefficient is the old error, whose top
coefficient is zero, and whose middle coefficients are the only thing the prover
has to publish.

---

## Related files

* [20-lookup-tables-explained.md](20-lookup-tables-explained.md) — the lookup
  argument itself: logUp, honest and cheating provers, vector lookups.
* [08-subprotocols.md](08-subprotocols.md) — `Π_LK` beside the other building
  blocks; Lemma 5.
* [05-step2-accumulation-scheme.md](05-step2-accumulation-scheme.md) — the generic
  accumulation scheme this file instantiates.
* [07-step4-error-term-algorithms.md](07-step4-error-term-algorithms.md) —
  Appendix B, the general sparse-witness algorithm behind Part 10.
* [19-page20-walkthrough.md](19-page20-walkthrough.md) — the same style applied to
  the R1CS/Hadamard case, with the toy commitment.
