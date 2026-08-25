# 14 — How Many Instances Do We Fold? Step by Step, With Numbers

Companion to [05-step2-accumulation-scheme.md](05-step2-accumulation-scheme.md).
This file exists to settle one question completely, because the notation
invites exactly one misreading.

## The question

The relaxed verifier check is

```
V_sps^relaxed(pi, π.x, π.w, [r_i], μ)  :=  Σ_{j=0}^{d}  μ^{d−j} · f_j^{V_sps}(pi, π.w, [r_i])  =  e
```

There is a `Σ` running to `d`. Does that mean we fold `d` instances?

## The answer

**No. We fold exactly 2. Always.**

The `Σ_{j=0}^{d}` is **not** a sum over instances. It is the decomposition of
**one** verifier equation into its homogeneous degree components. `f_0` is the
constant part, `f_1` the linear part, `f_2` the quadratic part, … `f_d` the
degree-`d` part. It is one equation, sliced by degree.

| Symbol | What it ranges over | Not |
|---|---|---|
| `j = 0 … d` in `Σ μ^{d−j} f_j` | degree slices of **one** equation | instances |
| `i = 1 … k` in `[m_i]`, `[C_i]` | rounds of the protocol | instances |
| `i = 1 … ℓ` (the output length) | parallel equations checked | instances |
| the fold itself | **2 objects** | — |

Three different indices, none of them counting operands.

---

## Part 1 — What objects exist, before any folding

Two, and only ever two at a time:

**Object A — the new NARK proof `π`.** A fresh proof for this IVC step.
By Remark 2 it is *already* an accumulator, just a trivial one:

```
π  ≡  accumulator with   μ = 1   and   E = 0
```

**Object B — the running accumulator `acc`.** Carries everything folded so far.
Has non-trivial `μ'` and `E'`.

Both have the identical shape, which is why one folding routine handles
proof+accumulator, accumulator+accumulator, or proof+proof:

```
instance:  { pi, [C_i]_{i∈[k]}, [r_i]_{i∈[k−1]}, E, μ }
witness:   { [m_i]_{i∈[k]} }
```

---

## Part 2 — One fold, step by step (Figure 3), with the operand count annotated

```
STEP 1.  Recompute the challenges  r_i ← ρ_NARK(r_{i−1}, C_i)
         ................................................ operands touched: 1 (π)

STEP 2.  Form the polynomial identity in a formal variable X:

           Σ_{j=0}^{d} (X + μ')^{d−j} · f_j( X·π + acc )
             =  e'  +  Σ_{j=1}^{d−1} e_j X^j  +  X^d · V_NARK(π)

         Read off the d−1 middle coefficients e_1 … e_{d−1}.
         ................................................ operands: 2 (π and acc)
         NOTE: "X·π + acc" is a TWO-TERM linear combination.
               There is no third object anywhere in this expression.

STEP 3.  E_j ← Commit(ck, e_j)   for j ∈ [d−1]
         ................................................ d−1 commitments

STEP 4.  α ← ρ_acc(acc.x, pi, π.x, [E_j])
         ................................................ ONE challenge

STEP 5.  v  := ( 1,  pi,  [r_i], [C_i], [m_i] )      <- object A (π), μ = 1
         v' := ( μ', pi', [r'_i],[C'_i],[m'_i])      <- object B (acc)
         ................................................ TWO vectors

STEP 6.  v'' := α · v + v'
         ................................................ TWO operands, ONE α

STEP 7.  E'' := E' + Σ_{j=1}^{d−1} α^j · E_j
         ................................................ error bookkeeping
```

**Step 6 is the fold.** `α · v + v'`. Two terms. That is the entire folding
operation in the paper.

Everything indexed by `d` (steps 2, 3, 7) is *correction bookkeeping* for having
folded two things through a degree-`d` equation — not additional operands.

---

## Part 3 — Why `d−1` corrections appear when folding only 2 things

First, the role of `μ`. The vector `v` starts with `1` and `v'` starts with `μ'` —
so **`μ` is itself a coordinate that gets folded**. Once `μ` is inside the vector,

```
Σ_{j=0}^{d} μ^{d−j} · f_j(pi, w, [r_i])
```

is a **single homogeneous form of degree exactly `d`** in the extended vector
`(μ, pi, [r_i], [m_i])`. Each `f_j` has degree `j`; multiplying by `μ^{d−j}` tops
every term up to exactly `d`. **That is the only reason `μ` exists.**

Now feed a two-term combination into a homogeneous degree-`d` form:

```
f( X·v + v' )   =   a degree-d polynomial in X   =   d+1 coefficients
```

and the coefficients land as:

```
  X^d      ->  f(v)     = the NEW proof's check         known: = 0
  X^0      ->  f(v')    = the OLD accumulator's check   known: = e'
  X^1 … X^{d−1}  ->  e_1 … e_{d−1}    <- NOT known to the verifier: PUBLISH THEM
```

`d+1` coefficients, `2` of which are already known, leaving **`d−1` cross terms**.
Plain binomial expansion of a 2-term sum. Nothing to do with operand count.

---

## Part 4 — Fully worked numeric example, `d = 2`

Field `F_101`. Relation: the Hadamard/R1CS check `a ∘ b = c` with vectors of
length 2.

Homogeneous decomposition — `f_2(w) = a ∘ b`, `f_1(w) = −c`, `f_0 = 0` — so the
relaxed check is

```
μ²·0  +  μ·(−c)  +  (a ∘ b)   =   a ∘ b − μ·c   =   e
```

which is exactly **Nova's relaxed R1CS** `Az ∘ Bz = μ·Cz + e`. Good anchor: the
generic machinery reproduces the known scheme at `d = 2`.

### The two objects

**Object A — fresh proof `π`** (so `μ = 1`, `e = 0`):

```
a = (2, 3)      b = (4, 5)      c = (8, 15)      μ = 1
check:  2·4 = 8 ✓     3·5 = 15 ✓        so  a∘b − 1·c = (0,0) = e ✓
```

**Object B — running accumulator `acc`** (mid-chain, so `μ' ≠ 1`, `e' ≠ 0`):

```
a' = (1, 2)     b' = (3, 1)     c' = (5, 7)      μ' = 2

e' = a'∘b' − μ'·c'
   = (1·3, 2·1) − 2·(5, 7)
   = (3, 2) − (10, 14)
   = (−7, −12)
   = (94, 89)        mod 101
```

### Step 2 — the one cross term (`d − 1 = 1`)

```
e_1 = a∘b' + a'∘b − μ'·c − c'

  a∘b'  = (2·3, 3·1) = (6, 3)
  a'∘b  = (1·4, 2·5) = (4, 10)
  μ'·c  = 2·(8, 15)  = (16, 30)
  c'                 = (5, 7)

e_1 = (6 + 4 − 16 − 5,  3 + 10 − 30 − 7)
    = (−11, −24)
    = (90, 77)        mod 101
```

The prover commits `E_1 = Commit(ck, e_1)` and publishes `pf = [E_1]`.
**One** commitment, because `d − 1 = 1`.

### Steps 4–7 — the fold, with `α = 7`

```
μ'' = α + μ'        = 7 + 2                    = 9
a'' = α·a + a'      = 7·(2,3) + (1,2)          = (15, 23)
b'' = α·b + b'      = 7·(4,5) + (3,1)          = (31, 36)
c'' = α·c + c'      = 7·(8,15) + (5,7)         = (61, 112) = (61, 11)   mod 101
e'' = e' + α·e_1    = (94,89) + 7·(90,77)      = (724, 628) = (17, 22)  mod 101
E'' = E' + α·E_1                               (by commitment homomorphism)
```

### Verification — does the decider accept `acc''`?

The decider recomputes `a'' ∘ b'' − μ''·c''` and compares to `e''`:

```
a'' ∘ b''  = (15·31, 23·36) = (465, 828)  = (61, 20)   mod 101
μ''·c''    = 9·(61, 11)     = (549, 99)   = (44, 99)   mod 101

a''∘b'' − μ''·c''  = (61 − 44, 20 − 99) = (17, −79) = (17, 22)   mod 101
```

and `e'' = (17, 22)`. ✓ **They match.**

Cross-check by the polynomial route — evaluate the Step-2 identity at `X = α = 7`:

```
X²·(a∘b − c) + X·e_1 + e'  =  49·(0,0) + 7·(90,77) + (94,89)
                           =  (724, 628)  =  (17, 22)   ✓
```

Both routes agree.

### Operand tally for this fold

| Quantity | Count |
|---|---|
| objects folded | **2** (`π`, `acc`) |
| challenges sampled | **1** (`α = 7`) |
| linear combinations performed | **1** (`α·v + v'`) |
| cross terms published | **1** (`= d − 1`) |
| group commitments in `pf` | **1** |

At no point were 3 or more objects combined.

---

## Part 5 — Same thing at `d = 3`: still 2 objects, now 2 corrections

Field `F_101`, scalars for brevity. Relation `x³ = y`.
Decomposition `f_3 = x³`, `f_1 = −y`, so the relaxed check is `x³ − μ²·y = e`.

### The two objects

```
Object A (proof π):        x = 2,   y = 8,   μ = 1
                           check: 2³ = 8 ✓,  e = 8 − 1·8 = 0 ✓

Object B (accumulator):    x' = 3,  y' = 5,  μ' = 2
                           e' = 3³ − 2²·5 = 27 − 20 = 7
```

### Expansion — now `d − 1 = 2` cross terms

```
(X·x + x')³  −  (X + μ')²·(X·y + y')

  X³ :  x³ − y                    = 8 − 8            = 0     (new proof)  ✓
  X² :  3x²x' − y' − 2μ'y         = 36 − 5 − 32      = −1 = 100   -> e_2
  X¹ :  3x x'² − 2μ'y' − μ'²y     = 54 − 20 − 32     = 2          -> e_1
  X⁰ :  x'³ − μ'²y'               = 27 − 20          = 7     (old acc = e') ✓
```

So `pf = [E_1, E_2]` — **two** correction terms, because `d − 1 = 2`.

### The fold, `α = 5`

```
x''  = 5·2 + 3   = 13
y''  = 5·8 + 5   = 45
μ''  = 5 + 2     = 7
e''  = e' + α·e_1 + α²·e_2  = 7 + 5·2 + 25·100 = 2517 = 93   mod 101
```

### Verification

```
x''³      = 13³   = 2197  = 76        mod 101
μ''²·y''  = 49·45 = 2205  = 84        mod 101

x''³ − μ''²·y''  = 76 − 84 = −8 = 93   mod 101
```

and `e'' = 93`. ✓

### Tally

| Quantity | `d = 2` | `d = 3` |
|---|---|---|
| objects folded | 2 | **2** |
| challenges `α` | 1 | **1** |
| linear combinations | 1 | **1** |
| cross terms `e_j` | 1 | **2** |

Raising `d` buys **more corrections**, never more operands. And those `d−1`
corrections are `d−1` group operations in the recursive circuit — which is exactly
what the `CV` transform of §3.5 exists to eliminate
(see [06-step3-cv-compression.md](06-step3-cv-compression.md)).

---

## Part 6 — The three different `d`'s, kept apart

| `d` appears as | What it counts | Where |
|---|---|---|
| `μ^{d−j}` | homogenisation exponent — tops each `f_j` up to degree `d` | relaxed check |
| `e_1 … e_{d−1}` | cross terms the prover publishes in `pf` | Fig. 3 steps 2–3, 7 |
| `d+1` transcripts | what the **extractor** needs under rewinding | Theorem 2 proof |

The third is the most common misread. `Π_I` is `(d+1)`-special-sound because
`p(X)` has degree `d`, so the *extractor* needs `d+1` accepting transcripts with
distinct `α` to conclude `p ≡ 0`. **An honest execution produces one transcript
with one `α`.** `d+1` is a property of the security proof, not of the protocol.

---

## Part 6b — "Is it `ℓ`, then?" Also no.

**Protostar folds 2 instances. Not `d`, and not `ℓ`.**

### `ℓ` is not a count of instances — it is a count of *equations inside one instance*

An **instance** is one proof: one IVC step's worth of data, containing `k` prover
messages, `k−1` challenges, and whose verifier checks `ℓ` equations.

`ℓ` lives **inside** a single instance. It is the *width* of one instance, not a
number of instances.

```
                    ONE instance
   ┌────────────────────────────────────────────────┐
   │  messages [m_1..m_k]   challenges [r_1..r_{k−1}] │
   │  verifier checks:  eq_1, eq_2, …, eq_ℓ           │   <- ℓ is HERE, inside
   └────────────────────────────────────────────────┘

   folding:      instance  +  instance   ──►  instance
                     2 objects in,  1 out
```

Spreadsheet analogy: `ℓ` is how many **columns** a row has. Folding adds two
**rows** together. Widening the sheet does not change the fact that you are adding
two rows.

### Concretely, in the file-16 example

| Quantity | What it counts | Value |
|---|---|---|
| **instances folded per step** | **objects** | **2** |
| `ℓ` (gate part) | equations inside one instance | 9 |
| `ℓ` (all checks) | equations inside one instance | 15 |
| `v` | coordinates in one table row | 2 |
| `d` | degree of the verifier | 3 |
| `k` | prover messages | 3 |
| `T` | table rows | 2 |

Nine gate equations, two folded objects. The `9` and the `2` are unrelated
numbers describing different things.

### Where `ℓ` *does* appear as "how many things get combined"

`ℓ` **is** a combination count — but for `γ`, not for `α`:

```
γ  (§3.5)  combines  ℓ = 9  EQUATIONS   ->  1 equation
α  (§3.4)  combines      2  INSTANCES   ->  1 instance
```

That is the whole source of the confusion: both are random linear combinations,
so both use powers of a challenge, and `ℓ` is genuinely a combination count — just
for the *other* one. See [16-one-example-all-four-challenges.md](16-one-example-all-four-challenges.md).

### Over `m` IVC steps, do we fold `m` instances?

No — **`m−1` pairwise folds, sequentially, 2 at a time**:

```
 acc_0 ─┐
        ├─ fold(α_1) ─► acc_1 ─┐
 π_1 ───┘                      ├─ fold(α_2) ─► acc_2 ─┐
                        π_2 ───┘                      ├─ fold(α_3) ─► acc_3 ─► …
                                               π_3 ───┘
```

Always **2 in, 1 out**. There is never a moment where 3 or more objects are
combined.

### The property that makes this work: the accumulator never grows

This is why folding 2-at-a-time is not a limitation:

```
acc_1 :  ℓ = 9 equations,  k messages,  1 error term
acc_2 :  ℓ = 9 equations,  k messages,  1 error term     <- same size
acc_99:  ℓ = 9 equations,  k messages,  1 error term     <- still the same size
```

Folding two instances of shape `S` produces **one instance of shape `S`**. The
equation count `ℓ`, the message count `k`, and the accumulator size are all
invariant under folding. That is precisely the IVC efficiency requirement of
Def. 7 — "the size of `π_IVC` … [is] independent of the number of iterations."

If folding grew `ℓ`, IVC would be impossible: after `m` steps the accumulator
would be `m` times too big, and the recursive circuit with it.

### "So: 2 instances, each of width `ℓ`?" — Yes, with one important refinement

Correct as far as it goes: **both** folded objects are measured by the **same**
`ℓ`-equation verifier, so both carry an `ℓ`-wide error vector.

The refinement: **`ℓ` is the width of the verifier's OUTPUT (the error vector) —
not the size of the instance that enters the recursive circuit.** Those are
different objects, and the gap between them is the entire efficiency story.

Using the file-16 instance (`ℓ = 15`, `k = 3`, `d = 3`):

```
                     π  (new proof)              acc  (accumulator)
  ─────────────────────────────────────────────────────────────────────
  μ                  1                           μ'   (≠ 1)
  error vector e     (0,0,…,0) ∈ F^15            e' ∈ F^15, generally ≠ 0     <- ℓ-wide
  E                  0  (identity)               E' = Commit(e')              <- ONE group elt
  commitments        C_1, C_2, C_3               C'_1, C'_2, C'_3
  challenges         β, r                        β', r'
  messages           m_1, m_2, m_3               m'_1, m'_2, m'_3             <- long
```

So each object is associated with a 15-wide error vector — but **stores** only its
**commitment** `E`, a single group element.

### What the fold actually touches

```
  μ''   = α·1  + μ'                                        1 field op
  β''   = α·β  + β'                                        1 field op
  r''   = α·r  + r'                                        1 field op
  C''_i = α·C_i + C'_i        (i = 1,2,3)                  3 group ops
  E''   = E' + α·E_1 + α²·E_2   (d−1 = 2 cross terms)      2 group ops
  ─────────────────────────────────────────────────────────────────────
  m''_i = α·m_i + m'_i        <- PROVER ONLY, native, never in the circuit
```

**Nowhere does the recursive circuit fold 15 coordinates.** The `ℓ`-wide vector
`e` is compressed into one group element `E` *before* it ever reaches the circuit,
and folding `E` costs one group operation regardless of whether `ℓ` is 15 or
15 million.

That is precisely the splitting-accumulation idea from report 04 stage 1 — the
`.x` / `.w` split — and it is why Theorem 1's requirement that `V_acc` be
"sublinear in its input" is satisfiable at all.

### Where the `ℓ`-wide arithmetic *does* happen

| Who | Touches the full `F^ℓ` vector? | Cost |
|---|---|---|
| `P_acc` (native prover) | **yes** — computes `e_1, e_2 ∈ F^15` | `L(V_sps, d)` |
| `V_acc` (recursive circuit) | **no** — only `E`, one group element | `k + d − 1` group ops |
| `D` (decider, runs once at the end) | **yes** — recomputes `e''` and checks `E'' = Commit(e'')` | linear in `Σ\|m_i\|` |

The middle row is the one that compounds across IVC steps, and it is `ℓ`-free.
`CV` (report 06) then shrinks even the *prover's* `ℓ`-wide work for the
high-degree part, by collapsing those equations to 1.

### One-line answer

> **Yes: 2 instances, both measured against the same `ℓ`-equation verifier
> (`ℓ = 15` in file 16, of which 9 are gate equations). But `ℓ` is the width of the
> committed error vector, not the size of the folded instance — the recursive
> circuit folds one group element `E`, never `ℓ` coordinates. Protostar folds 2,
> always, and the folded result has the same `ℓ` as its inputs.**

---

## Part 7 — The structural proof that the arity really is 2

If this scheme could fold `n` objects at once, full PCD would follow immediately,
since accumulation schemes compile to PCD when they accumulate an arbitrary number
of accumulators and proofs. It does not. From §2.5:

> "For simplicity, we only build accumulation for one proof and one accumulator,
> as well as for two accumulators. This enables PCD for **DAGs of degree two**.
> By transforming higher degree graphs into degree two graphs (by converting each
> degree `d` node into a `log₂(d)` depth tree), we can achieve PCD for these
> graphs."

A degree-`d` DAG node has to be rewritten as a `log₂(d)`-depth **binary** tree of
pairwise folds. If `d`-ary folding were available, that rewriting would be
unnecessary. This is decisive.

(Note the unfortunate notation collision in that quotation: the `d` in "degree `d`
node" is the DAG out-degree, unrelated to the verifier degree `d`.)

---

## Part 8 — Misreading checklist

| Misreading | Correct |
|---|---|
| "`Σ_{j=0}^{d}` sums over `d` instances" | It sums the `d+1` homogeneous **degree slices** of one equation |
| "we fold `d` accumulators" | We fold **2** objects |
| "we need `d+1` proofs to accumulate" | `d+1` transcripts is the **extractor's** rewinding requirement |
| "`d−1` error terms means `d−1` operands" | `d−1` is the count of **middle binomial coefficients** |
| "`k` in `[C_i]_{i∈[k]}` counts instances" | `k` counts **protocol rounds** (prover messages) |
| "`ℓ` counts instances" | `ℓ` counts **parallel equations** the verifier checks |
| "a NARK proof and an accumulator are different types" | Same type. A proof is an accumulator with `μ = 1`, `E = 0` (Remark 2) |

---

## One-line summary

**Fold arity = 2. One challenge `α`. One linear combination `α·v + v'`. The degree
`d` only determines how many `e_j` corrections that single 2-way fold has to
publish: `d − 1` of them.**
