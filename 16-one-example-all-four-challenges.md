# 16 — One Example, All Four Challenges: `β`, `r`, `γ`, `α`

Files 14 and 15 each isolated one challenge. This file runs **a single concrete
IVC step** end to end, so you can see exactly where each of the four challenges
enters, what it combines, and why the counts differ.

Everything is in **`F_101`**. Every number below is checked.

---

## The instance

**One IVC step proving two things at once:**

1. **9 cube gates** (degree `d = 3`): `x_i³ = y_i` for `i ∈ [9]`
2. **1 vector lookup** (`v = 2`, table size `T = 2`): the pair `(x_1, y_1)` is a
   row of a preprocessed table

Witness:

```
i :     1    2    3    4    5    6    7    8    9
x_i:    2    3    4    5    1    1    1    1    1
y_i:    8   27   64   24    1    1    1    1    1        (y_4 = 5³ = 125 = 24 mod 101)
```

Table (2 columns, 2 rows):

```
t_1 = (2, 8)          t_2 = (3, 27)
```

Lookup: `w_1 = (x_1, y_1) = (2, 8)` — should be found at row 1.

**Verifier's equations, and which challenge handles which:**

```
 9 gate checks         x_i³ − y_i = 0            deg 3   -> compressed by γ
 1 sum check           Σ h = Σ g                 deg 1   -> uses r
 1 lookup check        h_1·(w_1(β)+r) = 1        deg 3   -> uses β and r
 2 table checks        g_i·(t_i(β)+r) = m_i      deg 2   -> uses β and r
 2 β-consistency       β_1 = 1,  β_2 = β_1·β     deg 2
 ─────────────────────────────────────────────
 ℓ = 15 equations total,  max degree d = 3
```

Then the whole proof gets folded with the running accumulator — that is `α`.

---

## What exactly *are* the `ℓ` equations? All 15, written out

`ℓ` is defined in §3.1 as the verifier's **output length**: `V_sps` is an algebraic
map that outputs a **vector of `ℓ` field elements**, and the verifier accepts iff
that vector is **all zeros**.

So `ℓ` = *how many scalar "= 0" checks there are*.

### First, what "an equation" means here

An **equation** is just **one arithmetic expression that must come out to zero**.
Nothing more exotic than that.

Toy warm-up. Suppose the claim is *"I know `x, y` with `x² = 9` and `x + y = 5`."*
Rewrite each claim as "something = 0":

```
eq_1 :  x² − 9      = 0
eq_2 :  x + y − 5   = 0
```

That is `ℓ = 2`. The verifier is the map

```
V(x, y)  =  ( x² − 9 ,  x + y − 5 )   ∈  F²
```

and it **accepts iff the output vector is all zeros**:

```
witness x=3, y=2  ->  (9−9, 3+2−5) = (0, 0)   ACCEPT ✓
witness x=3, y=7  ->  (9−9, 3+7−5) = (0, 5)   REJECT — entry 2 is not zero ✗
```

`ℓ` = how many entries that output vector has. That's it. Now the same thing with
15 entries instead of 2.

### All 15 equations of this instance, in one table

Recall the data: `x = (2,3,4,5,1,1,1,1,1)`, `y = (8,27,64,24,1,1,1,1,1)`,
`t_1 = (2,8)`, `t_2 = (3,27)`, `m = (1,0)`, `β = 4` (`β_1=1, β_2=4`), `r = 3`,
`h_1 = 71`, `g = (71, 0)`.

| # | Family | The expression that must be 0 | Plugged in | Result |
|---|---|---|---|---|
| 1 | gate | `x_1³ − y_1` | `2³ − 8 = 8 − 8` | **0** ✓ |
| 2 | gate | `x_2³ − y_2` | `3³ − 27 = 27 − 27` | **0** ✓ |
| 3 | gate | `x_3³ − y_3` | `4³ − 64 = 64 − 64` | **0** ✓ |
| 4 | gate | `x_4³ − y_4` | `5³ − 24 = 125 − 24 = 101` | **0** ✓ |
| 5 | gate | `x_5³ − y_5` | `1 − 1` | **0** ✓ |
| 6 | gate | `x_6³ − y_6` | `1 − 1` | **0** ✓ |
| 7 | gate | `x_7³ − y_7` | `1 − 1` | **0** ✓ |
| 8 | gate | `x_8³ − y_8` | `1 − 1` | **0** ✓ |
| 9 | gate | `x_9³ − y_9` | `1 − 1` | **0** ✓ |
| 10 | lookup sum | `Σh_i − Σg_i` | `71 − (71 + 0)` | **0** ✓ |
| 11 | lookup | `h_1·(x_1β_1 + y_1β_2 + r) − 1` | `71·(2+32+3) − 1 = 71·37 − 1 = 1 − 1` | **0** ✓ |
| 12 | table row 1 | `g_1·(t_{1,1}β_1 + t_{1,2}β_2 + r) − m_1` | `71·(2+32+3) − 1 = 1 − 1` | **0** ✓ |
| 13 | table row 2 | `g_2·(t_{2,1}β_1 + t_{2,2}β_2 + r) − m_2` | `0·(3+108+3) − 0 = 0·13` | **0** ✓ |
| 14 | β-consistency | `β_1 − 1` | `1 − 1` | **0** ✓ |
| 15 | β-consistency | `β_2 − β_1·β` | `4 − 1·4` | **0** ✓ |

```
V_sps(…) = (0,0,0,0,0,0,0,0,0, 0, 0, 0,0, 0,0)      all zeros  ->  ACCEPT ✓
```

### Where the number 15 comes from

Each family contributes one equation per "thing" it is about:

```
   9   one per GATE                (n = 9 gates)
+  1   one sum check               (always exactly 1)
+  1   one per LOOKUP              (lk = 1 lookup)
+  2   one per TABLE ROW           (T = 2 rows)
+  2   one per β POWER             (v = 2 columns)
────
  15   =  ℓ
```

Change the circuit and `ℓ` changes with it: 1000 gates and a `2^16`-row table would
give `ℓ = 1000 + 1 + lk + 65536 + v`.

### What a cheating prover looks like

Suppose the prover lies about gate 3, claiming `y_3 = 65` instead of `64`.
Fourteen entries stay zero; entry 3 becomes

```
eq_3 :  x_3³ − y_3  =  64 − 65  =  −1  =  100     ≠ 0
```

so the output vector is `(0,0,100,0,…,0)` — **not** all zeros → **REJECT**.

Think of it as a test suite: 15 assertions, every one must pass.

### ⚠️ Do we combine these 15 with `β⁰ … β¹⁵`? **No — wrong challenge.**

This is the single most important thing to get right.

```
β  combines   v = 2   COLUMNS inside one table row   ->  powers β⁰, β¹   (that's ALL)
γ  combines   the     EQUATIONS                       ->  powers γ⁰, γ¹, γ², …
```

**There is no `β²`, and certainly no `β¹⁵`.** `β` only ever goes up to `β^{v−1}`,
and here `v = 2`, so the list is exactly `β_1 = 1`, `β_2 = 4`. Two powers. Done.

`β` is not a tool for combining equations — it is a *variable that appears inside*
equations 11–15. Look at the table above: `β_1` and `β_2` show up as ordinary
quantities being multiplied, exactly like `h_1` or `g_2`.

### "Then WHICH equations does β combine?" — **None. Zero. It never combines equations.**

`β` combines **numbers inside a single equation**. Zoom in on equation 11:

```
 eq_11 :   h_1 · ( x_1·β_1  +  y_1·β_2  +  r )  −  1   =  0
                  └──────────┬──────────┘
                             │
                   THIS is what β combines:
                   the 2 COLUMNS of the table row (x_1, y_1) = (2, 8)
                   squashed into ONE number:   2·1 + 8·4  =  34
```

`β` did its job entirely **within** equation 11. It did not touch equation 12, or
any other equation. Equation 11 is still one equation before and after.

Now compare `γ`, which really does combine equations:

```
 γ :   eq_1  +  γ·eq_2  +  γ²·eq_3  +  …  +  γ⁸·eq_9   =  0

       9 separate equations  ──────►  1 equation
```

`γ` takes nine *whole equations* and merges them into one. `β` takes two *numbers*
and merges them into one. Completely different operations that happen to use the
same "multiply by powers of a random value" arithmetic.

### The picture

```
   THE EQUATION LIST                        ONE TABLE ROW
   ┌───────────────┐                        ┌───────┬───────┐
   │ eq_1          │ ┐                      │  x_1  │  y_1  │
   │ eq_2          │ │                      │   2   │   8   │
   │  …            │ ├── γ combines         └───┬───┴───┬───┘
   │ eq_9          │ ┘   these (9 -> 1)         └───┬───┘
   │ eq_10         │                               │
   │  …            │                        β combines these (2 -> 1)
   │ eq_15         │                        2·β⁰ + 8·β¹ = 34
   └───────────────┘
      ↑ γ works DOWN this list                ↑ β works ACROSS one row
```

`γ` operates on **rows of the equation list**. `β` operates on **columns of a
table row**. Different axes of a different object.

### Both readings of your question, answered

| Question | Answer |
|---|---|
| Which equations are **combined by** `β`? | **None.** `β` never merges equations. |
| Which equations **contain** `β` as a variable? | eq 11, 12, 13, 14, 15 |
| Which equations are **combined by** `γ`? | eq 1–9 (the gate family) → one equation |
| How many powers of `β` exist? | `v = 2`: just `β⁰ = 1` and `β¹ = 4` |
| How many powers of `γ` exist? | `ℓ_gate = 9`: `γ⁰ … γ⁸` |

### So which challenge touches which equation?

| eq # | Family | Compressed **by γ**? | Contains `β` as a variable? | Contains `r`? |
|---|---|---|---|---|
| 1–9 | gate | **yes** → `γ⁰…γ⁸` | no | no |
| 10 | lookup sum | no | no | yes |
| 11 | lookup | no | yes (`β_1, β_2`) | yes |
| 12–13 | table rows | no | yes | yes |
| 14–15 | β-consistency | no | yes | no |

So the compression is `γ⁰ … γ⁸` over the **9 gate equations only** — not `β`, and
not all 15.

### Why only the 9, and not all 15?

Because of the selective-`CV` decision in §6 (report 06, final section). Only the
gate equations are **high degree** (3); everything else is degree ≤ 2, and
compressing the lookup/table equations would destroy the sparsity trick that makes
the prover independent of table size `T`.

```
 15 equations
 ├── 9 gate equations, degree 3   ──γ⁰…γ⁸──►  1 equation of degree 3+2 = 5
 │                                            + 2√9 = 6 new degree-2 checks (γ,δ consistency)
 └── 6 other equations, degree ≤ 2  ──────►  left completely alone
```

### An honest note on this toy size

At `ℓ_gate = 9` the compression barely shrinks the equation *count*:
`9 → 1 + 6 = 7`. That is because `2√ℓ = 6` is almost as big as `ℓ = 9`.

**But shrinking the count was never the goal.** The goal is that after `CV` there
is exactly **one high-degree equation**, so its `d+1` error terms are single field
elements committed with the identity function — **zero group operations** — instead
of `d−1` vectors in `F⁹` each needing a real group commitment. The 6 new checks
are degree 2 and their errors are absorbed into **one** committed vector.

The count-shrinking becomes dramatic at real sizes: `ℓ = 2²⁰` gates gives
`2√ℓ = 2048` instead of `1,048,576`.

### "And this is only ONE instance?" — **Yes.**

Everything on this page — all 15 equations, all the messages, and the challenges
`β`, `r`, `γ` — belongs to **one single proof `π`, for one IVC step**:

```
ONE INSTANCE  π
├── prover messages    m_1 = (x, y, m)          <- witness + multiplicities
│                      m_2 = (empty)            <- the β round carries no message
│                      m_3 = ([β_i], h, g)      <- β powers + log-derivative vectors
│                      m_4 = ([γ_i], [δ_i])     <- γ powers  (added by CV)
├── challenges         β = 4,  r = 3,  γ = 5
└── verifier output    15 numbers, all of which must be 0
```

`β`, `r`, `γ` are all **internal** to this one instance. They are the challenges of
its own special-sound protocol.

Only **`α`** operates *between* instances:

```
   instance π   +   instance acc   ──α──►   instance acc''
   (15 equations)   (15 equations)          (15 equations)
```

Two instances in, one out — and the result still has 15 equations, because folding
never changes the shape. See
[14-how-many-instances-do-we-fold.md](14-how-many-instances-do-we-fold.md) Part 6b.

### Family-by-family detail

The same 15, grouped, with the degree of each family noted.

### Family 1 — the 9 gate equations (degree 3)

`eq_i : x_i³ − y_i = 0`

```
 eq_1 :  2³ − 8   =   8 −  8  = 0      ✓
 eq_2 :  3³ − 27  =  27 − 27  = 0      ✓
 eq_3 :  4³ − 64  =  64 − 64  = 0      ✓
 eq_4 :  5³ − 24  = 125 − 24  = 101 = 0  mod 101   ✓
 eq_5 :  1³ − 1   =   0                ✓
 eq_6 …  eq_9  :  identical, all 0     ✓
```

**One equation per gate.** This is Definition 11: `R_GATE` requires
`Σ_j s_{j,i}·G_j(...) = 0` **for all `i ∈ [n]`** — so `n` gates give `n` equations.

### Family 2 — the sum check (1 equation, degree 1)

```
 eq_10 :  Σ h_i − Σ g_i  =  71 − (71 + 0)  = 0     ✓
```

### Family 3 — the lookup check (1 per lookup, degree 3)

`h_i·(x_i·β_1 + y_i·β_2 + r) − 1 = 0`

```
 eq_11 :  71·(2·1 + 8·4 + 3) − 1  =  71·37 − 1  =  1 − 1  = 0     ✓
                                     (71·37 = 2627 = 26·101 + 1)
```

Degree 3 because it multiplies three witness-level quantities: `h_i · x_i · β_j`.

### Family 4 — the table checks (1 per table row, degree 2)

`g_i·(t_{i,1}·β_1 + t_{i,2}·β_2 + r) − m_i = 0`

```
 eq_12 :  71·(2 + 8·4 + 3) − 1  =  71·37 − 1  =  1 − 1  = 0       ✓
 eq_13 :   0·(3 + 27·4 + 3) − 0 =   0·13 − 0             = 0       ✓
```

Degree **2**, not 3: the table `t` is **preprocessed public data**, so `t_{i,j}` is
a *constant*, not a variable. Only `g_i` and `β_j` are witness-level.

### Family 5 — the β-consistency checks (`v` of them, degree 2)

```
 eq_14 :  β_1 − 1        =  1 − 1    = 0     ✓
 eq_15 :  β_2 − β_1·β    =  4 − 1·4  = 0     ✓
```

### The output vector

```
V_sps( pi, messages, challenges )  =  ( 0,0,0,0,0,0,0,0,0, 0, 0, 0,0, 0,0 )  ∈  F^15
                                        └── gates ──┘  sum lk table  β
                                                                                ℓ = 15
```

**`ℓ = 15` is the length of that vector.** The verifier accepts because it is the
zero vector. A cheating prover who breaks gate 3 makes entry `eq_3` non-zero, and
the vector is no longer all-zero.

### Why `ℓ` matters — three places it shows up

1. **The error vector has one slot per equation.** Without `CV`, each accumulation
   error term is `e_j ∈ F^ℓ = F^15` — literally one correction number per
   equation — and each needs a real group commitment.
2. **`CV` compresses exactly this vector.** `γ` collapses the 9 gate entries into
   1, so their error terms become scalars (report 06).
3. **It sets the soundness arity of the `γ` round**: Lemma 3 needs `ℓ` distinct
   `γ` values, because the polynomial `Σ X^j c_j` has degree `ℓ−1`.

### The general formula, for Plonkup

For `Π_plonkup` (§5) with `n` gates, arity `c`, `in` public inputs, `|L|` lookups,
table size `T`:

```
ℓ  =   c·n        permutation checks   w_i − w_{σ(i)} = 0,  one per wire
     +   n        gate checks          one per gate
     +  in        public-input checks  one per public input
     +   1        lookup sum check
     + |L|        lookup checks        one per lookup
     +   T        table checks         one per table row
```

§6 quotes the dominant terms as `n + lk + T + c·n`. **Only the `n` gate checks are
high-degree**; everything else is degree ≤ 2. That asymmetry is exactly why `CV`
is applied selectively to the `GATE` part only (report 06, final section).

### `ℓ` vs the other counts — don't mix them up

| Symbol | Counts | Here |
|---|---|---|
| **`ℓ`** | **equations the verifier checks** | **15** |
| `n` | gates in the circuit | 9 |
| `T` | rows in the lookup table | 2 |
| `v` | columns in a table row | 2 |
| `k` | prover **messages** (rounds) | 3 |
| `d` | max **degree** of any equation | 3 |
| — | **instances folded** | **2** |

`ℓ = 15` and "folds 2 instances" describe different things: 15 is the width of one
instance, 2 is how many instances are combined. See
[14-how-many-instances-do-we-fold.md](14-how-many-instances-do-we-fold.md) Part 6b.

---

## Stage 1 — `β` collapses each **tuple** into one field element

**Problem:** the log-derivative identity works on single field elements, but a
table row here is a *pair*. Fix: read the pair as polynomial coefficients and
evaluate at a random point.

**Verifier sends `β = 4`.** Prover sends the power list `[β_i = β^{i−1}]`:

```
β_1 = 1        β_2 = 4
```

Verifier's consistency checks (degree 2):

```
β_1 =? 1                1 = 1        ✓
β_2 =? β_1 · β          4 = 1·4      ✓
```

Compression — coordinate `j` gets weight `β^{j−1}`:

```
w_1(β) = x_1·β_1 + y_1·β_2  =  2·1 + 8·4  =  34
t_1(β) = 2·1 + 8·4          =  34
t_2(β) = 3·1 + 27·4 = 111   =  10          mod 101
```

`w_1(β) = 34 = t_1(β)` ✓ and `34 ≠ 10` ✓ — the pair matched **row 1**, not row 2.

**Why not just add the coordinates?** `2 + 8 = 10` and `3 + 27 = 30`… fine here,
but the forged pair `(8, 2)` also sums to `10` and would be accepted as `t_1`.
With `β = 4`: `8·1 + 2·4 = 16 ≠ 34` → rejected ✓

**Count:** `v = 2` coordinates combined → `2` powers of `β` (`β⁰, β¹`).

---

## Stage 2 — `r` separates the **table rows** from each other

`β` collapsed each row to a scalar. Now Haböck's identity needs a second variable
to distinguish those scalars from one another.

**Verifier sends `r = 3`.** Multiplicity vector over the table: `m = (1, 0)` —
row 1 used once, row 2 unused.

```
h_1 = 1/(w_1(β) + r) = 1/(34+3) = 1/37 = 71        (37 · 71 = 2627 = 26·101 + 1)
g_1 = m_1/(t_1(β) + r) = 1/37 = 71
g_2 = m_2/(t_2(β) + r) = 0/13 = 0
```

Verifier checks:

```
Σ h_i =? Σ g_i                 71  =?  71 + 0            ✓
h_1 · (w_1(β) + r) =? 1        71 · 37 = 1  mod 101      ✓
g_1 · (t_1(β) + r) =? m_1      71 · 37 = 1  = m_1        ✓
g_2 · (t_2(β) + r) =? m_2       0 · 13 = 0  = m_2        ✓
```

**Note the division of labour:** `β` works *across columns* of a row; `r` works
*across rows* of the table. Two different axes, hence two different challenges —
this is why `Π_VLK` is a 5-move (`k = 3`) protocol.

**Count:** `r` is used as a single value, not as a power list — it enters the
log-derivative denominators, it does not form a linear combination.

---

## Stage 3 — `γ` compresses the **9 gate equations** into 1

**Problem:** the verifier checks `ℓ = 9` separate degree-3 equations. That means
the accumulation prover must commit to error **vectors** in `F^9`, costing
`d−1 = 2` group operations in the recursive circuit — and that count grows with `d`.

**Fix (`CV`, §3.5):** random-linear-combine the 9 equations into 1, so each error
term becomes a single **scalar** needing no group commitment.

**Verifier sends `γ = 5`.** With `ℓ = 9`, `√ℓ = 3`, so the prover sends
`2(√ℓ−1) = 4` elements — two power lists, both derived from the *same* `γ`:

```
sent:      γ_1 = 5     γ_2 = 25          δ_1 = γ³ = 24     δ_2 = γ⁶ = 71
implicit:  γ_0 = 1                       δ_0 = 1
```

Consistency checks (degree 2, `2√ℓ` of them):

```
γ_1 =? γ            5 = 5                    ✓
γ_2 =? γ_1·γ       25 = 5·5                  ✓
δ_1 =? γ_2·γ       24 = 125 mod 101          ✓
δ_2 =? δ_1·δ_1     71 = 576 mod 101          ✓
```

All 9 weights recovered with **one multiplication each**, `γ^{i+3j} = γ_i · δ_j`:

```
 γ⁰=1     γ¹=5      γ²=25
 γ³=24    γ⁴=19     γ⁵=95
 γ⁶=71    γ⁷=52     γ⁸=58
```

The nine gate checks `c_j := x_{j+1}³ − y_{j+1}` become one equation:

```
V' = c_0 + 5c_1 + 25c_2 + 24c_3 + 19c_4 + 95c_5 + 71c_6 + 52c_7 + 58c_8  =?  0
```

- **Honest prover:** every `c_j = 0` → `V' = 0` ✓
- **Cheater** who satisfies 8 gates but sets `y_3 = 65` instead of `64`:
  `c_2 = 64 − 65 = 100`, so `V' = 25 · 100 = 2500 = 76 ≠ 0` → **caught** ✓

The cheat survives only if `γ` is one of the ≤ 8 roots of `Σ X^j c_j`.

**Note `γ` is applied to the gate checks only** — not to the lookup checks. That is
the selective-`CV` point of §6: touching the lookup checks would break the
`O(lk)` table-independence trick of §4.3.

**Count:** `ℓ = 9` equations combined → `9` powers of `γ`, delivered as `3 × 3`.

---

## Stage 4 — `α` folds **2 instances** into 1

Everything above produced **one proof `π`** for this step. Now it is folded into
the running accumulator. This is the only stage that involves two *objects*.

Take gate 1 as the representative check. Its relaxed form (report 05) with
`d = 3` is `x³ − μ²y = e`:

```
Object A — the new proof π :     x = 2,  y = 8,  μ = 1
                                 e = 2³ − 1·8 = 0            ✓ (fresh proof)

Object B — the accumulator  :    x' = 3, y' = 5, μ' = 2
                                 e' = 3³ − 2²·5 = 27 − 20 = 7
```

Substituting the **two-term** combination `X·π + acc` and expanding:

```
(X·x + x')³  −  (X + μ')²·(X·y + y')

  X³ :  x³ − y                  = 8 − 8         = 0     <- new proof's check  ✓
  X² :  3x²x' − y' − 2μ'y       = 36 − 5 − 32   = 100   <- e_2   } cross terms
  X¹ :  3x x'² − 2μ'y' − μ'²y   = 54 − 20 − 32  = 2     <- e_1   } d−1 = 2 of them
  X⁰ :  x'³ − μ'²y'             = 27 − 20       = 7     <- old accumulator's e' ✓
```

**Verifier sends `α = 5`.** The fold:

```
x''  = α·x + x'   = 5·2 + 3  = 13
y''  = α·y + y'   = 5·8 + 5  = 45
μ''  = α + μ'     = 5 + 2    = 7
e''  = e' + α·e_1 + α²·e_2   = 7 + 5·2 + 25·100 = 2517 = 93     mod 101
```

Decider check on the new accumulator:

```
x''³      = 13³   = 2197 = 76         mod 101
μ''²·y''  = 49·45 = 2205 = 84         mod 101
x''³ − μ''²·y''   = 76 − 84 = −8 = 93                    = e''   ✓
```

**Count:** `2` objects folded → powers `α⁰, α¹` (only `α¹` visible). But the
*error* accumulation combines `d = 3` objects (`e'`, `e_1`, `e_2`), so there you
see `α⁰, α¹, α²` — which is why `α` appears with higher powers in step 7 of
Figure 3 but not in step 6.

---

## The whole step on one timeline

```
     ┌──────────────── building the proof π (the special-sound protocol) ────────────────┐
     │                                                                                   │
 send w, m ──► β=4 ──► compress tuples ──► r=3 ──► log-derivative ──► γ=5 ──► compress   │
                       (2,8) -> 34                 h=g=71             9 eqs -> 1 eq      │
     │                                                                                   │
     └───────────────────────────── π is now complete ───────────────────────────────────┘
                                            │
                                            ▼
                        ┌──── accumulation (§3.4) ────┐
                        │   α=5 :  acc'' = α·π + acc  │      <- 2 objects, ONE fold
                        └─────────────────────────────┘
```

`β`, `r`, `γ` are all spent **inside** `π`, before folding exists. They end up
stored in the accumulator's challenge list `[r_i]` and get folded like any other
coordinate — e.g. `β'' = α·β + β'`.

---

## The four challenges side by side

| | `β` | `r` | `γ` | `α` |
|---|---|---|---|---|
| **Section** | 4.4 | 4.3 | 3.5 | 3.4 |
| **Layer** | inside `π` | inside `π` | inside `π` | accumulation |
| **Combines / separates** | `v` **coordinates** of a row | the `ℓ+T` **rows** | the `ℓ` **equations** | **2 objects** |
| **In this example** | 2 coordinates | 3 rows (1 lookup + 2 table) | 9 gate equations | proof + accumulator |
| **Value used** | 4 | 3 | 5 | 5 |
| **Powers used** | `β⁰, β¹` (2) | none — enters denominators | `γ⁰ … γ⁸` (9, as 3×3) | `α⁰, α¹` (fold); `α⁰,α¹,α²` (errors) |
| **Powers sent by prover** | 2 | — | 4 (`γ_1,γ_2,δ_1,δ_2`) | — |
| **Degree cost** | +1 | — | +2 | — |
| **Present in Protostar §6?** | no (scalar lookup) | **yes** | **yes** (GATE part only) | **yes** |

### The rule that unifies them

> **Number of powers = number of things being combined.**
>
> - 2 objects folded → `α⁰, α¹` — one visible power, so nobody calls it "powers"
> - 2 coordinates → 2 powers of `β`
> - 9 equations → 9 powers of `γ` (sent as `2√ℓ = 4` elements via the `3×3` split)
> - `d = 3` error objects → `α⁰, α¹, α²`
>
> The counts differ because the *quantities* differ — not because the mechanisms
> differ. It is one trick used four times.

### And the rule for *how* the powers are delivered

| #powers needed | delivery | why |
|---|---|---|
| 2 (`α`, `β` here) | trivial / flat list | too few to bother optimising |
| `v` (small) | flat list, `v` elements | `v ≈ 2–4` in practice |
| `ℓ` (large) | **two-level `√ℓ × √ℓ`** | a flat list would be as big as the thing being compressed |

That last row is the whole content of §3.5's "Attempt 3", and the reason `γ` costs
`+2` degree while `β` costs `+1`: recovering `γ^{i+j√ℓ} = γ_i · δ_j` needs **two**
factors, `β^{j−1}` needs one.
