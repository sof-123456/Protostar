# 15 — The `β` Challenge: Combining a Tuple by Degree (Section 4.4)

Companion to [08-subprotocols.md](08-subprotocols.md) §4.4 and
[06-step3-cv-compression.md](06-step3-cv-compression.md).

## Symbol caveat, up front

`pdftotext` dropped **every Greek glyph** in this PDF (the same extraction loses
`α`, `μ`, `ρ`, `γ` in the figures). The vector-lookup challenge symbol is
therefore not recoverable from the text layer; this report names it **`β`**. The
paper may use a different letter. Its **role** is unambiguous from the equations
and is what this file explains.

Two facts *are* recoverable and pinned down:

```
Compute [β_i = β^{i−1}]_{i=1}^{v}          <-- note the exponent: i−1, not i
Verifier checks:  β_1 =? 1,   β_{i+1} =? β_i · β  ∀ i ∈ [v−1]
```

so `β_1 = β^0 = 1`. (An earlier draft of report 08 said `β_i = β^i`; corrected.)

---

## Part 0 — "We fold 2 instances, so why are there several β?"

The single most common confusion, so it goes first.

### β has nothing to do with folding

`β` and `α` live on **two different layers** and are spent at **two different
times**:

| | `α` (Figure 3) | `β` (§4.4) |
|---|---|---|
| Layer | the **accumulation scheme** (§3.4) | **inside one special-sound protocol** (§4.4) |
| Combines | 2 **objects** (proof + accumulator) | `v` **coordinates of one tuple** |
| When | *after* a proof exists | *while building* the proof |
| Who samples it | `ρ_acc` | the verifier, mid-protocol |
| Exists in `Π_LK`? | yes (all protocols get folded) | no — scalar lookup needs no β |

### The timeline makes it obvious

```
t = 0   Prover builds the proof π for THIS IVC step:
          round 1:  send w, m
          round 2:  verifier sends β    <- compress the v coordinates inside each tuple
          round 3:  verifier sends r    <- separate the ℓ+T rows from each other
          π is now complete.  β and r are baked INTO π as its challenges [r_i].

t = 1   Accumulation:  fold π with acc using α.
          v'' := α·v + v'               <- 2 objects, 1 α
```

By the time `α` appears, `β` has already been spent and is sitting inside `π` as
an ordinary transcript challenge. `β` never sees the accumulator.

(Amusing consequence: `β` *itself* then gets folded. `acc.x` carries
`[r_i]_{i∈[k−1]}`, which for `Π_VLK` (`k = 3`) is the pair `[β, r]`. So
Figure 3 step 6 computes `β'' = α·β + β'` — a folded challenge. That is fine
precisely because the relaxed check is homogeneous.)

### The unifying rule: #powers = #things combined

Here is the part that dissolves the question. **Folding also uses powers of a
challenge** — you just never notice, because with 2 objects the powers are `1`
and `α`:

```
fold 2 objects:      α^0 · acc  +  α^1 · π          =  acc + α·π
combine v coords:    β^0 · w_1  +  β^1 · w_2  + … +  β^{v−1} · w_v
```

**Same pattern.** A random linear combination of `N` items needs `N` coefficients,
and the coefficients are taken to be `1, c, c², …, c^{N−1}` for a single challenge
`c`. With `N = 2` that list is `(1, α)` — one visible coefficient — so nobody
writes it as "powers". With `N = v` the powers become visible.

Every "powers of a challenge" in the paper is this one idea:

| Where | Combines | How many items | Powers used | Visible? |
|---|---|---|---|---|
| Fold, Fig. 3 step 6 | proof + accumulator | **2** | `α^0, α^1` | no — looks like "one α" |
| Error accum., Fig. 3 step 7 | `e'` and `e_1…e_{d−1}` | **`d`** | `α^0 … α^{d−1}` | **yes** — `E'' = E' + Σ α^j E_j` |
| `β`, §4.4 | coordinates of a tuple | **`v`** | `β^0 … β^{v−1}` | **yes** |
| `γ`, §3.5 (`CV`) | verification equations | **`ℓ`** | `γ^0 … γ^{ℓ−1}` | **yes** (via the `√ℓ` split) |

Note row 2: **`α` does appear with higher powers** — in the error accumulation,
because there you are combining `d` objects, not 2. So it was never "α gets one
power, β gets many." It is always: *as many powers as there are items.*

### So, restated

> **We fold 2 instances → 1 nontrivial power of α.
> We compress `v` coordinates → `v` powers of β.
> Different counts because different numbers of things are being combined —
> not because folding and compressing are different mechanisms.**

### Why powers of *one* β, instead of `v` independent challenges?

You could sample `v` independent challenges `β^{(1)}, …, β^{(v)}` and set
`w_i(β) = Σ_j w_{i,j}·β^{(j)}`. It would be sound. It is rejected because:

1. **Hash cost.** Each independent challenge is another Fiat–Shamir hash — and
   those hashes land **in the recursive circuit**, where they are among the most
   expensive operations (non-native field arithmetic). Powers of one β cost
   **one** hash regardless of `v`.
2. **Soundness is barely worse.** Independent challenges give error `≈ 1/|F|`;
   powers give `(v−1)/|F|` by the degree-`(v−1)` root bound. With `|F| ≈ 2^256`
   and `v ≈ 3`, indistinguishable.
3. **Transcript size.** One challenge, one transcript element.

The price paid: the powers must be supplied by the prover and checked
(`β_{i+1} = β_i·β`), which costs `v−1` degree-2 constraints and `+1` verifier
degree. Cheap hashes-for-degree trade — the same trade `CV` makes with `γ`.

---

## Part 0b — In which case do we use β at all?

### The one-line rule

> **`β` is used when, and only when, a lookup table row is a TUPLE (`v ≥ 2`).**
> Single-column table (`v = 1`) → no β. No lookup at all → no β.

`β` is not a general-purpose part of the framework. It belongs to exactly one
sub-protocol: **`Π_VLK`, the vector-valued lookup of §4.4**.

### Protocol-by-protocol

| Protocol | Uses β? | Why |
|---|---|---|
| `Π_perm` (§4.1) permutation | ❌ | no lookup; prover just sends `w` |
| `Π_GATE` (§4.2) custom gates | ❌ | no lookup |
| `Π_select` (§4.5) circuit selection | ❌ | no lookup |
| `Π_ccs` (App. C) | ❌ | no lookup |
| **`Π_LK` (§4.3) scalar lookup** | ❌ | `v = 1` — a row is already one field element, nothing to compress |
| **`Π_VLK` (§4.4) vector lookup** | ✅ | `v ≥ 2` — must collapse a tuple to one element |
| `Π_plonkup` (§5) | ❌ | built on the **scalar** `Π_LK` |
| **`Π_mplkup` (§6) — Protostar itself** | ❌ | also built on the **scalar** lookup — see below |
| `Π_mccs+` (App. C) | ❌ | also scalar |
| the accumulation layer (§3.4) | ❌ | that layer uses `α` |

### Important: Protostar as written in §6 does *not* use β

Read step 7 of `Π_mplkup` (§6) carefully:

```
h_i := 1/( w_{L_pc[i]} + r )        <-- w_{L_pc[i]} is a SINGLE field element
g_i := m_i/( t_i + r )              <-- t_i is a SINGLE field element
```

No `β`, no `β_j`, no `w_i(β)`. The headline Protostar protocol is specified with
**scalar** lookups. The same is true of `Π_mccs+` in Appendix C.

`Π_VLK` is a **drop-in module you substitute** when your table needs tuple rows.
That is why the abstract writes "(vector) lookups" with parentheses — vector
lookup is *supported*, not *always on*. From §1: "we extend `Π_LK` in §4.4 to
further support vector-valued lookup, where each table entry is a vector of
elements. This feature is useful in applications like zkEVM and for simulating bit
operations in circuits."

### When you genuinely need it — real cases

**Need β (`v ≥ 2`):**

| Table | `v` | Row |
|---|---|---|
| bitwise AND / XOR / OR | 3 | `(a, b, a⊕b)` |
| zkEVM opcode metadata | 4 | `(opcode, gas, stack_in, stack_out)` |
| memory / storage trace | 2–3 | `(addr, value)` or `(addr, value, timestamp)` |
| tagged range check | 2 | `(value, bit_width)` |
| S-box / round-constant tables | 2+ | `(in, out)` |

**Don't need β (`v = 1`):**

| Table | Row |
|---|---|
| plain range check | `value ∈ [0, 2^16)` |
| membership in a set of single values | `x ∈ {allowed values}` |
| "is this a valid opcode byte" | `opcode` |

### Why you can't dodge β with `v` separate scalar lookups

The tempting shortcut: run `v` independent scalar lookups, one per column. **It is
unsound** — it proves each component appears *somewhere in its column*, not that
the components appear **in the same row**.

Concretely, with the Part 4 table:

```
table rows:   t_1 = (7, 2, 9)        t_2 = (1, 1, 1)

column 1 = {7, 1}      column 2 = {2, 1}      column 3 = {9, 1}
```

Now take the **forged** tuple `(7, 1, 9)`:

```
7 ∈ {7,1} ✓      1 ∈ {2,1} ✓      9 ∈ {9,1} ✓        all three column lookups PASS
```

but `(7,1,9)` is **not a row of the table**. Per-column lookups accept it.

With `β = 4` it is caught immediately:

```
(7,1,9)(β) = 7·1 + 1·4 + 9·16 = 155 = 54    mod 101
t_1(β) = 58        t_2(β) = 21
54 ∉ {58, 21}   ->  REJECTED ✓
```

This is the same failure mode as the permutation collision in Part 3, and it is
why `β` is **necessary**, not merely convenient: the tuple must be bound together
into one value before the log-derivative identity is applied.

### What turning β on costs you

| | scalar `Π_LK` | vector `Π_VLK` |
|---|---|---|
| moves / `k` | 3-move, `k = 2` | 5-move, `k = 3` (2nd prover msg empty) |
| verifier degree | 2 (3 perfectly complete) | 3 (5 perfectly complete) |
| non-zeros in prover msg | `≤ 4ℓ` | `≤ (v+3)ℓ + v` |
| accumulation prover | `O(ℓ)`, independent of `T` | `O(vℓ)`, still independent of `T` |
| **recursive circuit** | — | **`1` extra challenge computation** |

That last row is the number that matters, and the paper states it in §1: "We also
support tables that store tuples of size `v` using **1 additional challenge
computation** within the recursive circuit." Table 1 records it as the `1H` entry
on Protostar's "w/ lookup" row.

So: tuple-valued lookups of **any width `v`** cost one extra in-circuit challenge.
Not `v` extra — one. That is the payoff of using *powers of a single* `β` rather
than `v` independent challenges (Part 0, final subsection).

---

## Part 1 — The problem β solves

The scalar lookup protocol `Π_LK` (§4.3) rests on Haböck's Lemma 4, which is a
statement about **single field elements**:

```
{w_i} ⊆ {t_i}   ⟺   ∃ m :   Σ_{i∈[ℓ]} 1/(X + w_i)  =  Σ_{i∈[T]} m_i/(X + t_i)
```

But a real lookup table has **tuple-valued rows**:

- `(a, b, a XOR b)` — bitwise operations
- `(opcode, gas_cost, stack_delta)` — a zkEVM opcode table
- `(x, x², x³)` — precomputed powers

So you need `w_i ∈ F^v`, not `w_i ∈ F`. The identity above does not accept tuples.

**β's entire job: collapse a `v`-tuple into one field element, so the scalar
machinery runs unchanged.**

---

## Part 2 — The mechanism: coordinate `j` gets degree `j−1`

Treat each tuple as the **coefficient list of a polynomial** in a formal
variable `Y`:

```
w_i(Y) := Σ_{j=1}^{v} w_{i,j} · Y^{j−1}  =  w_{i,1} + w_{i,2}·Y + w_{i,3}·Y² + … + w_{i,v}·Y^{v−1}
t_i(Y) := Σ_{j=1}^{v} t_{i,j} · Y^{j−1}
```

Then evaluate at a random challenge `β`. Eqn. 7 of the paper:

```
Σ_{i=1}^{ℓ}  1/(X + w_i(β))   =   Σ_{i=1}^{T}  m_i/(X + t_i(β))
```

That is the whole idea. **Coordinate `j` is tagged with degree `j−1`** — this is
the "combine by degree" the section title refers to. Position in the tuple becomes
exponent of `β`.

Note there are now **two** formal variables in play, and they do different jobs:

| Variable | Separates | Instantiated by |
|---|---|---|
| `Y` (→ `β`) | the `v` **coordinates within** one tuple | challenge `β` |
| `X` (→ `r`) | the `ℓ + T` **different rows** from each other | challenge `r` |

That is why `Π_VLK` needs **two** challenge rounds where `Π_LK` needed one, and
why it is a 5-move (`k = 3`) protocol rather than 3-move.

---

## Part 3 — Why powers, and not a plain sum

The naive compression "just add the coordinates" fails immediately.

Work in `F_101`, `v = 3`:

```
tuple A = (7, 2, 9)
tuple B = (9, 2, 7)          <-- same multiset, permuted
```

**Plain sum:** `7+2+9 = 18` and `9+2+7 = 18`. **Collision.** A prover could pass
off a permuted tuple as a genuine table row — fatal for a table like
`(a, b, a XOR b)` where order carries all the meaning.

**Powers of `β`, with `β = 4`** → `β_1 = 1`, `β_2 = 4`, `β_3 = 16`:

```
A(β) = 7·1 + 2·4 + 9·16  =  7 + 8 + 144  =  159  =  58   mod 101
B(β) = 9·1 + 2·4 + 7·16  =  9 + 8 + 112  =  129  =  28   mod 101
```

`58 ≠ 28` ✓ — separated. A near-miss in the last coordinate is caught too:

```
C = (7, 2, 8):   7 + 8 + 128 = 143 = 42   mod 101      42 ≠ 58 ✓
```

**Why it works in general.** Two distinct tuples are two distinct polynomials of
degree `≤ v−1`. Distinct polynomials of degree `≤ v−1` agree on at most `v−1`
points. So a uniformly random `β` separates them except with probability
`(v−1)/|F|`.

---

## Part 4 — A complete worked instance

`F_101`, `v = 3`, table size `T = 2`, number of lookups `ℓ = 1`.

### Setup

```
table    t_1 = (7, 2, 9)        t_2 = (1, 1, 1)
lookup   w_1 = (7, 2, 9)        (so w_1 should be found at row 1)
```

### Round 1 — prover sends `w`, `m`

Multiplicity vector over the **table**: `m = (1, 0)` — row 1 used once, row 2 unused.

### Round 2 — verifier sends `β = 4`

Prover computes the power list and the compressed values:

```
β_1 = 1,   β_2 = 4,   β_3 = 16

t_1(β) = 7·1 + 2·4 + 9·16 = 159 = 58     mod 101
t_2(β) = 1·1 + 1·4 + 1·16 = 21           mod 101
w_1(β) = 7·1 + 2·4 + 9·16 = 159 = 58     mod 101
```

### Round 3 — verifier sends `r = 3`

Prover computes `h` and `g`:

```
h_1 = 1 / (w_1(β) + r)   = 1/(58+3) = 1/61 = 53      mod 101
g_1 = m_1/(t_1(β) + r)   = 1/(58+3) = 1/61 = 53      mod 101
g_2 = m_2/(t_2(β) + r)   = 0/(21+3) = 0
```

(`61⁻¹ = 53` because `61 · 53 = 3233 = 32·101 + 1`.)

### Prover sends `[β_i], h, g` — verifier checks all five equations

```
1.  β_1 =? 1                          1 = 1                         ✓
2.  β_{i+1} =? β_i · β                β_2 = 1·4 = 4    ✓
                                      β_3 = 4·4 = 16   ✓
3.  Σ h_i =? Σ g_i                    53  =?  53 + 0  = 53          ✓
4.  h_i · (Σ_j w_{i,j}·β_j + r) =? 1  53 · 61 = 3233 = 1 mod 101    ✓
5.  g_i · (Σ_j t_{i,j}·β_j + r) =? m_i
       row 1:  53 · 61 = 1  = m_1                                   ✓
       row 2:   0 · 24 = 0  = m_2                                   ✓
```

All checks pass. The `v = 3`-wide lookup has been verified using **only the scalar
log-derivative machinery**, because `β` reduced each row to one field element.

### The cheating attempt

A prover claiming `(9,2,7) ∈ t` compresses to `28`, not `58`, so it must produce
`h_1 = 1/31 = 88` — and then check 3 (`Σh = Σg`) no longer matches what any honest
multiplicity vector over the table can produce.

**Honest caveat:** for a *single* fixed `β` a cheating prover can sometimes get
lucky. Special-soundness is not a statement about one transcript — it is
Lemma 6's extraction from a **tree** of transcripts with many distinct `(β, r)`.
See Part 6.

---

## Part 5 — Degree accounting: why β costs exactly +1

### Why the prover supplies the powers rather than the verifier computing them

If the verifier computed `β, β², …, β^{v−1}` itself, the verification equation
would have **degree `v`** — the degree would scale with the tuple width. Instead
the prover sends the list `[β_i]` as part of its message, and the verifier checks
the list is well-formed using cheap degree-2 constraints:

```
β_1     =?  1                       (degree 1)
β_{i+1} =?  β_i · β                 (degree 2)   ∀ i ∈ [v−1]
```

This is the identical device used by `CV` in §3.5 — see Part 7.

### The main equation's degree

Recall that in this framework the challenges `r` are *also* folded variables
(they sit inside `v = (1, pi, [r_i], [C_i], [m_i])`), so `r` counts as degree 1,
not as a constant.

```
h_i · ( Σ_j w_{i,j} · β_j  +  r )  =?  1
 ↑         ↑          ↑        ↑
deg 1    deg 1      deg 1    deg 1

  h_i · w_{i,j} · β_j   ->  degree 3
  h_i · r               ->  degree 2
                            ------------
                     maximum degree = 3
```

Compare the **scalar** lookup:

```
h_i · ( w_i + r ) =? 1        ->   h_i·w_i : degree 2,  h_i·r : degree 2   ->  degree 2
```

**So `β` costs exactly +1 degree**, and that single `β_j` factor is the entire
difference between `Π_LK` (degree 2) and `Π_VLK` (degree 3).

### And the perfect-completeness patch costs +2 more

Applying the §4.3 patch (multiply through by the denominator to handle
`w_i(β) + r = 0`):

```
( w_i(β) + r ) · ( h_i·(w_i(β) + r) − 1 )  =  0
      ↑                      ↑
   degree 2              degree 3
                     ------------------
                       degree 5
```

which is exactly the paper's "The degree of the verifier is 5" for the
perfectly-complete `Π_VLK`. (Scalar `Π_LK` goes 2 → 3 by the same argument.)

---

## Part 6 — Where β shows up in the soundness proof (Lemma 6)

> **Lemma 6.** For any `v ∈ N`, the perfectly-complete `Π_VLK` is
> `[1 + (v−1)·(ℓ+T−1),  2(ℓ+T)]`-special-sound.

A **two-level** arity vector, because there are two challenge rounds:

```
level 1  (challenge β)  ->  arity  1 + (v−1)(ℓ+T−1)
level 2  (challenge r)  ->  arity  2(ℓ+T)
```

The proof builds the **bivariate** polynomial

```
p(X,Y) = Π_k (X + w_k(Y)) · Π_j (X + t_j(Y)) · [ Σ_i 1/(X + w_i(Y)) − Σ_i m_i/(X + t_i(Y)) ]
```

with

```
deg_X p  =  ℓ + T − 1              <-- separating the ROWS       -> needs ℓ+T values of r
deg_Y p  ≤  (v−1)(ℓ+T−1)           <-- separating the COORDINATES -> needs that many β
```

Each arity is exactly `degree + 1` in its variable, so that a polynomial vanishing
at that many points is identically zero:

- **`2(ℓ+T)` for `r`** — the factor 2 is the pigeonhole slack: up to `ℓ+T`
  challenges are "bad" (some denominator `w_i(β)+r` or `t_i(β)+r` vanishes), so you
  sample twice as many to guarantee `ℓ+T` good ones.
- **`1 + (v−1)(ℓ+T−1)` for `β`** — one more than `deg_Y`.

**Read the arity as a price tag for β.** Vector lookup with `v = 1` degenerates to
`1 + 0 = 1` — a single `β` level, i.e. no `β` round at all, recovering `Π_LK`. The
`(v−1)` factor is precisely what tuple-width costs you in knowledge error.

---

## Part 7 — β's sibling: γ in the `CV` transform (§3.5)

Both are the same pattern — *combine many things into one using powers of a random
challenge, with the prover supplying the powers and the verifier checking them
with degree-2 constraints.* They differ only in what they combine and how many
powers are needed.

| | **β** (§4.4, vector lookup) | **γ** (§3.5, `CV`) |
|---|---|---|
| Combines | the `v` **coordinates within one tuple** | the `ℓ` **verification equations** |
| Powers needed | `v` (small — tuple width, 2–4) | `ℓ` (huge — gate count) |
| Layout | flat list `[β_i]_{i∈[v]}` | two-level: `γ^i = γ_j · δ_k`, `i = j + k√ℓ` |
| Extra message length | `v` | `2√ℓ` |
| Consistency checks | `β_1 = 1`, `β_{i+1} = β_i·β` | `γ_{i+1} = γ_i·γ`, `δ_{i+1} = δ_i·δ_1` |
| Degree cost | **+1** (one `β_j` factor) | **+2** (a `γ_j` **and** a `δ_k` factor) |
| Result degree | `2 → 3` | `d → d+2` |
| Soundness cost | arity `1 + (v−1)(ℓ+T−1)` | arity `ℓ` (Lemma 3) |
| Purpose | make the log-derivative identity accept tuples | make error terms **scalars** so they need no group commitment |

**Why γ needs the `√ℓ` split and β does not.** The naive "prover sends all powers"
approach costs an extra message of length equal to the number of powers. For β
that is `v ≈ 3` — negligible. For γ that is `ℓ ≈ n` — as large as the thing being
compressed, which defeats the purpose. Hence `CV`'s two-level trick: send `√ℓ`
powers of `γ` and `√ℓ−1` powers of `γ^{√ℓ}`, recover any `γ^i` with **one
multiplication** `γ_j · δ_k`, total message `2√ℓ`. The cost of that second factor
is the extra `+1` degree — `d+2` instead of `d+1`.

**In one line:** β is the flat version of the same trick; γ is the version that had
to be square-rooted because `ℓ` is big.

---

## Part 8 — Where this lands in Protostar

`Π_VLK`'s cost line from report 08:

```
k = 3  (5-move; the 2nd prover message is EMPTY — it exists only to carry the β round)
verifier degree      3   (5 with the perfect-completeness patch)
non-zeros in msg     ≤ (v+3)ℓ + v
accumulation         O(vℓ), INDEPENDENT of table size T
```

The `O(vℓ)` table-independence comes from the same six-cached-commitment trick as
scalar lookup (report 08 §4.3) — `β` does not interfere with it, because
`w_i(β)` and `t_i(β)` are still *linear* in the witness for fixed `β`.

The paper's competitive claim rests on this: **HyperNova's lookup argument does not
support vector-valued lookups at all**, which the authors call "essential for
applications like zkEVM and encoding bit-wise operations in circuits."

---

## Part 9 — Misreading checklist

| Misreading | Correct |
|---|---|
| "`β_1 = β`" | `β_1 = β^0 = 1`. The list is `β_i = β^{i−1}` and the verifier checks `β_1 =? 1` |
| "β combines the different table rows" | **`r`** separates rows. **`β`** separates coordinates *within* a row |
| "β is a folding challenge like α" | No. `α` folds two accumulators (report 14). `β` is an ordinary verifier challenge *inside* the special-sound protocol, applied before any folding happens |
| "the verifier computes β²,β³,…" | The **prover** sends them; the verifier only checks `β_{i+1} = β_i·β` |
| "β makes the protocol degree v" | Degree **3**, independent of `v` — that is the whole point of prover-supplied powers |
| "one accepting transcript proves the lookup" | Soundness is Lemma 6's extraction from a `[1+(v−1)(ℓ+T−1), 2(ℓ+T)]`-tree of transcripts |
| "β and γ are the same challenge" | Different challenges, different jobs, same *design pattern* — see Part 7 |

---

## One-line summary

**`β` turns a `v`-tuple into one field element by reading the tuple as polynomial
coefficients — coordinate `j` gets degree `j−1` — and evaluating at a random point.
The prover supplies the powers so the check stays degree 3 instead of degree `v`;
the cost is `+1` verifier degree and a `(v−1)` factor in the special-soundness
arity.**
