# 20 — Lookup Tables, From Scratch, With Numbers

**What this file answers:** what a lookup table *is*, why a "`w_i ∈ t`" statement
cannot be handled by an ordinary constraint, how Protostar's `Π_LK` (§4.3) turns
it into two degree-2 equations, and why the whole thing costs `O(ℓ)` instead of
`O(T)`.

**Provenance:** Definition 12, Lemma 4, and the `Π_LK` figure are at
`_source/paper-extracted-text.txt:1537–1600`; the vector version `Π_VLK` at
`:1725–1800`. The condensed statements live in
[08-subprotocols.md](08-subprotocols.md) §4.3–4.4; this file is the worked
arithmetic behind them.

Everything in **`F_101`**. Every number verified.

---

## 1. What a lookup table is

A **lookup argument** lets a circuit assert

> "this witness value appears somewhere in this fixed, public table"

instead of *computing* the relation with gates. The table `t ∈ F^T` is
preprocessed public data. The witness `w ∈ F^ℓ` is the list of `ℓ` values being
looked up.

Why anyone bothers:

| Operation | As arithmetic gates | As a lookup |
|---|---|---|
| `x ∈ [0, 2^16)` (range check) | 16 bit-decomposition constraints + 16 booleanity | 1 lookup into `t = [0..65535]` |
| `a XOR b` on 8-bit limbs | ~24 constraints after decomposition | 1 lookup into a 65536-row `(a, b, a⊕b)` table |
| EVM opcode semantics, S-boxes, `keccak` round tables | hundreds of gates each | 1 row each |

The payoff only exists if the cost is proportional to the number of **lookups**
`ℓ`, not the **table size** `T`. Making that true under folding is the content of
§4.3 and the reason the paper calls it "the most efficient lookup protocol today"
(`_source/paper-extracted-text.txt:240`).

## 2. Why it is not just another constraint

`Π_gate` and `Π_perm` work by "prover sends the witness, verifier checks an
equation". That fails here:

> "The statement of the lookup relation is **not algebraic**."
> — `_source/paper-extracted-text.txt:392–393`

`w_i ∈ t` is **set membership**. Written naively it is

```
Π_{j∈[T]} (w_i − t_j)  =  0
```

which is a single equation of **degree `T`**. Protostar's entire cost model is
driven by verifier degree `d` — a degree-`65536` check is unusable. The job is to
get membership down to degree 2.

## 3. The fix: Haböck's logarithmic-derivative identity

**Lemma 4** (= Lemma 5 of `[Hab22]`, `_source/paper-extracted-text.txt:1546`).
Let `char(F) = p > max(ℓ, T)`. Then `{w_i} ⊆ {t_i}` as sets **iff** there exists
`[m_i]_{i∈[T]}` with

```
   ℓ                 T
   Σ   1/(X + w_i)  =  Σ   m_i/(X + t_i)                             (Eqn. 6)
  i=1               i=1
```

Read it as: take `Π(X + w_i)` and `Π(X + t_i)^{m_i}`; the sums above are their
logarithmic derivatives. Two products have equal log-derivatives iff they have the
same roots with the same multiplicities. `m_i` is exactly **the multiplicity of
table entry `t_i` among the lookups**.

The win: an identity between *rational functions* becomes one field equation once
the verifier picks a random `X = r`, and after clearing denominators every check
is **degree 2**.

## 4. The protocol `Π_LK`

```
Prover P(C_LK, w ∈ F^ℓ)                             Verifier V(C_LK)

m_i := Σ_{j∈[ℓ]} 1(w_j = t_i)   ∀i ∈ [T]
                        --- w, m --->
                        <--- r ---                   r ←$ F
h_i := 1/(w_i + r)    ∀i ∈ [ℓ]
g_i := m_i/(t_i + r)  ∀i ∈ [T]
                        --- h, g --->
                                                     Σ_{i∈[ℓ]} h_i =? Σ_{i∈[T]} g_i
                                                     h_i·(w_i + r) =? 1     ∀i ∈ [ℓ]
                                                     g_i·(t_i + r) =? m_i   ∀i ∈ [T]
```

`k = 2` (3-move), **verifier degree 2**, `≤ 4ℓ` non-zeros in the prover messages.

The first check is Eqn. 6 evaluated at `r`. The other two are what *force* `h`
and `g` to be the honest inverse vectors — without them the prover could send any
`h, g` summing to the same thing.

---

## 5. Worked example — a 2-bit range check

Field `F_101`. Table `t = [0, 1, 2, 3]` (`T = 4`). Witness `w = [2, 0, 2, 3]`
(`ℓ = 4`). Every `w_i` really is in `t`, so an honest prover should convince the
verifier.

### Round 1 — prover sends `w` and the multiplicities `m`

```
m_0 = 1     value 0 looked up once      (w_2)
m_1 = 0     value 1 never looked up
m_2 = 2     value 2 looked up twice     (w_1, w_3)
m_3 = 1     value 3 looked up once      (w_4)
```

Two sanity properties, both used later:

* `Σ_i m_i = 4 = ℓ` — the multiplicities always sum to the number of lookups.
* `m` has **3 non-zero entries out of `T = 4`**. In general at most `ℓ` of the `T`
  entries can be non-zero, because `ℓ` lookups can touch at most `ℓ` distinct
  rows. This sparsity is the whole cost story (§7).

### Round 2 — verifier sends a random challenge

```
r = 5
```

### Round 3 — prover sends the inverse vectors

```
w + r = [7, 5, 7, 8]
h     = [1/7, 1/5, 1/7, 1/8]      = [29, 81, 29, 38]

t + r = [5, 6, 7, 8],   m = [1, 0, 2, 1]
g     = [1/5, 0, 2/7, 1/8]        = [81,  0, 58, 38]
```

Inverses mod 101, each verified: `5·81 = 405 = 4·101 + 1`;
`7·29 = 203 = 2·101 + 1`; `8·38 = 304 = 3·101 + 1`.

### The verifier's checks

**Check 1 — the log-derivative identity at `X = r`:**

```
Σ h_i = 29 + 81 + 29 + 38 = 177 ≡ 76   (mod 101)
Σ g_i = 81 +  0 + 58 + 38 = 177 ≡ 76             ✓
```

**Check 2 — `h_i·(w_i + r) = 1`, one per lookup (degree 2):**

```
29·7 = 203 ≡ 1  ✓      81·5 = 405 ≡ 1  ✓
29·7 = 203 ≡ 1  ✓      38·8 = 304 ≡ 1  ✓
```

**Check 3 — `g_i·(t_i + r) = m_i`, one per table row (degree 2):**

```
81·5 = 405 ≡ 1 = m_0  ✓        0·6 =   0 ≡ 0 = m_1  ✓
58·7 = 406 ≡ 2 = m_2  ✓       38·8 = 304 ≡ 1 = m_3  ✓
```

Accepted. Note that nowhere did the verifier evaluate a degree-`T` polynomial —
every equation it touched was a product of two committed values.

---

## 6. The same example with a cheating prover

Now `w = [2, 0, 2, 4]`. The value `4` is **not** in `t = [0,1,2,3]`.

The prover must commit to `w` and `m` in round 1, **before** seeing `r`. Its best
move is to lie about the multiplicity — claim the stray `4` was really a `3`, i.e.
send the same `m = [1, 0, 2, 1]` as before.

Symbolically, the round-3 sums are

```
Σ h − Σ g  =  [ 1/(2+r) + 1/(0+r) + 1/(2+r) + 1/(4+r) ]
              − [ 1/(0+r) + 2/(2+r) + 1/(3+r) ]

           =  1/(4+r) − 1/(3+r)

           =  −1 / ( (4+r)(3+r) )        ≠ 0 for every r
```

The numerator is the constant `(3+r) − (4+r) = −1`, which is never zero. At the
verifier's `r = 5`:

```
h = [1/7, 1/5, 1/7, 1/9] = [29, 81, 29, 45]      (9·45 = 405 ≡ 1)
Σ h = 29 + 81 + 29 + 45 = 184 ≡ 83
Σ g = 76        (unchanged from §5)

83 ≠ 76        REJECTED
```

**Where the soundness bound comes from.** Clear denominators in Eqn. 6 and you get

```
p(X) = Π_{k∈[ℓ]}(X + w_k) · Π_{j∈[T]}(X + t_j) · [ Σ 1/(X+w_i) − Σ m_i/(X+t_i) ]
```

a polynomial of degree `ℓ + T − 1 = 7`. If the witness is invalid, `p ≢ 0`, so it
has at most 7 roots — the cheating prover wins for at most **7 of the 101**
possible challenges. In a 256-bit field that is `(ℓ+T)/|F|`, negligible.

That argument, run backwards over `2(ℓ+T)` transcripts (the factor 2 is pigeonhole
slack for challenges where some `w_i + r = 0`), is **Lemma 5**: `Π_LK` is
`2(ℓ+T)`-special-sound. See [08-subprotocols.md](08-subprotocols.md) §4.3.

---

## 7. Why Protostar formulates it this way

Two properties, both visible in the example above.

### (a) Verifier degree 2

`h_i·(w_i + r) = 1` is a product of two committed values — degree 2. Protostar's
recursive-circuit cost is `k + d + O(1)` field operations; only **degree** and
**round count** matter, and the verifier's *linear-time* work over all `T` rows is
irrelevant because it gets compressed by `CV[·]` ([06](06-step3-cv-compression.md)).
That is the paper's design philosophy in one line:

> "While the verification is linear time, it is low degree (2) and thus compatible
> with our generic compiler."

**Implementer's fork in the road.** The protocol as written is *not perfectly
complete*: if `w_i + r = 0` or `t_i + r = 0`, `h_i` / `g_i` is undefined. The patch
sets those entries to 0 and changes the checks to

```
(w_i + r)·( h_i·(w_i + r) − 1 )  = 0
(t_i + r)·( g_i·(t_i + r) − m_i ) = 0
```

which **raises the verifier degree from 2 to 3**. The authors note the unpatched
completeness error is `(ℓ+T)/|F|` and "can likely be ignored in practice". So:
degree 2 with negligible completeness error, or degree 3 with a clean theorem.
Flagged in [12-critique-and-open-problems.md](12-critique-and-open-problems.md).

### (b) `O(ℓ)` accumulation, independent of `T`

`m` and `g` live in `F^T` but have `≤ ℓ` non-zeros, so committing to a *fresh*
proof is `O(ℓ)`. The danger is the **accumulator**: `acc.m` and `acc.g` are random
linear combinations of many proofs and are **not** sparse.

The escape is that the prover never needs the error *vector* `e_1^{(3)} ∈ F^T`,
only its *commitment*, and that commitment is a **linear** function of six
commitments to `ℓ`-sparse or cached values:

```
E_1^{(3)} = GT' + π.r·G' + acc.μ·GT + acc.r·G − acc.μ·M − M'
```

with `G' , M' , GT'` cached and updated in place (`G' ← G' + α·G`, …). Full
derivation in [08-subprotocols.md](08-subprotocols.md) §4.3 "crown jewel".

**Consequence:** a `2^16`-row table costs the folding prover nothing per step
beyond the `ℓ` lookups actually performed. This is the claim in the abstract —
"independent of the table size in the lookup"
(`_source/paper-extracted-text.txt:27`).

---

## 8. Vector lookups — looking up *tuples*

A one-column table cannot express `a XOR b = c`. Real tables have `v` columns.
`Π_VLK` (§4.4) folds each row into a univariate polynomial at a fresh challenge
`β`, then runs the same logUp identity on the compressed values:

```
w_i(Y) := Σ_{j=1}^{v} w_{i,j} Y^{j−1}        t_i(Y) := Σ_{j=1}^{v} t_{i,j} Y^{j−1}

Σ_i 1/(X + w_i(Y))  =  Σ_i m_i/(X + t_i(Y))                          (Eqn. 7)
```

### Worked example — 1-bit XOR table

`F_101`, `v = 3` columns `(a, b, a⊕b)`, `T = 4` rows, `ℓ = 2` lookups.

```
t_1 = (0,0,0)      t_2 = (0,1,1)      t_3 = (1,0,1)      t_4 = (1,1,0)
w_1 = (1,0,1)      w_2 = (1,1,0)
m   = [0, 0, 1, 1]
```

Challenges `β = 7` (so `β_1 = 1, β_2 = 7, β_3 = 49`) and `r = 5`.

**Compress each row** as `x_1 + x_2·β + x_3·β²`:

```
t_1(β) = 0 + 0·7 + 0·49 =  0
t_2(β) = 0 + 1·7 + 1·49 = 56
t_3(β) = 1 + 0·7 + 1·49 = 50
t_4(β) = 1 + 1·7 + 0·49 =  8

w_1(β) = 1 + 0·7 + 1·49 = 50      (= t_3(β), as it should be)
w_2(β) = 1 + 1·7 + 0·49 =  8      (= t_4(β))
```

**Prover's third message:**

```
h_1 = 1/(50+5) = 1/55 = 90        (55·90 = 4950 = 49·101 + 1)
h_2 = 1/( 8+5) = 1/13 = 70        (13·70 =  910 =  9·101 + 1)

g_1 = 0/( 0+5) =  0               g_2 = 0/(56+5) =  0
g_3 = 1/(50+5) = 90               g_4 = 1/( 8+5) = 70
```

**Verifier's checks:**

```
Σ h = 90 + 70 = 160 ≡ 59
Σ g =  0 + 0 + 90 + 70 = 160 ≡ 59                          ✓

h_1·(Σ_j w_{1,j}β_j + r) = 90·55 ≡ 1   ✓
h_2·(Σ_j w_{2,j}β_j + r) = 70·13 ≡ 1   ✓
g_3·(Σ_j t_{3,j}β_j + r) = 90·55 ≡ 1 = m_3   ✓
g_4·(Σ_j t_{4,j}β_j + r) = 70·13 ≡ 1 = m_4   ✓
g_1·5 = 0 = m_1  ✓        g_2·61 = 0 = m_2  ✓

β_1 =? 1        1 = 1        ✓
β_2 =? β_1·β    7 = 1·7      ✓
β_3 =? β_2·β   49 = 7·7      ✓
```

The last three are what stop the prover from choosing the `β`-powers freely; they
are why the prover *sends* `[β_i]` as part of its message. See
[15-the-beta-challenge.md](15-the-beta-challenge.md) for `β`'s other role.

**Cheating:** suppose the prover claims `(1, 0, 0)` — a wrong XOR result. Then
`w(β) = 1 + 0 + 0 = 1`, which must coincide with one of `{0, 56, 50, 8}`. It does
not, and it can only do so for the `β` that are roots of a degree-`(v−1) = 2`
polynomial per row pair. Formally: `Π_VLK` is
`[1 + (v−1)(ℓ+T−1), 2(ℓ+T)]`-special-sound (Lemma 6), the two coordinates being
the `β`-tree and the `r`-tree.

Cost: `k = 3` (5-move, **second prover message empty**), verifier degree **3**
(5 patched), non-zeros `≤ (v+3)ℓ + v`, accumulation `O(vℓ)` — still independent of
`T`.

> The paper stresses that HyperNova's lookup **does not** support vector-valued
> lookups, "which is essential for applications like ZK-EVM and encoding bit-wise
> operations" (`_source/paper-extracted-text.txt:284–286`).

---

## 9. Summary table

| | `Π_LK` (§4.3) | `Π_VLK` (§4.4) |
|---|---|---|
| Relation | `w_i ∈ t`, `t ∈ F^T` | `w_i ∈ t`, `t ∈ (F^v)^T` |
| Moves | 3 (`k = 2`) | 5 (`k = 3`, 2nd msg empty) |
| Verifier degree | **2** (3 perfectly complete) | 3 (5 perfectly complete) |
| Prover non-zeros | `≤ 4ℓ` | `≤ (v+3)ℓ + v` |
| Special-soundness | `2(ℓ+T)` | `[1+(v−1)(ℓ+T−1), 2(ℓ+T)]` |
| Accumulation cost | `O(ℓ)`, independent of `T` | `O(vℓ)`, independent of `T` |

The one sentence to remember: **membership is not an equation, but its
logarithmic derivative is — and that derivative is degree 2.**

---

## Where to go next

* [08-subprotocols.md](08-subprotocols.md) — `Π_LK` in context alongside `Π_perm`,
  `Π_gate`, `Π_select`, and the full `O(ℓ)` accumulation derivation.
* [09-protostar-and-ccs.md](09-protostar-and-ccs.md) — how the lookup composes into
  `Π_mplkup` (non-uniform Plonkup).
* [07-step4-error-term-algorithms.md](07-step4-error-term-algorithms.md) — the
  error-term machinery the sparsity trick plugs into.
* [10-efficiency-comparison.md](10-efficiency-comparison.md) — the `lk`-dependent
  rows of Table 1.
