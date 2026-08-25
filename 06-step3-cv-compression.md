# 06 — Step 3: The `CV[·]` Verifier-Compression Trick (Section 3.5) and Hi/Low Accumulation (Appendix A)

## The bottleneck being attacked

From report 05: the accumulation prover commits to `d−1` error **vectors**
`e_j ∈ F^ℓ`, and the accumulation verifier does `d−1` group operations to fold
those `d−1` commitments. Total verifier group multiplications: `k + d − 1`.

For high-degree gates — precisely the feature the paper is selling — `d` is large,
so `Θ(d)` group operations *in the recursive circuit* would cancel out the
benefit of using high-degree gates. This is exactly the criticism levelled at
Sangria in report 02. So the authors need `d` out of the group-operation count.

## Scope check: is §3.5 about lookup tables? **No.**

Worth settling before anything else, because §3.5 uses "powers of a challenge"
just like the lookup protocols do, and the two get conflated.

**§3.5 is about high-degree GATES.** It is a *generic* transform applied to **any**
special-sound protocol — it knows nothing about lookups, tables, or tuples.
Lookups are §4.3 (scalar) and §4.4 (vector), a completely different layer.

| | **§3.5 `CV` / `γ`** | **§4.4 vector lookup / `β`** |
|---|---|---|
| Layer | generic compiler transform (§3) | one concrete sub-protocol (§4) |
| Applies to | **any** `sps` | only lookups with tuple rows |
| Combines | the **`ℓ` verification EQUATIONS** | the **`v` COORDINATES of one table row** |
| Motivated by | high-degree custom gates | tuple-valued tables |
| Goal | make error terms **scalars** → no group commitment | make the log-derivative identity accept tuples |
| Saves | `d − 3` group mults in the recursive circuit | (nothing — it *adds* 1 challenge) |
| Present in Protostar? | **yes**, on the `GATE` part only | **no** — §6 uses scalar lookup |

### What `ℓ` actually is here

`ℓ` is the **verifier's output length** — how many equations `V_sps` checks
(§3.1: "output length `ℓ` (i.e. the verifier checks `ℓ` degree `d` equations)").
For `Π_GATE` that is `ℓ = n`, **one equation per gate**. So §3.5 is compressing
*"the verifier checks `n` separate gate equations"* down to *"the verifier checks
1 equation."*

> ⚠️ **Notation collision in the paper.** §3.1 uses `ℓ` for the verifier output
> length; §4.3 uses `ℓ` for the **number of lookups**. Two different meanings,
> same glyph. Section 6 quietly switches to `lk` for the lookup count to avoid
> exactly this. When you read `ℓ` in §3.5, it means *equations*, never *lookups*.

### The three "powers of a challenge" uses, kept apart

They share a design pattern and nothing else:

```
γ  (§3.5)    combines  ℓ  VERIFICATION EQUATIONS       ->  1 equation      "rows of V_sps's output"
β  (§4.4)    combines  v  TUPLE COORDINATES            ->  1 element       "columns of a table row"
r  (§4.3)    separates ℓ+T  TABLE ROWS from each other ->  log-derivative  "rows of the table"
α  (§3.4)    combines  2  OBJECTS (proof + accumulator)->  1 accumulator   "the fold"
```

Four challenges, four different jobs, one recurring trick. See
[15-the-beta-challenge.md](15-the-beta-challenge.md) Part 0 for why the *number of
powers* differs in each case.

### The one place `CV` and lookups do meet — and it is a conflict

`CV` does not *serve* lookups; in Protostar it has to **avoid** them. From §6:

> "Unfortunately, applying `CV` to `Π_mplkup` seems to have a major tradeoff. The
> number of verification checks is `n + lk + T + c·n`. This requires using
> `CV[Π_mplkup]` and is **not composable with the sparseness optimizations for
> lookup** described in Sections 4.3 and Appendix B."

So the authors apply `CV` **only to the `GATE` part**:

```
total verification checks in Π_mplkup :   n  +  lk  +  T  +  c·n
                                          ↑     └───────┬──────┘
                                   HIGH DEGREE d      degree ≤ 2
                                   -> CV applies       -> CV must NOT touch these
```

Result (report 06, final section): `d+1` error terms of length **1** for the
compressed gate check, plus **one** error vector of length
`T + lk + cn + O(√n)` for everything else — the low-degree checks including all
the lookup machinery, left alone so the `O(lk)` table-independent trick of §4.3
still works.

**Summary: §3.5 exists because of high-degree gates. Lookups are the thing it has
to be carefully kept away from.**

## The idea in one line

**Collapse the `ℓ` degree-`d` equations into a single equation by taking a random
linear combination with powers of a challenge `γ`.** Then there is only *one*
equation, so each error term `e_j` is a *single field element*, not a length-`ℓ`
vector — and a single field element can be "committed" with the identity
function, costing zero group operations.

## Getting there, and the two failed attempts

Worked example from the paper. Suppose
`V_sps(x_1,x_2) = (x_1 + x_2, x_1 x_2)`, i.e. `ℓ = 2`. Set

```
V'_sps(x_1, x_2, γ) := V_{sps,1} + γ · V_{sps,2} = (x_1 + x_2) + γ·x_1 x_2
```

**Attempt 1 — naive.** Output length drops to 1. But the verifier must compute
`γ, γ², …, γ^{ℓ−1}` itself, which raises the degree by `ℓ`. Unacceptable.

**Attempt 2 — prover supplies all powers.** Prover sends `γ, γ², …, γ^ℓ`; the
verifier checks consistency with degree-2 checks `γ^{i+1} = γ^i · γ`, and the main
equation's degree rises only by 1. Degree fixed — but now the prover sends an
extra message of length `ℓ`, which is as large as what we were trying to avoid.

**Attempt 3 — the actual construction: √ℓ decomposition.** Write each exponent as

```
i = j + k·√ℓ        for  j, k ∈ [1, √ℓ]
```

(w.l.o.g. `ℓ` is a perfect square.) The prover sends:
- `√ℓ` powers of `γ` — call them `[γ_i]`
- `√ℓ − 1` powers of `γ^{√ℓ}` — call them `[δ_i]`

From these, **any** power `γ^i` for `i ∈ [1,ℓ]` is recovered with **one
multiplication** `γ_j · δ_k`. So the extra prover message has length `2√ℓ`
instead of `ℓ`.

## The transformed protocol `CV[sps]` (Figure 6)

```
Prover                                       Verifier
m_i ← P_sps(...)          --m_i-->
   repeat k−1 times       <--r_i--           r_i ←$ F
final message m_k         --m_k-->
                          <--γ-----          γ ←$ F
[γ_i]_{i=1}^{√ℓ−1}
[δ_j]_{j=1}^{√ℓ−1}        --m_{k+1} = [γ_i, δ_i]-->
                                             V'_sps(pi, [m_i]_{i=1}^{k+1}, ([r_i], γ)) =? 0
                                             γ_{i+1} = γ_i · γ        ∀ i ∈ [1, √ℓ−2]
                                             δ_{i+1} = δ_i · δ_1      ∀ i ∈ [1, √ℓ−2]
                                             γ_1 = γ,   δ_1 = γ^{√ℓ−1} · γ
```

with the compressed check

```
V'_sps(pi, [m_i]_{i=1}^{k+1}, ([r_i], γ))
   :=  Σ_{i=0}^{√ℓ−1} Σ_{j=0}^{√ℓ−1}  γ_i · δ_j · V_{sps, i+j√ℓ}(pi, [m_i], [r_i])
    =  Σ_{j=0}^{ℓ−1}  γ^j · V_{sps,j}(pi, [m_i], [r_i])
```

### Net accounting of the transform

| | before | after |
|---|---|---|
| moves | `2k − 1` | `2k + 1` (one extra round for `γ`) |
| high-degree checks | `ℓ` of degree `d` | **1** of degree `d + 2` |
| extra low-degree checks | — | `2√ℓ` of degree 2 |
| extra prover message | — | length `2√ℓ` |

Degree goes `d → d+2`: one `+1` from multiplying by `γ_i`, one `+1` from `δ_j`.

### "So here we also use β?" — No. Here it is `γ`. And there is still only ONE challenge.

Same *family* of trick as `β` in §4.4, different letter and different target. Two
things to get straight:

**1. `δ` is not a second challenge — it is derived from `γ`.** Figure 6 checks
`δ_1 = γ_{√ℓ−1} · γ`, i.e.

```
δ_1 = γ^{√ℓ−1} · γ = γ^{√ℓ}          so    δ_k = γ^{k·√ℓ}
```

Only **one** challenge `γ` is ever sampled. `δ` is just the "stride" list of
`√ℓ`-th powers of that same `γ`. So the hash cost is one challenge, exactly as
with `β`.

**2. Index convention differs from `β`.** For `β`, the verifier checks `β_1 = 1`,
so `β_i = β^{i−1}`. For `γ`, Figure 6 checks `γ_1 = γ`, so `γ_i = γ^i`; the
`i = 0` terms in the double sum use `γ_0 = δ_0 = 1`, which are free constants and
are not sent. That is why the prover transmits `[γ_i]_{i=1}^{√ℓ−1}` and
`[δ_j]_{j=1}^{√ℓ−1}` — a message of length `2(√ℓ − 1) ≈ 2√ℓ`, not `2√ℓ + 2`.

### Worked numeric example: `ℓ = 9` equations, `F_101`, `γ = 5`

Take a toy protocol whose verifier checks **`ℓ = 9` equations** — think 9 gates,
each producing one output component `c_0 … c_8`. Then `√ℓ = 3`.

**The two power lists.** The prover sends `2(√ℓ−1) = 4` field elements:

```
sent:      γ_1 = 5          γ_2 = 25            δ_1 = γ³ = 24       δ_2 = γ⁶ = 71
implicit:  γ_0 = 1                              δ_0 = 1
```

(`γ³ = 125 = 24 mod 101`; `δ_2 = δ_1² = 24² = 576 = 71 mod 101`.)

**Verifier's consistency checks** — all degree 2, and there are `2√ℓ` of them:

```
γ_1 =? γ                 5 = 5              ✓
γ_2 =? γ_1 · γ           25 = 5·5           ✓
δ_1 =? γ_2 · γ           24 = 25·5 = 125    ✓
δ_2 =? δ_1 · δ_1         71 = 24·24 = 576   ✓
```

**Recovering all 9 powers with one multiplication each** via `γ^{i + 3j} = γ_i · δ_j`:

```
 exponent   i,j     γ_i · δ_j        value      check γ^e mod 101
 γ⁰        (0,0)     1 · 1            1          1
 γ¹        (1,0)     5 · 1            5          5
 γ²        (2,0)    25 · 1           25         25
 γ³        (0,1)     1 · 24          24        125 = 24   ✓
 γ⁴        (1,1)     5 · 24 = 120    19        625 = 19   ✓
 γ⁵        (2,1)    25 · 24 = 600    95       3125 = 95   ✓
 γ⁶        (0,2)     1 · 71          71                   ✓
 γ⁷        (1,2)     5 · 71 = 355    52                   ✓
 γ⁸        (2,2)    25 · 71 = 1775   58                   ✓
```

**9 powers from 4 transmitted elements.** Compare the rejected Attempt 2, which
would have transmitted all 9. At realistic scale — `ℓ = n = 2^20` gates — this is
`2·2^10 = 2048` elements instead of `1,048,576`.

**The compression itself.** The verifier now checks one equation instead of nine:

```
V'_sps  =  Σ_{j=0}^{8} γ^j · c_j
        =  c_0 + 5c_1 + 25c_2 + 24c_3 + 19c_4 + 95c_5 + 71c_6 + 52c_7 + 58c_8   =?  0
```

- **Honest prover:** every `c_j = 0`, so `V'_sps = 0` ✓
- **Cheating prover** who satisfies 8 gates but has `c_3 = 7`:
  `V'_sps = 24 · 7 = 168 = 67 ≠ 0` → **caught**.

The cheat only survives if `γ` happens to be a root of the degree-8 polynomial
`p(X) = Σ X^j c_j` — at most 8 bad values out of `|F|`. That is exactly Lemma 3
below, and it is why the arity of the new challenge round is `ℓ`.

### Why this was worth doing: the group-operation payoff

The whole point is what happens to the **error terms**. Suppose a degree-`d = 5`
custom gate in `Π_GATE` (`k = 1`):

| | error terms | each lives in | commitment | group mults in recursive circuit |
|---|---|---|---|---|
| **Before `CV`** | `d−1 = 4` | `F^ℓ = F^9` | real vector commitment ×4 | `k + d − 1` = **5 G** |
| **After `CV`** | `d+1 = 6` | `F^1` — a **scalar** | identity, free ×6 | `k + 2` = **3 G** |

And the gap widens with `d`, which is the entire motivation:

```
d = 5   ->   5 G  becomes  3 G
d = 10  ->  10 G  becomes  3 G
d = 20  ->  20 G  becomes  3 G      <-- recursive circuit no longer grows with d
```

There is still **one** real group commitment after `CV` — for the length-`2√ℓ`
error vector belonging to the `2√ℓ` degree-2 consistency checks above. That is the
"2" in `k + 2`.

### One-line answer to the question

> **§3.5 uses `γ` (plus `δ = γ^{√ℓ}` derived from it), not `β`. One challenge, two
> power lists, because `ℓ` is large. `β` in §4.4 is the same trick with one flat
> list, because `v` is small.**

### Lemma 3 — soundness of the transform

> Let `sps` be a `(2k−1)`-move protocol for `R` with `(a_1,…,a_{k−1})`
> special-soundness whose verifier outputs `ℓ` elements. Then `CV[sps]` is
> `(a_1,…,a_{k−1}, ℓ)`-special-sound.

I.e. one extra level of arity `ℓ` is appended to the arity vector — the cost of
the extra `γ` round.

*Proof.* Fix an internal node `u` at depth `k−1` with messages
`msg = (pi, [m_i], [r_i])`. It has `ℓ` children with distinct `γ`. Define the
degree-`(ℓ−1)` univariate polynomial `p(X) := Σ_{j=0}^{ℓ−1} X^j · c_j` where
`c_j := V_{sps,j}(msg)`. Since all transcripts accept, `p` vanishes at `ℓ`
distinct points, so `p ≡ 0`, so **every** `c_j = 0` — meaning `V_sps` outputs the
zero vector on `msg`. Hence every root-to-`u` sub-transcript is accepting for
`sps`, so the depth-`(k−1)` subtree is a valid `(a_1,…,a_{k−1})`-tree, and
`Ext_sps` succeeds. ∎

This is the standard "random linear combination is sound because a nonzero
polynomial has few roots" argument, packaged as a transcript-tree statement.

## Hi/low-degree accumulation (Appendix A) — cashing in the trick

After `CV`, the verifier has **one** high-degree check plus **`ℓ'` low-degree
(degree-2) checks**. Appendix A builds `acc_HL` for
`V_sps = V_{sps,1} ‖ V_{sps,2}` where `V_{sps,1}` is degree `d` mapping to `F`
and `V_{sps,2}` is degree 2 mapping to `F^ℓ`. It is "essentially a parallel
composition" of the Section 3.4 scheme applied to each part:

- The prover computes error terms **separately** for `V_{sps,1}` and `V_{sps,2}`:
  `d−1` **constant-size** error terms, and **1** error-term **vector** of
  length `ℓ`.
- The `d` scalar error terms are committed with the **identity function** —
  `Commit(ck, e_j) := e_j` — **zero group operations**.
- The single length-`ℓ` error vector gets a real homomorphic vector commitment.
- The accumulator stores two error terms: a field element `e` and a commitment `E`.
- `V_acc` folds each separately: `d−1` **field** operations, and **1** group
  scalar multiplication.

### The resulting count

```
Group scalar multiplications in the recursive circuit:
    k   (fold the k+1 message commitments... )   +   2
  = k + 2        instead of        k + d − 1
```

Trade-off, stated plainly by the paper: **`k+2` group ops, at the cost of 1 more
hash and `O(d)` more field operations.** Favourable whenever `d ≥ 3`. The
accumulator instance must additionally carry the challenge `γ` and two more
commitments (for `m_{k+1}` and for `e`).

Prover-side extra cost: `O(√ℓ)` additional group operations to commit to
`m_{k+1}` (length `2√ℓ`) and to `e`, plus computing the coefficients of a
degree-`(d+2)` univariate polynomial expressed as a sum of `O(ℓ)` polynomials.

### Corollary 2 — security of `acc_HL`

> `acc_HL` for `FS[V_{sps,1} ‖ V_{sps,2}]` satisfies perfect completeness and has
> knowledge error `(Q+1)·(d+4)/|F| + negl(λ)`.

*Proof sketch (the paper's own).* Completeness is immediate from Theorem 2. For
knowledge soundness, `acc_HL` is a parallel composition of two accumulation
schemes; an adversary breaking `acc_HL` breaks one of them, and a union bound
gives `(d+4)/|F|`. The `+4` accounts for the degree rising to `d+2` plus the
degree-2 component.

The paper explicitly notes the restriction to "a single field element output for
`V_{sps,1}` and degree 2 for `V_{sps,2}`" is only for simplicity and "naturally
extends to more arbitrary degrees, sizes and more components." That extension is
in fact *used* in Section 6 — see the next paragraph.

## The critical caveat: `CV` is applied selectively in practice

This is easy to miss and it matters. Applying `CV` to the *whole* `Π_mplkup`
protocol would be a disaster, because:

- the total number of verification checks is `n + lk + T + c·n` — so the extra
  prover message would be `O(√(n+T+…))`, and
- it is **not composable** with the sparseness optimisations of Section 4.3 and
  Appendix B that make the prover independent of `T`.

The resolution: only `n` of the checks are high-degree (the `Π_GATE` part);
everything else is degree ≤ 2. So — "with a slight abuse of notation" — the
authors define `CV[Π_mplkup]` as **applying `CV` only to the `GATE` part**. The
result:

- `d+1` cross-error vectors, each of length **1**, for the degree-`(d+2)` check in
  `CV[Π_GATE]`;
- **1** cross-error vector of length `T + lk + cn + O(√n)` for everything else
  (the low-degree checks of `Π_mplkup` plus the `O(√n)` degree-2 consistency
  checks introduced by `CV[Π_GATE]`).

Then the error-separation technique commits to the field elements with the
identity and to the one long vector with a vector commitment, and the
homomorphism trick of Section 4.3 keeps the prover independent of `T`.

**Implementer's takeaway:** `CV` is not a black box you wrap around your protocol.
It is a scalpel you apply to the high-degree sub-check only, and doing so
correctly requires knowing which of your verification equations are high-degree.
