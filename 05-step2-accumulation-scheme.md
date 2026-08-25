# 05 — Step 2: The Generic Accumulation Scheme (Section 3.4)

This is the technical heart of the paper. Everything else is either setup for it
or an application of it.

## The accumulated predicate — the "relaxed" NARK verifier

Given public input `pi`, challenges `[r_i]_{i∈[k−1]}`, a NARK proof
`π.x = [C_i]`, `π.w = [m_i]`, and a **slack variable `μ`**, the predicate checks:

1. `r_i = ρ_NARK(r_{i−1}, C_i)` for all `i ∈ [k−1]`, with `r_0 := ρ_NARK(pi)`
2. `Commit(ck, m_i) = C_i` for all `i ∈ [k]`
3. the **relaxed algebraic check**:

```
V_sps^relaxed(pi, π.x, π.w, [r_i], μ)  :=  Σ_{j=0}^{d}  μ^{d−j} · f_j^{V_sps}(pi, π.w, [r_i])  =  e
```

For an honest NARK proof, `μ = 1` and `e = 0`, and this collapses to the original
`V_sps = 0`.

**Why `μ` exists.** Each `f_j` is homogeneous of degree exactly `j`, so the terms
have mismatched degrees. Multiplying `f_j` by `μ^{d−j}` makes every term degree
`d` in the joint variables — i.e. it *homogenises* the whole check. A folded
instance is a linear combination of two instances, and homogenisation is what
makes "linear combination" commute with "degree-`d` polynomial evaluation" up to
correction terms.

**Why `e` exists.** Folding two satisfying assignments of a degree-`d` equation
does not give a satisfying assignment — it gives one that is off by cross terms.
`e` (and its commitment `E`) is the bookkeeping slot that absorbs that noise. The
paper's phrasing: "we also need to introduce an error vector/commitment into the
accumulator witness/instance to absorb the 'noise' that arises after each
accumulation/folding step."

## The accumulator format

```
acc.x  :=  { pi, [C_i]_{i∈[k]}, [r_i]_{i∈[k−1]}, E, μ }      -- instance  (SHORT)
acc.w  :=  { [m_i]_{i∈[k]} }                                  -- witness   (LONG)
```

- `pi ∈ M_in` — accumulated public input (constant size by Remark 1)
- `[C_i] ∈ C^k` — accumulated commitments to prover messages
- `[r_i] ∈ F^{k−1}` — accumulated challenges
- `E ∈ C` — commitment to the accumulated error vector
- `μ ∈ F` — slack variable

Instance size: `in` field elements for the input + `k−1` for the challenges + 1
for `μ` + `k` commitments + (`d−1` commitments for the error terms, in the proof
`pf`).

**Remark 2 — accumulator vs. folding scheme.** A NARK proof `π` *is* an
accumulator with `μ = 1` and `E = 0`. The same scheme therefore folds:
proof+accumulator, or accumulator+accumulator (one extra group scalar
multiplication for the non-trivial `μ`, `e`, `E` of the second accumulator), or
two NARK instances into an accumulator. This is exactly Nova's "relaxed R1CS
instance" idea, generalised.

## The accumulation prover `P_acc` (Figure 3)

Input: `ck` (hardwireable), `acc`, and `(pi, π)`.

```
1.  r_i ← ρ_NARK(r_{i−1}, C_i)  ∀ i ∈ [k−1],  r_0 := ρ_NARK(pi)

2.  Compute [e_j]_{j=1}^{d−1} ∈ (F^ℓ)^{d−1} such that

    Σ_{j=0}^{d} (X + μ')^{d−j} · f_j( X·pi + pi',  [X·m_i + m'_i],  [X·r_i + r'_i] )

      =  Σ_{j=0}^{d} μ'^{d−j} f_j(pi', [m'_i], [r'_i])       <-- the old accumulator's e'
       + X^d · V_NARK(pi, [m_i], [r_i])                       <-- the new proof's check, = 0
       + Σ_{j=1}^{d−1} e_j X^j                                <-- THE CROSS TERMS

      =  e' + Σ_{j=1}^{d−1} e_j X^j

3.  E_j ← Commit(ck, e_j)   ∀ j ∈ [d−1]

4.  α ← ρ_acc(acc.x, pi, π.x, [E_j]_{j=1}^{d−1})              <-- the folding challenge

5.  v  := ( 1,  pi,  [r_i], [C_i], [m_i] )                    (the new proof, μ = 1)
    v' := ( μ', pi', [r'_i],[C'_i],[m'_i])                    (the old accumulator)

6.  v'' := ( μ'', pi'', [r''_i], [C''_i], [m''_i] )  ←  α · v + v'      <-- ONE linear combination

7.  E'' ← E' + Σ_{j=1}^{d−1} α^j · E_j                        <-- error accumulation

8.  acc''.x := { pi'', [C''_i], [r''_i], E'', μ'' },  acc''.w := { [m''_i] }

9.  pf := [E_j]_{j=1}^{d−1}
```

Read step 2 as a **polynomial identity in a formal variable `X`**. Substituting
`X = α` in step 6/7 is what makes the folded accumulator satisfy the relaxed check
with the new error. The constant term (`X=0`) recovers the old accumulator's
check; the leading term (`X^d`) recovers the new proof's check; the `d−1`
intermediate coefficients are precisely the correction terms the prover must
publish. Nothing else is needed — this is the whole scheme.

## How many things get folded? **Two** — always. Never `d`.

Easy to conflate, because `d` shows up three times in this section. Separate them
once and for all:

| `d` appears as | What it counts | Count |
|---|---|---|
| `μ^{d−j}` | homogenisation exponent | — |
| `e_1 … e_{d−1}` | **cross terms the prover must publish** | `d−1` |
| `d+1` transcripts (Theorem 2) | what the **extractor** needs, under rewinding | `d+1` |

**The folding arity is 2.** One accumulation step takes one old accumulator + one
new NARK proof (or two accumulators, Remark 2), samples **one** challenge `α`, and
performs **one** linear combination — Figure 3 step 6, `v'' := α·v + v'`. Two
operands, one challenge.

`d` is the *degree of the equation being folded*, not the number of operands.

### Why `d−1` cross terms fall out of folding just 2 things

Once `μ` is a coordinate of the folded vector — and it is: `v` begins with `1`,
`v'` begins with `μ'` — the relaxed check
`Σ_{j=0}^{d} μ^{d−j} f_j(pi, w, [r_i])` is a **single homogeneous form of degree
exactly `d`** in the extended vector `(μ, pi, [r_i], [m_i])`. That is the entire
purpose of `μ`.

Substitute `X·v + v'` into a degree-`d` homogeneous form and you get a degree-`d`
polynomial in `X` — hence `d+1` coefficients:

```
X^0        ->  f(v')   = the OLD accumulator's check      (already known: = e')
X^d        ->  f(v)    = the NEW proof's check            (= 0, the proof is valid)
X^1 … X^{d−1}  ->  e_1 … e_{d−1}    <-- mixed terms, nobody knows them: PUBLISH
```

Two operands, `d−1` corrections. Binomial expansion, nothing more.

### Worked example, `d = 2` — and it reproduces Nova exactly

Relation: the Hadamard/R1CS check `a ∘ b = c`, witness `w = (a, b, c)`. Homogeneous
decomposition: `f_2(w) = a ∘ b`, `f_1(w) = −c`, `f_0 = 0`. The relaxed check is

```
μ²·f_0 + μ·f_1(w) + f_2(w)  =  a ∘ b − μ·c  =  e
```

— i.e. literally Nova's relaxed R1CS `Az ∘ Bz = μ·Cz + e`. Good sanity anchor.

Fold the new proof `π = (μ=1, a, b, c)` with the accumulator
`acc = (μ', a', b', c')`, where `a' ∘ b' − μ'c' = e'`. Substitute
`(X + μ', X a + a', X b + b', X c + c')`:

```
(Xa + a') ∘ (Xb + b')  −  (X + μ')(Xc + c')

= X²(a∘b) + X(a∘b' + a'∘b) + a'∘b'  −  [ X²c + X(μ'c + c') + μ'c' ]

= X²·[ a∘b − c ]                      <-- new proof's check      = 0
+ X ·[ a∘b' + a'∘b − μ'c − c' ]       <-- e_1, THE ONE CROSS TERM
+     [ a'∘b' − μ'c' ]                <-- old accumulator's error = e'
```

So `d − 1 = 1` cross term. The prover commits `E_1 = Commit(ck, e_1)`, publishes it
as `pf`, receives `α = ρ_acc(…)`, and folds:

```
μ'' = α + μ'      a'' = αa + a'      b'' = αb + b'      c'' = αc + c'
E'' = E' + α·E_1
```

Check it closes: evaluating the identity at `X = α` gives
`a'' ∘ b'' − μ''·c'' = α²·0 + α·e_1 + e' = e''`, and
`Commit(e'') = E' + α·E_1 = E''` by homomorphism. ✓

**Two operands. One challenge `α`. One cross term.**

### Worked example, `d = 3` — the pattern, not a special case

Relation `x ∘ x ∘ x = y`. Decomposition: `f_3 = x³` (writing `x³` for `x∘x∘x`),
`f_1 = −y`. Relaxed check: `x³ − μ²·y = e`. Fold
`x'' = Xx + x'`, `y'' = Xy + y'`, `μ'' = X + μ'`:

```
(Xx + x')³  −  (X + μ')²(Xy + y')

  X³ :  x³ − y                        <-- new proof's check       = 0
  X² :  3x²x' − y' − 2μ'y             <-- e_2
  X¹ :  3x x'² − 2μ'y' − μ'²y         <-- e_1
  X⁰ :  x'³ − μ'²y'                   <-- old accumulator's error = e'
```

`d − 1 = 2` cross terms now — but still **two operands and one `α`**. Raising `d`
buys more `e_j` to commit to (and `d−1` group operations in the recursive circuit,
which is exactly what `CV` in report 06 eliminates). It never changes how many
objects are combined.

### And the `d+1` in Theorem 2 is a *third*, unrelated thing

That is the **extractor's** requirement under rewinding, not the protocol's.
`Π_I` is `(d+1)`-special-sound because `p(X)` has degree `d`, so `d+1` accepting
transcripts with distinct `α` are needed to conclude `p ≡ 0`. An honest execution
produces **one** transcript with **one** `α`.

### The confirming structural detail

If this scheme could fold `n` objects at once, full PCD would be immediate. It
cannot — see report 03 §10:

> "we only build accumulation for one proof and one accumulator, as well as for
> two accumulators. This enables PCD for **DAGs of degree two**."

Higher-degree DAG nodes must be rewritten as `log₂(d)`-depth **binary** trees of
pairwise folds. That is decisive: the folding arity is 2.

## The accumulation verifier `V_acc` (Figure 4) — the recursive circuit

```
1.  r_i ← ρ_NARK(r_{i−1}, C_i)  ∀ i ∈ [k−1],  r_0 := ρ_NARK(pi)
2.  α ← ρ_acc(acc.x, pi, π.x, pf)
3.  v  := ( 1, pi, [r_i], [C_i] )
    v' := ( acc'.μ, pi', [r'_i], [C'_i] )
4.  Check  ( acc''.μ, pi'', [r''_i], [C''_i] )  =?  α · v + v'
5.  Check  acc''.E  =?  acc'.E + Σ_{j=1}^{d−1} α^j · E_j
```

**This is what becomes the recursive statement.** Note what is absent: no `[m_i]`,
no `e_j` vectors, no `Commit` evaluations over the witness, no reference to `n`,
`T`, `|w|`, or `ℓ`. It touches only the instance parts and `pf`.

Cost, itemised by the paper:
- `k−1` constant-size queries to `ρ_NARK`, 1 query of size `d` to `ρ_acc`
- `|R| + 2` field operations to combine `(μ, pi, [r_i])`
- `k` group operations to combine `[C_i]`
- `d−1` group operations to add `[E_j]` onto `E`

Total group scalar multiplications: **`k + d − 1`**. This is the figure that the
`CV[·]` trick in report 06 reduces to `k + 2`.

## The decider `D_acc` (Figure 5)

```
1.  C_i =? Commit(ck, m_i)   for all i ∈ [k]
2.  e  ←  Σ_{j=0}^{d} μ^{d−j} · f_j^{V_sps}(pi, [m_i], [r_i])
3.  E  =? Commit(ck, e)
```

Run **once**, at the end, by the IVC verifier. Cost: about `|M| + ℓ` group
operations (`|M|` = total elements in the prover messages) plus evaluating `ℓ`
degree-`d` multivariate polynomials. Linear in the witness — hence the IVC
verifier is not succinct unless the decider is outsourced to a SNARK
(see report 03 §10).

## `P_acc` cost summary

- `k−1` queries to `ρ_NARK`, 1 to `ρ_acc`
- `E_j = Commit(ck, e_j)` for `j ∈ [d−1]`, where `e_j ∈ F^ℓ` → the `(d−1)` group
  commitments that `CV` will eliminate
- `|R| + |M| + 2` field ops to combine `(μ, pi, [r_i], [m_i])`
- `k` group ops to combine `[C_i]`
- computing the coefficients of `ℓ` degree-`d` polynomials for `[e_j]`
  — this is the term written `L(V_sps, d)` in Theorem 3, and it is the real
  prover bottleneck (see report 07)

Note `|M^≠|` (non-zero elements) vs `|M|` (all elements): with a sparse prover
message the commitment cost is `|M^≠|`, which is what makes non-uniformity and
table-size-independent lookups possible.

## Theorem 2 — Security

> Let `(P_NARK, V_NARK)` be the RO-NARK of Section 3.3, `cm` a binding
> homomorphic commitment scheme, `ρ_acc` another random oracle. Then
> `(P_acc, V_acc, D_acc)` satisfies **perfect completeness** and has knowledge
> error
> ```
> (Q + 1) · (d+1)/|F|  +  negl(λ)
> ```
> against any randomized polynomial-time `Q`-query adversary.

### Completeness argument, in brief

Take `((pi,π), acc') ∈ R_acc`. `V_acc` accepts because `P_acc` and `V_acc` derive
`[r_i]` and `α` by the identical process, so their linear combinations agree.
`D(acc'')` accepts because:
- `acc''.{C_i, m_i} = acc'.{C_i, m_i} + α · π.{C_i, m_i}`, and both
  `π.C_i = Commit(π.m_i)` (since `V_NARK` accepted) and
  `acc'.C_i = Commit(acc'.m_i)` (since `D(acc')` accepted), so the check survives
  **by homomorphism of the commitment**;
- the new error `e''` equals `e' + Σ α^j e_j` by construction of `pf`, so
  `E'' = Commit(ck, e'')` again by homomorphism.

Homomorphism is used twice and is the only property of the commitment beyond
binding that the proof needs.

### Knowledge-soundness argument — the key move

The authors do **not** prove knowledge soundness directly. Instead they exhibit
an *interactive* protocol `Π_I` and show it is special-sound, then invoke Lemma 1:

`Π_I`: `P_I` sends `pf = [E_j] ∈ G^{d−1}`; `V_I` sends random `α ←$ F`;
`P_I` responds with `acc''`. `V_I` accepts iff `D_acc(acc'') = 0` and
`V_acc(...) = 0` using the real random `α` rather than a Fiat-Shamir challenge.

**Claim: `Π_I` is `(d+1)`-special-sound.** Given `d+1` accepting transcripts
`{T_i = (pi, π.x, acc'.x; acc''_i, pf)}` with distinct `α_1,…,α_{d+1}`:

1. From the `V_acc` check `Commit(e_i) = E_i = acc'.E + Σ α_i^j E_j`, a
   **Vandermonde matrix** in `α_1..α_d` lets the extractor solve for `e'` and
   `[e_j]`, so that `E_j = Commit(e_j)` and `acc'.E = Commit(e')`.
2. From **two** challenges `(α_1, α_2)`, the extractor recovers
   `π.w = [m_j] = [(acc''_1.m_j − acc''_2.m_j)/(α_1 − α_2)]`, and then
   `acc'.m_j = acc''_1.m_j − α_1 · π.m_j`. If any *other* challenge disagreed
   with this decomposition, that disagreement is a **commitment break** — which
   happens with negligible probability by assumption. (This is where the
   `negl(λ)` in the theorem statement comes from.)
3. Consequently the degree-`d` polynomial
   ```
   p(X) = Σ_{j=0}^{d} (X + acc'.μ)^{d−j} · f_j( X·pi + acc'.pi, [X·m_i + acc'.m_i], [X·r_i + acc'.r_i] )
          − e' − Σ_{j=1}^{d−1} e_j X^j
   ```
   vanishes at `d+1` distinct points, hence is **identically zero**. Now read off
   coefficients:
   - **constant term = 0** ⟹ `D(acc') = 0`, i.e. the old accumulator was valid;
   - **degree-`d` term = 0** ⟹ `Σ_j f_j(pi, [π.m_i], [π.r_i]) = 0`, i.e.
     `V_NARK(pi, π) = 0` — combined with `V_acc` having checked that the `r_i`
     were derived correctly.

So the extractor outputs a valid `(π.w, acc'.w) ∈ R_acc`. Applying Lemma 1 to a
`(d+1)`-special-sound protocol over challenge space `F` gives knowledge error
`(Q+1)·(d+1)/|F|`, and `acc = FS[Π_I]` inherits it. ∎

**Reading the proof structurally:** the polynomial `p(X)` is zero everywhere, and
its two extreme coefficients are exactly the two things you wanted to know
(old accumulator valid, new proof valid). The `d−1` middle coefficients are the
`e_j` the prover already published. That is an unusually clean argument, and it is
why the scheme generalises to arbitrary `d` for free where Sangria could not.
