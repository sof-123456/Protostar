# 07 — Step 4: How the Error Terms Are Actually Computed

The accumulation *verifier* is cheap; the accumulation *prover* has to compute the
cross-error terms, and that is where all the real work lives. Three separate
algorithms address it: Section 3.6 (general), Section 3.6.1 (branched gates),
and Appendix B (sparse witnesses).

## The quantity to be computed

Without `CV`, the prover needs the coefficients of the degree-`d` polynomial
(Eqn. 3):

```
e(X) := Σ_{j=0}^{d} (μ + X)^{d−j} · f_j^{V_sps}(acc + X · π)
```

With `CV`, the degree-`(d+2)` polynomial (Eqn. 4):

```
e(X) := Σ_{a=0}^{√ℓ−1} Σ_{b=0}^{√ℓ−1} (X·π.γ_a + acc.γ_a)(X·π.δ_b + acc.δ_b)
                                    · Σ_{j=0}^{d} (μ + X)^{d−j} · f_{j, a+b√ℓ}^{V_sps}(acc + X·π)
```

Here every input is a **linear function in the formal variable `X`**, and
`f_{j,i}` is the `i`-th component of `f_j`'s output. The cost of computing these
coefficients is written `L(V_sps, d)` and `L(V_sps, d+2)` in all the efficiency
tables.

**Footnote 4 is the headline complexity fact:** "if `f_d = Π_{i=1}^{d}(a_i + b_i·X)`
then a naive algorithm takes `O(d²)` time but using FFTs it can be computed in
time `O(d log² d)` `[CBBZ22]`." Hence the bound stated later:
`L(V_sps, d+2) = O(n·d·log²d)`.

## Algorithm 1 — the general method (Section 3.6)

"The algorithm has similarities with computing the round polynomials in a single
round of the sumcheck protocol `[LFKN90]`." Let `d' = d + 2`.

```
1.  For each i = 0 … d':
        e^{(i)}(X) := Σ_{a,b} (X·π.γ_a + acc.γ_a)(X·π.δ_b + acc.δ_b) · f_{i, a+b√ℓ}(acc + X·π)

2.  Compute e^{(i)}(j) for all j ∈ [0, i+2].
    Interpolate e^{(i)}(X) from these evaluations using fast interpolation (iFFT).

3.  Compute the coefficient form of  e(X) = Σ_{i=0}^{d'} e^{(i)}(X) · (μ + X)^{d'−i}
    by computing coefficients of each e^{(i)}(X)·(μ+X)^{d'−i} via FFT and summing
    coefficient-wise.   Complexity: O(d² log d).
```

### The practical observation that makes this cheap

> "In the worst case, this algorithm is equivalent to evaluating the circuit at
> `d+2` different inputs. However, it can perform **much better in practice**. The
> reason is that many of the `n` gates may only be low degree. E.g. 90% of the
> gates are degree 1 or 2 addition and multiplication gates, and 10% are more
> high degree gates. Then the prover only has to evaluate the 10% of the circuit
> at `d+2` points and 90% of the circuit only at 4 points."

**Why this works here and not in Plonk.** "Note that the selector polynomials are
static in the classification of NP plonkup (defined in Section 5). This means that
each gate has precisely the degree of the active component. This stands in
contrast to relations such as high-degree Plonk, where the selectors are
pre-processed, and the selectors are preprocessed witnesses. In Plonk and related
systems, each gate essentially has the same degree."

This is a genuinely important structural advantage: **static (non-witness)
selectors mean per-gate degree is known at compile time**, so the prover pays the
high-degree price only on the gates that are actually high-degree. In Plonk,
because selectors are preprocessed *witnesses*, the effective degree is uniform
across all gates and you pay the maximum everywhere. This also underwrites the
Protostar claim that "there is no additional cost for additional gate types (of
degree less than `d`) and additional selectors."

## Algorithm 2 — branched gates (Section 3.6.1)

This is what makes **non-uniformity free**. Suppose each gate decomposes as a sum
of `I` parts of which **at most one involves the new proof `π`**:

```
f_{i, a+b√ℓ}(acc + X·π)  =  g_pc(acc + X·π)  +  Σ_{j ∈ [I] \ {pc}} g_j(acc)
```

Caching algorithm:

```
1.  Initialize   V := Σ_{j=1}^{I} g_j(acc).

2.  On receiving a new NARK proof π during accumulation:
        set  f(acc) = V
        compute  U = g_pc(acc)
        for every k ∈ [1, i+2]:
            f(acc + k·π)  =  V + g_pc(acc + k·π) − U

3.  After the accumulation, with folding challenge α:
        V  ←  V + g_pc(acc + α·π) − U
```

Correctness: `V` is maintained as `Σ_{j∈[I]} g_j(acc)` for the *current*
accumulator, always.

**The payoff:** cost is proportional to evaluating `g_pc` alone — i.e.
`O(d·|C_pc|)` — instead of `O(d·(|C_1| + … + |C_I|))`. The `I−1` inactive branch
circuits are never re-evaluated; their contribution is carried in the cached
scalar `V` and patched with a single subtraction. This is the mechanism behind
"the IVC prover's computation is independent of `I`" and it is why Protostar's
non-uniformity beats SuperNova's (whose accumulator remains linear in the total
size of all instances).

## Algorithm 3 — sparse witnesses (Appendix B)

Goal: compute the cross-error commitments `E_j = Commit(ck, e_j)` in time
**independent of `|π.w|`**, depending only on `m := #non-zeros in π.w`.

**Stated limitation up front:** "the algorithm is **not fully compatible** with the
technique in Sect. 3.5 for compressing the number of verifier checks. We leave it
an open problem for integrating the algorithm with the `CV` trick."

### The required form (Eqn. 8)

```
e(X) = Σ_{i=1}^{c} a_i(acc + X·π) · [ T_i ∘ h_{i,1}(acc + X·π) ∘ … ∘ h_{i,d−i}(acc + X·π) ]
```

where `c` is a **constant**, and for every `i`:
- `a_i(acc + X·π)` is a degree-`i` polynomial whose coefficients are computable in
  `O(d³m)`;
- `T_i ∈ F^ℓ` is a **preprocessed** vector;
- each `h_{i,j}(acc + X)` is **linear**, and `h_{i,j}(x)` is sparse whenever `x`
  is (no more than `η` times as many non-zeros, `η` a constant; set `η = 1` for
  exposition).

Remark 5 notes Eqn. 8 is homogeneous — every one of the `c` terms has degree
exactly `d` — which is w.l.o.g. because lower-degree terms are padded with
`(acc.μ + X)^{d−i}`.

### The algorithm

```
1.  For every i ∈ [c]:  U_i := Commit(ck, T_i ∘ h_{i,1}(acc) ∘ … ∘ h_{i,d−i}(acc)).
    Also store acc and each T_i.

2.  On a new NARK proof π, for every i ∈ [c], k ∈ [d−i], commit to
        v_{i,k} := Σ_{S ⊆ [d−i], |S| = k}  T_i ∘ (∘_{j∈S} h_{i,j}(π)) ∘ (∘_{j∉S} h_{i,j}(acc))
    giving V_{i,k}.                                                        (Eqn. 9)

3.  For every i ∈ [c], k ∈ [0,d], compute the degree-k coefficient a_{i,k} of
        a_i(acc + X).       (a_{i,k} = 0 for k > i;  O(d³m) field ops total.)

4.  For j ∈ [d−1]:   E_j = Σ_{i=1}^{c} [ a_{i,j}·U_i + Σ_{ν=0}^{j−1} a_{i,ν}·V_{i,j−ν} ]
    (with V_{i,j} := commitment to the zero vector for j ∈ [d−i+1, d).)

5.  After accumulation with folding challenge α:  U_i ← U_i + Σ_{j=1}^{d−i} α^j · V_{i,j}.
```

### Complexity (Lemma 9)

> `O(d³m)` field operations and `O(d²m)` group operations.

The inner engine (proof of Lemma 9) is a small dynamic program. Fix `i`, set
`d' = d−i`. Extract the index set `S` of positions where some `h_{i,j}(π)` is
non-zero; `|S| ≤ d'm`, and outside `S` every `v_{i,k}` is zero. Then:

```
f_0^{(0)}[S] = T_i[S];   f_k^{(0)}[S] = 0  for k ∈ [d']
for j = 1 … d':
    f_0^{(j)}[S] = f_0^{(j)}[S] ∘ h_{i,j}(acc)[S]
    for k = 1 … j:
        f_k^{(j)}[S] = f_{k−1}^{(j−1)}[S] ∘ h_{i,j}(π)[S]  +  f_k^{(j−1)}[S] ∘ h_{i,j}(acc)[S]
```

and `f_k^{(d')}[S] = v_{i,k}[S]`. Cost `O(d'²|S|) = O(d³m)`. Each `v_{i,k}` has at
most `d'm` non-zeros so committing costs `O(d'm)` group ops.

Two supporting lemmas close it out:
- **Lemma 10** — `E_j` really is the commitment to the degree-`j` coefficient of
  `e(X)`, by the commitment homomorphism.
- **Lemma 11** — `U_i + Σ_{j=1}^{d−i} α^j V_{i,j}` is the commitment to
  `T_i ∘ h_{i,1}(acc'') ∘ … ∘ h_{i,d−i}(acc'')` for the updated accumulator
  `acc'' = acc + α·π`, i.e. step 5 correctly maintains the cache.

### Worked application: the lookup protocol

Appendix B ends by showing the lookup error polynomial fits Eqn. 8, with
`d = 2`, `c = 7`, writing `intp_v(X) := acc.v + X·π.v`:

```
e^{(1)}(X) = intp_μ(X) · ( Σ_{i∈[ℓ]} intp_{h_i}(X) − Σ_{i∈[T]} intp_{g_i}(X) )
e^{(2)}(X) = intp_h(X) ∘ (intp_w(X) + intp_r(X)·1) − intp_μ(X)² · 1
e^{(3)}(X) = intp_g(X) ∘ (intp_μ(X)·t + intp_r(X)·1_T) − intp_μ(X) · intp_m(X)
```

The 7 terms: 1 for `e^{(1)}` (with `T_1 = [1‖0^{ℓ+T}]`), 3 for `e^{(2)}`, 3 for
`e^{(3)}` — e.g. `a_5 = intp_μ(X)`, `T_5 = [0^{ℓ+1}‖t]`,
`h_{5,1} = [0^{ℓ+1}‖intp_g(X)]`. All the `h` vectors are `ℓ`-sparse, giving time
complexity `O(ℓ) ≪ T`.

## Summary: which algorithm to use when

| Situation | Algorithm | Cost |
|---|---|---|
| General high-degree verifier | Sec 3.6 (iFFT interpolation) | `O(d² log d)`; `L(V_sps,d+2) = O(n d log²d)` |
| Non-uniform / branch circuits | Sec 3.6.1 (caching `V`) | `O(d·\|C_pc\|)` not `O(d·Σ\|C_i\|)` |
| Sparse witness, large table | App. B (cached `U_i`, `V_{i,k}`) | `O(d³m)` F, `O(d²m)` G — **but incompatible with `CV`** |
| Lookup specifically | Sec 4.3 (6 cached commitments) | `O(ℓ)`, independent of `T` |

The last row is the specialised, `CV`-compatible instance actually used in
Protostar; Appendix B is the general theory behind it. See report 08.
