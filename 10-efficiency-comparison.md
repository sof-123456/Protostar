# 10 — Efficiency: Theorem 3, Corollary 1, and Table 1 Decoded

## Theorem 3 — the generic result

> Let `F` be a finite field with `|F| ≥ 2^λ` and `cm = (Setup, Commit)` a binding
> homomorphic commitment scheme for vectors in `F`. Let `sps = (P_sps, V_sps)` be
> a special-sound protocol for an **NP-complete** relation `R_NP` with:
>
> - it is `(2k−1)`-move;
> - it is `(a_1,…,a_{k−1})`-out-of-`|F|` special-sound, with knowledge error
>   `κ = 1 − ∏_{i=1}^{k−1}(1 − a_i/|F|) = negl(λ)`;
> - inputs in `F^{in}`;
> - verifier of degree `d = poly(λ)` with output in `F^ℓ`.
>
> Then, under the Fiat-Shamir heuristic for a hash `H` (Def. 9), there exist two
> IVC schemes `IVC` and `IVC_CV` with predicates in `R_NP` and the efficiencies
> tabulated below.

Note the **NP-completeness** requirement on `R_NP` — needed to apply BCLMS21's
Theorem 1, which is stated for circuit satisfiability.

### The cost table

| | **No CV** | **With CV** |
|---|---|---|
| **`P_IVC` native** | `Σ_{i∈[k]} \|m_i\|` + `(d−1)` G<br>`P_sps` + `L(V_sps, d)` | `Σ_{i∈[k]} \|m_i^≠\|` + `O(√ℓ)` G<br>`P_sps` + `L(V_sps, d+2)` |
| **`P_IVC` recursive** | `k + d − 1` G<br>`k + in` F<br>`(k + d + O(1))`H + `1·H_in` | **`k + 2`** G<br>`k + in + d + 1` F<br>`(k + d + O(1))`H + `1·H_in` |
| **`V_IVC`** | `Σ_{i∈[k]} \|m_i\|` G<br>`V_sps`<br>`k + in` F | `Σ_{i∈[k]} \|m_i\|` + `O(√ℓ)` G<br>`O(ℓ)` + `V_sps`<br>`k + in + 1` F |
| **`\|π_IVC\|`** | `k + 1` G<br>`Σ_{i∈[k]} \|m_i\|` F | `k + 2` G<br>`Σ_{i∈[k]} \|m_i\|` + `O(√ℓ)` |

*Table-layout note:* the `(k + d + O(1))H` cell for the CV column is garbled in the
PDF's text layer (two table cells overlap). It is reconstructed from Appendix A's
itemised cost — "`k−1` queries to `ρ_NARK` with **constant-sized** inputs and 1
query to `ρ_acc` with input size `d + O(1)`" — which sums to `k + d + O(1)` hashed
elements. Corollary 1's `d + O(1)`H at `k = 2` is consistent with this reading.

### Legend

- `|m_i|` — prover message length; `|m_i^≠|` — number of **non-zero** elements.
  This distinction is where sparsity pays: `P_IVC` native commits only to
  non-zeros.
- `G` in rows 1–3 is the **total length of the messages committed**, not a count
  of group multiplications (for `|π_IVC|` it *is* a count of commitments).
- `F` = field operations. `H` = total input length to the hash. `H_in` = hashing
  the public input and accumulator instance.
- `P_sps` / `V_sps` = cost of running the underlying prover / algebraic verifier.
- `L(V_sps, d)` = cost of computing the coefficients of Eqn. 3;
  `L(V_sps, d+2)` = cost for Eqn. 4. See report 07.
  **Bound: `L(V_sps, d+2) = O(n·d·log²d)`.**

### Reading the table

**The one row that matters is row 2** (`P_IVC` recursive) — it is the recursive
circuit, and it is the only thing whose cost compounds across IVC steps.

The `CV` trade, made concrete:

| | group mults | field ops |
|---|---|---|
| No CV | `k + d − 1` | `k + in` |
| With CV | `k + 2` | `k + in + d + 1` |

You pay `d + 1` extra field operations and gain `d − 3` fewer group scalar
multiplications. Since one group scalar multiplication costs orders of magnitude
more than one field multiplication in-circuit, **`CV` wins for any `d ≥ 3`** — as
the paper states.

Also note what `CV` costs elsewhere: `O(√ℓ)` more committed elements for the
prover, `O(ℓ)` more verifier work, `O(√ℓ)` larger proof. All acceptable, none in
the recursive circuit.

### Proof structure (Theorem 3)

Two NARKs are constructed:

```
NARK    = FS[cm[sps]]
NARK_CV = FS[cm[CV[sps]]]
```

then `(P_acc, V_acc) = acc[NARK]` from Section 3.4 and
`(P_acc,HL, V_acc,HL) = acc_HL[NARK_CV]` from Appendix A, then Theorem 1 is applied
to each.

**Security accounting:**
- By Lemmas 1 + 2, `NARK` has knowledge error
  `(Q+1)·(1 − ∏_{i}(1 − a_i/|F|))` for `R^{R_NP}_cm`. A witness for `R^{R_NP}_cm`
  is either a real witness or a binding break; the latter is `negl(λ)`. So
  `NARK` has error `κ = (Q+1)·(1 − ∏(1 − a_i/|F|)) + negl(λ)` for `R_NP`.
- Using Lemma 3 as well, `NARK_CV` has error
  `κ' = (Q+1)·(1 − (1 − ℓ/|F|)·∏(1 − a_i/|F|)) + negl(λ)`. The extra
  `(1 − ℓ/|F|)` factor is the price of the `CV` challenge round.
- Theorem 2 / Corollary 2 give the accumulation schemes, with negligible error
  since `d = poly(λ)`. The Fiat-Shamir heuristic moves everything to the standard
  model. Theorem 1 yields the IVC schemes.

**Efficiency accounting:** `P_IVC` runs `P_sps`, commits to all messages, computes
`e_1..e_{d−1}` (by symbolically evaluating Eqn. 4 with linear functions as inputs)
and commits to them. The accumulator instance is `in` field elements for the input,
`k−1` for the interactive challenges, 1 for the folding challenge `α`, plus `k`
commitments for the messages and `d−1` for the error terms.

For `IVC_CV`: one extra message `m_{k+1}` of length `O(√ℓ)` to commit; error-term
count rises from `d−1` to `d+1`, **but each is a single field element**, so the
identity commitment is free; there is one separate error vector `e ∈ F^{2√ℓ}` for
the `O(√ℓ)` degree-2 checks, needing one real commitment. Accumulator instance:
`in` + `k` challenges + 1 folding challenge + `k+1` message commitments + `d+1`
field elements for the high-degree error terms + 1 commitment for `e`.

## Corollary 1 — Protostar concretely

For `m = 1` gate type per circuit and `in = 1`:

| `P` native | `P` recursive | `V` | `\|π\|` |
|---|---|---|---|
| `O(\|w\| + lk)` G | **`3G`** | `O(cn + T + lk)` G | `O(cn + T + lk)` |
| `L(C_pc, d+2) + 2lk` F | `d + 4` F | `n + Σ_{i∈[I]} C_i + T + lk` F | |
| | `d + O(1)` H + `1·H_in` | | |

Sanity check against Theorem 3: `Π_mplkup` has `k = 2`, so `k + 2 = 4` group
mults from the generic table, and Corollary 1 reports `3G`. The reduction comes
from the concrete accounting — `Π_mplkup`'s second prover message contributes no
separate commitment fold in the way the generic bound assumes (the generic `k+2`
is an upper bound covering `k` message commitments plus 2 for the hi/low error
terms). The `3G` figure is the one quoted in the abstract and Table 1.

## Table 1 — the head-to-head, re-read

| | Protostar | HyperNova | SuperNova |
|---|---|---|---|
| Language | Non-uniform degree-`d` Plonk/CCS | Degree-`d` CCS | R1CS (degree 2) |
| P native | yes | no | yes |
| extra P native | `\|w\|` G, `O(\|w\|d log²d)` F | `\|w\|` G, `O(\|w\|d log²d)` F | `\|w\|` G |
| — w/ lookup | `O(\|lk\|)` G | `O(T)` F | N/A |
| **P recursive** | **`3G`** | `1G` | `2G` |
| extra P recursive | `(d+O(1))H + H_in`,<br>`(d+O(1))` F | `d log n·H + H_in`,<br>`O(d log n)` F | `H_in + O(1)H + 1H_G` |
| — w/ lookup | `1H` | `O(log T)` H,<br>`O(lk log T)` F | N/A |

### The three comparisons that actually decide the trade

**1. Group multiplications in the recursive circuit: 3 vs 1 vs 2.**
Protostar loses this line. HyperNova's `1G` is the best in the table. Protostar's
argument is that the other two lines more than compensate.

**2. Hashes and non-native field operations: `d` vs `d·log n`.**
This is Protostar's strongest quantitative claim. "In Protostar `d` field elements
are hashed **once** and in HyperNova `d` field elements are hashed **`log n`
times**." In-circuit hashing and non-native field arithmetic are notoriously the
dominant recursive-circuit cost in practice, so a `log n` factor here (`log n` is
20–30 for realistic circuits) plausibly dwarfs 2 extra group multiplications.
Protostar's recursive circuit is **entirely independent of `n`**; HyperNova's is
not.

**3. Lookups.** Protostar: `O(lk)` group ops native, **`1H`** recursive, and
**zero extra group scalar multiplications**. HyperNova: `O(T)` field ops native,
`O(log T)` hashes and `O(lk·log T)` field ops recursive. When `T ≫ lk` — the
normal case for zkEVM range/bitwise tables, where `T` might be `2^16`–`2^32` and
`lk` a few thousand — this is not a close call. SuperNova has no lookup support at
all.

Plus two qualitative wins the table cannot express: HyperNova has no explicit
non-uniform construction and no **vector-valued** lookup, both of which Protostar
provides.

### The fine print worth keeping in view

- SuperNova's `O(1)H` "involves constant number of hashes to the input of two
  accumulator instances and one circuit verification key, by using multiset-based
  offline memory checking in a circuit `[SAGL18]`" — i.e. that `O(1)` hides real
  machinery, plus a **hash-to-group** gadget (`1H_G`), which is expensive
  in-circuit.
- SuperNova's accumulator, and therefore its final proof, is **linear in the total
  size of all `I` instances**. Protostar's is `O(cn + T + lk)` — independent of the
  sum over branch circuits. For a zkEVM with hundreds of opcode circuits this is
  the difference between feasible and not.
- The `Σ_{i∈[I]} C_i` term in Protostar's `V` column — evaluating all circuits on a
  random input — is paid **once**, by the verifier/decider, not per IVC step.
- `O(|w| d log²d)` appears in **both** Protostar's and HyperNova's native prover
  cost. That is the error-polynomial interpolation, and it is the honest answer to
  "the prover computes no FFTs": no FFTs over the witness domain, but `O(d log²d)`
  work per witness element.

## What the tables do *not* contain

**There are no benchmarks anywhere in this paper.** No implementation, no wall-clock
numbers, no constant factors, no comparison of concrete proving times. Everything
above is asymptotic accounting plus operation counts. The `3G` vs `1G` vs `2G`
comparison in particular is exactly the kind of claim where constants and curve
choice decide the outcome. See report 12.
