# 01 — Paper Overview

## Metadata

| Field | Value |
|---|---|
| Title | Protostar: Generic Efficient Accumulation/Folding for Special-sound Protocols |
| Authors | Benedikt Bünz (Stanford University, Espresso Systems); Binyi Chen (Espresso Systems) |
| Venue / ID | IACR Cryptology ePrint Archive, Report **2023/620** |
| Version date | December 6, 2023 |
| Length | 57 pages (6 sections + Appendices A, B, C) |
| File | `2023-620.pdf` (680,709 bytes) |

## Structure of the document

```
1  Introduction ................................ p.3
   1.1 Technical overview ...................... p.7
   1.2 Organization ............................ p.11
2  Preliminaries .............................. p.11
   2.1 Special-sound protocols & Fiat-Shamir
   2.2 Adaptive Fiat-Shamir
   2.3 Commitment scheme
   2.4 Incremental Verifiable Computation (IVC)
   2.5 Simple Accumulation
3  Protocols .................................. p.16   <-- the generic compiler
   3.1 Special-sound protocols
   3.2 Commit and open
   3.3 Fiat-Shamir transform
   3.4 Accumulation scheme for V_NARK ......... p.19   <-- core construction
   3.5 Compressing verification checks ....... p.25   <-- the CV trick
   3.6 Computation of error terms ............ p.30
       3.6.1 Dealing with branched gates
4  Special-sound subprotocols ................. p.32   <-- the building blocks
   4.1 Permutation | 4.2 High-degree gate | 4.3 Lookup
   4.4 Vector-valued lookup | 4.5 Circuit selection
5  Special-sound protocols for Plonkup ........ p.39
6  Protostar .................................. p.41   <-- the instantiation
A  Accumulation for high/low degree verifier .. p.49
B  Cross error commitments for sparse witnesses p.51
C  Protostar for CCS .......................... p.54
```

Note the shape: **Sections 2–3 are generic machinery**, **Sections 4–6 are one
instantiation of it**. Almost all of the reusable value is in Section 3.

## The abstract, decoded claim by claim

> "We provide a generic, efficient accumulation (or folding) scheme for any
> `(2k−1)`-move special-sound protocol with a verifier that checks `ℓ` degree-`d`
> equations."

**Claim 1 — Genericity.** The input to the compiler is characterised by exactly
three numbers: `k` (number of prover messages), `d` (verifier degree), `ℓ`
(number of verification equations). Nothing else about the protocol matters.
This is the paper's main conceptual contribution — prior folding schemes
(Nova, Sangria, Origami) were each hand-designed for one constraint system and
needed an individual security proof.

> "The accumulation verifier only performs `k+2` elliptic curve multiplications
> and `k+d+O(1)` field/hash operations."

**Claim 2 — Recursive-circuit cost.** The `k+2` figure requires the `CV[·]`
optimisation of Section 3.5 (see report 06). Without it the count is `k+d−1`
group multiplications. The `k+2` version is favourable whenever `d ≥ 3`.

> "…this enables building efficient IVC schemes where the recursive circuit only
> depends on the number of rounds and the verifier degree of the underlying
> special-sound protocol but not the proof size or the verifier time."

**Claim 3 — What the recursive circuit does *not* depend on.** This is the
economically important part. The recursive statement is independent of `|w|`,
of the lookup table size `T`, of the number of gates `n`, and of the number of
branch circuits `I`. Compare HyperNova, whose recursive circuit carries
`d·log n` hashes.

> "Protostar is a non-uniform IVC scheme for Plonk that supports high-degree
> gates and (vector) lookups. The recursive circuit is dominated by 3 group
> scalar multiplications and a hash of `d` field elements."

**Claim 4 — The instantiation.** `3G` because the compiled protocol has `k = 2`,
so `k + 2 = 4` in general but the concrete accounting in Corollary 1 lands at
`3G`. Non-uniformity (choosing 1 of `I` circuits per step) is bought with a
degree-2 selector sub-protocol that raises the verifier degree from `d` to
`d+1` — described by the authors as "negligible overhead".

> "The scheme does not require a trusted setup or pairings, and the prover does
> not need to compute any FFTs."

**Claim 5 — Assumptions.** Only a binding *homomorphic* vector commitment is
needed; Pedersen over any prime-order group works, so security rests on
discrete log in the ROM. Caveat: "no FFTs" means no FFTs *over the witness
domain*. FFTs of size `O(d)` are still used to interpolate the error-term
polynomial (Section 3.6 explicitly recommends iFFT), and `L(V_sps, d)` is
bounded by `O(n·d·log²d)`.

> "The prover in each accumulation/IVC step is also only logarithmic in the
> number of supported circuits and independent of the table size in the lookup."

**Claim 5b.** The table-size independence is the strongest single result in
Section 4 and is what makes the lookup argument competitive. See report 08 for
the six cached commitments that make it work. (The "logarithmic in the number of
supported circuits" phrasing in the abstract contradicts Section 1's
"independent of `I`" — flagged in report 12.)

## The two research questions the paper poses

Stated verbatim on p.4:

1. **Recipe for accumulation.** "Is there a general recipe for building
   accumulation schemes? Can we formalize this recipe, simplifying the task of
   constructing secure and efficient accumulation schemes?"
2. **Efficient accumulation for ZK-EVM.** "Can we build an accumulation/folding
   scheme for a language that combines the benefits of the most advanced proof
   systems today? Can we support multiple circuits, high-degree, and lookup
   gates?"

Both are answered affirmatively — question 1 by Section 3 (Theorem 3),
question 2 by Section 6 (Corollary 1).

## Target application

The paper is explicitly motivated by the **zkEVM**: each VM opcode is a
different circuit (hence non-uniformity), opcodes need high-degree custom gates,
and bit operations / range checks need lookups into large precomputed tables
(hence table-size-independent lookups). A secondary motivation given is a
per-smart-contract or per-transaction-type circuit selector, where proving cost
scales with the size of the *invoked* contract rather than the sum of all of them.
