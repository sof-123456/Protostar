# 02 — The Problem and the Prior Work

## Why IVC at all

**Incrementally Verifiable Computation** (Valiant, TCC'08) lets a possibly
infinite computation run such that the correctness of the state can be verified
at any point. Its DAG generalisation is **PCD** (Proof-Carrying Data,
Chiesa–Tromer ICS'10).

Applications the paper cites: distributed computation, blockchains (Mina/Coda,
Proof of Necessary Work), verifiable delay functions (an IVC-based VDF is the
current Ethereum VDF candidate, MinRoot), verifiable photo editing (PhotoProof),
SNARKs for machine computations, and — the headline motivation — the **ZK-EVM**:
proving that Ethereum blocks as they exist today are valid.

## The historical arc

### Generation 1 — recursive SNARKs
Prove at each step that the previous step's SNARK verified. Cost: the recursive
circuit contains a whole SNARK verifier. Expensive; usually needs pairings,
trusted setup, and FFTs.

### Generation 2 — accumulation / folding (Halo, 2019)
Instead of *verifying* a proof at each step, **accumulate** its verification
check with all previous checks. An accumulator is an object such that:

```
accumulate(new proof, old accumulator) -> new accumulator
decide(new accumulator) = accept  ==>  all previously accumulated proofs were valid
```

The recursive statement now only has to assert *that the accumulation step was
performed correctly*, which is much cheaper than verifying a SNARK. The lineage
is Halo (BGH19) → BCMS20 → BCLMS21 → Nova (KST22).

Two surprises drove the field:
1. Accumulation can be *far* cheaper than SNARK verification.
2. **You don't even need a SNARK.** BCLMS21 showed a non-succinct **NARK**
   suffices, provided it has an efficient accumulation scheme.

The best of these reduce the recursive circuit to as few as **2 elliptic curve
scalar multiplications**, need only discrete log in the ROM, and require no
trusted setup, no pairings, no FFTs.

### The limitation Generation 2 hit

Nova and its relatives build accumulation for **one fixed (but universal) R1CS**
language, by taking a random linear combination of the accumulator and the new
proof. R1CS is `A·z ∘ B·z = C·z` — three matrices, degree-2, essentially
addition and multiplication gates. Two problems:

- **Inflexible.** Current constructions fix the R1CS matrices, used for *every*
  computation step.
- **Mismatched with modern SNARK practice.** Non-IVC SNARK development went the
  other way: high-degree custom gates (Plonk, HyperPlonk) and lookup gates
  (plookup, Caulk, Caulk+, Baloo, cq), where `n` lookups into a precomputed
  table of size `T` cost `O(n log n)` *independent of `T`*.

For a zkEVM this is acute: each OP-CODE is a different circuit, each uses
high-degree gates, and range proofs / bit operations want lookups.

## The immediate predecessors, and exactly what each failed to do

| Scheme | What it added | Limitation the paper identifies |
|---|---|---|
| **Nova** (KST22) | Folding for R1CS; recursive circuit ≈ 2 EC mults | Fixed degree-2 R1CS, single uniform circuit |
| **SuperNova** (KS22) | Select the right R1CS instance at runtime without a circuit linear in all instances | Recursive circuit still needs many (constant) hashes **and a hash-to-group gadget**; the accumulator — and therefore the final proof — is still **linear in the total size of all instances** |
| **Sangria** (Moh23) | Folding for Plonk-like systems with degree-2 gates | Higher-degree gates only sketched in future work, **no security proof**; group operations grow by a factor of `d`, cancelling out the benefit of using high-degree gates in the first place |
| **Origami** (ZV23) | Folding scheme for lookups via a product check | Uses degree-7 polynomials |
| **HyperNova** (KS23, concurrent) | IVC for CCS (generalises R1CS + Plonkish), high additive fan-in; recursive circuit ≈ 1 group mult | See the dedicated comparison below |

The meta-criticism the paper levels at all of these: they are "built from simple
underlying protocols performing a linear combination between an accumulator and
a proof. However, the constructions seem **ad hoc and need individual security
proof**." That observation is what motivates a generic compiler.

## The concurrent-work comparison: HyperNova

HyperNova (Kothapalli–Setty, ePrint 2023) is concurrent and the closest
competitor. It uses **CCS** (Setty–Thaler–Wahby) and is built on
**multi-folding schemes** over sumcheck.

**HyperNova's recursive circuit:** 1 group scalar multiplication,
`d·log n + in` hash operations, `O(d·log n + in)` field multiplications.

**Protostar's recursive circuit:** 3 group scalar multiplications,
`O(in + d)` field/hash operations — **entirely independent of `n`**.

The authors' argument that this trade is favourable:
- The 2 extra group operations are "likely offset" by lookup support and by
  having far fewer hashes and non-native field operations (`d` vs `d·log n`).
- HyperNova's lookup argument costs the accumulation prover `O(T)` field
  operations and the accumulation verifier `O(lk·log T)` field ops plus
  `O(log T)` hashes — undesirable when `T ≫ lk`. Protostar's prover is `O(lk)`
  and its verifier adds **no group scalar multiplications at all** for lookups.
- HyperNova "does not explicitly explain how to integrate lookup to Plonk/CCS in
  their IVC scheme or provide any explicit constructions for non-uniform
  computations."
- HyperNova's lookup does **not** support vector-valued lookups, which the
  authors call essential for zkEVM and bit-wise operations.

Fairness note: the authors concede that HyperNova's CCS "covers the Plonkish
relations" and "enables gates with a high additive fan-in", and that Protostar
also has no fan-in restriction — and they subsequently showed their compiler
applies directly to CCS too (Appendix C), which levels the playing field on
expressiveness.

## Table 1 of the paper, reproduced

| | Protostar | HyperNova | SuperNova |
|---|---|---|---|
| **Language** | Non-uniform degree-`d` Plonk/CCS | Degree-`d` CCS | R1CS (degree 2) |
| **P native** | yes | no | yes |
| extra P native | `\|w\|` G, `O(\|w\|d log²d)` F | `\|w\|` G, `O(\|w\|d log²d)` F | `\|w\|` G |
| — w/ lookup | `O(\|lk\|)` G | `O(T)` F | N/A |
| **P recursive** | `3G` | `1G` | `2G` |
| extra P recursive | `(d+O(1))H + H_in`, `(d+O(1))` F | `d log n·H + H_in`, `O(d log n)` F | `H_in + O(1)H + 1H_G` |
| — w/ lookup | `1H` | `O(log T)` H, `O(lk log T)` F | N/A |

Legend: `|w|` = number of non-zero witness entries for circuit `i`; `lk` = number
of lookups into a table of size `T`; `G` = group scalar multiplication;
`F` = field multiplication; `xH` = hashing `x` field elements; `H_G` =
hash-to-group; `H_in` = hashing the public input and accumulator instance.

Two details in the fine print worth keeping:
- "In Protostar `d` field elements are hashed **once** and in HyperNova `d`
  field elements are hashed **`log n` times**."
- SuperNova's `O(1)H` involves a constant number of hashes over two accumulator
  instances and one circuit verification key, via multiset-based offline memory
  checking in-circuit (SAGL18) — i.e. it is not as small as `O(1)` suggests.

Also note the **"P native: no"** row for HyperNova — its accumulation prover is
not natively supported in the same sense, a point the table asserts but the text
does not elaborate.
