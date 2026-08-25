# 12 — Critique, Caveats, and Open Problems

Reading the paper critically. Nothing here contradicts its results; these are the
things a reader would want flagged before building on it.

## Open problems the authors state explicitly

1. **Standard-model NARK + accumulation scheme.** "It remains an open problem to
   construct such schemes." Everything is in the ROM; Theorem 1 wants the standard
   model; the gap is bridged by the Fiat-Shamir Heuristic (Def. 9). Structurally
   unavoidable here — `V_acc` becomes a circuit, and a circuit cannot query a
   random oracle. Shared by all practical folding schemes.
2. **Integrating the Appendix B sparse-witness algorithm with `CV`.** "the
   algorithm is not fully compatible with the technique in Sect. 3.5 for
   compressing the number of verifier checks. We leave it an open problem for
   integrating the algorithm with the `CV` trick." The workaround used in
   Section 6 — apply `CV` only to `Π_GATE`, and use the specialised Section 4.3
   trick for lookups — is a construction-specific patch, not a general solution.
   Anyone instantiating the compiler with a *different* high-degree protocol that
   also needs sparse-witness error commitments will hit this.

## Internal inconsistency worth noting

**Abstract vs. Section 1 on the dependence on `I`.**

- Abstract: "The prover in each accumulation/IVC step is also only
  **logarithmic** in the number of supported circuits…"
- Section 1: "The IVC-prover, including the recursive statement, only requires one
  exponentiation per non-zero bit in the witness. The prover's computation is
  **independent of `I`**."
- Section 6: the branched-gate caching gives `O(d·|C_pc|)` rather than
  `O(d·Σ|C_i|)` — independent of `I`.

The body's "independent of `I`" is what the construction actually delivers for the
dominant costs. The abstract's "logarithmic" is presumably conservative, covering
e.g. indexing into the branch-circuit configuration or the `2I` degree-2 selector
checks in step 2 of `Π_mplkup` (which are `O(I)` for the verifier, though the
*commitment* cost is sparse). **These `2I` selector checks are worth attention:**
they are `O(I)` verification equations, and while low-degree and folded into the
long error vector, an implementer should confirm they do not reintroduce an `O(I)`
per-step prover cost in their instantiation.

## No implementation, no benchmarks

The paper contains **zero** experimental results: no implementation, no wall-clock
times, no constant factors, no curve choice, no comparison of concrete proving
cost against Nova/SuperNova/HyperNova. Everything is asymptotic analysis plus
operation counts.

Why this matters for the central claim: the headline comparison is
**3G vs 1G vs 2G** in the recursive circuit, offset against `d` vs `d·log n`
hashes and non-native field operations. That trade is *entirely* decided by
constants — how expensive an in-circuit Poseidon/Rescue hash is relative to an
in-circuit scalar multiplication on your curve cycle, and how expensive non-native
field arithmetic is. The paper's argument ("the 2 additional group operations
compared to HyperNova are **likely** offset by…") is a plausibility argument, not
a measurement. It is probably right — `log n ≈ 20–30` is a big multiplier — but it
is asserted, not shown.

(Context: Protostar was subsequently implemented in several projects, and the
compiler is widely regarded as sound and practical. But that validation is not in
this document.)

## The completeness fork

Restating from report 11 because it is the most likely source of a
spec-vs-implementation divergence:

`Π_LK` and `Π_VLK` are **not** perfectly complete. The patch costs verifier degree
(2→3 for `Π_LK`, 3→5 for `Π_VLK`). The authors recommend *not* implementing the
patch, since the completeness error `(ℓ+T)/|F|` is negligible — but perfect
completeness is required by the IVC definition and by BCLMS21's Theorem 1.

So the pragmatic deployment is formally outside the theorem statement. This is a
reasonable engineering call, but it should be a recorded decision, not an
accident. Note the degree increase is not free either: for `Π_VLK` going 3→5 feeds
into `L(V_sps, d+2)` and the error-term count.

## Where "no FFTs" needs qualification

The abstract says "the prover does not need to compute any FFTs." Accurate as
intended — no FFTs over the **witness/evaluation domain**, which is what makes
Plonk-style provers memory-hungry and forbids arbitrary field choice.

But Section 3.6 **explicitly recommends iFFT** for interpolating `e^{(i)}(X)` and
FFTs for computing coefficients of `e^{(i)}(X)·(μ+X)^{d−i}`, with complexity
`O(d² log d)`; footnote 4 cites `[CBBZ22]` for the `O(d log² d)` method; and
`L(V_sps, d+2) = O(n·d·log²d)` appears in Corollary 1. Table 1 lists
`O(|w| d log²d)` field operations under "extra P native."

So: FFTs of size `O(d)`, not size `O(n)`. Small, and the same term appears in
HyperNova's column. But "any FFTs" is literally too strong, and a reader budgeting
prover cost should carry the `d log²d` factor.

## Costs that are asymptotically fine but concretely large

- **`V_Protostar`: `n + Σ_{i∈[I]} C_i + T + lk` field operations.** The
  `Σ_{i∈[I]} C_i` term — "the cost of evaluating **all** circuits on some random
  input" — is paid once by the final verifier, not per step, so it does not
  compound. But for a zkEVM with hundreds of opcode circuits it is not small, and
  it is the one place where the total number of branch circuits does enter a cost.
- **Proof size / accumulator size `O(cn + T + lk)`.** Linear in the **lookup table
  size `T`**. The *prover per step* is independent of `T` (the whole point of
  Section 4.3), but the accumulator carries `acc.m ∈ F^T` and `acc.g ∈ F^T`. For a
  `2^32`-entry table this is fatal to the proof size unless the decider is
  outsourced. The paper is silent on this specific tension: it advertises
  table-size-independent *prover* work while the *accumulator* remains `O(T)`.
  Anyone using large tables must plan on the SNARK-wrapped decider — which brings
  us to:
- **Outsourcing the decider breaks strict IVC completeness.** "when outsourcing
  the decider, the IVC cannot continue. This breaks the strict completeness
  requirement of IVC, which says that any prover can continue from any valid IVC
  proof. Nevertheless, this may be fine for some applications." Combined with the
  point above, the practical deployment is: run the IVC, and at the end wrap with
  a SNARK, accepting that you have produced a terminal proof. Fine for a
  block-proving pipeline; not fine for a system that must resume from a published
  proof.

## Zero-knowledge is entirely absent

Not a criticism of the paper's scope — it never claims ZK — but a caveat for
anyone reaching for it. The commitment scheme is required only to be **binding**,
not hiding. The decider receives `acc.w`. `cm[sps]` sends the openings. Nothing
here hides the witness.

Adding ZK means hiding commitments (Pedersen with randomness) plus a zkSNARK for
the decider, plus re-checking that the homomorphic error-term manipulations
survive the added randomness — because every step of Section 4.3's six-cached-
commitment trick relies on exact linear relations between commitments. That
composition is unanalysed here.

## Presentational and reproducibility notes

- **Lemma 3's arity vector is typeset ambiguously** in the PDF text layer
  (`(a_1,…,ℓ, a_{k−1}, ℓ)`). From the proof — one extra level of arity `ℓ` for the
  new `γ` round — the intended statement is `(a_1,…,a_{k−1}, ℓ)`.
- **Theorem 3's cost table has overlapping cells** in the extracted text layer
  (the `P_IVC recursive` / `V_IVC` hash rows interleave). Report 10 reconstructs
  it from Appendix A's itemised costs; the reconstruction is self-consistent with
  Corollary 1 at `k = 2`.
- **`Π_select` has no numbered special-soundness lemma**, only an inline argument.
  It is 1-special-sound (the prover sends the witness), so nothing is missing
  mathematically.
- **`Corollary 1`'s `3G` vs `Theorem 3`'s `k+2 = 4G`.** The corollary's figure is
  tighter than the generic bound. The derivation is not spelled out; an
  implementer should re-derive the group-operation count for their own
  instantiation rather than trusting `3G` as a general law.
- **Uniformity assumption in Section 6.** All `I` circuits are assumed to share
  `n, c, d, m, in, lk`. "The scheme naturally extends when different branch
  circuits have different parameters" — asserted, not shown. For a zkEVM, where
  opcode circuits differ wildly in size, the extension is the case that matters,
  and the accounting for it is left to the reader.

## What the paper gets unambiguously right

Worth stating plainly, because the list above is a list of caveats:

- **The central abstraction is the right one.** Characterising a protocol by
  `(k, d, ℓ)` and nothing else, and showing that these three numbers alone
  determine the recursive-circuit cost, is a genuine simplification of the field.
  Appendix C is the proof: porting to CCS took one trivial protocol and no new
  security argument.
- **It eliminates a class of ad-hoc security proofs.** The criticism it levels at
  Sangria and Origami — "constructions seem ad hoc and need individual security
  proof" — is fair, and the paper actually fixes it. Sangria's high-degree
  extension had *no* proof; here high degree is handled for arbitrary `d` by
  construction.
- **The log-derivative lookup with the six cached commitments is a strong result
  independently of the rest.** `O(lk)` accumulation prover, degree 2, zero extra
  recursive group operations, table-size-independent — and vector-valued lookups
  on top.
- **The branched-gate caching algorithm (3.6.1) is the right answer to
  non-uniformity**, and it is cleaner than SuperNova's (no hash-to-group gadget,
  accumulator not linear in the sum of all circuits).
- **The paper is candid about its gaps** — the dotted arrow in Figure 1, the two
  stated open problems, the completeness caveats, the decider-outsourcing
  trade-off. That candour is why the caveat list above could be assembled largely
  from the paper's own sentences.

## If you are implementing this

A short checklist distilled from the above:

1. Decide the perfect-completeness question for lookups and record it.
2. Confirm the `2I` selector checks do not reintroduce `O(I)` per-step prover cost
   in your parameterisation.
3. Budget `O(d log²d)` per witness element for error-term interpolation; pick `d`
   with that in mind, not just gate expressiveness.
4. Apply `CV` **only** to your high-degree sub-check; verify which of your
   equations are actually degree `> 2`.
5. Plan the decider: `O(T)` accumulator means large tables force a SNARK wrapper,
   which forecloses resuming the IVC.
6. Re-derive your own recursive group-operation count; do not assume `3G`.
7. If you need ZK, treat it as new design work, not a configuration flag.
