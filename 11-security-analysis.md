# 11 — Security Analysis: Every Claim and What It Rests On

## The trust surface, in one list

Protostar's security requires **all** of the following:

1. **A binding, homomorphic commitment scheme** over a prime-order group. With
   Pedersen this is the **discrete logarithm assumption**. No trusted setup, no
   pairings, no knowledge-of-exponent, no algebraic group model.
2. **The random oracle model** for two oracles, `ρ_NARK` and `ρ_acc`.
3. **The Fiat-Shamir Heuristic (Def. 9)** — replacing those random oracles with a
   concrete cryptographic hash `H` preserves negligible knowledge error in the
   standard/CRS model. **This is an unproven heuristic and the paper says so.**
4. **`|F| ≥ 2^λ`** and `char(F) > max(ℓ, T)` (needed for Haböck's Lemma 4).
5. **`d = poly(λ)`.**
6. BCLMS21's Theorem 1, which additionally requires **constant-depth compliance
   predicates** and `V_acc` **sublinear in its input**.

Item 3 is the weak link, and it is structural rather than incidental — see below.

## Every soundness statement in the paper

| Result | Statement | Where used |
|---|---|---|
| **Lemma 1** `[AFK22]` | FS of `(a_1..a_μ)`-out-of-`N` special-sound proof is knowledge sound with error `(Q+1)·(1 − ∏(1 − a_i/N))` | Everywhere. The workhorse. |
| **Lemma 2** | `cm[sps]` is `(a_1,…,a_μ)`-special-sound for `R^R_cm` — **arity unchanged** | Theorem 3 |
| **Lemma 3** | `CV[sps]` is `(a_1,…,a_{k−1}, ℓ)`-special-sound | Theorem 3, Corollary 1 |
| **Theorem 2** | The Sec 3.4 accumulation scheme is perfectly complete with knowledge error `(Q+1)(d+1)/\|F\| + negl(λ)` | Theorem 3 |
| **Corollary 2** | `acc_HL` (Appendix A) is perfectly complete with knowledge error `(Q+1)(d+4)/\|F\| + negl(λ)` | Theorem 3, Corollary 1 |
| **Lemma 5** | perfectly-complete `Π_LK` is `2(ℓ+T)`-special-sound | Lemma 7 |
| **Lemma 6** | perfectly-complete `Π_VLK` is `[1+(v−1)(ℓ+T−1), 2(ℓ+T)]`-special-sound | (vector lookup variant) |
| **Lemma 7** | `Π_plonkup` is `2(T+\|L\|)`-special-sound | Lemma 8 |
| **Lemma 8** | `Π_mplkup` is `2(T+lk)`-special-sound | Corollary 1 |
| **Lemma 9/10/11** | correctness + `O(d³m)` F / `O(d²m)` G complexity of the Appendix B sparse algorithm | (efficiency only, not soundness) |
| **Theorem 1** `[BCLMS21]` | standard-model NARK + accumulation scheme ⟹ IVC | Theorem 3 |
| **Theorem 3** | the generic `sps → IVC` compiler, with costs | Corollary 1 |
| **Corollary 1** | Protostar is a secure IVC for `R_mplkup` with knowledge error `(Q+1)(n + 2(T+lk))/\|F\| + negl(λ)` | — |

`Π_perm`, `Π_GATE`, `Π_ccs` are **1-special-sound** (perfectly sound): the prover
sends the witness and the verifier checks it, so a single accepting transcript
contains the witness. `Π_select`'s soundness is argued inline, not as a numbered
lemma.

## The single proof technique, used seven times

Every special-soundness proof in this paper is the same argument:

1. Collect enough accepting transcripts (the arity vector).
2. Construct a polynomial whose coefficients encode the thing you want to prove.
3. Observe it vanishes at more points than its degree.
4. Conclude it is identically zero, and read off the coefficient you care about.

Concretely:

| Where | The polynomial | Degree | Points |
|---|---|---|---|
| Theorem 2 | `p(X) = Σ_j (X+μ)^{d−j} f_j(acc + X·π) − e − Σ e_j X^j` | `d` | `d+1` challenges `α` |
| Lemma 3 | `p(X) = Σ_j X^j · V_{sps,j}(msg)` | `ℓ−1` | `ℓ` challenges `γ` |
| Lemma 5 | `p(X) = Π(X+w_k)Π(X+t_j)[Σ 1/(X+w_i) − Σ m_i/(X+t_i)]` | `ℓ+T−1` | `ℓ+T` challenges `r` |
| Lemma 6 | bivariate `p(X,Y)`, same shape with `w_i(Y)`, `t_i(Y)` | `(ℓ+T−1, (v−1)(ℓ+T−1))` | a grid of `(r, β)` |

The extra tooling: a **Vandermonde matrix** in Theorem 2 to solve for `e'` and the
`e_j` from `d+1` commitment equations; a **pigeonhole argument** in Lemmas 5 and 6
to discard the `≤ ℓ+T` bad challenges where a denominator vanishes (this is the
source of the factor-2 in `2(ℓ+T)`).

The uniformity of the technique is precisely why the framework is a *recipe*: to
add a feature you need only find its polynomial and count its roots.

## The two most instructive proof details

### Theorem 2's coefficient extraction

The zero polynomial

```
p(X) = Σ_{j=0}^{d} (X + acc.μ)^{d−j} · f_j(X·pi + acc.pi, [X·m_i + acc.m_i], [X·r_i + acc.r_i]) − e − Σ_{j=1}^{d−1} e_j X^j
```

has:
- **constant term** `= Σ_j acc.μ^{d−j} f_j(acc.…) − e`, and its vanishing is
  exactly `D(acc) = 0` — the old accumulator was valid;
- **degree-`d` term** `= Σ_j f_j(pi, [π.m_i], [π.r_i])`, and its vanishing is
  exactly `V_NARK(pi, π) = 0` — the new proof was valid (given `V_acc` separately
  verified the `r_i` were correctly derived).

Two facts extracted from opposite ends of one polynomial. This is the paper's
most elegant moment.

### Where binding is actually used

Twice, and both times in the same way — as an escape hatch in the extractor:

1. **Lemma 2.** If two transcripts have inconsistent openings at a shared node,
   that *is* a witness for `R^R_cm` (a binding break). So the extractor never
   fails; it either outputs a real witness or a break.
2. **Theorem 2, step 2.** After recovering `π.m_j` and `acc.m_j` from two
   challenges, if any *third* challenge's accumulator disagrees with the linear
   decomposition, that disagreement yields a commitment collision. "This happens
   with negligible probability by assumption" — and this is exactly where the
   `+ negl(λ)` in every knowledge-error bound comes from.

## Knowledge-error budget for Protostar end to end

```
Π_mplkup                 2(T + lk)-special-sound                        (Lemma 8)
CV[Π_GATE part]          adds one arity-n level                         (Lemma 3)
  ⟹ FS[cm[CV[Π_mplkup]]] knowledge error  (Q+1)·(n + 2(T+lk))/|F| + negl(λ)
acc_HL                   knowledge error   (Q+1)·(d+4)/|F| + negl(λ)    (Corollary 2)
  ⟹ IVC via Theorem 1 + Fiat-Shamir heuristic
```

With `|F| ≥ 2^λ ≈ 2^256`, `n`, `T`, `lk`, `d`, `Q` all polynomial, every term is
comfortably negligible. **There is no tightness problem here** — the security loss
is a small polynomial factor over the field size, not the usual
`recursion-depth × soundness-error` blowup.

Note also that the knowledge error does **not** degrade with the number of IVC
steps: BCLMS21's Theorem 1 handles constant-depth compliance predicates and the
accumulation scheme's error is per-step-independent. That is a real advantage of
the accumulation route over naive recursive composition.

## The Fiat-Shamir gap, stated precisely

This deserves its own section because the paper is unusually candid about it.

> "Note that both the NARK and accumulation scheme we construct are in the random
> oracle model. However, Theorem 1 requires a NARK and an accumulation scheme in
> the **standard model**. It remains an **open problem** to construct such
> schemes. However, we can heuristically instantiate the random oracle with a
> cryptographic hash function and assume that the resulting schemes still have
> knowledge soundness."

Figure 1's final arrow is drawn **dotted** for this reason: "This last connection
is dotted as it requires heuristically replacing random oracles with cryptographic
hash functions."

**Why this is not a mere formality.** The BCLMS21 compiler *implements `V_acc` as a
circuit*. `V_acc` makes random-oracle queries (`ρ_NARK` for the `r_i`, `ρ_acc` for
`α`). You cannot put a random oracle in a circuit — you must put a concrete hash
in. So the heuristic is not an optional convenience for a cleaner theorem; it is
**forced by the construction**. This is a well-known and universally accepted gap
shared by every practical IVC/folding scheme (Halo, Nova, SuperNova, HyperNova
included) — but it is a gap, and it is the one place where "provably secure" is
doing less work than it appears to.

## The completeness wrinkles

Perfect completeness is required by the IVC definition (Def. 7, "perfect
adversarial completeness") and by BCLMS21's Theorem 1. Two protocols do not have
it natively:

- **`Π_LK`** — if `w_i + r = 0` or `t_i + r = 0`, the prover message is undefined.
  Completeness error `(ℓ+T)/|F|`. Patch: extra multiplicative factors, raising the
  verifier degree **2 → 3**.
- **`Π_VLK`** — same issue, degree **3 → 5**.
- **`Π_plonkup`** — inherits it; degree becomes `max(d, 3)`.

The authors' stance, stated twice: "This completeness error can likely be ignored
in practice, and these checks do not need to be implemented. However, to achieve
the full definition of PCD (which has perfect completeness) and use Theorem 1 by
`[BCLMS21]`, we require that all protocols have perfect completeness."

**This is a genuine specification fork for an implementer.** Ship the patch and pay
`d = 3` (or 5) on lookups; or skip it and have a scheme with negligible-but-nonzero
completeness error, formally outside the theorem. The paper endorses the latter for
practice, which is defensible — but it means the deployed system is not the system
the theorem covers. Worth an explicit decision record rather than a silent choice.

## What is *not* proven or claimed

- **No zero-knowledge.** The paper builds NARKs and IVC, never zkNARKs or zkIVC.
  The commitment is only required to be *binding*, not *hiding*. Nothing in the
  paper hides the witness — the decider receives `acc.w` in the clear, and the
  openings are sent in `cm[sps]`. If you need ZK you must add it (e.g. hiding
  commitments plus a zkSNARK for the decider), and the paper does not analyse that
  composition.
- **No succinctness of the IVC verifier.** `V_IVC` runs the decider, which is
  linear in `Σ|m_i|`, i.e. `O(cn + T + lk)` for Protostar. Succinctness requires
  outsourcing the decider to a SNARK — which, per report 03 §10, **breaks strict
  IVC completeness** because the IVC can no longer continue.
- **Full PCD.** Only degree-2 DAGs are supported directly; higher-degree nodes
  must be converted into `log₂ d`-depth trees.
- **`Π_select`'s special-soundness is not stated as a lemma** — only an inline
  soundness argument. It is 1-special-sound by the same reasoning as `Π_GATE`
  (prover sends the witness), so this is a presentational gap, not a real one.
- **The Appendix B algorithm is not proven compatible with `CV`.** The authors
  state it is not fully compatible and leave integration as an open problem. The
  specialised Section 4.3 lookup trick *is* used with `CV` in Protostar, via the
  selective-`CV` construction of Section 6.
