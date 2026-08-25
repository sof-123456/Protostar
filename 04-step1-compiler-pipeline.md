# 04 — Step 1: The Compiler Pipeline

This is the paper's headline contribution: a mechanical, four-stage pipeline from
a toy interactive protocol to a production IVC scheme.

## The pipeline (Figure 1 of the paper)

```
                     Sec 3.5        Sec 3.2         Sec 3.3            Sec 3.4          Thm 1
   sps  ───────────>  CV[sps]  ──────────>  cm[CV[sps]]  ─────>  FS[cm[CV[sps]]]  ────>  acc[…]  ┄┄┄>  IVC[…]
 (Sec 3.1)         compress ℓ           commit to each         Fiat–Shamir:          accumulation      BCLMS21
                   verifier checks      prover message         a RO-NARK             scheme            compiler
                   into 1               (commit-and-open)
```

The dashed final arrow is dashed **in the paper itself**, because it requires
heuristically replacing the random oracle with a real hash function (Def. 9).
That heuristic is the only non-provable step in the chain.

Restated as the four numbered steps from the introduction:

1. **Compress the prover messages** by committing to them in a homomorphic
   commitment scheme.
2. **Apply Fiat–Shamir** to yield a secure NARK (`[AFK22]`, `[Wik21]`).
3. **Build a simple and efficient accumulation scheme** that samples a random
   challenge and takes a linear combination between the current accumulator and
   the new NARK.
4. **Apply the BCLMS21 compiler** to yield a secure IVC scheme.

(The `CV[·]` transform of Section 3.5 is an optional stage-0 optimisation,
applied *before* the commit step. It is covered separately in report 06.)

## Stage 0 — What counts as valid input: `sps` (Section 3.1)

A special-sound protocol `sps = (P_sps, V_sps)` for relation `R` qualifies if its
verifier is **algebraic**. Three parameters characterise it entirely:

| Param | Meaning |
|---|---|
| `k` | number of prover messages, so `sps` is `(2k−1)`-move |
| `d` | verifier degree |
| `ℓ` | verifier output length — the number of degree-`d` equations checked |

Protocol shape: in round `i ∈ [k]`, the prover computes
`m_i ← P_sps(pi, w, [m_j, r_j] for j < i)` and sends it; the verifier replies with
`r_i ←$ F`. After the final message `m_k`, the verifier checks

```
V_sps(pi, [m_i]_{i∈[k]}, [r_i]_{i∈[k−1]})  =?  0     (a zero vector of length ℓ)
```

### The one structural requirement: homogeneous decomposition

`deg(V_sps) = d` and it must decompose as

```
V_sps(pi, [m_i], [r_i])  =  Σ_{j=0}^{d}  f_j^{V_sps}(pi, [m_i], [r_i])
```

where each `f_j` is a **homogeneous** degree-`j` algebraic map outputting `ℓ`
field elements. "Degree-`j` homogeneity says that each monomial term of `f_j` has
degree exactly `j`."

This decomposition is not a technicality — it is *the* mechanism. Homogeneity is
what lets the slack variable `μ` re-homogenise a folded instance, and it is what
makes the error polynomial `e(X)` well-defined. If your verifier cannot be split
into homogeneous parts, the compiler does not apply.

**Motivating example given in the paper** (naive Hadamard product): the prover
sends `a, b, c ∈ F^n`; the verifier checks `a_i · b_i = c_i` for all `i ∈ [n]`.
This is special-sound with a degree-2 algebraic verifier, `k=1`, `ℓ=n`. It also
illustrates the problem: the prover message is huge, so accumulating the verifier
predicate directly would be expensive. Hence stage 1.

## Stage 1 — Commit and open (Section 3.2)

Define the relation

```
R^R_cm = (x; w, m, m') :  (x,w) ∈ R  ∨  (Commit(m) = Commit(m') ∧ m ≠ m')
```

i.e. **a witness is either a real witness for `R`, or a break of the commitment
scheme.** This "or a break" pattern is standard and is what lets the reduction be
unconditional up to the binding assumption.

The transformed protocol `Π_cm = cm[sps]`:

- `P_cm` runs `P_sps` to get `m_i`, then sends `C_i ← Commit(ck, m_i)` instead of
  `m_i`.
- After the final commitment `C_k`, `P_cm` sends the **openings** `[m_i]_{i∈[k]}`.
- `V_cm` checks `Commit(ck, m_i) =? C_i` for all `i ∈ [k]`, then runs `V_sps` on
  the openings.

Note what has and has not changed. The protocol is *not* yet succinct — the
openings are still sent. What has changed is the **structure**: there is now a
short instance part (`[C_i]`) and a long witness part (`[m_i]`). This is
"inspired by the splitting accumulation scheme `[BCLMS21]`". The split is exactly
what `V_acc` will later exploit to stay sublinear.

### Lemma 2 — `cm[sps]` preserves special-soundness

If `sps` is `(a_1,…,a_μ)`-out-of-`N` special-sound for `R` and `Commit` is
binding, then `cm[sps]` is `(a_1,…,a_μ)`-out-of-`N` special-sound for `R^R_cm`.
**The arity vector is unchanged.**

*Proof idea.* `Ext_cm` first scans the transcript tree for two transcripts whose
final-message openings disagree at a shared node — that yields
`Commit(m_i) = Commit(m'_i)` with `m_i ≠ m'_i`, a commitment break, which is
itself a valid witness for `R^R_cm`. Otherwise all openings are consistent, so
`Ext_cm` replaces every commitment with its opening, obtaining a genuine
transcript tree for `sps`, and calls `Ext_sps`.

## Stage 2 — Fiat–Shamir (Section 3.3)

`FS[cm]` with random oracle `ρ_NARK`:

```
Prover                                        Verifier
r_0 ← ρ(pi)
for i ∈ [k−1]:
    m_i ← P_sps(pi, w, [m_j,r_j]_{j<i})
    C_i ← Commit(ck, m_i)
    r_i ← ρ(r_{i−1}, C_i)
m_k ← P_sps(...)
C_k ← Commit(ck, m_k)
        π.x = [C_i]_{i∈[k]}                   r_0 ← ρ(pi)
        π.w = [m_i]_{i∈[k]}                   r_i ← ρ(r_{i−1}, C_i)  ∀i ∈ [k−1]
                                              Commit(ck, m_i) =? C_i ∀i ∈ [k]
                                              V_sps(pi, π.x, π.w, [r_i]) =? 0
```

The proof is now explicitly split into `π.x` (the `k` commitments — short) and
`π.w` (the `k` openings — long). By Lemma 1 + Lemma 2, `FS[cm[sps]]` is knowledge
sound with error `(Q+1)·(1 − ∏(1 − a_i/|F|))`, plus `negl(λ)` from binding.

**Remark 1 (important, easily missed).** "Without loss of generality, we assume
that the public input `pi` is of constant size, as otherwise, we can set it as the
hash of the original public input." This assumption is load-bearing: it is what
keeps `V_acc` sublinear in its input, as Theorem 1 demands, and it is where the
`H_in` cost term in every efficiency table comes from.

**Remark 3.** For simplicity `pi`, prover messages, and challenges are all in the
same field `F`. Not strictly necessary — challenges could come from a subset of
`F`, and prover messages could even be *group* elements given a homomorphic
commitment to group elements (e.g. `[AFGHO10]`).

## Stage 3 — Accumulation → Stage 4 — IVC

Covered in report 05 (the accumulation scheme itself) and closed out by
Theorem 3, which composes all four stages and states the resulting IVC costs
(report 10).

## Why this decomposition is the real contribution

Before this paper, adding a feature to a folding scheme meant designing a new
random-linear-combination protocol and writing a new security proof by hand —
which is why Sangria's high-degree extension shipped *without* a proof and why
Origami needed degree-7 polynomials.

After this paper, adding a feature means: **write the dumbest possible
interactive protocol for it, count `k`, `d`, `ℓ`, prove one special-soundness
lemma by polynomial interpolation, and turn the crank.** Every protocol in
Section 4 is genuinely trivial — the permutation protocol is literally "the
prover sends `w`, the verifier checks `w_i = w_{σ(i)}`" — and that is the point.
The intellectual work has been moved out of the per-feature design and into the
compiler, once.
