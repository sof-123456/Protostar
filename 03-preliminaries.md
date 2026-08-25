# 03 — Preliminaries: the Definitions You Must Have Straight

Section 2 of the paper. The definitions of special-soundness are taken from
Attema–Fehr–Klooß (TCC'22, `[AFK22]`); the accumulation and IVC definitions from
BCLMS21 and Nova.

## Notation baseline

- `λ` — security parameter. `F` — prime field of order `p` with `log p = Θ(λ)`.
- `[n] = {1,…,n}`; `[a,b) = {a,…,b−1}`; `[a,b] = {a,…,b}`.
- `v[S]` — the subvector of `v` indexed by `S`, in increasing index order.
- `∘` — Hadamard (component-wise) product.

## 1. Public-coin interactive proof (Def. 1)

An interactive protocol between prover `P` and polynomial-time verifier `V`.
Both take public input `pi`; `P` additionally takes witness `w ∈ R(pi)`.

**Convention that trips people up:** `V` **outputs 0 to accept** and a non-zero
value to reject. This holds throughout the paper, including for the accumulation
verifier and the decider. Read every `= 0` in the paper as "accepts".

*Public coin* = the verifier's randomness is public. Verifier messages are
called **challenges**. The protocol is `(2k−1)`-move if there are `k` prover
messages and `k−1` verifier messages (so `P` moves first and last).

## 2. Tree of transcripts (Def. 2)

An `(a_1,…,a_μ)`-tree of transcripts for a `(2μ+1)`-move public-coin proof is a
set of `a_1·a_2···a_μ` **accepting** transcripts arranged in a tree of depth `μ`
and arity `a_1,…,a_μ`:

- nodes ↔ prover messages,
- edges ↔ verifier challenges,
- every internal node at depth `i−1` has `a_i` children with **distinct**
  challenges,
- every root-to-leaf path is one transcript.

Written `(a^μ)`-tree when all arities are equal.

## 3. Special-sound interactive protocol (Def. 3)

A `(2μ+1)`-move public-coin proof where the verifier draws challenges from a set
of size `N` is **`(a_1,…,a_μ)`-out-of-`N` special-sound** if there is a
polynomial-time algorithm that, given `pi` and *any* `(a_1,…,a_μ)`-tree of
transcripts, outputs `w ∈ R(pi)`.

This is the paper's single entry-point abstraction. Everything in Section 4 is
"here is a tiny protocol, here is its arity vector".

## 4. RO-NARK (Def. 4)

A **N**on-interactive **A**rgument of **K**nowledge in the random oracle model:
a pair `(P,V)` of RO algorithms. `P(pi,w) → π`; `V(pi,π) → 0` to accept.

- **Perfect completeness:** the honest proof always verifies, probability 1.
- **Knowledge soundness with knowledge error `κ`:** there is an extractor `Ext`
  which, given oracle access to any `Q`-query RO prover `P*`, runs in expected
  polynomial time in `|pi| + Q`, and the probability it extracts a valid witness
  is at least `(ε(P*) − κ(n,Q)) / poly(n)`, where `ε(P*)` is `P*`'s success
  probability. `Ext` implements the RO for `P*` and **may program it arbitrarily**.

Note the *knowledge error* formulation — an additive slack `κ` subtracted from
the adversary's success probability — rather than plain soundness error. This is
the `[AFK22]` style, and it is what makes the tight `(Q+1)·k/|F|` bounds later
come out cleanly.

## 5. Fiat–Shamir transform, adaptive (Def. 5)

`FS[Π] = (P_fs, V_fs)`. The prover runs `P` but derives challenges itself:

```
c_0 = ρ(pi)
c_i = ρ(c_{i−1}, m_i)
```

Output `π = (m_1,…,m_μ)`. The verifier recomputes the chain and runs `V`.

The chaining matters for efficiency later: `c_i` depends on `c_{i−1}` and `m_i`,
not on the full transcript, so each of the `k−1` in-circuit hash calls has
**constant-size input**. That is why the recursive circuit's hash cost comes out
as `k+d+O(1)` rather than proportional to the transcript length.

### Lemma 1 — FS of a special-sound protocol `[AFK22]`

The Fiat–Shamir transform of an `(a_1,…,a_μ)`-out-of-`N` special-sound proof is
knowledge sound with knowledge error

```
κ_fs(Q) = (Q + 1) · κ        where    κ = 1 − ∏_{i=1..μ} (1 − a_i/N)
```

This lemma is the workhorse: it is invoked to prove *every* soundness result in
the paper. The pattern is always: build an interactive special-sound protocol →
count its arity vector → apply Lemma 1.

## 6. Commitment scheme (Def. 6)

`cm = (Setup, Commit)`:
- `Setup(1^λ) → ck`
- `Commit(ck, m ∈ M) → C`

**Binding**: no poly-time adversary given `ck` finds `m ≠ m'` with
`Commit(ck,m) = Commit(ck,m')`, except with negligible probability.

**Homomorphic**: the commitment space `(C, +)` is an additive group of prime
order `p`.

That is the *entire* requirement. No hiding, no succinctness assumption beyond
what the accumulator instance size implies, no algebraic structure beyond a
prime-order group. Pedersen qualifies, so security rests on discrete log.

## 7. IVC (Def. 7)

`IVC = (P_IVC, V_IVC)` for predicates expressed in an NP relation `R_NP`:

- `P_IVC(m, z_0, z_m, z_{m−1}, w_loc, π_{m−1}) → π_m`
- `V_IVC(m, z_0, z_m, π_m) → b` (0 = accept)

**Perfect adversarial completeness** — the strong form. For *any*, possibly
adversarially created, tuple satisfying
`φ(z_0,z_m,z_{m−1},w_loc) ∧ (V_IVC(m−1,z_0,z_{m−1},π_{m−1}) = 0)`,
the new proof must verify. "Adversarial" means the previous proof need not have
been honestly generated — merely valid. This is the requirement that later forces
the awkward perfect-completeness patches in the lookup protocols (report 08) and
that is broken by outsourcing the decider.

**Knowledge soundness** — for every expected-poly-time `P*` there is an
expected-poly-time extractor recovering the whole chain `[z_i, w_i]` for
`i = 1..m`, with `m` constant.

**Efficiency** — runtime of `P_IVC`, `V_IVC` and `|π_IVC|` depend only on `|φ|`
and are **independent of the number of iterations**.

### Non-uniform IVC

Introduced by SuperNova: the predicate `φ` is selected from a fixed set at every
step, the selection depending on the current state. Formally this fits the
definition above by taking `φ` to be the union of all predicates plus the
selection circuit — but with one **extra efficiency requirement**:

> the IVC prover in step `i` only depends on the size of the predicate being
> executed in step `i`.

The paper states that Protostar achieves this. That requirement is the whole
point; without it non-uniformity is definitionally free but practically useless.

## 8. Simple accumulation scheme (Def. 8)

An accumulation scheme for a NARK `(P_NARK, V_NARK)` is a triple
`acc = (P_acc, V_acc, D)`, all with access to random oracles `ρ_acc` and `ρ_NARK`:

- `P_acc(pi, π = (π.x, π.w), acc = (acc.x, acc.w)) → {acc', pf}`
  — the accumulation prover; outputs a new accumulator and **correction terms**.
- `V_acc(pi, π.x, acc.x, acc'.x, pf) → v`
  — takes only the *instances* (the short parts) plus `pf`. 0 = accept.
- `D(acc) → v` — the **decider**. 0 = accept.

The `.x` / `.w` split (instance vs witness) is the crux: `V_acc` touches only
`.x` and `pf`, and **that** is what gets compiled into the recursive circuit.
`D` touches `.w` and is run only once, at the very end, by the IVC verifier.

**Knowledge soundness with error `κ`** is defined indirectly and elegantly: the
scheme has knowledge error `κ` if the RO-NARK `(P,V)` has knowledge error `κ` for
the relation

```
R_acc((pi, π.x, acc.x); (π.w, acc.w)) :  V_NARK(pi,π) = 0  ∧  D(acc) = 0
```

where the prover of that NARK outputs `(acc', pf)` and its verifier accepts if
`D(acc') = 0 ∧ V_acc(pi, π.x, acc.x, acc'.x, pf) = 0`.

Read plainly: *if you can produce a new accumulator that the decider accepts,
together with a `V_acc`-accepting transcript, then you must have known a valid
NARK proof and a valid old accumulator.* Soundness of accumulation is thus
reduced to soundness of a NARK — which lets the authors reuse Lemma 1 again.

**Perfect completeness** of the accumulation scheme = perfect completeness of
that RO-NARK for `R_acc`.

## 9. Theorem 1 — IVC from accumulation (BCLMS21)

> Given a **standard-model** NARK for circuit satisfiability and a
> **standard-model** accumulation scheme for that NARK, both with negligible
> knowledge error, there exists an efficient transformation that outputs an IVC
> scheme for **constant-depth compliance predicates**, assuming that the circuit
> complexity of `V_acc` is **sublinear in its input**.

Three conditions to hold onto:

1. **Standard model** — but everything Protostar builds is in the ROM. The paper
   is explicit: "It remains an open problem to construct such schemes." They
   proceed under the **Fiat-Shamir Heuristic** (Def. 9): replacing the RO with a
   cryptographic hash `H` preserves negligible knowledge error in the standard
   (CRS) model. This is the *dotted* arrow in Figure 1 of the paper.
2. **Constant-depth compliance predicates.**
3. **`V_acc` sublinear in its input** — this is why the `.x`/`.w` split and the
   "assume `pi` is a hash" convention (Remark 1) are needed.

## 10. Complexity of the IVC transformation, and two escape hatches

The BCLMS21 transformation recursively proves the previous accumulation was
correct, by implementing `V_acc` as a circuit. Crucially the recursive circuit is
**independent of `|π.w|`, `|acc.w|`, and the runtime of `D`**.

The IVC prover is linear in (recursive circuit size + the step circuit size).
The final IVC verifier and proof size are linear in these too.

**PCD.** Accumulation schemes compile to full PCD if they can accumulate an
arbitrary number of accumulators and proofs. The paper only builds accumulation
for (one proof + one accumulator) and (two accumulators), giving **PCD for DAGs
of degree 2**. Higher-degree DAGs are handled by converting each degree-`d` node
into a `log₂ d`-depth tree.

**Outsourcing the decider.** The accumulators here are linear in the witness of a
single step, so the IVC verifier is not succinct. One can outsource `D` by
supplying a SNARK proving knowledge of `acc.w` with `D(acc) = 0` (Nova builds a
custom, concretely efficient one for its scheme). **But**: once outsourced, the
IVC cannot continue, which "breaks the strict completeness requirement of IVC,
which says that any prover can continue from any valid IVC proof." The authors
say this may be fine for some applications. Treat it as a real design fork, not a
footnote — see report 12.
