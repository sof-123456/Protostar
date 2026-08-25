# 09 — Assembling Protostar (Section 6) and Protostar_ccs (Appendix C)

## What Protostar is, formally

```
Protostar  :=  SPS-IVC[Π_mplkup]  =  IVC[ acc[ FS[ cm[ CV[Π_mplkup] ] ] ] ]
```

where `Π_mplkup` is a special-sound protocol for the **non-uniform Plonkup
relation**: one of `I` branch circuits is satisfied, and which one is determined
by a program counter `pc` that forms part of the public input.

## The application framing

Two use cases the paper names explicitly:

1. **zkEVM.** The `I` circuits are the opcodes supported by the EVM. `pc` can be
   computed from the online public input, or derived from the previous step's `pc`
   and register state (the paper points to Figure 4 of Nova `[KST22]` for how to
   constrain `pc' ` against `pc`). The circuit then checks that `opcode[pc]`
   executed correctly this step.
2. **Smart contracts / transaction types.** The `I` circuits are `I` contract
   predicates. A user invokes one by specifying `pc`, and **"the cost of proving
   correct execution is only proportional to the size of an individual smart
   contract/transaction type rather than the sum of the sizes of the supported
   smart contracts/transaction types."**

That second sentence is the commercial pitch of the entire paper.

## Uniformity simplification

For exposition all `I` circuits share: number of gates `n`, gate arity `c`, max
gate degree `d`, number of gate types `m`, number of public inputs `in`, number of
lookup gates `lk`. "The scheme naturally extends when different branch circuits
have different parameters."

**Def. 16.** `C_mplkup := (pp = [n,T,c,d,m,in,lk]; [C_i]_{i=1}^{I}; t)` with
`C_i := (pp, σ_i, [s_{i,j}, G_{i,j}]_{j=1}^{m}, L_i)` and global table `t ∈ F^T`.
For public input `pi := (pc, pi')` with `pc ∈ [I]`, the pair `(pi, w ∈ F^{cn})` is
in `R_mplkup` iff `(pi, w) ∈ R_plonkup` w.r.t. `(C_pc, t)`.

## The protocol `Π_mplkup`

```
1.  P sends b = (0,…,0, b_pc = 1, 0,…,0) ∈ F^I
2.  V checks  b_i(1 − b_i) =? 0,   b_i(i − pc) =? 0   ∀ i ∈ [I],   Σ_{i∈[I]} b_i =? 1
3.  P sends m ∈ F^T  with  m_i := Σ_{j ∈ L_pc} 1(w_j = t_i)
4.  P sends the SPARSE vector  w̃ := (w^{(1)},…,w^{(I)}) ∈ F^{Icn}
        with w^{(i)} = 0^{cn} for all i ≠ pc,  and  w^{(pc)} = w
5.  V checks
      Permutation:   Σ_{j∈[I]} b_j ( w_i^{(j)} − w^{(j)}_{σ_j(i)} )  =? 0        ∀ i ∈ [cn]
      Public input:  Σ_{j∈[I]} b_j · w^{(j)}[1..in]                  =? pi
      Gate:          Σ_{j∈[I]} b_j · GT_{j,i}( w_i^{(j)},…,w^{(j)}_{i+cn−n} ) = 0  ∀ i ∈ [n]
                       where GT_{j,i}(x_1..x_c) := Σ_{k∈[m]} s_{j,k}[i] · G_{j,k}(x_1..x_c)
6.  V samples and sends  r ←$ F
7.  P computes h ∈ F^{lk}, g ∈ F^T:   h_i := 1/(w_{L_pc[i]} + r),   g_i := m_i/(t_i + r)
8.  V checks   Σ_{i∈[lk]} h_i =? Σ_{i∈[T]} g_i
               Σ_{j∈[I]} b_j · h_i · ( w^{(j)}_{L_j[i]} + r ) =? 1   ∀ i ∈ [lk]
               g_i · (t_i + r) =? m_i                               ∀ i ∈ [T]
```

`k = 2` (3-move); verifier degree `d + 1`.

**The non-uniformity trick, stated plainly:** every algebraic equation `G` from
`Π_plonkup` is replaced by `Σ_{i∈[I]} G_i · b_i`. Since `b` is a unit vector,
this selects the active circuit. Cost: verifier degree goes `d → d+1` (one extra
multiplication by `b_j`), plus `2I` degree-2 checks and one sum check in step 2.
Hence the paper's claim that "the IVC scheme for the non-uniform Plonkup relation
adds negligible overhead to that for the Plonkup relation."

**Remark 4.** The public-input check `Σ_j b_j w^{(j)}[1..in] =? pi` is equivalent
to `w[1..in] = w^{(pc)}[1..in] =? pi` provided `b` passed step 2. This guarantees
`w[1] = pc`, so the circuit relation can impose further constraints on `pc`
depending on the application.

**Lemma 8.** `Π_mplkup` is `2(T + lk)`-special-sound. Proof: if step 2 passes, `b`
must be a Boolean unit vector with its single 1 at `pc`. Given `2(T+lk)` accepting
transcripts with distinct `r`, `b` cannot change. So the sub-transcript after
step 2 is a `Π_plonkup` transcript for configuration `(n, T, c, d, C_pc, t)`, and
Lemma 7 applies. ∎

## The two efficiency problems, and their fixes

### Problem 1 — `w̃` has length `O(In)`

Naively, folding `w̃` onto `acc.w̃` would take `O(In)` time — defeating the whole
purpose.

**Fix:** `w̃` is **sparse**. Only `w^{(pc)}` is non-zero, and `pc` is determined at
runtime. Using the commitment to `acc.w̃` and homomorphism, folding costs `O(n)`.

### Problem 2 — computing the error terms `[e_j]_{j=1}^{d−1}`

Each gate check splits into `I` parts of which at most one is active:
`Σ_j b_j · GT_{j,i}(…)` decomposes into `I` branch gates, the `j`-th being
`b_j · GT_{j,i}(w^{(j)}_i, …)`.

**Fix:** exactly the branched-gate caching algorithm of Section 3.6.1
(report 07). Result: `O(d·|C_pc|)` instead of `O(d·(|C_1| + … + |C_I|))`.

### Problem 3 — composing `CV` with the sparse-lookup optimisations

Covered in detail at the end of report 06. Short version: apply `CV` **only to the
`GATE` part**, because only `n` of the `n + lk + T + cn` checks are high-degree.
Yields `d+1` length-1 error terms (identity-committed) plus **one** error vector
of length `T + lk + cn + O(√n)` (vector-committed), with homomorphism keeping the
prover independent of `T`.

## Corollary 1 — Protostar's costs

Stated for `m = 1` (each circuit has a single degree-`d` gate type) and public
input length `in = 1`; cost terms negligible relative to the dominant parts are
omitted.

| `P_Protostar` native | `P_Protostar` recursive | `V_Protostar` | `\|π_Protostar\|` |
|---|---|---|---|
| `O(\|w\| + lk)` G | **`3G`** | `O(c·n + T + lk)` G | `O(c·n + T + lk)` |
| `L(C_pc, d+2) + 2lk` F | `d + 4` F | `n + Σ_{i=1}^{I} C_i + T + lk` F | |
| | `d + O(1)` H `+ 1·H_in` | | |

Where:
- `|w| ≤ cn` — number of **non-zero** witness entries
- `Σ_{i=1}^{I} C_i` — cost of evaluating **all** circuits on some random input
  (paid by the *verifier*/decider, once, not by the prover per step)
- `L(C_pc, d+2)` — cost of the error polynomial coefficients (report 07), bounded
  by `O(n·d·log²d)`
- `H_in` — hashing the public input and the constant-sized accumulator instance

**Proof.** `Protostar = SPS-IVC[Π_mplkup]` where
`SPS-IVC[Π] = IVC[acc[FS[cm[CV[Π]]]]]` is Theorem 3's transformation including
`CV`. Apply Theorem 3.

**Security.** Since `CV[Π_GATE]` is applied only to `Π_GATE`, which has *perfect*
soundness, Lemmas 8 and 3 give that `FS[cm[CV[Π_mplkup]]]` has knowledge error

```
(Q + 1) · ( n + 2(T + lk) ) / |F|  +  negl(λ)
```

Theorem 2 and Corollary 2 supply the accumulation scheme (negligible knowledge
error since `d = poly(λ)`), and Theorem 1 plus the Fiat-Shamir heuristic close it
out.

### Reading the recursive-circuit line

`3G`, `d+4` field ops, `d+O(1)` hashes plus one `H_in`. **Nothing in that row
depends on `n`, `T`, `I`, or `|w|`.** That is the entire result of the paper,
compressed into one table row.

## Appendix C — Protostar_ccs

**Def. 17 (CCS, `[STW23]`).** Public params `m, n, N, in, t, q, d`. Matrices
`M_1,…,M_t ∈ F^{m×n}` with at most `N` total non-zero entries; multisets
`S_1,…,S_q` over `[t]` each of cardinality `≤ d`; constants `c_1,…,c_q ∈ F`.
`(pi, w) ∈ F^{in} × F^{n−in−1}` is in `R_ccs` iff, with `z = (1, pi, w)`,

```
Σ_{i=0}^{q−1} c_i · ( ∘_{j ∈ S_j} M_j · z )  =  0^m
```

CCS generalises R1CS, captures Plonk constraints, allows high-degree gates, and
**does not require a permutation argument**.

`Π_ccs`: prover sends `w`, verifier forms `z = (1,pi,w)` and checks the equation.
`k = 1`, verifier degree `d`. Trivial, as expected.

**Def. 18.** `Π_mccs+` extends CCS to multi-circuit + lookup:
`C_mccs+ := (pp = [m,n,N,in,t,q,d,T,lk]; [C_i]_{i=1}^{I}; t)` with
`C_i := (pp, [M_{j,i}]_{j=1}^{t}, [S_{j,i}, c_{j,i}]_{j=1}^{q}, L_i)`.

The protocol is structurally identical to `Π_mplkup` — selector vector `b`, sparse
`w̃`, then the log-derivative lookup round — with step 5 becoming

```
V computes z^{(k)} = (1, pi, w^{(k)}) ∈ F^n for all k ∈ [I] and checks
    Σ_{k∈[I]} b_k · Σ_{i∈[q]} c_{i,k} · ( ∘_{j ∈ S_{i,k}} M_{j,k} · z^{(k)} )  =  0^m
```

**Complexity.** `k = 2` (3-move); verifier degree `d + 1`; non-zeros in the prover
message `≤ n + 3lk`; total prover message length `≤ I + n + 3T`. Accumulation
prover `O(n + lk)`, **independent of table size**; accumulator size `O(n + T + I)`,
**independent of the sum of the sizes of the branch circuits**.

| `P` native | `P` recursive | `V` | `\|π\|` |
|---|---|---|---|
| `O(\|w\| + lk)` G | `3G` | `O(n + T + lk)` G | `O(n + T + lk)` |
| `L(ccs_pc, d+2) + 2lk` F | `d + 4` F | `n + I·N + T + lk` F | |
| | `d + O(1)` H `+ 1·H_in` | | |

"The efficiency is almost identical to the Protostar scheme for `R_mplkup`."

### Why Appendix C exists

It is a direct response to the concurrent HyperNova paper. HyperNova's selling
point was CCS; Appendix C shows the Protostar compiler ports to CCS in a couple of
pages, keeping Protostar's advantages (native non-uniformity, cheap lookups,
`n`-independent recursive circuit) while dropping `Π_mplkup`'s need for a
permutation argument and copy constraints. The authors state this outright: "We
show that our general compiler is powerful enough to port the benefits of
Protostar directly to CCS."

It is also the strongest single piece of evidence for the paper's central claim.
The compiler was designed for Plonkup; adapting it to a different NP
characterisation took one trivial base protocol (`Π_ccs`) and no new security
argument. That is what a genuine recipe looks like.
