# 13 — Glossary and Notation

## Protocol parameters (the three numbers that matter)

| Symbol | Meaning |
|---|---|
| `k` | number of prover messages; the protocol is `(2k−1)`-move |
| `d` | degree of the algebraic verifier |
| `ℓ` | verifier output length — the number of degree-`d` equations checked |

After `CV[·]`: `(2k+1)`-move, **1** degree-`(d+2)` check plus `2√ℓ` degree-2
checks.

## Core symbols

| Symbol | Meaning |
|---|---|
| `λ` | security parameter |
| `F` | prime field of order `p`, `log p = Θ(λ)`; requires `\|F\| ≥ 2^λ` |
| `G` / `C` | commitment space; an additive group of prime order `p` |
| `pi` | public input (assumed constant-size — hash it if not; Remark 1) |
| `w` | witness |
| `m_i` | the `i`-th prover message |
| `C_i` | `Commit(ck, m_i)` |
| `r_i` | the `i`-th verifier challenge (from `ρ_NARK`) |
| `α` | the **folding challenge** (from `ρ_acc`) |
| `γ`, `γ_i`, `δ_i` | the `CV` compression challenge and its `√ℓ`-decomposed powers |
| `β`, `β_i` | the vector-lookup challenge and its powers |
| `μ` | **slack variable** — homogenises the relaxed verifier check |
| `e` | error **vector**; `E = Commit(ck, e)` the error commitment |
| `e_j` | the `j`-th cross-error / correction term |
| `pf` | accumulation proof = `[E_j]_{j=1}^{d−1}` (or field elements, under `CV`) |
| `ck` | commitment key |
| `Q` | number of random-oracle queries by the adversary |
| `∘` | Hadamard (component-wise) product |
| `[n]` | `{1,…,n}` |
| `v[S]` | subvector of `v` indexed by `S` |

## The `.x` / `.w` split

| Notation | Meaning |
|---|---|
| `π.x = [C_i]` | proof **instance** — short; goes into the recursive circuit |
| `π.w = [m_i]` | proof **witness** — long; never enters the recursive circuit |
| `acc.x = {pi, [C_i], [r_i], E, μ}` | accumulator instance |
| `acc.w = {[m_i]}` | accumulator witness |

**`V_acc` touches only `.x` and `pf`. `D` touches `.w`.** That split is the whole
efficiency story.

## Algorithms

| Symbol | Meaning |
|---|---|
| `P_sps`, `V_sps` | prover/verifier of the base special-sound protocol |
| `f_j^{V_sps}` | the homogeneous degree-`j` component of `V_sps`; outputs `ℓ` field elements |
| `V_{sps,j}` | the `(j+1)`-th of the `ℓ` equations checked by `V_sps` |
| `P_acc`, `V_acc`, `D` | accumulation prover, verifier, decider |
| `Ext` | knowledge extractor |
| `ρ_NARK`, `ρ_acc` | the two random oracles |
| `H` | the concrete hash replacing them (Fiat-Shamir heuristic) |

## Transforms

| Notation | Meaning | Section |
|---|---|---|
| `cm[Π]` | commit-and-open transform | 3.2 |
| `FS[Π]` | Fiat–Shamir transform | 3.3 / Def. 5 |
| `CV[Π]` | **C**ompressed **V**erifier — collapse `ℓ` checks into 1 | 3.5 |
| `acc[Π]` | accumulation scheme for a Fiat-Shamired NARK | 3.4 |
| `acc_HL[Π]` | hi/low-degree accumulation (separate error terms) | App. A |
| `IVC[·]` | the BCLMS21 accumulation→IVC compiler | Thm 1 |
| `SPS-IVC[Π]` | `IVC[acc[FS[cm[CV[Π]]]]]` — the full pipeline | Thm 3 |

## Relations and protocols

| Name | Relation | `k` | degree |
|---|---|---|---|
| `Π_perm` | `R_σ`: `w_i = w_{σ(i)}` | 1 | 1 |
| `Π_GATE` | `R_GATE`: `Σ_j s_{j,i} G_j(…) = 0` | 1 | `d` |
| `Π_LK` | `R_LK`: `w_i ∈ t` | 2 | 2 (3 perfect-complete) |
| `Π_VLK` | `R_VLK`: `w_i ∈ t`, entries are `v`-vectors | 3 | 3 (5 perfect-complete) |
| `Π_select` | `R_select`: `b` is the unit vector at `pc` | 1 | 2 |
| `Π_plonkup` | `R_plonkup` = perm ∧ gate ∧ lookup ∧ public input | 2 | `d` (`max(d,3)`) |
| `Π_mplkup` | `R_mplkup`: non-uniform Plonkup, `I` branch circuits | 2 | `d + 1` |
| `Π_ccs` | `R_ccs` (Setty–Thaler–Wahby) | 1 | `d` |
| `Π_mccs+` | `R_mccs+`: non-uniform CCS + lookup | 2 | `d + 1` |

## Circuit / relation parameters

| Symbol | Meaning |
|---|---|
| `n` | number of gates per circuit |
| `c` | gate arity (fan-in) |
| `m` | number of gate types / selector-formula pairs |
| `s_i` | selector vectors — **static public data**, not preprocessed witnesses |
| `G_i` | gate formulas |
| `σ` | wiring permutation on `[cn]` |
| `L` | index set of variables carrying a lookup gate |
| `lk`, `ℓ` (in §4.3) | number of lookups |
| `T` | lookup table size; `t ∈ F^T` the table |
| `v` | arity of a vector-lookup table entry |
| `m_i` (in §4.3) | multiplicity of table entry `t_i` among the lookups — **note the collision with prover-message notation `m_i`; disambiguate by context** |
| `h`, `g` | the log-derivative helper vectors, lengths `lk` and `T` |
| `I` | number of branch circuits |
| `pc` | program counter, `pc ∈ [I]`, selects the active circuit |
| `b ∈ F^I` | the selector unit vector, `b_pc = 1` |
| `w̃ = (w^{(1)},…,w^{(I)})` | the sparse multi-circuit witness; only `w^{(pc)} ≠ 0` |
| `in` | public input length |
| `\|w\|` | number of **non-zero** witness entries |
| `\|M\|` / `\|M^≠\|` | total / non-zero elements in the prover messages |

## Cost notation in the tables

| Symbol | Meaning |
|---|---|
| `G` | group scalar multiplication (rows 1–3 of Thm 3: total committed length) |
| `F` | field multiplication |
| `xH` | cost of hashing `x` field elements |
| `H_in` | cost of hashing the public input and the accumulator instance |
| `H_G` | hash-to-group (SuperNova only) |
| `L(V_sps, d)` | cost of the coefficients of `e(X)` (Eqn. 3), degree `d` |
| `L(V_sps, d+2)` | same for Eqn. 4; bounded `O(n·d·log²d)` |
| `C_i` | evaluation cost of the `i`-th branch circuit |

## Acronyms

| Term | Expansion |
|---|---|
| **IVC** | Incrementally Verifiable Computation |
| **PCD** | Proof-Carrying Data (the DAG generalisation of IVC) |
| **NARK** | Non-interactive ARgument of Knowledge (**not** necessarily succinct) |
| **SNARK** | Succinct NARK |
| **RO** / **ROM** | Random Oracle / Random Oracle Model |
| **FS** | Fiat–Shamir |
| **sps** | special-sound protocol |
| **CV** | Compressed Verifier (the §3.5 transform) |
| **HL** | High/Low degree (the App. A accumulation variant) |
| **R1CS** | Rank-1 Constraint System (degree 2: `Az ∘ Bz = Cz`) |
| **CCS** | Customizable Constraint System (`[STW23]`; generalises R1CS) |
| **VDF** | Verifiable Delay Function |
| **zkEVM** | zero-knowledge Ethereum Virtual Machine |

## Reference keys used in the paper

| Key | Work |
|---|---|
| `[Val08]` | Valiant — IVC |
| `[CT10]` | Chiesa–Tromer — PCD |
| `[BCCT13]` | Bitansky–Canetti–Chiesa–Tromer — recursive composition |
| `[BGH19]` | Bowe–Grigg–Hopwood — **Halo** |
| `[BCMS20]` | Bünz–Chiesa–Mishra–Spooner — recursion from accumulation |
| `[BCLMS21]` | Bünz–Chiesa–Lin–Mishra–Spooner — **PCD without succinct arguments** (Theorem 1) |
| `[KST22]` | Kothapalli–Setty–Tzialla — **Nova** |
| `[KS22]` | Kothapalli–Setty — **SuperNova** |
| `[KS23]` | Kothapalli–Setty — **HyperNova** (concurrent work) |
| `[Moh23]` | Mohnblatt — **Sangria** |
| `[ZV23]` | Zhang–Vark — **Origami** |
| `[GWC19]` | Gabizon–Williamson–Ciobotaru — **PLONK** |
| `[GW20]` | Gabizon–Williamson — **plookup** |
| `[Hab22]` | Haböck — **multivariate lookups from logarithmic derivatives** (Lemma 4) |
| `[STW23]` | Setty–Thaler–Wahby — **CCS** |
| `[AFK22]` | Attema–Fehr–Klooß — FS of multi-round interactive proofs (Lemma 1) |
| `[Wik21]` | Wikström — special soundness in the ROM |
| `[CBBZ22]` | Chen–Bünz–Boneh–Zhang — **HyperPlonk** (the `O(d log²d)` bound) |
| `[LFKN90]` | Lund–Fortnow–Karloff–Nisan — **sumcheck** |
| `[Ped92]` | Pedersen — commitments |
| `[SAGL18]` | Setty–Angel–Gupta–Lee — offline memory checking |
| `[ZBKMNS22]` / `[ZGKMR22]` / `[PK22]` / `[EFG22]` | Caulk / Baloo / Caulk+ / cq — table-independent lookups |
| `[XCZBFKC22]` | **VERI-ZEXE** |
| `[But22]` | Buterin — "The different types of ZK EVM" |
| `[AFGHO10]` | Abe et al. — structure-preserving commitments to group elements (Remark 3) |
