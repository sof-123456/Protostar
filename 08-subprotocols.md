# 08 — The Building Blocks (Section 4)

Once you have the compiler, designing a feature reduces to writing the dumbest
possible interactive protocol and counting `(k, d, ℓ)`. Section 4 is five such
protocols. Note how trivial the first two are — that is the compiler earning its
keep.

Composition map (Figure 2 of the paper):

```
Π_mplkup  (Sec 6)            =  Π_perm  +  Π_GATE  +  Π_LK  +  Π_select
Π_mccs+   (Appendix C)       =  Π_ccs   +  Π_LK    +  Π_select        (no permutation needed)
```

Summary table:

| Protocol | Relation | `k` | moves | verifier degree | non-zeros in prover msg |
|---|---|---|---|---|---|
| `Π_perm` (4.1) | permutation / wiring | 1 | 1 | **1** | `n` |
| `Π_GATE` (4.2) | high-degree custom gate | 1 | 1 | `d` | `cn` |
| `Π_LK` (4.3) | lookup | 2 | 3 | **2** (3 for perfect compl.) | `≤ 4ℓ` |
| `Π_VLK` (4.4) | vector lookup, arity `v` | 3 | 5 | 3 (5 for perfect compl.) | `≤ (v+3)ℓ + v` |
| `Π_select` (4.5) | circuit selection | 1 | 1 | **2** | `n` |
| `Π_plonkup` (5) | full Plonkup | 2 | 3 | `d` (`max(d,3)`) | `≤ cn + 3\|L\|` |
| `Π_mplkup` (6) | non-uniform Plonkup | 2 | 3 | `d + 1` | `≤ cn + 3lk` (+ `I`) |
| `Π_ccs` (App C) | CCS | 1 | 1 | `d` | `n` |
| `Π_mccs+` (App C) | non-uniform CCS + lookup | 2 | 3 | `d + 1` | `≤ n + 3lk` |

## 4.1 Permutation relation

**Def. 10.** For a permutation `σ : [n] → [n]`, `R_σ` = the set of `w ∈ F^n` with
`w_i = w_{σ(i)}` for all `i ∈ [n]`.

```
Prover P(σ, w ∈ F^n)                  Verifier V(σ)
                 --- w --->
                                       Check  w_i − w_{σ(i)} = 0   ∀ i ∈ [n]
```

`k = 1`, verifier degree **1**. That is the entire protocol. Compare Plonk, which
needs a grand-product permutation argument with challenges and quotient
polynomials — here the compiler absorbs all of it, because a non-succinct
protocol is allowed.

## 4.2 High-degree custom gate relation

**Def. 11.** Configuration `C_GATE := (n, c, d, [s_i ∈ F^n, G_i]_{i=1}^{m})` where
`n` = #gates, `c` = arity per gate, `d` = gate degree, `[s_i]` = selector vectors,
`[G_i]` = gate formulas. `R_GATE` = the `w ∈ F^{cn}` with

```
Σ_{j=1}^{m} s_{j,i} · G_j(w_i, w_{i+n}, …, w_{i+(c−1)n})  =  0     ∀ i ∈ [n]
```

```
Prover P(C_GATE, w ∈ F^{cn})           Verifier V(C_GATE)
                 --- w --->
                                        Σ_j s_{j,i} G_j(w_i, …, w_{i+(c−1)n}) =? 0  ∀ i
```

`k = 1`, verifier degree `d`. Again: prover sends the witness, verifier checks.
The selectors `s_j` are **static public data**, not preprocessed witnesses — which
is the property exploited in report 07 to make the error-term computation pay only
for the genuinely high-degree gates, and which yields the claim that additional
gate types of degree `< d` and additional selectors are **free**.

## 4.3 Lookup relation — the technically interesting one

**Def. 12.** Configuration `C_LK := (T, ℓ, t)` with `ℓ` lookups and table
`t ∈ F^T`. `R_LK` = the `w ∈ F^ℓ` with `w_i ∈ t` for all `i ∈ [ℓ]`.

The statement "`w_i ∈ t`" is **not algebraic**, so this cannot be done by "send the
witness". The fix is Haböck's logarithmic-derivative identity.

### Lemma 4 (Lemma 5 of `[Hab22]`)

Let `char(F) = p > max(ℓ, T)`. For sequences `[w_i]_{i∈[ℓ]}` and `[t_i]_{i∈[T]}`,
`{w_i} ⊆ {t_i}` as **sets** (multiplicities removed) **iff** there exists
`[m_i]_{i∈[T]}` with

```
Σ_{i=1}^{ℓ}  1/(X + w_i)   =   Σ_{i=1}^{T}  m_i/(X + t_i)          (Eqn. 6)
```

`m_i` is the multiplicity of table entry `t_i` among the lookups.

### The protocol `Π_LK`

```
Prover P(C_LK, w ∈ F^ℓ)                              Verifier V(C_LK)
m_i := Σ_{j∈[ℓ]} 1(w_j = t_i)   ∀ i ∈ [T]
                       --- w, m --->
                       <--- r ---                     r ←$ F
h_i := 1/(w_i + r)      ∀ i ∈ [ℓ]
g_i := m_i/(t_i + r)    ∀ i ∈ [T]
                       --- h, g --->
                                                      Σ_{i∈[ℓ]} h_i  =?  Σ_{i∈[T]} g_i
                                                      h_i · (w_i + r) =? 1     ∀ i ∈ [ℓ]
                                                      g_i · (t_i + r) =? m_i   ∀ i ∈ [T]
```

`k = 2` (3-move), verifier degree **2**, and — crucially — **at most `4ℓ`
non-zero elements in the prover message**. (`w` and `h` have length `ℓ`; `m` and
`g` have length `T` but at most `ℓ` non-zero entries, since at most `ℓ` distinct
table entries are ever looked up.)

The authors' assessment: "This is the most efficient lookup protocol today. While
the verification is linear time, it is low degree (2) and thus compatible with our
generic compiler." That sentence captures the whole design philosophy — *linear
verifier time is fine, only degree matters.*

### Perfect completeness patch

The protocol as written is **not perfectly complete**: if `w_i + r = 0` or
`t_i + r = 0`, the prover message is undefined. Fix: the verifier sets `h_i = 0`
(resp. `g_i = 0`) in that case, and the checks become

```
(w_i + r) · ( h_i·(w_i + r) − 1 )  = 0
(t_i + r) · ( g_i·(t_i + r) − m_i ) = 0
```

which force *either* `h_i = 1/(w_i+r)` *or* `w_i + r = 0`. **This raises the
verifier degree from 2 to 3.**

The authors' pragmatic note: without the patch the completeness error is
`(ℓ+T)/|F|`, negligible, and "can likely be ignored in practice, and these checks
do not need to be implemented." The patch is needed only to satisfy the *perfect*
completeness demanded by the full PCD definition and by Theorem 1 of BCLMS21.
**An implementer therefore has a real choice here: degree 2 with negligible
completeness error, or degree 3 with a clean theorem.**

### Accumulation with `O(ℓ)` prover complexity — the crown jewel

The problem: `Π_LK`'s prover message is sparse, but **there is no guarantee that
the accumulated `acc.g` and `acc.m` stay sparse**. And the prover must compute the
error term `e_1`, which naively touches all `T` entries.

Expanding the three verification checks gives three components:

```
e_1^{(1)} = Σ_{i∈[ℓ]} acc.h_i − Σ_{i∈[T]} acc.g_i  +  μ(Σ π.h_i − Σ π.g_i)     ∈ F
e_1^{(2)} = acc.h ∘ (π.w + π.r·1) + π.h ∘ (acc.w + acc.r·1) − 2μ·1             ∈ F^ℓ
e_1^{(3)} = acc.g ∘ (t + π.r·1_T) + π.g ∘ (μ·t + acc.r·1_T) − μ·π.m − acc.m    ∈ F^T
```

Handled one at a time:

- **`e_1^{(1)} = 0`, always.** `Σπ.h_i − Σπ.g_i = 0` because `π` is valid, and
  `Σacc.h_i − Σacc.g_i = acc.e^{(1)}/acc.μ`. So
  `e_1^{(1)} = acc.e^{(1)}/acc.μ`, and since IVC initialises `acc.e^{(1)} = 0`,
  **it is zero for every subsequent iteration**. A nice inductive freebie.
- **`e_1^{(2)}` is `O(ℓ)`** — all terms have length `ℓ`.
- **`e_1^{(3)}` is length `T`** — the actual problem. But the prover only needs
  the **commitment** `E_1`, not the vector. And since `acc.μ`, `acc.r`, `π.r` are
  scalars, `E_1^{(3)}` is a *linear* function of six commitments:

```
1. G  = Commit(ck, π.g)        4. M' = Commit(ck, acc.m)
2. G' = Commit(ck, acc.g)      5. GT  = Commit(ck, π.g ∘ t)
3. M  = Commit(ck, π.m)        6. GT' = Commit(ck, acc.g ∘ t)

E_1^{(3)}  =  GT'  +  π.r·G'  +  acc.μ·GT  +  acc.r·G  −  acc.μ·M  −  M'
```

`G`, `M`, `GT` are commitments to **`ℓ`-sparse** vectors, so computable in `O(ℓ)`.
The prover **caches** `G'`, `M'`, `GT'` and updates them incrementally:

```
G' ← G' + α·G        M' ← M' + α·M        GT' ← GT' + α·GT
acc.m ← acc.m + α·π.m                     acc.g ← acc.g + α·π.g
```

All in `O(ℓ)`, **independent of `T = |t|`**.

Composition note: when `Π_LK` runs alongside a higher-degree protocol, the error
terms get homogenised with a `(X+μ)^{d−2}` factor; the contribution to each `e_i`
remains a **linear** function of `acc.g`, `acc.m`, `acc.g ∘ t`, so the same
homomorphic trick still applies. Appendix B generalises this to higher degrees and
more general polynomial forms.

### Lemma 5 — `Π_LK` (perfectly complete version) is `2(ℓ+T)`-special-sound

*Proof.* Take `2(ℓ+T)` transcripts sharing `(w, m)` but with distinct
`(r^{(j)}, h^{(j)}, g^{(j)})`. By **pigeonhole**, some subset `S` of size `ℓ+T`
has `w_i + r^{(j)} ≠ 0` and `t_i + r^{(j)} ≠ 0` for all `i`, `j ∈ S` — hence the
factor-2 in the arity. For those, `h_i = 1/(w_i + r^{(j)})` and
`g_i = m_i/(t_i + r^{(j)})`. Define the degree-`(ℓ+T−1)` polynomial

```
p(X) = Π_{k∈[ℓ]}(X + w_k) · Π_{j∈[T]}(X + t_j) · [ Σ_i 1/(X+w_i) − Σ_i m_i/(X+t_i) ]
```

`p` vanishes at `ℓ+T` points, hence `p ≡ 0`, hence Eqn. 6 holds, hence
`(C_LK; w) ∈ R_LK` by Lemma 4. ∎

## 4.4 Vector-valued lookup

**Def. 13.** `C_VLK := (T, ℓ, v ∈ N, t)` where each table entry
`t_i = (t_{i,1},…,t_{i,v}) ∈ F^v`. `w ∈ (F^v)^ℓ` is in `R_VLK` iff every `w_i ∈ t`.

Extension of Lemma 4 (from §3.4 of `[Hab22]`) — replace Eqn. 6 with

```
Σ_{i=1}^{ℓ} 1/(X + w_i(Y))  =  Σ_{i=1}^{T} m_i/(X + t_i(Y))        (Eqn. 7)

where  w_i(Y) := Σ_{j=1}^{v} w_{i,j} Y^{j−1},   t_i(Y) := Σ_{j=1}^{v} t_{i,j} Y^{j−1}
```

i.e. each vector is folded into a univariate polynomial evaluated at a fresh
challenge `β`. The protocol adds one round:

```
Prover                                        Verifier
m_i := Σ_j 1(w_j = t_i)
                   --- w, m --->
                   <--- β ---                  β ←$ F
                   <--- r ---                  r ←$ F      (2nd prover message is EMPTY)
[β_i = β^{i−1}]_{i∈[v]}          <-- note: β_1 = β^0 = 1, NOT β
h_i := 1/(w_i(β) + r),  g_i := m_i/(t_i(β) + r)
                   --- [β_i], h, g --->
                                               Σ h_i =? Σ g_i
                                               h_i·(Σ_j w_{i,j} β_j + r) =? 1     ∀ i ∈ [ℓ]
                                               g_i·(Σ_j t_{i,j} β_j + r) =? m_i   ∀ i ∈ [T]
                                               β_{i+1} =? β_i · β  ∀ i ∈ [v−1],  β_1 =? 1
```

`k = 3` (5-move, **2nd prover message empty**), verifier degree **3** (5 with the
perfect-completeness patch), non-zeros `≤ (v+3)ℓ + v`. The same `O(ℓ)`
homomorphic trick from 4.3 applies, giving `O(vℓ)` accumulation independent of `T`.

**Lemma 6.** The perfectly-complete `Π_VLK` is
`[1 + (v−1)(ℓ+T−1), 2(ℓ+T)]`-special-sound.

*Proof.* Two-level tree. At each depth-1 node (fixing `w, m, β`) there are
`2(ℓ+T)` choices of `r`; pigeonhole gives `ℓ+T` good ones. Define the **bivariate**
polynomial `p(X,Y)` with `deg_X = ℓ+T−1` and `deg_Y ≤ (v−1)(ℓ+T−1)`:

```
p(X,Y) = Π_k(X + w_k(Y)) · Π_j(X + t_j(Y)) · [ Σ_i 1/(X + w_i(Y)) − Σ_i m_i/(X + t_i(Y)) ]
```

There are `(v−1)(ℓ+T−1) + 1` depth-1 nodes (distinct `β`) each with `ℓ+T` good
children (distinct `r`), so `p` vanishes at enough points to be identically zero
— and Eqn. 7 gives validity via the extended Lemma 4. ∎

Why this matters: vector lookups are what let you look up *tuples*, e.g.
`(a, b, a XOR b)`, which is how bitwise operations and multi-column zkEVM tables
are encoded. The paper stresses HyperNova's lookup does **not** support this.

## 4.5 Circuit selection

**Def. 14.** `R_select` = the `(b, pc) ∈ F^n × F` with `b_i = 0` for all
`i ∈ [n]\{pc}`, and `b_pc = 1` if `pc ∈ [n]`.

```
Prover P(b ∈ F^n, pc ∈ F)             Verifier V
              --- b, pc --->
                                       b_i · (pc − i)  =? 0   ∀ i ∈ [n]
                                       b_i · (b_i − 1) =? 0   ∀ i ∈ [n]
                                       Σ_{i∈[n]} b_i   =? 1
```

`k = 1`, verifier degree **2**. Soundness is elementary and stated inline:
`b_i(b_i−1)=0` forces `b` Boolean; `b_i(pc−i)=0` forces `b_i = 0` for `i ≠ pc`;
the sum check then forces `b_pc = 1`.

This is the entire mechanism behind non-uniform IVC — a degree-2, one-move
protocol. Contrast SuperNova, which needs a **hash-to-group gadget** in its
recursive circuit for the same functionality.

## Section 5 — `Π_plonkup`: parallel composition

**Def. 15.** `C_plonkup := (n, T; σ; c, d, [s_i, G_i]_{i=1}^m; L, t)` where
`σ : [cn] → [cn]` is the wiring permutation, `L ⊆ [cn]` indexes the variables
carrying a lookup gate, `t ∈ F^T` the table. `R_plonkup` = the
`(pi ∈ F^{in}, w ∈ F^{cn})` with

```
w ∈ R_σ   ∧   w ∈ R_GATE   ∧   w_L ∈ R_LK   ∧   w[1..in] = pi
```

`Π_plonkup` is literally the **parallel composition** of `Π_perm`, `Π_GATE`,
`Π_LK`, plus the public-input check. `k = 2` (3-move), verifier degree `d`
(`max(d,3)` with the perfect-completeness patch), non-zeros `≤ cn + 3|L|`.

**Lemma 7.** `Π_plonkup` is `2(T + |L|)`-special-sound. Proof: `Π_perm` and
`Π_GATE` are trivially 1-special-sound (the prover just sends the witness); the
public-input check holds by inspection; `Π_LK` is `2(T+|L|)`-special-sound by
Lemma 5; parallel composition takes the max.

**This is the payoff of the whole framework.** Building a folding scheme for
Plonk-with-lookups reduces to: write four toy protocols, compose them in
parallel, take the max arity. No new random-linear-combination protocol, no new
security proof.
