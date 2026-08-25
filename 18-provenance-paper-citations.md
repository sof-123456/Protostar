# 18 — Provenance: Where Every Claim in File 17 Is Written in the Paper

Every statement in [17-instance-equation-combine-from-scratch.md](17-instance-equation-combine-from-scratch.md)
traced to its source, with section, PDF page, and verbatim text.

**Reading the quotes.** `pdftotext` drops every Greek glyph and most math
operators from this PDF, so raw extracted lines have gaps. Each citation below
gives the **raw extracted line** (so you can verify it yourself) and the
**restored reading**. `L<n>` = line number in `_source/paper-extracted-text.txt`.

Verify any row with:

```bash
sed -n '<L>p' _source/paper-extracted-text.txt
```

---

## PART 1 claims — "What is an instance"

### C1. The three parameters `k`, `d`, `ℓ`

**§3.1, p.16, L698–700.**

```
The protocol sps has 3 essential parameters k, d,   N, meaning that sps is a (2k - 1)-
move protocol with verifier degree d and output length  (i.e. the verifier checks  degree
d algebraic equations).
```

> Restored: "The protocol `Π_sps` has 3 essential parameters `k, d, ℓ ∈ N`, meaning
> that `Π_sps` is a `(2k−1)`-move protocol with verifier degree `d` and **output
> length `ℓ` (i.e. the verifier checks `ℓ` degree-`d` algebraic equations)**."

This one line is the source for: `k` = number of prover messages, `d` = degree,
and — critically — **`ℓ` = number of equations**, not instances.

### C2. The instance format (`acc.x`)

**§3.4, p.20, L831.**

```
    � Accumulator instance acc.x := {pi, [Ci]ki=1, [ri]ki=-11, E, �}, where pi  Min is the accu-
```

> Restored: "Accumulator instance `acc.x := {pi, [C_i]_{i=1}^{k}, [r_i]_{i=1}^{k−1},
> E, μ}`".

This is where file 17's "one instance = one commitment + `μ` + `E`" comes from.
With `k = 1` and no challenges, the list collapses to `{pi, C_1, E, μ}`.

### C3. The witness format (`acc.w`)

**§3.4, p.20, L835.**

```
    � Accumulator witness acc.w := {[mi]ki=1}, where [mi]ik=1 are the accumulated prover
```

> Restored: "Accumulator witness `acc.w := {[m_i]_{i=1}^{k}}`, where `[m_i]` are the
> accumulated prover messages."

### C4. `μ` is the slack variable

**§3.4, p.20, L834.**

```
       terms, and �  F is a slack variable.
```

> Restored: "…and `μ ∈ F` is a slack variable."

### C5. A proof **is** an accumulator with `μ = 1`, `E = 0`

**Remark 2, §3.4, p.20, L856ff.**

```
Remark 2. The accumulation scheme for VNARK is also naturally a folding scheme as
defined in Nova [KST22], where we can view an accumulator as a relaxed NP instance
with error terms. A NARK proof  is an accumulator with � = 1 and E = 0  G.
```

> Restored: "A NARK proof `π` is an accumulator with `μ = 1` and `E = 0 ∈ G`."

Remark 2 continues — and this is the direct source for the **fold-arity-2** claim:

> "We can use the same accumulation scheme to fold two accumulators `(acc, acc')`
> into a new accumulator `acc''`. … In the language of folding schemes, we can fold
> two NARK instances into an accumulator; or fold a NARK instance and an
> accumulator into an updated accumulator; or fold two accumulators into an updated
> accumulator."

**Three listed cases, all of them "two into one."** No case combines three or more.

---

## PART 2 claims — "What is an equation"

### C6. The verifier outputs a **zero vector of length `ℓ`**

**§3.1, p.16, L706.**

```
and checks that the output is a zero vector of length . More precisely, deg(Vsps) = d, s.t.
```

> Restored: "…and checks that the output is a **zero vector of length `ℓ`**. More
> precisely, `deg(V_sps) = d`."

This is the source for file 17's "`V_sps` outputs a vector of 4 numbers and accepts
iff all are zero."

### C7. The homogeneous decomposition `f_j`

**§3.1, p.16, L708–712** (the displayed formula), and **§3.4, p.19, L822–823**:

```
where e = 0 and � = 1 for the NARK verifier VNARK. Here fjVsps is a degree-j homogeneous
algebraic map that outputs  field elements. Degree-j homogeneity says that each monomial
term of fjVsps has degree exactly j.
```

> Restored: "Here `f_j^{V_sps}` is a **degree-`j` homogeneous** algebraic map that
> outputs `ℓ` field elements. Degree-`j` homogeneity says that each monomial term of
> `f_j^{V_sps}` has degree **exactly `j`**."

Source for file 17's "`μ` homogenises the check" explanation — and note it says the
map "outputs `ℓ` field elements", i.e. one per equation.

### C8. The relaxed check, and that `e = 0, μ = 1` for a fresh proof

**§3.4, p.19, L818–822.**

```
                Vsps(pi, .x, .w, [ri]ki=-11, �) := �d-j � fjVsps (pi, .w, [ri]ik=-11) = e
where e = 0 and � = 1 for the NARK verifier VNARK.
```

> Restored: `V_sps^relaxed(pi, π.x, π.w, [r_i], μ) := Σ_{j=0}^{d} μ^{d−j} ·
> f_j^{V_sps}(pi, π.w, [r_i]) = e`, "where `e = 0` and `μ = 1` for the NARK verifier
> `V_NARK`."

### C9. One equation per gate

**Definition 11, §4.2, p.32, L1514ff.**

```
Definition 11. Given configuration CGATE := (n, c, d, [si  Fn, Gi]mi=1) where n is the
number of gates, c is the arity per gate, d is the gate degree, [si]im=1 are the selector vectors,
and [Gi]mi=1 are the gate formulas, the relation RGATE is the set of tuples w  Fcn such
that  m  sj,i � Gj (wi, wi+n, . . . , wi+(c-1)�n) = 0 for all i  [n].
      j=1
```

> Restored: "…the relation `R_GATE` is the set of tuples `w ∈ F^{cn}` such that
> `Σ_{j=1}^{m} s_{j,i}·G_j(w_i, …, w_{i+(c−1)n}) = 0` **for all `i ∈ [n]`**."

**"for all `i ∈ [n]`" is the source for "one equation per gate", hence `ℓ = n` for
`Π_GATE`** — which is why file 17's 4-gate circuit has `ℓ = 4`.

**§4.2, p.33, L1535:**

```
Complexity. GATE is a 1-move protocol (i.e. k = 1) with verifier degree d.
```

Source for file 17's `k = 1`. (File 17 uses degree-2 multiplication gates, so
`d = 2` there.)

---

## PART 3 claims — "`γ` combines EQUATIONS"

### C10. `γ` takes a random linear combination **of the equations**

**§3.5, p.25, L1136–1139.**

```
can transform sps into a special-sound protocol CV[sps] where the Vsps reduces from 
degree-d checks to 1 degree-(d + 2) check and additionally 2  degree-2 checks. Instead
of checking the output of Vsps to be  zeroes, we take a random linear combination of
the  verification equations using powers of a challenge .
```

> Restored: "…where `V_sps` reduces from **`ℓ` degree-`d` checks to 1 degree-`(d+2)`
> check** and additionally `2√ℓ` degree-2 checks. Instead of checking the output of
> `V_sps` to be `ℓ` zeroes, **we take a random linear combination of the `ℓ`
> verification equations using powers of a challenge `γ`.**"

**This is the decisive sentence.** It says explicitly that what is combined is
*"the `ℓ` verification equations"* — not instances, not coordinates — and that the
weights are *"powers of a challenge `γ`"*. It is the source for file 17 Part 3 in
full.

### C11. The worked `ℓ = 2` example the paper itself gives

**§3.5, p.25, L1139–1141.**

```
For example, if the map is
Vsps(x1, x2) := (Vsps,1(x1, x2), Vsps,2(x1, x2)) = (x1 + x2, x1x2) we can set the new algebraic
map as Vsps(x1, x2, ) := Vsps,1(x1, x2) +  � Vsps,2(x1, x2) = (x1 + x2) + x1x2 for a random
```

> Restored: `V'_sps(x_1,x_2,γ) := V_{sps,1} + γ·V_{sps,2} = (x_1+x_2) + γ·x_1x_2`.

The paper's own miniature version of file 17's
`eq_1 + γ·eq_2 + γ²·eq_3 + γ³·eq_4`.

### C12. The `√ℓ` decomposition

**§3.5, p.25, L1152–1158.**

```
but requires the prover to send another messageof length . To achieve a more optimal
tradeoff, we write each i =j + k �  for j, k  [1, ]. The prover then sends  powers of
 and  - 1 powers of  . From these, each power of  from 1 to  can be recomputed
using just one multiplication. This results in the prover sending an additional message of
length 2 , the original  verification checks being transformed into a single degree d + 2
check and additionally 2  degree 2 checks for the consistency of the powers of .
```

> Restored: "we write each `i = j + k·√ℓ` for `j,k ∈ [1,√ℓ]`. The prover then sends
> `√ℓ` powers of `γ` and `√ℓ−1` powers of `γ^{√ℓ}`. From these, **each power of `γ`
> from 1 to `ℓ` can be recomputed using just one multiplication.** This results in
> the prover sending an additional message of **length `2√ℓ`**, the original `ℓ`
> verification checks being transformed into a **single degree `d+2` check** and
> additionally `2√ℓ` degree-2 checks for the consistency of the powers of `γ`."

Source for file 17's `γ_1 = 3`, `δ_1 = 9`, and the "one multiplication each" weight
recovery. It also confirms the two *rejected* attempts described in report 06.

### C13. Why the compression is sound (the polynomial-root argument)

**Lemma 3 proof, §3.5, p.27, L1218–1228.**

```
Define the degree  - 1 univariate polynomial
                                    p(X) := Xj � cj
where cj := Vsps,j(msg)  F is Vsps,j's output on message msg. Since the transcripts are
accepting, it holds that p evaluates to zero on the  different values of  that correspond
to the  children of node u. Thus the univariate polynomial p is a zero polynomial, which
implies that Vsps outputs zero vector on message msg.
```

> Restored: "Define the degree `ℓ−1` univariate polynomial `p(X) := Σ X^j·c_j`
> where `c_j := V_{sps,j}(msg)` … `p` evaluates to zero on the `ℓ` different values
> of `γ` … Thus `p` is a **zero polynomial**, which implies that `V_sps` outputs the
> zero vector on message `msg`."

Exactly file 17 §3.4's `p(X) = eq_1 + eq_2·X + eq_3·X² + eq_4·X³` and the
"at most `ℓ−1` roots" bound.

### C14. Error terms become **single field elements** — the payoff

**§3.5, p.27, L1232–1234.**

```
High-low degree accumulation. After the transformation, the error vectors ej (1 
j  d + 1) become single field elements, and we can use the trivial commitment Ej :=
Commit(ck, ej ) := ej without group operations.
```

> Restored: "After the transformation, the error vectors `e_j` (`1 ≤ j ≤ d+1`)
> **become single field elements**, and we can use the trivial commitment
> `E_j := Commit(ck, e_j) := e_j` **without group operations**."

Source for file 17's "commitment for them: the identity function — free."

### C15. `k + 2` instead of `k + d − 1`

**§3.5, p.28, L1245–1247.**

```
The accumulator verifier needs to
do only k + 2 (rather than k + d - 1) group scalar multiplications, with the tradeoff of 1
more hash and O(d) more field operations.
```

> Restored: verbatim as shown.

Source for the last row of file 17's "what was actually gained" table.

---

## PART 4 claims — "`α` combines INSTANCES"

### C16. There are `d − 1` cross terms

**Figure 3, step 2, §3.4, p.21, L870.**

```
   2. Compute [ej]dj=-11  (F)d-1, such that
```

> Restored: "Compute `[e_j]_{j=1}^{d−1} ∈ (F^ℓ)^{d−1}`, such that …"

Note the type: **`d−1` vectors, each in `F^ℓ`.** That is precisely file 17's
"`d−1 = 1` vector in `F⁴`". Both counts, `d−1` and `ℓ`, appear in this one symbol —
and they are different things.

### C17. The fold is a **two-term** linear combination

**Figure 3, steps 5–6, §3.4, p.21, L897–902.**

```
5. Set vectors
v := 1, pi, [ri]ki=-11, [Ci]ki=1, [mi]ik=1 , v := �, pi, [ri]ik=-11, [Ci]ik=1, [mi ]ki=1 .
6. v := �, pi, [ri]ki=-11, [Ci]ki=1, [mi]ki=1   � v + v.
```

> Restored: `v := (1, pi, [r_i], [C_i], [m_i])` (the new proof, note the leading
> **1** = its `μ`), `v' := (μ', pi', [r'_i], [C'_i], [m'_i])` (the accumulator), and
> **`v'' ← α·v + v'`**.

**Two vectors on the right-hand side. One challenge `α`.** This is the single most
direct proof of the fold-arity-2 claim, and the source for file 17 §4.2's
`μ''=α·1+μ'`, `a''=α·a+a'`, etc.

### C18. Error accumulation uses powers of `α`

**Figure 3, step 7, §3.4, p.21.**

```
7. E  E +               d-1  j  �       Ej .
                        j=1
```

> Restored: `E'' ← E' + Σ_{j=1}^{d−1} α^j · E_j`.

Note: **here `α` does appear with powers** — because `d` objects are being
combined, not 2. At `d = 2` (file 17) the sum has a single term, `α¹·E_1`.

### C19. The decider's checks

**Figure 5, §3.4, p.22, L931–940.**

```
Dacc(acc = (acc.x = {pi, [Ci]ik=1, [ri]ik=-11, E, �}, acc.w = {[mi]ki=1}))
1. Ci =? Commit(ck, mi) for all i  [k].
2. e   d  �d-j  fjVsps (pi, [mi]ki=1, [ri]ik=-11)
       j=0
3. E =? Commit(ck, e).
```

Source for file 17 §4.3's decider verification
`a''∘b'' − μ''·c'' =? e''`.

### C20. Knowledge error `(d+1)/|F|`, and the `d+1` transcripts

**Theorem 2, p.22, L970ff** — knowledge error
`(Q+1)·(d+1)/|F| + negl(λ)`.

**Claim 1 in its proof, p.23, L1038–1039:**

```
Claim 1: I is (d + 1)-special-sound Consider the relation Racc where Racc is defined
in Definition 8. Consider d + 1 accepting transcripts for I :
```

**p.24, L1094:**

```
is zero on d + 1 points (1, . . . , d+1), i.e. is zero everywhere. The constant term of this
```

> Restored: "…is zero on `d+1` points `(α_1, …, α_{d+1})`, i.e. is zero everywhere.
> **The constant term** of this polynomial is … It being 0 implies that `D(acc) = 0`.
> Additionally, the **degree-`d` term** of the polynomial is … this implies that
> `V_NARK(pi, π) = 0`."

Source for file 17's note that `d+1` is the **extractor's** requirement, not the
protocol's: it appears only inside the soundness proof, applied to `d+1`
*transcripts*, never to `d+1` instances in an honest run.

### C21. Fold arity is 2 — the structural confirmation

**§2.5 "PCD", p.15, L674–679.**

```
Accumulation schemes can be compiled
into full PCD if they support accumulating an arbitrary number of accumulators and
proofs[BCMS20; BCLMS21]. For simplicity, we only build accumulation for one proof and
one accumulator, as well as for two accumulators. This enables PCD for DAGs of degree
two. By transforming higher degree graphs into degree two graphs (by converting each
degree d node into a log2(d) depth tree), we can achieve PCD for these graphs.
```

> Restored: verbatim as shown.

**Decisive.** Full PCD would follow *if* the scheme accumulated "an arbitrary
number of accumulators and proofs". It does not — only "one proof and one
accumulator, as well as for two accumulators" — giving PCD for **degree-two DAGs**
only, with higher-degree nodes rewritten as `log₂(d)`-depth **binary** trees.

(Watch the notation: the `d` in "degree `d` node" is the DAG out-degree, unrelated
to the verifier degree `d`.)

---

## Summary table

| File 17 claim | Source | Page | Line |
|---|---|---|---|
| `k`, `d`, `ℓ` are the three parameters; `ℓ` = #equations | §3.1 | 16 | 698–700 |
| Verifier outputs a zero vector of length `ℓ` | §3.1 | 16 | 706 |
| `f_j` is degree-`j` homogeneous, outputs `ℓ` elements | §3.4 | 19 | 822–823 |
| Relaxed check `Σ μ^{d−j} f_j = e`; `e=0, μ=1` for a proof | §3.4 | 19 | 818–822 |
| Instance = `{pi, [C_i], [r_i], E, μ}` | §3.4 | 20 | 831 |
| Witness = `{[m_i]}` | §3.4 | 20 | 835 |
| `μ` is the slack variable | §3.4 | 20 | 834 |
| A proof is an accumulator with `μ=1, E=0` | Remark 2 | 20 | 856 |
| One equation per gate (`ℓ = n` for `Π_GATE`) | Def. 11 | 32 | 1514 |
| `Π_GATE` is 1-move, `k = 1` | §4.2 | 33 | 1535 |
| **`γ` combines the `ℓ` verification equations by powers** | §3.5 | 25 | 1136–1139 |
| The paper's own `(x_1+x_2, x_1x_2)` example | §3.5 | 25 | 1139–1141 |
| `√ℓ` split; `2√ℓ` message; one mult per power | §3.5 | 25 | 1152–1158 |
| Soundness = degree-`(ℓ−1)` polynomial has `≤ ℓ−1` roots | Lemma 3 | 27 | 1218–1228 |
| Error terms become single field elements, free commitment | §3.5 | 27 | 1232–1234 |
| `k+2` rather than `k+d−1` group mults | §3.5 | 28 | 1245–1247 |
| `d−1` cross terms, each in `F^ℓ` | Fig. 3 §2 | 21 | 870 |
| **The fold is `v'' ← α·v + v'` — two vectors** | Fig. 3 §5–6 | 21 | 897–902 |
| `E'' = E' + Σ α^j E_j` | Fig. 3 §7 | 21 | 903 |
| Decider checks | Fig. 5 | 22 | 931–940 |
| `d+1` transcripts is the **extractor's** need | Thm 2 proof | 23–24 | 1038, 1094 |
| **Only 2-way accumulation is built → PCD degree two** | §2.5 | 15 | 674–679 |

---

## The two load-bearing quotes

If you keep only two sentences from this file, keep these — they settle the
question the last several exchanges kept returning to.

**On what `γ` combines (equations, by powers) — §3.5, p.25:**

> "Instead of checking the output of `V_sps` to be `ℓ` zeroes, **we take a random
> linear combination of the `ℓ` verification equations using powers of a challenge
> `γ`**."

**On how many instances are folded (two) — Figure 3, step 6, p.21:**

> `v'' ← α · v + v'`

and **§2.5, p.15:**

> "we only build accumulation for **one proof and one accumulator, as well as for
> two accumulators**. This enables PCD for DAGs of degree two."

---

## Caveat on this file's method

All citations are to the PDF's **text layer**, extracted with `pdftotext -layout`.
That layer is faithful for prose and structure but **drops Greek letters, arrows,
and some operators**, and interleaves cells of multi-column tables. Every quote
above is prose or a numbered protocol step, where extraction is reliable — none
depends on reading a table cell. Where a restored symbol could be contested
(`β` in §4.4, and the `(k+d+O(1))H` cell of Theorem 3's table), that is flagged at
the point of use in files 15 and 10 respectively, not silently resolved.
