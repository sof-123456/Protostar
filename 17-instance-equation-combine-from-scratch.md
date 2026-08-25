# 17 — From Scratch: What Is an Instance, What Is an Equation, How Are Equations Combined

The smallest possible complete example. **No lookup, no `β`, no non-uniformity** —
just 4 multiplication gates, so nothing distracts from the three questions.

Everything in **`F_101`**. Every number verified.

---

## The setup

The claim being proved:

> *"I know 12 numbers `a_1..a_4`, `b_1..b_4`, `c_1..c_4` such that
> `a_i · b_i = c_i` for `i = 1,2,3,4`."*

That is a circuit with **4 multiplication gates**. The prover's witness:

```
 i :    1     2     3     4
 a_i:   2     3     5     7
 b_i:   4     6     8     9
 c_i:   8    18    40    63          (2·4=8, 3·6=18, 5·8=40, 7·9=63)
```

Protocol parameters:

```
 k = 1     one prover message (it just sends the witness)
 d = 2     the verifier's equations are degree 2  (a·b is degree 2)
 ℓ = 4     the verifier checks 4 equations
```

---

## PART 1 — What is an INSTANCE?

An **instance** is *one complete proof for one IVC step*. Concretely it is this
pair of objects:

```
π.w  (witness — LONG, stays with the prover)
     m_1 = ( a_1..a_4 , b_1..b_4 , c_1..c_4 )
         = ( 2,3,5,7 , 4,6,8,9 , 8,18,40,63 )        12 field elements

π.x  (instance — SHORT, goes into the recursive circuit)
     C_1 = Commit(ck, m_1)                            1 group element
     μ   = 1                                          slack variable
     E   = 0                                          error commitment
```

That's it. **One instance = one commitment + `μ` + `E`** (plus challenges, of which
there are none here since `k = 1`).

Three things to notice:

1. **The instance is small.** 12 witness values collapse into **one** group element
   `C_1`. That compression is what makes the recursive circuit cheap.
2. **`μ = 1` and `E = 0`** because this is a *fresh proof*. An accumulator is the
   same shape with `μ ≠ 1` and `E ≠ 0` (Remark 2 — a proof *is* an accumulator).
3. **`ℓ = 4` is nowhere in this list.** `ℓ` describes what the *verifier checks*,
   not what the instance *stores*.

---

## PART 2 — What is an EQUATION in it?

An equation is **one arithmetic expression that must come out to zero**.

The verifier `V_sps` is a function that outputs a **vector of `ℓ = 4` numbers**:

```
V_sps( a, b, c )  =  ( a_1b_1 − c_1 ,  a_2b_2 − c_2 ,  a_3b_3 − c_3 ,  a_4b_4 − c_4 )
```

and it **accepts iff that vector is all zeros**. Plugging in the witness:

| # | Equation | Numbers | Result |
|---|---|---|---|
| eq_1 | `a_1·b_1 − c_1` | `2·4 − 8 = 8 − 8` | **0** ✓ |
| eq_2 | `a_2·b_2 − c_2` | `3·6 − 18 = 18 − 18` | **0** ✓ |
| eq_3 | `a_3·b_3 − c_3` | `5·8 − 40 = 40 − 40` | **0** ✓ |
| eq_4 | `a_4·b_4 − c_4` | `7·9 − 63 = 63 − 63` | **0** ✓ |

```
V_sps(a,b,c)  =  ( 0, 0, 0, 0 )   ∈ F⁴          all zeros  ->  ACCEPT ✓
```

**`ℓ = 4` is the length of that output vector.** One entry per gate.

If the prover cheats — say `c_3 = 41` instead of `40`:

```
V_sps(a,b,c)  =  ( 0, 0, 40−41, 0 )  =  ( 0, 0, 100, 0 )      ->  REJECT ✗
```

### Instance vs equation, side by side

| | **Instance** | **Equation** |
|---|---|---|
| What it is | one proof for one step | one "must be 0" expression |
| How many | **2 get folded** | `ℓ = 4` in this instance |
| Lives where | `π.x` + `π.w` | inside the verifier's definition |
| In this example | `(C_1, μ=1, E=0)` + 12 witness values | `a_i·b_i − c_i` for `i=1..4` |

**An instance CONTAINS `ℓ` equations. Folding COMBINES 2 instances.** Different
words for different things.

---

## PART 3 — How the algorithm COMBINES EQUATIONS (`γ`, §3.5)

**Goal:** turn 4 separate equations into **1** equation, so the accumulation error
terms become single numbers instead of length-4 vectors.

**Method:** multiply equation `j` by `γ^{j}` and add them all up.

### Step 3.1 — the verifier picks `γ = 3`

`ℓ = 4`, so `√ℓ = 2`. The prover sends `2(√ℓ−1) = 2` elements:

```
sent:      γ_1 = 3                δ_1 = γ² = 9
implicit:  γ_0 = 1                δ_0 = 1
```

Verifier's consistency checks (degree 2, cheap):

```
γ_1 =? γ           3 = 3            ✓
δ_1 =? γ_1 · γ     9 = 3·3          ✓
```

### Step 3.2 — recover all 4 weights, one multiplication each

Using `γ^{i + 2j} = γ_i · δ_j`:

```
 exponent   i,j     γ_i · δ_j      weight    check 3^e mod 101
 γ⁰        (0,0)     1 · 1     =     1        1
 γ¹        (1,0)     3 · 1     =     3        3
 γ²        (0,1)     1 · 9     =     9        9
 γ³        (1,1)     3 · 9     =    27       27
```

### Step 3.3 — the combined equation

```
COMBINED  =  eq_1  +  3·eq_2  +  9·eq_3  +  27·eq_4    =?  0
```

**Honest prover:**

```
COMBINED  =  0 + 3·0 + 9·0 + 27·0  =  0        ✓ ACCEPT
```

**Cheating prover** (`c_3 = 41`, so `eq_3 = 40 − 41 = 100`):

```
COMBINED  =  0 + 3·0 + 9·100 + 27·0  =  900  =  92   mod 101      ✗ REJECT
                                                (900 − 8·101 = 92)
```

**One equation caught the lie that four equations would have caught.** That is the
whole trick.

### Step 3.4 — why `γ` must be random *and* come after the commitment

A cheater who **knew `γ = 3` in advance** could break two gates so they cancel.
Solve `3·eq_2 + 9·eq_3 = 0`, e.g. `eq_2 = 98`, `eq_3 = 1`:

```
c_2 = 18 − 98 = −80 = 21          c_3 = 40 − 1 = 39

COMBINED  =  0 + 3·98 + 9·1 + 0  =  294 + 9  =  303  =  0    mod 101   ✗ CHEAT PASSES
                                                    (303 = 3·101)
```

But `γ` is **not** known in advance — it is `ρ(C_1)`, derived *after* the prover
commits. Try the same forged witness against `γ = 5`:

```
COMBINED  =  0 + 5·98 + 25·1 + 0  =  490 + 25  =  515  =  10   mod 101   ✓ CAUGHT
                                                        (515 − 5·101 = 10)
```

**Why this is safe in general.** Write the equation outputs as coefficients of a
polynomial:

```
p(X)  =  eq_1 + eq_2·X + eq_3·X² + eq_4·X³
      =  0    + 98·X   + 1·X²    + 0
      =  X² + 98X  =  X·(X + 98)
```

`p` is a **nonzero** polynomial of degree 2, so it has **at most 2 roots**: here
`X = 0` and `X = −98 = 3`. Only those 2 values of `γ` out of 101 let the cheat
through — probability `2/101`. In a real field, `≤ (ℓ−1)/|F| ≈ ℓ/2²⁵⁶`.

That is exactly **Lemma 3**: a cheating prover survives only if `γ` lands on a root
of a degree-`(ℓ−1)` polynomial, and the extractor needs `ℓ` distinct `γ` to force
`p ≡ 0` and hence every `eq_j = 0`.

### What was actually gained

| | before `γ` | after `γ` |
|---|---|---|
| equations checked | 4, degree 2 | 1, degree 4 (`d+2`) + 4 degree-2 consistency checks |
| accumulation error terms | `d−1 = 1` vector in **`F⁴`** | `d+1 = 3` **single numbers** |
| commitment for them | a real group commitment | **the identity function — free** |
| group ops in recursive circuit | `k + d − 1` | `k + 2` |

At `ℓ = 4` the saving is tiny. At `ℓ = 2²⁰` gates with `d = 10`, it is the
difference between a recursive circuit that grows with `d` and one that does not.

---

## PART 4 — How the algorithm COMBINES INSTANCES (`α`, §3.4)

Different operation entirely. Now we take **2 instances** and produce **1**.

### The two instances

```
Instance A — the new proof π           Instance B — the accumulator acc
  a  = (2, 3, 5, 7)                      a' = (1, 1, 2, 2)
  b  = (4, 6, 8, 9)                      b' = (3, 2, 1, 4)
  c  = (8,18,40,63)                      c' = (1, 1, 1, 1)
  μ  = 1                                 μ' = 2
  e  = (0,0,0,0)                         e' = a'∘b' − μ'·c'
       (it's a valid fresh proof)            = (3,2,2,8) − (2,2,2,2)
                                             = (1, 0, 0, 6)
```

Both satisfy the **relaxed** check `a∘b − μ·c = e`. (At `μ=1, e=0` that is the
original check — Remark 2.)

### Step 4.1 — the cross term (`d − 1 = 1` of them)

```
e_1 = a∘b' + a'∘b − μ'·c − c'

  a∘b'  = (2·3, 3·2, 5·1, 7·4) = ( 6,  6,  5, 28)
  a'∘b  = (1·4, 1·6, 2·8, 2·9) = ( 4,  6, 16, 18)
  μ'·c  = 2·(8,18,40,63)       = (16, 36, 80,126)
  c'                            = ( 1,  1,  1,  1)

e_1 = (6+4−16−1, 6+6−36−1, 5+16−80−1, 28+18−126−1)
    = (−7, −25, −60, −81)
    = (94, 76, 41, 20)      mod 101
```

Prover commits `E_1 = Commit(e_1)` and publishes it as `pf`.

### Step 4.2 — the fold, with `α = 5`

```
μ''  = α·1 + μ'      = 5 + 2                          = 7
a''  = α·a  + a'     = 5·(2,3,5,7)   + (1,1,2,2)      = (11, 16, 27, 37)
b''  = α·b  + b'     = 5·(4,6,8,9)   + (3,2,1,4)      = (23, 32, 41, 49)
c''  = α·c  + c'     = 5·(8,18,40,63)+ (1,1,1,1)      = (41, 91, 100, 13)   mod 101
e''  = e' + α·e_1    = (1,0,0,6) + 5·(94,76,41,20)    = (67, 77,  3,  5)    mod 101
E''  = E' + α·E_1                                      (by commitment homomorphism)
```

### Step 4.3 — verify: does the decider accept?

Recompute `a''∘b'' − μ''·c''` and compare to `e''`:

```
a''∘b''  = (11·23, 16·32, 27·41, 37·49)
         = (253, 512, 1107, 1813)     =  (51,  7, 97, 96)   mod 101

μ''·c''  = 7·(41, 91, 100, 13)
         = (287, 637, 700, 91)        =  (85, 31, 94, 91)   mod 101

difference = (51−85, 7−31, 97−94, 96−91)
           = (−34, −24, 3, 5)         =  (67, 77,  3,  5)   mod 101
```

and `e'' = (67, 77, 3, 5)`. ✓ **All four coordinates match. The decider accepts.**

Note what happened: **2 instances went in, 1 came out**, and the result still has
**4 equations** — same `ℓ`, same shape, same size. That invariance is why IVC can
run forever without the proof growing.

---

## PART 5 — The two "combine" operations side by side

| | **γ combines EQUATIONS** | **α combines INSTANCES** |
|---|---|---|
| Section | 3.5 (`CV`) | 3.4 (accumulation) |
| Input | `ℓ = 4` equations | **2** instances |
| Output | 1 equation | 1 instance |
| Formula | `eq_1 + γ·eq_2 + γ²·eq_3 + γ³·eq_4` | `α·π + acc` |
| Powers used | `γ⁰, γ¹, γ², γ³` (4) | `α⁰, α¹` (2) |
| Value here | `γ = 3` → weights `1, 3, 9, 27` | `α = 5` |
| Extra data published | `γ_1, δ_1` (2 elements) | `E_1` (1 commitment) |
| Happens | inside **one** instance | **between** instances |
| Changes `ℓ`? | yes: `4 → 1` | **no**: `4 → 4` |

### The rule connecting them

> **Both are "multiply by powers of a random challenge and add up."
> The number of powers = the number of things being combined.**
>
> - 4 equations → 4 powers of `γ`: `γ⁰, γ¹, γ², γ³`
> - 2 instances → 2 powers of `α`: `α⁰, α¹` — and since `α⁰ = 1`, it just looks
>   like `α·π + acc`, which is why nobody calls it "powers"

That single sentence resolves every "why so many powers here but only one there"
question in this paper.

---

## PART 6 — Vocabulary recap

| Term | In this example |
|---|---|
| **instance** | one proof: `(C_1, μ, E)` + the 12 witness values |
| **equation** | one "must be 0" expression, e.g. `a_1·b_1 − c_1` |
| **`ℓ`** | how many equations: **4** |
| **`d`** | max degree of an equation: **2** (`a·b`) |
| **`k`** | how many prover messages: **1** |
| **`μ`** | slack variable; `1` for a fresh proof |
| **`e` / `E`** | error vector / its commitment; `0` for a fresh proof |
| **`γ`** | challenge that **combines the 4 equations into 1** |
| **`α`** | challenge that **folds 2 instances into 1** |
| **fold arity** | **2**, always |
