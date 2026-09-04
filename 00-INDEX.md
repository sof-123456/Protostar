# Protostar (ePrint 2023/620) — Analysis Report

**Source:** `2023-620.pdf` — *Protostar: Generic Efficient Accumulation/Folding for
Special-sound Protocols*, Benedikt Bünz (Stanford / Espresso Systems) and
Binyi Chen (Espresso Systems), version dated **December 6, 2023**, 57 pages.
IACR ePrint Archive report 2023/620.

This report is a step-by-step walkthrough of the paper. Read the files in order;
each one is self-contained but assumes the previous ones.

## Reading order

| # | File | What it covers |
|---|------|----------------|
| 01 | [01-paper-overview.md](01-paper-overview.md) | Metadata, abstract decoded, the 5 headline claims |
| 02 | [02-problem-and-prior-work.md](02-problem-and-prior-work.md) | Why IVC, why folding, what Nova/SuperNova/Sangria/Origami could not do |
| 03 | [03-preliminaries.md](03-preliminaries.md) | Special-soundness, transcript trees, NARK, IVC, accumulation definitions |
| 04 | [04-step1-compiler-pipeline.md](04-step1-compiler-pipeline.md) | **Step 1** — the 4-stage compiler `sps → cm → FS → acc → IVC` |
| 05 | [05-step2-accumulation-scheme.md](05-step2-accumulation-scheme.md) | **Step 2** — the generic accumulation scheme (Fig. 3/4/5, Thm 2) |
| 06 | [06-step3-cv-compression.md](06-step3-cv-compression.md) | **Step 3** — the `CV[·]` verifier-compression trick and hi/low-degree accumulation |
| 07 | [07-step4-error-term-algorithms.md](07-step4-error-term-algorithms.md) | **Step 4** — how error terms are actually computed (Sec 3.6, 3.6.1, App. B) |
| 08 | [08-subprotocols.md](08-subprotocols.md) | The building blocks: permutation, high-degree gate, lookup, vector lookup, circuit selection |
| 09 | [09-protostar-and-ccs.md](09-protostar-and-ccs.md) | Assembling Protostar (`Π_mplkup`) and Protostar_ccs (App. C) |
| 10 | [10-efficiency-comparison.md](10-efficiency-comparison.md) | Table 1 + Theorem 3 + Corollary 1 cost tables, decoded |
| 11 | [11-security-analysis.md](11-security-analysis.md) | Every soundness lemma, knowledge errors, assumptions, trust surface |
| 12 | [12-critique-and-open-problems.md](12-critique-and-open-problems.md) | Gaps, caveats, inconsistencies, what an implementer must decide |
| 13 | [13-glossary.md](13-glossary.md) | Notation and symbol table |
| 14 | [14-how-many-instances-do-we-fold.md](14-how-many-instances-do-we-fold.md) | **Fold arity settled step by step, with verified numeric traces at `d=2` and `d=3`** |
| 15 | [15-the-beta-challenge.md](15-the-beta-challenge.md) | **The `β` challenge: compressing a tuple by degree; β vs γ; worked `F_101` instance** |
| 16 | [16-one-example-all-four-challenges.md](16-one-example-all-four-challenges.md) | **ONE worked IVC step showing `β`, `r`, `γ`, `α` together and why their counts differ** |
| 17 | [17-instance-equation-combine-from-scratch.md](17-instance-equation-combine-from-scratch.md) | **START HERE if confused** — minimal 4-gate example: what an instance is, what an equation is, γ combining equations vs α combining instances |
| 18 | [18-provenance-paper-citations.md](18-provenance-paper-citations.md) | **Every claim in file 17 traced to section, page, and verbatim quote in the paper** |
| 19 | [19-page20-walkthrough.md](19-page20-walkthrough.md) | **Paper p.20 (accumulator format + the 3 algorithm interfaces) executed with real numbers, incl. Figures 3/4/5** |
| 20 | [20-lookup-tables-explained.md](20-lookup-tables-explained.md) | **What a lookup table is and why membership is not an equation — `Π_LK` and `Π_VLK` (XOR) run end-to-end in `F_101`, honest prover and cheating prover** |
| 21 | [21-folding-a-lookup-step-by-step.md](21-folding-a-lookup-step-by-step.md) | **FOLDING a lookup: `f_j` decomposition, where the error terms come from (one number at a time), 3 instances folded in a chain, and the `O(ℓ)` cached-commitment trick — all verified in `F_101`** |

## One-paragraph summary

Protostar is a **recipe**, not a single protocol. It takes *any* `(2k−1)`-move
public-coin special-sound interactive protocol whose verifier only checks `ℓ`
algebraic equations of degree `d`, and mechanically turns it into an
Incrementally Verifiable Computation scheme whose recursive circuit costs
**`k+2` group scalar multiplications and `k+d+O(1)` field/hash operations** —
independent of proof size, witness size, and verifier running time. The authors
then instantiate the recipe with a hand-built special-sound protocol for
*non-uniform Plonkup* (multiple branch circuits, high-degree custom gates,
and vector lookups), obtaining an IVC whose recursive circuit is **3 group
scalar multiplications** plus a hash of `d` field elements, with no trusted
setup, no pairings, and no prover-side FFTs over the witness.

## Verification note

All figures, lemma numbers, and cost tables in this report were read directly
out of the PDF text layer (`pdftotext -layout`). Where the PDF's own numbers are
internally inconsistent, this is flagged explicitly in
[12-critique-and-open-problems.md](12-critique-and-open-problems.md) rather than
silently smoothed over.

## Source material

`_source/paper-extracted-text.txt` — the full text layer of the PDF as extracted
with `pdftotext -layout`, kept so every quotation and cost table above can be
checked against the original. Tables and figures survive extraction only
approximately; where a cell is garbled this is noted at the point of use.
