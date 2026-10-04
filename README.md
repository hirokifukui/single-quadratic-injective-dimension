# Single quadratic equations do not compress integer dimension — supplementary Lean 4 development

Version 1.0.0 (2026-10-04). Author: Hiroki Fukui. DOI: [10.5281/zenodo.23132400](https://doi.org/10.5281/zenodo.23132400).

## The paper

`paper/single_quadratic_injective_dimension_v0.8.pdf`. Call a relation on integer tuples *single-quadratic* (SE₂) if it is defined by one polynomial equation with integer coefficients and total degree at most two, with any finite number of existentially quantified integer unknowns. The paper proves:

- **Theorem 1.** An injective SE₂-definable function ℤⁿ → ℤᵐ exists if and only if n ≤ m.
- **Theorem 2 (structural dichotomy).** An SE₂-definable function either grows at most linearly or agrees on a coset ρ + Mℤⁿ with a vector of rational polynomials of degree at most two.
- **Corollary 3.** The graph of an integer polynomial is SE₂ exactly when its degree is at most two.
- **Corollary 4.** SE₂ is closed neither under composition nor under conjunction.

The paper is self-contained: every proof is written out in it. The formalization is a supplement, not part of the argument.

## What is formalized, and where

| Paper | Where |
|---|---|
| Theorem 1, and the two statements composed into Theorem 2 | the archived development [Fuk-L], doi:[10.5281/zenodo.23053094](https://doi.org/10.5281/zenodo.23053094) (GitHub `hirokifukui/single-quadratic-definability`, tag v0.31.0, commit `e9b1817`) |
| Theorem 2 (composed): `theorem2_sealed` | this repository, `lean/SelectionS65/Corr.lean` |
| Corollary 3: `DiophCompression.ResearchUpgrade.SelectionS67.polyFn_SE2_iff` | `lean/SelectionS65/PolyGraph.lean` |
| Corollary 4(a): `…SelectionS67.not_closed_under_composition` | `lean/SelectionS65/PolyGraph.lean` |
| Corollary 4(b): `…SelectionS67.not_closed_under_conjunction` | `lean/SelectionS65/Conjunction.lean` |

The paper's Appendix A gives the full correspondence table. The extension of Corollary 3 to integer-valued polynomials with rational coefficients is proved in the paper only.

`lean/` depends on the archived development by a git pin (`lakefile.lean`), so the archived sources are fetched, not copied. The library `SelectionS65` contains the modules the paper uses and their imports: `Corr`, `PolyGraph`, `Conjunction`, `DepCheck`, `Relations`, `NormDim`, `FourSq`, `QuadForm`, `Arith`, and the audit module `PaperAudit`. Some imported modules also contain statements about norm selections that the paper does not use; a few of those take the ternary-coset input TCER as an explicit hypothesis. No paper statement depends on them (see the dependency checks below). The file headers say "scratch, not sealed"; they were the working names and were left byte-identical to the sources that were audited.

## Trust boundary

- **Axioms.** Each of the 30 declarations listed in Appendix A depends only on `propext`, `Classical.choice`, `Quot.sound` (no `sorryAx`, no `Lean.ofReduceBool`).
- **Dependency checks (†).** For eight declarations, `#dep_check` walks the transitive closure of the constants used and fails if a constant name contains any string from a fixed list: the decidability results for quadratic equations, DPRM, the projection theorem and growth bounds of the archived development, and its conditional hypotheses (including TCER). This is a check on **names** against that list, not a semantic test.
- **Statement fidelity.** That a formal statement says what the paper says rests on reading both (Appendix A notes the differences); the kernel does not certify it.
- **mathlib** is taken at commit `d46bd45` with its upstream `.olean` cache; everything else is compiled from source by the replay.

## Replay

Requirements: [elan](https://github.com/leanprover/elan) (the toolchain `leanprover/lean4:v4.31.0-rc1` is read from `lean/lean-toolchain`), git, python3, network access.

```bash
cd lean
./replay.sh          # lake exe cache get; lake build; audit gate. Exit 0 only if both pass.
```

`replay.sh` runs with `set -euo pipefail`. The audit gate (`lean/scripts/audit_gate.py`, with `lean/scripts/required_roots.json`) exits non-zero unless each of the 30 required declarations has exactly one standard-axiom report, each of the 8 dependency-check declarations has exactly one `DEPCHECK OK`, no axiom report is left unparsed, and the forbidden-name list in each source contains the registry. The build log and gate output of the release check are in `lean/logs_release/`.

## Licensing

Lean sources and scripts: MIT (`LICENSE`). Paper and documentation: CC BY 4.0 (`LICENSE-CC-BY-4.0.txt`). See `LICENSING.md`.

## Use of AI tools

As disclosed in §1.4 of the paper: large language models (Claude and Claude Code by Anthropic; ChatGPT by OpenAI) were used to explore proof strategies, search for tactic-level proofs and draft Lean code against statements fixed by the author, draft and revise text, read adversarially, and assist the literature search. The Lean kernel checked the formal declarations; the author checked every definition, statement, proof and citation in the paper.
