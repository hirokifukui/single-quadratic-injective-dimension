# Single quadratic equations do not compress integer dimension — supplementary Lean 4 development

Version 1.0.1 (2026-10-04). Author: Hiroki Fukui. DOI of this version: [10.5281/zenodo.23132774](https://doi.org/10.5281/zenodo.23132774); all versions: [10.5281/zenodo.23132399](https://doi.org/10.5281/zenodo.23132399). The paper cites v1.0.0 ([10.5281/zenodo.23132400](https://doi.org/10.5281/zenodo.23132400)); v1.0.1 has the same Lean sources and corrects the documentation (see *Changes*).

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

`lean/` depends on the archived development by a git pin (`lakefile.lean`), so the archived sources are fetched, not copied. The library `SelectionS65` contains the modules the paper uses and their imports: `Corr`, `PolyGraph`, `Conjunction`, `DepCheck`, `Relations`, `NormDim`, `FourSq`, `QuadForm`, `Arith`, and the audit module `PaperAudit`. Some imported modules also contain statements about norm selections that the paper does not use; a few of those take the ternary-coset input TCER as an explicit hypothesis. No paper statement depends on them (see the dependency checks below). Some file headers say "scratch, not sealed" or carry session labels (S66, S67): these are internal working notes from development, not the status of this release; the files were left byte-identical to the sources that were audited.

## Trust boundary

- **Axioms.** Each of the 30 declarations listed in Appendix A depends only on `propext`, `Classical.choice`, `Quot.sound` (no `sorryAx`, no `Lean.ofReduceBool`).
- **Dependency checks (†).** For eight declarations, `#dep_check` walks the transitive closure of the constants used and reports `DEPCHECK FAIL` if a constant name contains any string from a fixed list (it reports; it does not stop `lake build`; the mandatory audit gate rejects any FAIL): the decidability results for quadratic equations, DPRM, the projection theorem and growth bounds of the archived development, and its conditional hypotheses (including TCER). This is a check on **names** against that list, not a semantic test.
- **Statement fidelity.** That a formal statement says what the paper says rests on reading both (Appendix A notes the differences); the kernel does not certify it.
- **Upstream cache.** mathlib is taken at commit `d46bd45`. `lake exe cache get` supplies compiled files for mathlib and for the upstream packages its cache covers (Batteries, Aesop, Qq, ProofWidgets and the other mathlib dependencies). The archived development (DiophCompression, MPUP, ResearchUpgrade) and this development (SelectionS65) are compiled from source: 263 modules in the release check.

## Replay

Requirements: Bash, [elan](https://github.com/leanprover/elan) (the toolchain `leanprover/lean4:v4.31.0-rc1` is read from `lean/lean-toolchain`), git, curl (used by the mathlib cache), python3, network access (GitHub and the mathlib cache server).

Run it in a fresh checkout or a freshly extracted archive. In a directory that already has `lean/.lake/`, `lake build` is incremental and reuses what is there.

```bash
cd lean
./replay.sh          # lake exe cache get; lake build; audit gate. Exit 0 only if both pass.
```

`replay.sh` runs with `set -euo pipefail`. The audit gate (`lean/scripts/audit_gate.py`, with `lean/scripts/required_roots.json`) exits non-zero unless each of the 30 required declarations has exactly one standard-axiom report, each of the 8 dependency-check declarations has exactly one `DEPCHECK OK`, no axiom report is left unparsed, and the forbidden-name list in each source contains the registry. `lake build` alone succeeding is not the check: the replay succeeds only if the gate also exits 0. The logs of the release checks are in `lean/logs_release/`.

## Changes

- **1.0.1** (documentation and PDF fonts only; Lean sources, `lakefile.lean`, `lake-manifest.json`, gate and required-root list unchanged from 1.0.0): the upstream-cache scope is stated precisely; the prerequisites (Bash, curl) and the fresh-directory assumption are stated; the role of `#dep_check` versus the gate is stated; `CITATION.cff` states the licence split; the paper PDF is rebuilt with vector (Type 1) fonts (Latin Modern) instead of bitmap Type 3 fonts, text unchanged; release check repeated from a freshly extracted archive that already contains the shipped `lake-manifest.json` (`lean/logs_release/*_v1.0.1.log`). The 1.0.0 check had started without a top-level manifest and generated the one that 1.0.0 ships.
- **1.0.0** (2026-10-04): first release.

## Licensing

Lean sources and scripts: MIT (`LICENSE`). Paper and documentation: CC BY 4.0 (`LICENSE-CC-BY-4.0.txt`). See `LICENSING.md`.

## Use of AI tools

As disclosed in §1.4 of the paper: large language models (Claude and Claude Code by Anthropic; ChatGPT by OpenAI) were used to explore proof strategies, search for tactic-level proofs and draft Lean code against statements fixed by the author, draft and revise text, read adversarially, and assist the literature search. The Lean kernel checked the formal declarations; the author checked every definition, statement, proof and citation in the paper.
