import Lake
open Lake DSL

-- Supplementary Lean 4 development for "Single quadratic equations do not compress integer dimension".
-- Built against the archived development (Zenodo 10.5281/zenodo.23053094 = GitHub
-- hirokifukui/single-quadratic-definability, tag v0.31.0, commit e9b1817), pinned by commit.
package «sq-injective-dimension» where
  leanOptions := #[⟨`autoImplicit, false⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "d46bd45325c5cdf0ecf5cee0f5ff6d6e3586eb35"

require «mpup-lean» from git
  "https://github.com/hirokifukui/single-quadratic-definability.git" @ "e9b1817eb1c233b55abbf29413919d5a83ff09c0" / "lean"

@[default_target]
lean_lib «SelectionS65» where
