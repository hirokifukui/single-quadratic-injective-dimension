/-
  S67-07 (conjunction), scratch.  Free variables (x, y, z) = (v 0, v 1, v 2) of ℤ³.
  {y = x²} and {z = y²} are SE₂ relations (one equation, no unknowns); their conjunction is not SE₂:
  turning y into an unknown would make the graph of z = x⁴ SE₂, contradicting `polyFn_SE2_iff`.
-/
import SelectionS65.PolyGraph

namespace DiophCompression.ResearchUpgrade.SelectionS67

open MvPolynomial DiophCompression.ResearchUpgrade.SelectionS66

def relY : Set (Fin 3 → ℤ) := {v | v 1 = v 0 ^ 2}
def relZ : Set (Fin 3 → ℤ) := {v | v 2 = v 1 ^ 2}

theorem relY_SE2 : SE2Set relY := by
  refine ⟨0, X (Sum.inl 1) - X (Sum.inl 0) ^ 2, ?_, ?_⟩
  · exact sc_td_sub ((sc_td_X _).trans (by norm_num)) (sc_td_sq (sc_td_X _))
  · intro v
    simp only [relY, Set.mem_setOf_eq, DiophCompression.evalAtZZ, map_sub, map_pow, eval_X, Sum.elim_inl]
    constructor
    · intro h; exact ⟨Fin.elim0, by rw [h]; ring⟩
    · rintro ⟨-, h⟩; linarith

theorem relZ_SE2 : SE2Set relZ := by
  refine ⟨0, X (Sum.inl 2) - X (Sum.inl 1) ^ 2, ?_, ?_⟩
  · exact sc_td_sub ((sc_td_X _).trans (by norm_num)) (sc_td_sq (sc_td_X _))
  · intro v
    simp only [relZ, Set.mem_setOf_eq, DiophCompression.evalAtZZ, map_sub, map_pow, eval_X, Sum.elim_inl]
    constructor
    · intro h; exact ⟨Fin.elim0, by rw [h]; ring⟩
    · rintro ⟨-, h⟩; linarith

/-- The variable map: x ↦ input, y ↦ new unknown 0, z ↦ output, old unknowns shifted. -/
def projVars (r : ℕ) : Fin 3 ⊕ Fin r → Fin (1 + 1) ⊕ Fin (r + 1) :=
  Sum.elim ![Sum.inl 0, Sum.inr 0, Sum.inl 1] (fun k => Sum.inr k.succ)

theorem elim_comp_projVars {r : ℕ} (v : Fin (1 + 1) → ℤ) (w : Fin (r + 1) → ℤ) :
    Sum.elim v w ∘ projVars r = Sum.elim ![v 0, w 0, v 1] (fun k => w k.succ) := by
  funext x
  rcases x with i | k
  · fin_cases i <;> rfl
  · rfl

theorem graph_fourth_iff (v : Fin (1 + 1) → ℤ) :
    v ∈ DiophCompression.graphVecZZ (polyFn (X 0 ^ 4 : MvPolynomial (Fin 1) ℤ)) ↔ v 1 = v 0 ^ 4 := by
  simp only [DiophCompression.graphVecZZ, Set.mem_setOf_eq]
  constructor
  · intro h
    have := congrFun h 0
    simpa [polyFn] using this
  · intro h
    funext j
    have hj : j = 0 := Subsingleton.elim j 0
    subst hj
    simpa [polyFn] using h

/-- **S67-07 (conjunction).** -/
theorem not_closed_under_conjunction : SE2Set relY ∧ SE2Set relZ ∧ ¬ SE2Set (relY ∩ relZ) := by
  refine ⟨relY_SE2, relZ_SE2, ?_⟩
  rintro ⟨r, P, hdeg, hrep⟩
  have hfour : DiophCompression.SingleQuadraticDefinableFunctionZZ (polyFn (X 0 ^ 4 : MvPolynomial (Fin 1) ℤ)) := by
    refine ⟨r + 1, rename (projVars r) P, (totalDegree_rename_le _ _).trans hdeg, ?_⟩
    intro v
    rw [graph_fourth_iff]
    simp only [DiophCompression.evalAtZZ, eval_rename, elim_comp_projVars]
    constructor
    · intro h
      have hu : (![v 0, v 0 ^ 2, v 1] : Fin 3 → ℤ) ∈ relY ∩ relZ := by
        refine ⟨?_, ?_⟩
        · simp [relY]
        · simp [relZ, h]; ring
      obtain ⟨y, hy⟩ := (hrep _).mp hu
      refine ⟨Fin.cons (v 0 ^ 2) y, ?_⟩
      simpa [DiophCompression.evalAtZZ] using hy
    · rintro ⟨w, hw⟩
      have hu := (hrep ![v 0, w 0, v 1]).mpr ⟨fun k => w k.succ, by simpa [DiophCompression.evalAtZZ] using hw⟩
      obtain ⟨h1, h2⟩ := hu
      simp [relY] at h1
      simp [relZ] at h2
      rw [h2, h1]; ring
  rw [polyFn_SE2_iff, totalDegree_X_pow] at hfour
  norm_num at hfour

end DiophCompression.ResearchUpgrade.SelectionS67
