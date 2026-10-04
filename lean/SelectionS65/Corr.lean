/- S67-05 (scratch): the sealed declarations behind paper I, recorded in the build log (types via #check, axioms,
   forbidden-dependency checks).  `theorem2_sealed` is the only new declaration: it composes two sealed ones so that
   Theorem 2 of the paper has one Lean statement about the original class. -/
import ResearchUpgrade
import SelectionS65.DepCheck

open DiophCompression DiophCompression.ResearchUpgrade DiophCompression.ResearchUpgrade.QuadraticGraphData

/-- Theorem 2 of paper I, for the original sealed class (composition of two sealed declarations). -/
theorem theorem2_sealed {n m : ℕ} {f : (Fin n → ℤ) → (Fin m → ℤ)}
    (hf : DiophCompression.SingleQuadraticDefinableFunctionZZ f) : LinearGrowth f ∨ WeakVectorCosetNF f := by
  obtain ⟨r, D, hD⟩ := graphData_of_singleQuadraticDefinable hf
  exact D.summit_of_defines hD

set_option pp.explicit false
#check @theorem2_sealed
#print axioms theorem2_sealed
#check @singleQuadratic_sharp_iff
#print axioms singleQuadratic_sharp_iff
#check @singleQuadratic_injective_dimension_sharp
#print axioms singleQuadratic_injective_dimension_sharp
#check @summit_of_defines
#print axioms summit_of_defines
#check @graphData_of_singleQuadraticDefinable
#print axioms graphData_of_singleQuadraticDefinable
#check @range_polarMapQ_eq_dualAnnihilator_ker
#print axioms range_polarMapQ_eq_dualAnnihilator_ker
#check @zLinQ_radicalQ_eq_zero
#print axioms zLinQ_radicalQ_eq_zero
#check @outCoordQ_radicalQ_eq_zero
#print axioms outCoordQ_radicalQ_eq_zero
#check @exists_affine_centre_of_all_inputs
#print axioms exists_affine_centre_of_all_inputs
#check @completeSquare
#print axioms completeSquare
#check @dim_le_of_linearGrowth_injective
#print axioms dim_le_of_linearGrowth_injective
#check @not_injective_of_weakVectorCosetNF
#print axioms not_injective_of_weakVectorCosetNF
#check @exists_collision_vector
#print axioms exists_collision_vector
#check @branch_exhaustive
#print axioms branch_exhaustive
#check @witnessCoeff_eq_zero
#print axioms witnessCoeff_eq_zero
#check @m_le_one_of_linear
#print axioms m_le_one_of_linear
#check @weakVectorCosetNF_of_linearBranch_general
#print axioms weakVectorCosetNF_of_linearBranch_general
#check @exists_isotropic_nonorthogonal_of_nonradical
#print axioms exists_isotropic_nonorthogonal_of_nonradical
#check @exists_rational_solution_of_isotropic
#print axioms exists_rational_solution_of_isotropic
#check @weakVectorCosetNF_of_isotropic
#print axioms weakVectorCosetNF_of_isotropic
#check @weakVectorCosetNF_of_isotropicBranch
#print axioms weakVectorCosetNF_of_isotropicBranch
#check @linearGrowth_of_offCentre_radical
#print axioms linearGrowth_of_offCentre_radical
#check @linearGrowth_of_semidefinite_defines
#print axioms linearGrowth_of_semidefinite_defines
#check @outCoord_sq_le
#print axioms outCoord_sq_le
#check @linearGrowth_of_negSemidefinite_defines
#print axioms linearGrowth_of_negSemidefinite_defines
#check @exists_visible_orthogonal
#print axioms exists_visible_orthogonal
#check @not_isSquare_of_quotientAnisotropic
#print axioms not_isSquare_of_quotientAnisotropic
#check @exists_pell_unit_congr
#print axioms exists_pell_unit_congr
#check @pell_branch_contradiction
#print axioms pell_branch_contradiction
#check @exists_graph_injective_pad
#print axioms exists_graph_injective_pad
#check @atomGraphZZ_capacity_eq_one
#print axioms atomGraphZZ_capacity_eq_one
#check @dim_le_of_summit
#print axioms dim_le_of_summit
#check @summit_of_isotropicBranch
#print axioms summit_of_isotropicBranch
#check @summit_of_quotientAnisotropicBranch
#print axioms summit_of_quotientAnisotropicBranch
#dep_check singleQuadratic_sharp_iff forbid "TCER", "TernaryCoset", "DPRM", "Grunewald", "uniformGS", "perEquationGS", "globalGS", "ProjectionDichotomy", "projectionDichotomy", "quadraticProjection", "graphZZ_singleQuadratic_growth", "singleQuadratic_function_quadratic_growth"
#dep_check singleQuadratic_injective_dimension_sharp forbid "TCER", "TernaryCoset", "DPRM", "Grunewald", "uniformGS", "perEquationGS", "globalGS", "ProjectionDichotomy", "projectionDichotomy", "quadraticProjection", "graphZZ_singleQuadratic_growth", "singleQuadratic_function_quadratic_growth"
#dep_check theorem2_sealed forbid "TCER", "TernaryCoset", "DPRM", "Grunewald", "uniformGS", "perEquationGS", "globalGS", "ProjectionDichotomy", "projectionDichotomy", "quadraticProjection", "graphZZ_singleQuadratic_growth", "singleQuadratic_function_quadratic_growth"
#dep_check exists_pell_unit_congr forbid "TCER", "TernaryCoset", "DPRM", "Grunewald", "uniformGS", "perEquationGS", "globalGS", "ProjectionDichotomy", "projectionDichotomy", "quadraticProjection", "graphZZ_singleQuadratic_growth", "singleQuadratic_function_quadratic_growth"
