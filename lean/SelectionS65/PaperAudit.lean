/- Paper audit module: axiom reports and forbidden-name dependency checks for Corollaries 3 and 4.
   Derived from the scratch module Audit67.lean by removing the import of Residual44 and its three
   axiom reports (the selection track is not part of the paper). -/
import SelectionS65.DepCheck
import SelectionS65.Conjunction

open DiophCompression.ResearchUpgrade.SelectionS67

#print axioms polyFn_SE2_iff
#print axioms polyFn_SE2_of_degree_le
#print axioms totalDegree_le_two_of_linearGrowth
#print axioms totalDegree_le_two_of_weakNF
#print axioms not_closed_under_composition
#print axioms not_closed_under_conjunction

#dep_check polyFn_SE2_iff forbid "TCER", "TernaryCoset", "DPRM", "Grunewald", "uniformGS", "perEquationGS", "globalGS", "UniformCodeGS", "uniformCodeGS", "ProjectionDichotomy", "projectionDichotomy", "quadraticProjection", "graphZZ_singleQuadratic_growth", "singleQuadratic_function_quadratic_growth", "polynomial_graph_singleQuadratic_iff", "polynomial_graph_not_singleQuadratic_of_degree_ge_three"
#dep_check not_closed_under_composition forbid "TCER", "TernaryCoset", "DPRM", "Grunewald", "uniformGS", "perEquationGS", "globalGS", "ProjectionDichotomy", "projectionDichotomy", "quadraticProjection", "graphZZ_singleQuadratic_growth", "singleQuadratic_function_quadratic_growth", "fourth_power_graph_not_singleQuadratic", "singleQuadratic_functions_not_closed_under_composition"
#dep_check not_closed_under_conjunction forbid "TCER", "TernaryCoset", "DPRM", "Grunewald", "uniformGS", "perEquationGS", "globalGS", "ProjectionDichotomy", "projectionDichotomy", "quadraticProjection", "graphZZ_singleQuadratic_growth", "singleQuadratic_function_quadratic_growth"
-- Theorem 2 itself and Theorem 1 as sealed (for the correspondence table)
#dep_check DiophCompression.ResearchUpgrade.QuadraticGraphData.summit_of_defines forbid "TCER", "TernaryCoset", "DPRM", "Grunewald", "uniformGS", "perEquationGS", "globalGS", "ProjectionDichotomy", "projectionDichotomy", "quadraticProjection", "graphZZ_singleQuadratic_growth", "singleQuadratic_function_quadratic_growth"
