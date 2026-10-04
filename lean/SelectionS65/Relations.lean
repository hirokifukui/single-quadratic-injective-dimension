/-
  S66-03 / S66-07 (scratch, not sealed).  The obstructions stated for RELATIONS: each relation below is itself
  SE₂ (one degree-2 equation, no witnesses), total, with finite fibers, and has no SE₂ selection under TCER.

  * `seven_counterexample`: y₀²+…+y₃² = 7a² + 1   (ℤ → ℤ⁴; arithmetic obstruction).
  * `four_to_four_counterexample`: ‖y‖² = ‖a‖² + 1   (ℤ⁴ → ℤ⁴; dimension obstruction).
  * `four_to_five_selection`: the same norm relation with five outputs HAS an SE₂ selection (no TCER).
-/
import SelectionS65.NormDim
import SelectionS65.FourSq

namespace DiophCompression.ResearchUpgrade.SelectionS66

open Matrix MvPolynomial

/-- A set `A ⊆ ℤᵏ` defined by one integer equation of total degree ≤ 2 with integer witnesses
(the predicate inside the sealed `SingleQuadraticDefinableFunctionZZ`, applied to an arbitrary set). -/
def SE2Set {k : ℕ} (A : Set (Fin k → ℤ)) : Prop :=
  ∃ r, ∃ P : MvPolynomial (Fin k ⊕ Fin r) ℤ, P.totalDegree ≤ 2 ∧ DiophCompression.RepresentsZZ P A

/-- The sealed function class is exactly `SE2Set` of the graph. -/
theorem singleQuadratic_iff_SE2Set_graph {n m : ℕ} (f : (Fin n → ℤ) → (Fin m → ℤ)) :
    DiophCompression.SingleQuadraticDefinableFunctionZZ f ↔ SE2Set (DiophCompression.graphVecZZ f) := Iff.rfl

/-- `{(a, y) : ‖y‖² = ‖a‖² + 1}` ⊆ ℤⁿ⁺ᵐ. -/
def normRel (n m : ℕ) : Set (Fin (n + m) → ℤ) :=
  {v | ∑ j : Fin m, (v (Fin.natAdd n j)) ^ 2 = ∑ i : Fin n, (v (Fin.castAdd m i)) ^ 2 + 1}

/-- `{(a, y) : y₀²+…+y₃² = 7a² + 1}` ⊆ ℤ¹⁺⁴. -/
def sevenRel : Set (Fin (1 + 4) → ℤ) :=
  {v | ∑ j : Fin 4, (v (Fin.natAdd 1 j)) ^ 2 = 7 * (v (Fin.castAdd 4 0)) ^ 2 + 1}

theorem normRel_SE2 (n m : ℕ) : SE2Set (normRel n m) := by
  refine ⟨0, ∑ j : Fin m, X (Sum.inl (Fin.natAdd n j)) ^ 2 - ∑ i : Fin n, X (Sum.inl (Fin.castAdd m i)) ^ 2 - 1,
    ?_, ?_⟩
  · exact sc_td_sub (sc_td_sub (sc_td_sum _ fun j => sc_td_sq (sc_td_X _))
      (sc_td_sum _ fun i => sc_td_sq (sc_td_X _))) (le_trans sc_td_one (by norm_num))
  · intro v
    simp only [normRel, Set.mem_setOf_eq, DiophCompression.evalAtZZ, map_sub, map_sum, map_pow, eval_X, map_one,
      Sum.elim_inl]
    constructor
    · intro h; exact ⟨Fin.elim0, by linarith⟩
    · rintro ⟨-, h⟩; linarith

theorem sevenRel_SE2 : SE2Set sevenRel := by
  refine ⟨0, ∑ j : Fin 4, X (Sum.inl (Fin.natAdd 1 j)) ^ 2 - C 7 * X (Sum.inl (Fin.castAdd 4 0)) ^ 2 - 1, ?_, ?_⟩
  · have h7 : (C 7 * X (Sum.inl (Fin.castAdd 4 (0 : Fin 1))) ^ 2 :
        MvPolynomial (Fin (1 + 4) ⊕ Fin 0) ℤ).totalDegree ≤ 2 := by
      refine le_trans (totalDegree_mul _ _) ?_
      have h1 := totalDegree_C (σ := Fin (1 + 4) ⊕ Fin 0) (7 : ℤ)
      have h2 := sc_td_sq (sc_td_X (σ := Fin (1 + 4) ⊕ Fin 0) (Sum.inl (Fin.castAdd 4 (0 : Fin 1))))
      omega
    exact sc_td_sub (sc_td_sub (sc_td_sum _ fun j => sc_td_sq (sc_td_X _)) h7) (le_trans sc_td_one (by norm_num))
  · intro v
    simp only [sevenRel, Set.mem_setOf_eq, DiophCompression.evalAtZZ, map_sub, map_sum, map_pow, map_mul, eval_X,
      eval_C, map_one, Sum.elim_inl]
    constructor
    · intro h; exact ⟨Fin.elim0, by linarith⟩
    · rintro ⟨-, h⟩; linarith

/-- Integer spheres are finite. -/
theorem sphere_finite {m : ℕ} (N : ℤ) : {y : Fin m → ℤ | ∑ j, (y j) ^ 2 = N}.Finite := by
  apply (Set.finite_Icc (fun _ : Fin m => -N) (fun _ => N)).subset
  intro y hy
  simp only [Set.mem_setOf_eq] at hy
  have hj : ∀ j, (y j) ^ 2 ≤ N := fun j =>
    hy ▸ Finset.single_le_sum (fun i _ => sq_nonneg (y i)) (Finset.mem_univ j)
  refine ⟨fun j => ?_, fun j => ?_⟩
  · have := Int.le_self_sq (-y j)
    have := hj j
    nlinarith
  · have := Int.le_self_sq (y j)
    have := hj j
    nlinarith

theorem normRel_fiber_finite (n m : ℕ) (a : Fin n → ℤ) : {y : Fin m → ℤ | pairVec a y ∈ normRel n m}.Finite := by
  simpa [normRel] using sphere_finite (m := m) (∑ i, (a i) ^ 2 + 1)

@[simp] theorem pairVec_zero_one_four (a : Fin 1 → ℤ) (y : Fin 4 → ℤ) : pairVec a y (0 : Fin (1 + 4)) = a 0 :=
  pairVec_left a y 0

theorem sevenRel_fiber_finite (a : Fin 1 → ℤ) : {y : Fin 4 → ℤ | pairVec a y ∈ sevenRel}.Finite := by
  simpa [sevenRel] using sphere_finite (m := 4) (7 * (a 0) ^ 2 + 1)

theorem normRel_select_iff {n m : ℕ} (f : (Fin n → ℤ) → (Fin m → ℤ)) :
    (∀ a, pairVec a (f a) ∈ normRel n m) ↔ NormSelects f := by
  simp [normRel, NormSelects, dotProduct, sq]

theorem sevenRel_select_iff (f : (Fin 1 → ℤ) → (Fin 4 → ℤ)) :
    (∀ a, pairVec a (f a) ∈ sevenRel) ↔ SelectsFourSq 7 f := by
  simp [sevenRel, SelectsFourSq]

theorem normRel_four_total (a : Fin 4 → ℤ) : ∃ y : Fin 4 → ℤ, pairVec a y ∈ normRel 4 4 := by
  obtain ⟨p, q, r, s, h⟩ := Nat.sum_four_squares (∑ i, (a i).natAbs ^ 2 + 1)
  refine ⟨![p, q, r, s], ?_⟩
  have h' := congrArg (Nat.cast : ℕ → ℤ) h
  push_cast at h'
  simp only [sq_abs] at h'
  simp only [normRel, Set.mem_setOf_eq, pairVec_left, pairVec_right, Fin.sum_univ_four] at h' ⊢
  simpa using h'

theorem sevenRel_total (a : Fin 1 → ℤ) : ∃ y : Fin 4 → ℤ, pairVec a y ∈ sevenRel := by
  obtain ⟨p, q, r, s, h⟩ := Nat.sum_four_squares (7 * (a 0).natAbs ^ 2 + 1)
  refine ⟨![p, q, r, s], ?_⟩
  have h' := congrArg (Nat.cast : ℕ → ℤ) h
  push_cast at h'
  simp only [sq_abs] at h'
  simp only [sevenRel, Set.mem_setOf_eq, pairVec_left, pairVec_right, Fin.sum_univ_four]
  simpa using h'

/-- **S66-03.**  TCER ⇒ the SE₂ relation `y₀²+…+y₃² = 7a² + 1` is total with finite fibers and has no SE₂ selection. -/
theorem seven_counterexample (hT : TCERBridge.TernaryCosetEventualRepresentation) :
    SE2Set sevenRel ∧ (∀ a, ∃ y, pairVec a y ∈ sevenRel) ∧ (∀ a, {y | pairVec a y ∈ sevenRel}.Finite) ∧
      ¬ ∃ f : (Fin 1 → ℤ) → (Fin 4 → ℤ),
        DiophCompression.SingleQuadraticDefinableFunctionZZ f ∧ ∀ a, pairVec a (f a) ∈ sevenRel :=
  ⟨sevenRel_SE2, sevenRel_total, sevenRel_fiber_finite, fun ⟨f, hf, hs⟩ =>
    no_selection_seven_of_TCER hT ⟨f, hf, (sevenRel_select_iff f).mp hs⟩⟩

/-- **S66-07.**  TCER ⇒ the SE₂ relation `‖y‖² = ‖a‖² + 1` on ℤ⁴ × ℤ⁴ is total with finite fibers and has no SE₂
selection ℤ⁴ → ℤ⁴. -/
theorem four_to_four_counterexample (hT : TCERBridge.TernaryCosetEventualRepresentation) :
    SE2Set (normRel 4 4) ∧ (∀ a, ∃ y, pairVec a y ∈ normRel 4 4) ∧
      (∀ a, {y | pairVec a y ∈ normRel 4 4}.Finite) ∧
      ¬ ∃ f : (Fin 4 → ℤ) → (Fin 4 → ℤ),
        DiophCompression.SingleQuadraticDefinableFunctionZZ f ∧ ∀ a, pairVec a (f a) ∈ normRel 4 4 :=
  ⟨normRel_SE2 4 4, normRel_four_total, normRel_fiber_finite 4 4, fun ⟨f, hf, hs⟩ =>
    absurd (norm_selection_dim_of_TCER hT (by norm_num) f hf ((normRel_select_iff f).mp hs)) (by norm_num)⟩

/-- **S66-07, contrast** (no TCER).  With five outputs the norm relation has an SE₂ selection, `a ↦ (1, a)`. -/
theorem four_to_five_selection :
    ∃ f : (Fin 4 → ℤ) → (Fin 5 → ℤ),
      DiophCompression.SingleQuadraticDefinableFunctionZZ f ∧ ∀ a, pairVec a (f a) ∈ normRel 4 5 := by
  obtain ⟨f, hf, hs⟩ := norm_selection_of_le (n := 4) (m := 5) le_rfl
  exact ⟨f, hf, (normRel_select_iff f).mpr hs⟩

end DiophCompression.ResearchUpgrade.SelectionS66
