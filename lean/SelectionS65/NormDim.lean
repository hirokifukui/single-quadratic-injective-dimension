/-
  S66-05 / S66-06 (scratch, not sealed).  Dimension barrier for norm-increasing selection.

  Relation  R_{n,m}(a, y) :  ‖y‖² = ‖a‖² + 1   (a ∈ ℤⁿ, y ∈ ℤᵐ).
  * `norm_selection_dim_of_commonSlope` (no TCER): a common-slope selection forces n + 1 ≤ m.
  * `norm_selection_of_le` (no TCER): if n + 1 ≤ m, a ↦ (1, a, 0) is an SE₂ selection.
  * `norm_selection_iff_of_TCER`: TCER, m ≥ 2 ⇒ (∃ SE₂ selection ↔ n + 1 ≤ m).
-/
import SelectionS65.QuadForm

namespace DiophCompression.ResearchUpgrade.SelectionS66

open Matrix

/-- `f` selects a solution of `‖y‖² = ‖a‖² + 1` for every `a`. -/
def NormSelects {n m : ℕ} (f : (Fin n → ℤ) → (Fin m → ℤ)) : Prop :=
  ∀ a : Fin n → ℤ, f a ⬝ᵥ f a = a ⬝ᵥ a + 1

/-- Linear algebra: a unit vector `c` orthogonal to the columns of `B` with `BᵀB = M² I`, `M ≠ 0`, forces `n + 1 ≤ m`.
(The `n + 1` vectors `c, B₁, …, Bₙ` have an invertible Gram matrix over ℚ.) -/
theorem dim_of_orthogonal_frame {n m : ℕ} (c : Fin m → ℤ) (B : Matrix (Fin m) (Fin n) ℤ) (M : ℤ)
    (hM : M ≠ 0) (hc : c ⬝ᵥ c = 1) (hBc : Bᵀ *ᵥ c = 0) (hBB : Bᵀ * B = (M ^ 2) • (1 : Matrix (Fin n) (Fin n) ℤ)) :
    n + 1 ≤ m := by
  classical
  let A : Matrix (Fin m) (Fin (n + 1)) ℚ :=
    Matrix.of fun i j => (Fin.cons (c i : ℚ) (fun k => (B i k : ℚ)) : Fin (n + 1) → ℚ) j
  have hc' : ∑ i, (c i : ℚ) * (c i : ℚ) = 1 := by
    have := congrArg (Int.cast : ℤ → ℚ) hc
    simpa [dotProduct] using this
  have hBc' : ∀ k, ∑ i, (B i k : ℚ) * (c i : ℚ) = 0 := by
    intro k
    have := congrArg (Int.cast : ℤ → ℚ) (congrFun hBc k)
    simpa [mulVec, dotProduct] using this
  have hBB' : ∀ j k, ∑ i, (B i j : ℚ) * (B i k : ℚ) = if j = k then (M : ℚ) ^ 2 else 0 := by
    intro j k
    have := congrArg (Int.cast : ℤ → ℚ) (congrFun (congrFun hBB j) k)
    by_cases hjk : j = k <;> simpa [Matrix.mul_apply, Matrix.one_apply, hjk] using this
  have hG : Aᵀ * A = diagonal (Fin.cons (1 : ℚ) (fun _ => (M : ℚ) ^ 2) : Fin (n + 1) → ℚ) := by
    ext j k
    rw [Matrix.mul_apply]
    refine Fin.cases ?_ (fun j' => ?_) j <;> refine Fin.cases ?_ (fun k' => ?_) k
    · simpa [A] using hc'
    · simpa [A, mul_comm, diagonal_apply, (Fin.succ_ne_zero k').symm] using hBc' k'
    · simpa [A] using hBc' j'
    · simpa [A, diagonal_apply, Fin.succ_inj] using hBB' j' k'
  have hunit : IsUnit (Aᵀ * A) := by
    rw [hG, isUnit_diagonal, Pi.isUnit_iff]
    intro i
    refine Fin.cases ?_ (fun i' => ?_) i
    · simp
    · simpa [isUnit_iff_ne_zero] using hM
  have h1 : (Aᵀ * A).rank = n + 1 := by simpa using rank_of_isUnit _ hunit
  have h2 : (Aᵀ * A).rank ≤ A.rank := rank_mul_le_right _ _
  have h3 : A.rank ≤ m := rank_le_height A
  omega

/-- **S66-05** (no TCER).  A common-slope selection of `‖y‖² = ‖a‖² + 1` needs `n + 1 ≤ m`. -/
theorem norm_selection_dim_of_commonSlope {n m : ℕ} (f : (Fin n → ℤ) → (Fin m → ℤ))
    (hcs : CommonSlopeIntNF f) (hs : NormSelects f) : n + 1 ≤ m := by
  obtain ⟨M, B, hM, h⟩ := hcs
  obtain ⟨h1, h2, h3⟩ := commonSlope_quadForm_coeffs (1 : Matrix (Fin m) (Fin m) ℤ) isSymm_one
    (1 : Matrix (Fin n) (Fin n) ℤ) isSymm_one 1 f M B h (by intro a; simpa using hs a)
  simp only [one_mulVec, Matrix.mul_one] at h1 h2 h3
  exact dim_of_orthogonal_frame (f 0) B (M : ℤ) (by exact_mod_cast (by omega : M ≠ 0)) h1 h2 h3

/-- TCER, `m ≥ 2` ⇒ an SE₂ selection of `‖y‖² = ‖a‖² + 1` needs `n + 1 ≤ m`. -/
theorem norm_selection_dim_of_TCER (hT : TCERBridge.TernaryCosetEventualRepresentation) {n m : ℕ}
    (hm : 2 ≤ m) (f : (Fin n → ℤ) → (Fin m → ℤ))
    (hf : DiophCompression.SingleQuadraticDefinableFunctionZZ f) (hs : NormSelects f) : n + 1 ≤ m :=
  norm_selection_dim_of_commonSlope f ((singleQuadratic_iff_commonSlope_of_TCER hT n m f hm).mp hf) hs

/-- The selection `a ↦ (1, a, 0, …, 0)`. -/
def stdSel (n k : ℕ) : (Fin n → ℤ) → (Fin (n + k + 1) → ℤ) :=
  fun a => Fin.cons (1 : ℤ) (Fin.append a (0 : Fin k → ℤ))

/-- Its slope matrix. -/
def stdSlope (n k : ℕ) : Matrix (Fin (n + k + 1)) (Fin n) ℤ :=
  Matrix.of fun j i => (Fin.cons (0 : ℤ) (Fin.append (Pi.single i (1 : ℤ)) (0 : Fin k → ℤ)) : Fin (n + k + 1) → ℤ) j

theorem stdSel_commonSlope (n k : ℕ) : CommonSlopeIntNF (stdSel n k) := by
  refine ⟨1, stdSlope n k, le_rfl, ?_⟩
  intro a t
  funext j
  refine Fin.cases ?_ (fun j' => ?_) j
  · simp [stdSel, stdSlope, Matrix.mulVec, dotProduct]
  · refine Fin.addCases (fun i0 => ?_) (fun l => ?_) j'
    · simp [stdSel, stdSlope, Matrix.mulVec, dotProduct, Pi.single_apply]
    · simp [stdSel, stdSlope, Matrix.mulVec, dotProduct]

theorem stdSel_norm (n k : ℕ) : NormSelects (stdSel n k) := by
  intro a
  simp only [stdSel, dotProduct, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, Fin.sum_univ_add,
    Fin.append_left, Fin.append_right, Pi.zero_apply, mul_zero, Finset.sum_const_zero, add_zero]
  ring

/-- **S66-06** (no TCER).  If `n + 1 ≤ m`, an SE₂ selection exists. -/
theorem norm_selection_of_le {n m : ℕ} (h : n + 1 ≤ m) :
    ∃ f : (Fin n → ℤ) → (Fin m → ℤ), DiophCompression.SingleQuadraticDefinableFunctionZZ f ∧ NormSelects f := by
  obtain ⟨k, rfl⟩ : ∃ k, m = n + k + 1 := ⟨m - n - 1, by omega⟩
  exact ⟨stdSel n k, singleQuadratic_of_commonSlope (stdSel_commonSlope n k), stdSel_norm n k⟩

/-- **S66-06.**  TCER, `m ≥ 2` ⇒ (an SE₂ selection of `‖y‖² = ‖a‖² + 1` exists ↔ `n + 1 ≤ m`). -/
theorem norm_selection_iff_of_TCER (hT : TCERBridge.TernaryCosetEventualRepresentation) (n m : ℕ)
    (hm : 2 ≤ m) :
    (∃ f : (Fin n → ℤ) → (Fin m → ℤ), DiophCompression.SingleQuadraticDefinableFunctionZZ f ∧ NormSelects f)
      ↔ n + 1 ≤ m :=
  ⟨fun ⟨f, hf, hs⟩ => norm_selection_dim_of_TCER hT hm f hf hs, norm_selection_of_le⟩

end DiophCompression.ResearchUpgrade.SelectionS66
