/-
  S66-02 / S66-10 (scratch, not sealed).  The four-square selection obstruction, rebuilt on the general extraction.

  * `three_sq_of_commonSlope_selection` (NO TCER): a common-slope selection of Σ y_i² = d a² + 1 forces d M² to be a
    sum of three squares for some M ≥ 1.  It is the case S = I₄, H = (d), λ = 1 of `commonSlope_quadForm_coeffs`.
  * `three_sq_of_selection_of_TCER`: TCER enters only here (D1), then the descent removes M.
  * `selection_iff_sum_three_sq_of_TCER` (S66-10): TCER ⇒ (SE₂ selection exists ↔ d is a sum of three squares).
    No Legendre hypothesis.
  * `selection_iff_not_excluded_of_TCER_of_legendre`: the congruence form; still needs Legendre's hard direction.
-/
import SelectionS65.QuadForm
import SelectionS65.Arith

namespace DiophCompression.ResearchUpgrade.SelectionS66

open Matrix

/-- `f` selects a solution of `y₀²+y₁²+y₂²+y₃² = d a² + 1` for every `a`. -/
def SelectsFourSq (d : ℕ) (f : (Fin 1 → ℤ) → (Fin 4 → ℤ)) : Prop :=
  ∀ a : Fin 1 → ℤ, ∑ i, (f a i) ^ 2 = (d : ℤ) * (a 0) ^ 2 + 1

/-- **S66-02** (no TCER).  Common slope + selection ⇒ `d M²` is a sum of three squares, `M ≥ 1`. -/
theorem three_sq_of_commonSlope_selection (d : ℕ) (f : (Fin 1 → ℤ) → (Fin 4 → ℤ))
    (hcs : CommonSlopeIntNF f) (hs : SelectsFourSq d f) :
    ∃ M : ℕ, 0 < M ∧ IsSumThreeSq ((d : ℤ) * (M : ℤ) ^ 2) := by
  obtain ⟨M, B, hM, h⟩ := hcs
  have hH : ((d : ℤ) • (1 : Matrix (Fin 1) (Fin 1) ℤ)).IsSymm := by
    simp [Matrix.IsSymm]
  have hq : ∀ a : Fin 1 → ℤ, f a ⬝ᵥ ((1 : Matrix (Fin 4) (Fin 4) ℤ) *ᵥ f a)
      = a ⬝ᵥ (((d : ℤ) • (1 : Matrix (Fin 1) (Fin 1) ℤ)) *ᵥ a) + 1 := by
    intro a
    have := hs a
    simp only [one_mulVec, Matrix.smul_mulVec, dotProduct, Fin.sum_univ_four, Fin.sum_univ_one,
      Pi.smul_apply, smul_eq_mul] at this ⊢
    linear_combination this
  obtain ⟨h1, h2, h3⟩ := commonSlope_quadForm_coeffs (1 : Matrix (Fin 4) (Fin 4) ℤ) isSymm_one
    ((d : ℤ) • (1 : Matrix (Fin 1) (Fin 1) ℤ)) hH 1 f M B h hq
  simp only [one_mulVec, Matrix.mul_one] at h1 h2 h3
  have hcc : (f 0 0) ^ 2 + (f 0 1) ^ 2 + (f 0 2) ^ 2 + (f 0 3) ^ 2 = 1 := by
    simp only [dotProduct, Fin.sum_univ_four] at h1
    linear_combination h1
  have hbc : B 0 0 * f 0 0 + B 1 0 * f 0 1 + B 2 0 * f 0 2 + B 3 0 * f 0 3 = 0 := by
    have e := congrFun h2 0
    simp only [mulVec, dotProduct, Fin.sum_univ_four, transpose_apply, Pi.zero_apply] at e
    linear_combination e
  have hbb : (B 0 0) ^ 2 + (B 1 0) ^ 2 + (B 2 0) ^ 2 + (B 3 0) ^ 2 = (d : ℤ) * (M : ℤ) ^ 2 := by
    have e := congrFun (congrFun h3 0) 0
    simp only [Matrix.mul_apply, Fin.sum_univ_four, transpose_apply, Matrix.smul_apply, Matrix.one_apply_eq,
      smul_eq_mul] at e
    linear_combination e
  set c0 := f 0 0
  set c1 := f 0 1
  set c2 := f 0 2
  set c3 := f 0 3
  set b0 := B 0 0
  set b1 := B 1 0
  set b2 := B 2 0
  set b3 := B 3 0
  -- Euler's four-square identity: the vector part of b·c̄ (Hamilton product order: b c̄).
  refine ⟨M, by omega, c0 * b1 - c1 * b0 + c2 * b3 - c3 * b2, c0 * b2 - c2 * b0 + c3 * b1 - c1 * b3,
    c0 * b3 - c3 * b0 + c1 * b2 - c2 * b1, ?_⟩
  linear_combination (b0 ^ 2 + b1 ^ 2 + b2 ^ 2 + b3 ^ 2) * hcc + hbb
    - (b0 * c0 + b1 * c1 + b2 * c2 + b3 * c3) * hbc

/-- TCER ⇒ an SE₂ selection forces `d` itself to be a sum of three squares (D1, then the descent). -/
theorem three_sq_of_selection_of_TCER (hT : TCERBridge.TernaryCosetEventualRepresentation) (d : ℕ)
    (f : (Fin 1 → ℤ) → (Fin 4 → ℤ)) (hf : DiophCompression.SingleQuadraticDefinableFunctionZZ f)
    (hs : SelectsFourSq d f) : IsSumThreeSq (d : ℤ) := by
  obtain ⟨M, hM, h⟩ := three_sq_of_commonSlope_selection d f
    ((singleQuadratic_iff_commonSlope_of_TCER hT 1 4 f (by norm_num)).mp hf) hs
  exact three_sq_of_three_sq_mul_sq (d : ℤ) M hM h

/-- `a ↦ (1, ua, va, wa)`. -/
def affSel (u v w : ℤ) : (Fin 1 → ℤ) → (Fin 4 → ℤ) := fun a => ![1, u * a 0, v * a 0, w * a 0]

theorem affSel_commonSlope (u v w : ℤ) : CommonSlopeIntNF (affSel u v w) := by
  refine ⟨1, fun i _ => ![0, u, v, w] i, le_rfl, ?_⟩
  intro a t
  funext i
  fin_cases i <;> simp [affSel, Matrix.mulVec, dotProduct] <;> ring

/-- Sufficiency (no TCER): `d = u²+v²+w²` ⇒ `a ↦ (1, ua, va, wa)` is an SE₂ selection. -/
theorem selection_of_three_sq (d : ℕ) (u v w : ℤ) (h : u ^ 2 + v ^ 2 + w ^ 2 = (d : ℤ)) :
    ∃ f : (Fin 1 → ℤ) → (Fin 4 → ℤ),
      DiophCompression.SingleQuadraticDefinableFunctionZZ f ∧ SelectsFourSq d f := by
  refine ⟨affSel u v w, singleQuadratic_of_commonSlope (affSel_commonSlope u v w), ?_⟩
  intro a
  simp only [affSel, Fin.sum_univ_four]
  simp
  linear_combination (a 0) ^ 2 * h

/-- **S66-10.**  TCER ⇒ (an SE₂ selection exists ↔ `d` is a sum of three integer squares).  No Legendre hypothesis. -/
theorem selection_iff_sum_three_sq_of_TCER (hT : TCERBridge.TernaryCosetEventualRepresentation) (d : ℕ) :
    (∃ f : (Fin 1 → ℤ) → (Fin 4 → ℤ),
      DiophCompression.SingleQuadraticDefinableFunctionZZ f ∧ SelectsFourSq d f) ↔ IsSumThreeSq (d : ℤ) := by
  constructor
  · rintro ⟨f, hf, hs⟩
    exact three_sq_of_selection_of_TCER hT d f hf hs
  · rintro ⟨u, v, w, h⟩
    exact selection_of_three_sq d u v w h

/-- TCER ⇒ no SE₂ selection when `d = 4^r(8s+7)` (elementary half of Legendre only). -/
theorem no_selection_of_excluded_of_TCER (hT : TCERBridge.TernaryCosetEventualRepresentation) (d : ℕ)
    (hd : Legendre3Excluded d) :
    ¬ ∃ f : (Fin 1 → ℤ) → (Fin 4 → ℤ),
      DiophCompression.SingleQuadraticDefinableFunctionZZ f ∧ SelectsFourSq d f := fun hex =>
  not_isSumThreeSq_of_excluded hd ((selection_iff_sum_three_sq_of_TCER hT d).mp hex)

/-- (a) of s65, re-derived: TCER ⇒ no SE₂ selection for `7a² + 1`. -/
theorem no_selection_seven_of_TCER (hT : TCERBridge.TernaryCosetEventualRepresentation) :
    ¬ ∃ f : (Fin 1 → ℤ) → (Fin 4 → ℤ),
      DiophCompression.SingleQuadraticDefinableFunctionZZ f ∧ SelectsFourSq 7 f :=
  no_selection_of_excluded_of_TCER hT 7 ⟨0, 0, by norm_num⟩

/-- Legendre's three-square theorem, hard direction (NOT in mathlib d46bd45); a named hypothesis only. -/
def LegendreThreeSquareHyp : Prop :=
  ∀ n : ℕ, ¬ Legendre3Excluded n → IsSumThreeSq (n : ℤ)

/-- Congruence form; still needs Legendre's hard direction as a hypothesis. -/
theorem selection_iff_not_excluded_of_TCER_of_legendre (hT : TCERBridge.TernaryCosetEventualRepresentation)
    (hL : LegendreThreeSquareHyp) (d : ℕ) :
    (∃ f : (Fin 1 → ℤ) → (Fin 4 → ℤ),
      DiophCompression.SingleQuadraticDefinableFunctionZZ f ∧ SelectsFourSq d f) ↔ ¬ Legendre3Excluded d := by
  rw [selection_iff_sum_three_sq_of_TCER hT d]
  exact ⟨fun h hd => not_isSumThreeSq_of_excluded hd h, fun h => hL d h⟩

end DiophCompression.ResearchUpgrade.SelectionS66
