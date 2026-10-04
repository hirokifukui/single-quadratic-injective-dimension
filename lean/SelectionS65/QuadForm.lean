/-
  S66-04 / S66-08 (scratch, not sealed).  Coefficient extraction for a common-slope function that
  carries a positive quadratic identity.  No TCER anywhere in this file.

  If `f (a + M t) = f a + B t` and `f(a)ᵀ S f(a) = aᵀ H a + λ` for all `a` (S, H symmetric), then with `c = f 0`:
      cᵀ S c = λ,      Bᵀ S c = 0,      Bᵀ S B = M² H.
-/
import ResearchUpgrade.VectorClassification

namespace DiophCompression.ResearchUpgrade.SelectionS66

open Matrix

/-- A quadratic function `k + 2 t·v + t·(G t)` with `G` symmetric that vanishes on all of `ℤⁿ` has zero coefficients. -/
theorem quad_coeffs_eq_zero {n : ℕ} (k : ℤ) (v : Fin n → ℤ) (G : Matrix (Fin n) (Fin n) ℤ)
    (hG : G.IsSymm) (h : ∀ t : Fin n → ℤ, k + 2 * (t ⬝ᵥ v) + t ⬝ᵥ (G *ᵥ t) = 0) :
    k = 0 ∧ v = 0 ∧ G = 0 := by
  have hk : k = 0 := by simpa using h 0
  have hv : ∀ i, v i = 0 ∧ G i i = 0 := by
    intro i
    have h1 := h (Pi.single i 1)
    have h2 := h (-Pi.single i 1)
    simp only [neg_dotProduct, mulVec_neg, dotProduct_neg, neg_neg, single_dotProduct,
      mulVec_single_one, Matrix.col_apply, one_mul, hk] at h1 h2
    constructor <;> linarith
  refine ⟨hk, funext fun i => (hv i).1, ?_⟩
  ext i j
  have h3 := h (Pi.single i 1 + Pi.single j 1)
  simp only [add_dotProduct, mulVec_add, dotProduct_add, single_dotProduct, mulVec_single_one,
    Matrix.col_apply, one_mul, hk, (hv i).1, (hv j).1, (hv i).2, (hv j).2] at h3
  have hs := hG.apply i j
  simp only [Matrix.zero_apply]
  linarith

theorem dot_mulVec_eq_transpose {m n : ℕ} (B : Matrix (Fin m) (Fin n) ℤ) (t : Fin n → ℤ) (w : Fin m → ℤ) :
    (B *ᵥ t) ⬝ᵥ w = t ⬝ᵥ (Bᵀ *ᵥ w) := by
  rw [mulVec_transpose, dotProduct_comm, dotProduct_mulVec, dotProduct_comm]

theorem dot_symm_mulVec {m : ℕ} (S : Matrix (Fin m) (Fin m) ℤ) (hS : S.IsSymm) (x y : Fin m → ℤ) :
    x ⬝ᵥ (S *ᵥ y) = y ⬝ᵥ (S *ᵥ x) := by
  rw [dotProduct_mulVec, ← mulVec_transpose, hS.eq, dotProduct_comm]

/-- **S66-04 / S66-08.**  Coefficient extraction (no TCER). -/
theorem commonSlope_quadForm_coeffs {n m : ℕ} (S : Matrix (Fin m) (Fin m) ℤ) (hS : S.IsSymm)
    (H : Matrix (Fin n) (Fin n) ℤ) (hH : H.IsSymm) (lam : ℤ)
    (f : (Fin n → ℤ) → (Fin m → ℤ)) (M : ℕ) (B : Matrix (Fin m) (Fin n) ℤ)
    (hcs : ∀ a t : Fin n → ℤ, f (a + (M : ℤ) • t) = f a + B *ᵥ t)
    (hq : ∀ a : Fin n → ℤ, f a ⬝ᵥ (S *ᵥ f a) = a ⬝ᵥ (H *ᵥ a) + lam) :
    f 0 ⬝ᵥ (S *ᵥ f 0) = lam ∧ Bᵀ *ᵥ (S *ᵥ f 0) = 0 ∧ Bᵀ * S * B = ((M : ℤ) ^ 2) • H := by
  set c := f 0 with hc
  have hG : (Bᵀ * S * B - ((M : ℤ) ^ 2) • H).IsSymm := by
    unfold Matrix.IsSymm
    rw [transpose_sub, transpose_smul, hH.eq, transpose_mul, transpose_mul, hS.eq, transpose_transpose,
      Matrix.mul_assoc]
  have key : ∀ t : Fin n → ℤ, (c ⬝ᵥ (S *ᵥ c) - lam) + 2 * (t ⬝ᵥ (Bᵀ *ᵥ (S *ᵥ c)))
      + t ⬝ᵥ ((Bᵀ * S * B - ((M : ℤ) ^ 2) • H) *ᵥ t) = 0 := by
    intro t
    have h1 := hq ((M : ℤ) • t)
    have hf : f ((M : ℤ) • t) = c + B *ᵥ t := by simpa [hc] using hcs 0 t
    rw [hf] at h1
    have e1 : (c + B *ᵥ t) ⬝ᵥ (S *ᵥ (c + B *ᵥ t))
        = c ⬝ᵥ (S *ᵥ c) + 2 * (t ⬝ᵥ (Bᵀ *ᵥ (S *ᵥ c))) + t ⬝ᵥ ((Bᵀ * S * B) *ᵥ t) := by
      rw [mulVec_add, add_dotProduct, dotProduct_add, dotProduct_add,
        dot_symm_mulVec S hS c (B *ᵥ t), dot_mulVec_eq_transpose B t (S *ᵥ c),
        dot_mulVec_eq_transpose B t (S *ᵥ (B *ᵥ t)), ← mulVec_mulVec, ← mulVec_mulVec]
      ring
    have e2 : ((M : ℤ) • t) ⬝ᵥ (H *ᵥ ((M : ℤ) • t)) = (M : ℤ) ^ 2 * (t ⬝ᵥ (H *ᵥ t)) := by
      rw [mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
      ring
    have e3 : t ⬝ᵥ ((Bᵀ * S * B - ((M : ℤ) ^ 2) • H) *ᵥ t)
        = t ⬝ᵥ ((Bᵀ * S * B) *ᵥ t) - (M : ℤ) ^ 2 * (t ⬝ᵥ (H *ᵥ t)) := by
      rw [sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
    rw [e1, e2] at h1
    rw [e3]
    linarith
  obtain ⟨hk, hv, hG0⟩ := quad_coeffs_eq_zero _ _ _ hG key
  exact ⟨by linarith, hv, sub_eq_zero.mp hG0⟩

end DiophCompression.ResearchUpgrade.SelectionS66
