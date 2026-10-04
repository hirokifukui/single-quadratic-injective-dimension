/-
  S67-06 / S67-07 (scratch, not sealed).  Polynomial graphs from the structural dichotomy ONLY.

  * `polyFn_SE2_iff`: for p ∈ ℤ[x₁,…,xₙ], the graph of a ↦ p(a) is SE₂ iff deg p ≤ 2.
    The forward direction uses only `graphData_of_singleQuadraticDefinable` and `summit_of_defines`
    (Theorem 2: linear growth ∨ weak coset normal form). It does not use the sealed quadratic-growth
    bound `graphZZ_singleQuadratic_growth`, the projection theorem, TCER, Grunewald–Segal or DPRM.
      - linear growth: along a line where the top homogeneous part is non-zero, degree ≥ 3 contradicts
        the linear bound (`abs_eval_nat_ge_of_natDegree_ge_three`).
      - coset form: p(ρ + Mt) agrees with a quadratic on ℤⁿ, hence equals it as a polynomial over ℚ
        (`MvPolynomial.funext_set`); the substitution x ↦ ρ + Mx is invertible over ℚ, and degree-one
        substitutions do not raise the degree.
  * `square_SE2`, `fourth_not_SE2`, `not_closed_under_composition`: x² is SE₂, x⁴ = x² ∘ x² is not.
  * `not_closed_under_conjunction`: {y = x²} and {z = y²} are SE₂ relations on ℤ³ (one equation, no
    unknowns); their conjunction is not SE₂.  Free variables x, y, z; if the conjunction were SE₂,
    making y an unknown would define z = x⁴.
-/
import ResearchUpgrade
import SelectionS65.Relations

namespace DiophCompression.ResearchUpgrade.SelectionS67

open MvPolynomial DiophCompression.ResearchUpgrade.SelectionS66

/-- The function `a ↦ p(a)`, one output. -/
noncomputable def polyFn {n : ℕ} (p : MvPolynomial (Fin n) ℤ) : (Fin n → ℤ) → (Fin 1 → ℤ) :=
  fun a _ => eval a p

/-! ### Sufficiency -/

theorem polyFn_SE2_of_degree_le {n : ℕ} (p : MvPolynomial (Fin n) ℤ) (hp : p.totalDegree ≤ 2) :
    DiophCompression.SingleQuadraticDefinableFunctionZZ (polyFn p) := by
  refine singleQuadratic_of_poly (W := Fin 0)
    (X (Sum.inl (Fin.natAdd n 0)) - rename (fun i => Sum.inl (Fin.castAdd 1 i)) p) ?_ (polyFn p) ?_
  · refine (totalDegree_sub _ _).trans (max_le ((totalDegree_X_le_one _).trans (by norm_num)) ?_)
    exact (totalDegree_rename_le _ _).trans hp
  · intro a b
    have hcomp : (Sum.elim (pairVec a b) (fun i : Fin 0 => i.elim0) ∘
        (fun i : Fin n => (Sum.inl (Fin.castAdd 1 i) : Fin (n + 1) ⊕ Fin 0))) = a := by
      funext i; simp [pairVec_left]
    constructor
    · intro h
      refine ⟨fun i => i.elim0, ?_⟩
      rw [map_sub, eval_X, eval_rename, hcomp]
      simp [pairVec_right, h, polyFn]
    · rintro ⟨w, hw⟩
      have hw0 : w = fun i => i.elim0 := funext fun i => i.elim0
      subst hw0
      rw [map_sub, eval_X, eval_rename, hcomp] at hw
      funext j
      have hj : j = 0 := Subsingleton.elim j 0
      subst hj
      simp [pairVec_right] at hw
      simp [polyFn]
      linarith

/-! ### Linear-growth branch -/

theorem totalDegree_le_two_of_linearGrowth {n : ℕ} (p : MvPolynomial (Fin n) ℤ)
    (h : LinearGrowth (polyFn p)) : p.totalDegree ≤ 2 := by
  by_contra hlt
  have hd : 3 ≤ p.totalDegree := by omega
  obtain ⟨C, hC⟩ := h
  have hp : p ≠ 0 := by rintro rfl; simp at hd
  obtain ⟨v, hv⟩ := exists_line_natDegree_eq_totalDegree p hp
  obtain ⟨S, hS⟩ := abs_eval_nat_ge_of_natDegree_ge_three (linePoly p v) (by rw [hv]; exact hd)
  set V : ℕ := 1 + ∑ i, (v i).natAbs with hV
  have hVi : ∀ i, (v i).natAbs ≤ V := by
    intro i
    have : (v i).natAbs ≤ ∑ j, (v j).natAbs :=
      Finset.single_le_sum (f := fun j => (v j).natAbs) (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
    omega
  set N : ℕ := S + C * (1 + V) + 1 with hN
  have hN1 : 1 ≤ N := by omega
  have hsup : supNorm (fun i => (N : ℤ) * v i) ≤ N * V := by
    unfold supNorm
    apply Finset.sup_le
    intro i _
    rw [Int.natAbs_mul, Int.natAbs_natCast]
    exact Nat.mul_le_mul_left N (hVi i)
  have hup := hC (fun i => (N : ℤ) * v i)
  have hcoord := abs_le_supNorm (polyFn p (fun i => (N : ℤ) * v i)) 0
  have hlow := hS N hN1
  rw [linePoly_eval] at hlow
  have hval : |polyFn p (fun i => (N : ℤ) * v i) 0| = |eval (fun i => (N : ℤ) * v i) p| := rfl
  have h1 : ((N : ℤ) - S) * (N : ℤ) ^ 2 ≤ (C : ℤ) * (1 + (N : ℤ) * V) := by
    have e1 : (supNorm (polyFn p (fun i => (N : ℤ) * v i)) : ℤ) ≤ (C : ℤ) * (1 + (supNorm (fun i => (N : ℤ) * v i) : ℤ)) := by
      exact_mod_cast hup
    have e2 : (supNorm (fun i => (N : ℤ) * v i) : ℤ) ≤ (N : ℤ) * V := by exact_mod_cast hsup
    have hC0 : (0 : ℤ) ≤ C := by positivity
    calc ((N : ℤ) - S) * (N : ℤ) ^ 2 ≤ |eval (fun i => (N : ℤ) * v i) p| := hlow
      _ = |polyFn p (fun i => (N : ℤ) * v i) 0| := hval.symm
      _ ≤ (supNorm (polyFn p (fun i => (N : ℤ) * v i)) : ℤ) := hcoord
      _ ≤ (C : ℤ) * (1 + (supNorm (fun i => (N : ℤ) * v i) : ℤ)) := e1
      _ ≤ (C : ℤ) * (1 + (N : ℤ) * V) := by nlinarith
  have hNeq : (N : ℤ) = S + C * (1 + V) + 1 := by rw [hN]; push_cast; ring
  have hV1 : 1 ≤ V := by omega
  have hV0 : (1 : ℤ) ≤ V := by exact_mod_cast hV1
  have hNpos : (1 : ℤ) ≤ N := by exact_mod_cast hN1
  have hC0 : (0 : ℤ) ≤ C := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hNpos hC0]

/-! ### Coset branch, over ℚ -/

theorem eval_aeval_Q {n : ℕ} (P : MvPolynomial (Fin n) ℚ) (φ : Fin n → MvPolynomial (Fin n) ℚ)
    (x : Fin n → ℚ) : eval x (aeval φ P) = eval (fun i => eval x (φ i)) P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp only [aeval_C, algebraMap_eq, eval_C]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i ih => simp only [map_mul, aeval_X, eval_X, ih]

theorem aeval_aeval_Q {n : ℕ} (P : MvPolynomial (Fin n) ℚ) (φ ψ : Fin n → MvPolynomial (Fin n) ℚ) :
    aeval ψ (aeval φ P) = aeval (fun i => aeval ψ (φ i)) P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp only [aeval_C, algebraMap_eq]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i ih => simp only [map_mul, aeval_X, ih]

theorem aeval_X_self_Q {n : ℕ} (P : MvPolynomial (Fin n) ℚ) : aeval (fun i => (X i : MvPolynomial (Fin n) ℚ)) P = P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp only [aeval_C, algebraMap_eq]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i ih => simp only [map_mul, aeval_X, ih]

theorem totalDegree_aeval_le_of_le_one_Q {σ τ : Type} (g : σ → MvPolynomial τ ℚ)
    (p : MvPolynomial σ ℚ) (hg : ∀ v, (g v).totalDegree ≤ 1) :
    (aeval g p).totalDegree ≤ p.totalDegree := by
  rw [aeval_def, eval₂_eq]
  apply totalDegree_finsetSum_le
  intro β hβ
  rw [algebraMap_eq]
  calc (C (coeff β p) * ∏ v ∈ β.support, (g v) ^ (β v)).totalDegree
      ≤ (C (coeff β p)).totalDegree + (∏ v ∈ β.support, (g v) ^ (β v)).totalDegree :=
        totalDegree_mul _ _
    _ = (∏ v ∈ β.support, (g v) ^ (β v)).totalDegree := by rw [totalDegree_C]; ring
    _ ≤ ∑ v ∈ β.support, ((g v) ^ (β v)).totalDegree := totalDegree_finsetProd _ _
    _ ≤ ∑ v ∈ β.support, (β v) * 1 := by
        apply Finset.sum_le_sum
        intro v _
        calc ((g v) ^ (β v)).totalDegree ≤ (β v) * (g v).totalDegree := totalDegree_pow _ _
          _ ≤ (β v) * 1 := by apply Nat.mul_le_mul_left; exact hg v
    _ = ∑ v ∈ β.support, β v := by simp
    _ ≤ p.totalDegree := le_totalDegree hβ

theorem totalDegree_map_cast {n : ℕ} (p : MvPolynomial (Fin n) ℤ) :
    (map (Int.castRingHom ℚ) p).totalDegree = p.totalDegree := by
  unfold totalDegree
  rw [support_map_of_injective _ Int.cast_injective]

theorem eval_map_castQ {n : ℕ} (p : MvPolynomial (Fin n) ℤ) (t : Fin n → ℤ) :
    eval (castQ t) (map (Int.castRingHom ℚ) p) = ((eval t p : ℤ) : ℚ) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i ih => simp [ih, castQ]

/-- The quadratic polynomial of a `QuadForm`. -/
noncomputable def quadPoly {n : ℕ} (q : QuadForm n) : MvPolynomial (Fin n) ℚ :=
  C q.c + ∑ i, C (q.l i) * X i + ∑ i, ∑ j, C (q.Q i j) * (X i * X j)

theorem eval_quadPoly {n : ℕ} (q : QuadForm n) (x : Fin n → ℚ) : eval x (quadPoly q) = q.eval x := by
  have h1 : ∑ i, ∑ j, q.Q i j * (x i * x j) = ∑ i, x i * ∑ j, q.Q i j * x j := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  simp only [quadPoly, QuadForm.eval, map_add, map_sum, map_mul, eval_C, eval_X, dotProduct,
    Matrix.mulVec]
  rw [h1]

theorem totalDegree_quadPoly_le {n : ℕ} (q : QuadForm n) : (quadPoly q).totalDegree ≤ 2 := by
  unfold quadPoly
  refine (totalDegree_add _ _).trans (max_le ((totalDegree_add _ _).trans (max_le ?_ ?_)) ?_)
  · rw [totalDegree_C]; norm_num
  · refine totalDegree_finsetSum_le fun i _ => (totalDegree_mul _ _).trans ?_
    rw [totalDegree_C, MvPolynomial.totalDegree_X]
    norm_num
  · refine totalDegree_finsetSum_le fun i _ => totalDegree_finsetSum_le fun j _ => (totalDegree_mul _ _).trans ?_
    rw [totalDegree_C, zero_add]
    exact (totalDegree_mul _ _).trans (by rw [MvPolynomial.totalDegree_X, MvPolynomial.totalDegree_X])

theorem totalDegree_le_two_of_weakNF {n : ℕ} (p : MvPolynomial (Fin n) ℤ)
    (hw : WeakVectorCosetNF (polyFn p)) : p.totalDegree ≤ 2 := by
  obtain ⟨M, ρ, q, hM, hq⟩ := hw
  have hMq : (M : ℚ) ≠ 0 := by exact_mod_cast (by omega : M ≠ 0)
  set P : MvPolynomial (Fin n) ℚ := map (Int.castRingHom ℚ) p with hPdef
  let φ : Fin n → MvPolynomial (Fin n) ℚ := fun i => C (ρ i : ℚ) + C (M : ℚ) * X i
  let ψ : Fin n → MvPolynomial (Fin n) ℚ := fun i => C (-(ρ i : ℚ) / M) + C (1 / (M : ℚ)) * X i
  -- the shifted polynomial agrees with the quadratic on ℤⁿ, hence equals it
  have hagree : aeval φ P = quadPoly (q 0) := by
    refine funext_set (fun _ => Set.range (Int.cast : ℤ → ℚ))
      (fun _ => Set.infinite_range_of_injective Int.cast_injective) ?_
    intro x hx
    have hx' : ∀ i, ∃ k : ℤ, (k : ℚ) = x i := fun i => hx i (Set.mem_univ i)
    choose t ht using hx'
    have hxt : x = castQ t := by funext i; simp [castQ, ht i]
    subst hxt
    rw [eval_aeval_Q, eval_quadPoly, ← hq t 0]
    have : (fun i => eval (castQ t) (φ i)) = castQ (ρ + (M : ℤ) • t) := by
      funext i; simp [φ, castQ]
    rw [this, hPdef, eval_map_castQ]
    rfl
  -- invert the substitution
  have hinv : aeval ψ (aeval φ P) = P := by
    rw [aeval_aeval_Q]
    have : (fun i => aeval ψ (φ i)) = fun i => (X i : MvPolynomial (Fin n) ℚ) := by
      funext i
      simp only [φ, ψ, map_add, map_mul, aeval_C, aeval_X, algebraMap_eq]
      have e : C (ρ i : ℚ) + C (M : ℚ) * (C (-(ρ i : ℚ) / M) + C (1 / (M : ℚ)) * X i)
          = C ((ρ i : ℚ) + (M : ℚ) * (-(ρ i : ℚ) / M)) + C ((M : ℚ) * (1 / (M : ℚ))) * X i := by
        simp only [C_add, C_mul]; ring
      rw [e]
      have h1 : (ρ i : ℚ) + (M : ℚ) * (-(ρ i : ℚ) / M) = 0 := by field_simp; ring
      have h2 : (M : ℚ) * (1 / (M : ℚ)) = 1 := by field_simp
      rw [h1, h2]
      simp
    rw [this, aeval_X_self_Q]
  have hψ : ∀ i, (ψ i).totalDegree ≤ 1 := by
    intro i
    refine (totalDegree_add _ _).trans (max_le (by rw [totalDegree_C]; norm_num) ?_)
    refine (totalDegree_mul _ _).trans ?_
    rw [totalDegree_C, zero_add, MvPolynomial.totalDegree_X]
  calc p.totalDegree = P.totalDegree := (totalDegree_map_cast p).symm
    _ = (aeval ψ (aeval φ P)).totalDegree := by rw [hinv]
    _ ≤ (aeval φ P).totalDegree := totalDegree_aeval_le_of_le_one_Q ψ _ hψ
    _ = (quadPoly (q 0)).totalDegree := by rw [hagree]
    _ ≤ 2 := totalDegree_quadPoly_le _

/-- **S67-06.**  The graph of a polynomial is SE₂ iff its total degree is at most two (from Theorem 2). -/
theorem polyFn_SE2_iff {n : ℕ} (p : MvPolynomial (Fin n) ℤ) :
    DiophCompression.SingleQuadraticDefinableFunctionZZ (polyFn p) ↔ p.totalDegree ≤ 2 := by
  refine ⟨fun h => ?_, polyFn_SE2_of_degree_le p⟩
  obtain ⟨r, D, hD⟩ := graphData_of_singleQuadraticDefinable h
  rcases D.summit_of_defines hD with hl | hw
  · exact totalDegree_le_two_of_linearGrowth p hl
  · exact totalDegree_le_two_of_weakNF p hw

/-! ### S67-07: non-closure -/

/-- `x ↦ x²` as a function `ℤ¹ → ℤ¹`. -/
def sqMap : (Fin 1 → ℤ) → (Fin 1 → ℤ) := fun a _ => a 0 ^ 2

theorem sqMap_eq : sqMap = polyFn (X 0 ^ 2) := by
  funext a j; simp [sqMap, polyFn]

theorem sqMap_comp_eq : (fun a => sqMap (sqMap a)) = polyFn (X 0 ^ 4) := by
  funext a j; simp [sqMap, polyFn]; ring

theorem square_SE2 : DiophCompression.SingleQuadraticDefinableFunctionZZ sqMap := by
  rw [sqMap_eq]
  exact polyFn_SE2_of_degree_le _ (by rw [totalDegree_X_pow])

theorem fourth_not_SE2 : ¬ DiophCompression.SingleQuadraticDefinableFunctionZZ (fun a => sqMap (sqMap a)) := by
  rw [sqMap_comp_eq, polyFn_SE2_iff, totalDegree_X_pow]
  norm_num

/-- **S67-07 (composition).** -/
theorem not_closed_under_composition :
    ¬ ∀ g h : (Fin 1 → ℤ) → (Fin 1 → ℤ), DiophCompression.SingleQuadraticDefinableFunctionZZ g →
      DiophCompression.SingleQuadraticDefinableFunctionZZ h →
      DiophCompression.SingleQuadraticDefinableFunctionZZ (fun a => h (g a)) :=
  fun H => fourth_not_SE2 (H sqMap sqMap square_SE2 square_SE2)

end DiophCompression.ResearchUpgrade.SelectionS67
