/-
  S66-09 (scratch, not sealed).  Pure arithmetic, no TCER, no Lean names from the mpup development.

  * `three_sq_of_three_sq_mul_sq`: if d M² (M ≥ 1) is a sum of three integer squares, so is d.
    This is the classical Davenport–Cassels (Aubry) denominator descent for x² + y² + z²; it is NOT new.
  * `not_three_sq_of_excluded`, `excluded_mul_sq`: the elementary half of Legendre (4^r(8s+7) is not a sum of
    three squares; the class is stable under multiplication by squares).
-/
import Mathlib

namespace DiophCompression.ResearchUpgrade.SelectionS66

/-- `n` has the form `4^r (8s+7)`. -/
def Legendre3Excluded (n : ℕ) : Prop := ∃ r s : ℕ, n = 4 ^ r * (8 * s + 7)

/-- `N` is a sum of three integer squares. -/
def IsSumThreeSq (N : ℤ) : Prop := ∃ x y z : ℤ, x ^ 2 + y ^ 2 + z ^ 2 = N

/-- Nearest-integer rounding: `x = M t + r` with `(2r)² ≤ M²`. -/
theorem round_exists (x M : ℤ) (hM : 0 < M) : ∃ t r : ℤ, x = M * t + r ∧ 4 * r ^ 2 ≤ M ^ 2 := by
  refine ⟨(2 * x + M) / (2 * M), x - M * ((2 * x + M) / (2 * M)), by ring, ?_⟩
  have h2M : 0 < 2 * M := by omega
  have hq := Int.emod_add_mul_ediv (2 * x + M) (2 * M)
  have hlo := Int.emod_nonneg (2 * x + M) (ne_of_gt h2M)
  have hhi := Int.emod_lt_of_pos (2 * x + M) h2M
  set q := (2 * x + M) / (2 * M)
  set s := (2 * x + M) % (2 * M)
  have hr : 2 * (x - M * q) = s - M := by linarith
  have hb1 : -M ≤ 2 * (x - M * q) := by linarith
  have hb2 : 2 * (x - M * q) ≤ M := by linarith
  nlinarith [hb1, hb2]

/-- **S66-09.**  Denominator descent (Davenport–Cassels for x²+y²+z²). -/
theorem three_sq_of_three_sq_mul_sq (d : ℤ) :
    ∀ M : ℕ, 0 < M → IsSumThreeSq (d * (M : ℤ) ^ 2) → IsSumThreeSq d := by
  intro M
  induction M using Nat.strong_induction_on with
  | _ M ih =>
  intro hM ⟨x, y, z, hxyz⟩
  have hM' : (0 : ℤ) < M := by exact_mod_cast hM
  obtain ⟨tx, rx, hx, hrx⟩ := round_exists x M hM'
  obtain ⟨ty, ry, hy, hry⟩ := round_exists y M hM'
  obtain ⟨tz, rz, hz, hrz⟩ := round_exists z M hM'
  subst hx hy hz
  set T := tx ^ 2 + ty ^ 2 + tz ^ 2 with hT
  set R := rx ^ 2 + ry ^ 2 + rz ^ 2 with hR
  set P := tx * rx + ty * ry + tz * rz with hP
  set e := d - T with he
  set h := e * (M : ℤ) - 2 * P with hh
  -- the key identity  R = M h
  have hRh : R = (M : ℤ) * h := by
    simp only [hR, hh, he, hT, hP]
    linear_combination hxyz
  have hR0 : 0 ≤ R := by positivity
  have hRlt : R < (M : ℤ) ^ 2 := by nlinarith [hrx, hry, hrz]
  have hh0 : 0 ≤ h := by
    by_contra hneg
    have hneg' : h < 0 := lt_of_not_ge hneg
    nlinarith
  have hhM : h < M := by nlinarith
  rcases eq_or_lt_of_le hh0 with h0 | hpos
  · -- h = 0: then r = 0 and d = T
    have hR' : R = 0 := by rw [hRh, ← h0, mul_zero]
    have hx0 : rx = 0 := by nlinarith [sq_nonneg rx, sq_nonneg ry, sq_nonneg rz]
    have hy0 : ry = 0 := by nlinarith [sq_nonneg rx, sq_nonneg ry, sq_nonneg rz]
    have hz0 : rz = 0 := by nlinarith [sq_nonneg rx, sq_nonneg ry, sq_nonneg rz]
    subst hx0 hy0 hz0
    refine ⟨tx, ty, tz, ?_⟩
    have hMM : (M : ℤ) ^ 2 * (tx ^ 2 + ty ^ 2 + tz ^ 2) = (M : ℤ) ^ 2 * d := by linear_combination hxyz
    exact mul_left_cancel₀ (by positivity) hMM
  · -- 0 < h < M: x' = h t − e r has ‖x'‖² = d h²
    have hhN : (h.toNat : ℤ) = h := Int.toNat_of_nonneg hh0
    have hlt : h.toNat < M := by omega
    apply ih h.toNat hlt (by omega)
    refine ⟨h * tx - e * rx, h * ty - e * ry, h * tz - e * rz, ?_⟩
    rw [hhN]
    simp only [hh, he, hT, hP]
    linear_combination (d - (tx ^ 2 + ty ^ 2 + tz ^ 2)) ^ 2 * hxyz

/-- `4^r(8s+7)` is not a sum of three squares (elementary half of Legendre). -/
theorem not_three_sq_of_excluded :
    ∀ (r s : ℕ) (x y z : ℤ), x ^ 2 + y ^ 2 + z ^ 2 ≠ (4 : ℤ) ^ r * (8 * (s : ℤ) + 7) := by
  intro r
  induction r with
  | zero =>
    intro s x y z h
    simp only [pow_zero, one_mul] at h
    have h8 := congrArg (Int.cast : ℤ → ZMod 8) h
    push_cast at h8
    rw [show (8 : ZMod 8) = 0 from rfl, zero_mul, zero_add] at h8
    revert h8
    generalize (x : ZMod 8) = a
    generalize (y : ZMod 8) = b
    generalize (z : ZMod 8) = c
    revert a b c
    decide
  | succ r ih =>
    intro s x y z h
    have h4 : (x : ZMod 4) ^ 2 + (y : ZMod 4) ^ 2 + (z : ZMod 4) ^ 2 = 0 := by
      have h' := congrArg (Int.cast : ℤ → ZMod 4) h
      push_cast at h'
      rw [h', pow_succ, show (4 : ZMod 4) = 0 from rfl]
      ring
    have key : ∀ a b c : ZMod 4, a ^ 2 + b ^ 2 + c ^ 2 = 0 → 2 * a = 0 ∧ 2 * b = 0 ∧ 2 * c = 0 := by decide
    have two_dvd : ∀ w : ℤ, 2 * (w : ZMod 4) = 0 → ∃ k, w = 2 * k := by
      intro w hw
      have hw' : ((2 * w : ℤ) : ZMod 4) = 0 := by push_cast; exact hw
      obtain ⟨k, hk⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd (2 * w) 4).mp hw'
      exact ⟨k, by push_cast at hk; omega⟩
    obtain ⟨hx, hy, hz⟩ := key _ _ _ h4
    obtain ⟨kx, rfl⟩ := two_dvd x hx
    obtain ⟨ky, rfl⟩ := two_dvd y hy
    obtain ⟨kz, rfl⟩ := two_dvd z hz
    apply ih s kx ky kz
    have h4' : 4 * (kx ^ 2 + ky ^ 2 + kz ^ 2) = 4 * ((4 : ℤ) ^ r * (8 * (s : ℤ) + 7)) := by
      linear_combination h
    exact mul_left_cancel₀ (by norm_num) h4'

theorem not_isSumThreeSq_of_excluded {d : ℕ} (hd : Legendre3Excluded d) : ¬ IsSumThreeSq (d : ℤ) := by
  obtain ⟨r, s, rfl⟩ := hd
  rintro ⟨x, y, z, h⟩
  exact not_three_sq_of_excluded r s x y z (by rw [h]; push_cast; ring)

end DiophCompression.ResearchUpgrade.SelectionS66
