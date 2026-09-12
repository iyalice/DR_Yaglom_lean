import DerridaRetaux.Analysis.MomentPassage
import DerridaRetaux.Analysis.OrbitConvolutionBounds
import Mathlib.Tactic

set_option autoImplicit false

open scoped BigOperators

namespace DerridaRetaux

noncomputable section

theorem pow_le_scale_pow_mul_cubicWeight
    (r j : ℕ) (L : ℝ) (hr : r ≤ 3) (hL : 0 < L) :
    (j : ℝ) ^ r ≤ L ^ r * cubicWeight L j := by
  have hz : 0 ≤ (j : ℝ) / L := div_nonneg (Nat.cast_nonneg j) hL.le
  have hbase : (j : ℝ) / L ≤ 1 + (j : ℝ) / L := by linarith
  interval_cases r
  · simp only [Nat.cast_zero, pow_zero, one_mul, cubicWeight]
    nlinarith [sq_nonneg ((j : ℝ) / L),
      mul_nonneg (sq_nonneg ((j : ℝ) / L)) hz]
  · simp only [pow_one, cubicWeight]
    have hcubic : (j : ℝ) / L ≤ (1 + (j : ℝ) / L) ^ 3 := by
      nlinarith [sq_nonneg ((j : ℝ) / L),
        mul_nonneg (sq_nonneg ((j : ℝ) / L)) hz]
    calc
      (j : ℝ) = L * ((j : ℝ) / L) := by field_simp
      _ ≤ L * (1 + (j : ℝ) / L) ^ 3 :=
        mul_le_mul_of_nonneg_left hcubic hL.le
  · simp only [cubicWeight]
    have hsquare : ((j : ℝ) / L) ^ 2 ≤ (1 + (j : ℝ) / L) ^ 3 := by
      nlinarith [sq_nonneg ((j : ℝ) / L),
        mul_nonneg (sq_nonneg ((j : ℝ) / L)) hz]
    calc
      (j : ℝ) ^ 2 = L ^ 2 * ((j : ℝ) / L) ^ 2 := by field_simp
      _ ≤ L ^ 2 * (1 + (j : ℝ) / L) ^ 3 :=
        mul_le_mul_of_nonneg_left hsquare (sq_nonneg L)
  · simp only [cubicWeight]
    have hcubic : ((j : ℝ) / L) ^ 3 ≤ (1 + (j : ℝ) / L) ^ 3 := by gcongr
    calc
      (j : ℝ) ^ 3 = L ^ 3 * ((j : ℝ) / L) ^ 3 := by field_simp
      _ ≤ L ^ 3 * (1 + (j : ℝ) / L) ^ 3 :=
        mul_le_mul_of_nonneg_left hcubic (by positivity)

/-- A cubic weighted `l1` estimate controls every normalized lattice moment
of order at most three, with the scale mismatch left explicit. -/
theorem scaledDiscreteMoment_le_weightedL1
    (rho : Seq) (r N : ℕ) (L : ℝ)
    (hr : r ≤ 3) (hN : 0 < N) (hL : 0 < L)
    (hrho : ∀ j : ℕ, 0 ≤ rho j)
    (hmoment : Summable (fun j : ℕ ↦ (j : ℝ) ^ r * rho j))
    (hweighted : Summable (weightedAbs L rho)) :
    scaledDiscreteMoment rho r N ≤
      ((N : ℝ) / (N : ℝ) ^ r) *
        (L ^ r * weightedL1Three L rho) := by
  have hterm : ∀ j : ℕ,
      (j : ℝ) ^ r * rho j ≤ L ^ r * weightedAbs L rho j := by
    intro j
    rw [weightedAbs, abs_of_nonneg (hrho j)]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
      (pow_le_scale_pow_mul_cubicWeight r j L hr hL) (hrho j)
  have hsumRight : Summable (fun j : ℕ ↦ L ^ r * weightedAbs L rho j) :=
    hweighted.mul_left (L ^ r)
  have hsum : (∑' j : ℕ, (j : ℝ) ^ r * rho j) ≤
      ∑' j : ℕ, L ^ r * weightedAbs L rho j :=
    hmoment.tsum_le_tsum hterm hsumRight
  have hscale : 0 ≤ (N : ℝ) / (N : ℝ) ^ r := by positivity
  rw [scaledDiscreteMoment, weightedL1Three_eq_tsum_weightedAbs, ← hweighted.tsum_mul_left]
  exact mul_le_mul_of_nonneg_left hsum hscale

end

end DerridaRetaux
