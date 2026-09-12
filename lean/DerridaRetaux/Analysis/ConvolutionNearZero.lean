import DerridaRetaux.Analysis.QuadraticConvolutionLimit
import Mathlib.Tactic

set_option autoImplicit false

open Set MeasureTheory
open scoped BigOperators Interval

namespace DerridaRetaux

noncomputable section

/-- A bounded lattice profile has a convolution bounded by the macroscopic
length of its finite convolution triangle. -/
theorem abs_latticeSelfConvolutionSum_le
    (u : ℝ → ℝ) (N k : ℕ) (B : ℝ)
    (hN : 0 < N) (hB : 0 ≤ B)
    (hu : ∀ j : ℕ, j ≤ k → |u ((j : ℝ) / (N : ℝ))| ≤ B) :
    |latticeSelfConvolutionSum u N k| ≤
      ((k + 1 : ℕ) : ℝ) / (N : ℝ) * B ^ 2 := by
  have hNreal : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  rw [latticeSelfConvolutionSum, abs_mul, abs_of_pos (inv_pos.mpr hNreal)]
  calc
    (N : ℝ)⁻¹ *
        |∑ i ∈ Finset.range (k + 1),
          u ((i : ℝ) / (N : ℝ)) *
            u (((k - i : ℕ) : ℝ) / (N : ℝ))| ≤
      (N : ℝ)⁻¹ *
        ∑ i ∈ Finset.range (k + 1),
          |u ((i : ℝ) / (N : ℝ)) *
            u (((k - i : ℕ) : ℝ) / (N : ℝ))| := by
      gcongr
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ (N : ℝ)⁻¹ * ∑ _i ∈ Finset.range (k + 1), B ^ 2 := by
      gcongr with i hi
      rw [abs_mul, sq]
      exact mul_le_mul
        (hu i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)))
        (hu (k - i) (Nat.sub_le k i)) (abs_nonneg _) hB
    _ = ((k + 1 : ℕ) : ℝ) / (N : ℝ) * B ^ 2 := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      rw [div_eq_mul_inv]
      ring

/-- A bounded continuous profile has convolution at most its interval length
times the square of the bound. -/
theorem abs_positiveSelfConvolution_le
    (u : ℝ → ℝ) (x R C : ℝ)
    (hx : x ∈ Icc (0 : ℝ) R) (hC : 0 ≤ C)
    (hu : ∀ y ∈ Icc (0 : ℝ) R, |u y| ≤ C) :
    |positiveSelfConvolution u x| ≤ x * C ^ 2 := by
  rw [positiveSelfConvolution]
  calc
    |∫ y in (0 : ℝ)..x, u y * u (x - y)| =
        ‖∫ y in (0 : ℝ)..x, u y * u (x - y)‖ := by
      rw [Real.norm_eq_abs]
    _ ≤ C ^ 2 * |x - 0| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro y hy
      rw [uIoc_of_le hx.1] at hy
      have hyR : y ∈ Icc (0 : ℝ) R :=
        ⟨hy.1.le, hy.2.trans hx.2⟩
      have hxyR : x - y ∈ Icc (0 : ℝ) R := by
        exact ⟨sub_nonneg.mpr hy.2, (sub_le_self x hy.1.le).trans hx.2⟩
      rw [Real.norm_eq_abs, abs_mul, sq]
      exact mul_le_mul (hu y hyR) (hu (x - y) hxyR)
        (abs_nonneg _) hC
    _ = x * C ^ 2 := by rw [sub_zero, abs_of_nonneg hx.1]; ring

end

end DerridaRetaux
