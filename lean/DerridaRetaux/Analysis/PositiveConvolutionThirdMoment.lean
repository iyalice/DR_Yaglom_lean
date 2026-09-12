import DerridaRetaux.Analysis.PositiveConvolutionHigherMoments
import Mathlib.Tactic

set_option autoImplicit false

open MeasureTheory Set

namespace DerridaRetaux

noncomputable section

/-- The third moment of the positive self-convolution. -/
theorem integral_pow_three_mul_positiveSelfConvolution
    (u : ℝ → ℝ) (hucont : ContinuousOn u (Ici (0 : ℝ)))
    (h0 : IntegrableOn u (Ici 0))
    (h1 : IntegrableOn (fun x : ℝ ↦ x * u x) (Ici 0))
    (h2 : IntegrableOn (fun x : ℝ ↦ x ^ 2 * u x) (Ici 0))
    (h3 : IntegrableOn (fun x : ℝ ↦ x ^ 3 * u x) (Ici 0)) :
    ∫ x in Ici (0 : ℝ), x ^ 3 * positiveSelfConvolution u x =
      2 * continuumMoment u 0 * continuumMoment u 3 +
        6 * continuumMoment u 1 * continuumMoment u 2 := by
  have h0' : IntegrableOn (fun x : ℝ ↦ x ^ 0 * u x) (Ici 0) := by simpa using h0
  have h1' : IntegrableOn (fun x : ℝ ↦ x ^ 1 * u x) (Ici 0) := by simpa using h1
  have h30 := integrableOn_positiveConvolutionMomentTerm u 3 0 h3 h0'
  have h21 := integrableOn_positiveConvolutionMomentTerm u 2 1 h2 h1'
  have h12 := integrableOn_positiveConvolutionMomentTerm u 1 2 h1' h2
  have h03 := integrableOn_positiveConvolutionMomentTerm u 0 3 h0' h3
  have hpoint : ∀ x ∈ Ici (0 : ℝ),
      x ^ 3 * positiveSelfConvolution u x =
        positiveConvolutionMomentTerm u 3 0 x +
          3 * positiveConvolutionMomentTerm u 2 1 x +
          3 * positiveConvolutionMomentTerm u 1 2 x +
            positiveConvolutionMomentTerm u 0 3 x := by
    intro x hx
    rcases eq_or_lt_of_le (show 0 ≤ x from hx) with rfl | hx
    · simp [positiveSelfConvolution, positiveConvolutionMomentTerm]
    have huI : ContinuousOn u (Icc (0 : ℝ) x) :=
      hucont.mono fun _ hy ↦ hy.1
    have hrev : ContinuousOn (fun y : ℝ ↦ u (x - y)) (Icc 0 x) :=
      huI.comp (continuous_const.sub continuous_id).continuousOn
        (fun y hy ↦ ⟨sub_nonneg.mpr hy.2, by linarith [hy.1]⟩)
    have hsub : ContinuousOn (fun y : ℝ ↦ x - y) (Icc 0 x) :=
      (continuous_const.sub continuous_id).continuousOn
    have hi30 : IntervalIntegrable
        (fun y : ℝ ↦ y ^ 3 * u y * u (x - y)) volume 0 x :=
      (((continuousOn_id.pow 3).mul huI).mul hrev).intervalIntegrable_of_Icc hx.le
    have hi21 : IntervalIntegrable
        (fun y : ℝ ↦ y ^ 2 * u y * ((x - y) * u (x - y))) volume 0 x :=
      (((continuousOn_id.pow 2).mul huI).mul
        (hsub.mul hrev)).intervalIntegrable_of_Icc hx.le
    have hi12 : IntervalIntegrable
        (fun y : ℝ ↦ y * u y * ((x - y) ^ 2 * u (x - y))) volume 0 x :=
      ((continuousOn_id.mul huI).mul
        ((hsub.pow 2).mul hrev)).intervalIntegrable_of_Icc hx.le
    have hi03 : IntervalIntegrable
        (fun y : ℝ ↦ u y * ((x - y) ^ 3 * u (x - y))) volume 0 x :=
      (huI.mul ((hsub.pow 3).mul hrev)).intervalIntegrable_of_Icc hx.le
    calc
      x ^ 3 * positiveSelfConvolution u x =
          ∫ y in (0 : ℝ)..x, x ^ 3 * (u y * u (x - y)) := by
        rw [positiveSelfConvolution, intervalIntegral.integral_const_mul]
      _ = ∫ y in (0 : ℝ)..x,
          y ^ 3 * u y * u (x - y) +
            3 * (y ^ 2 * u y * ((x - y) * u (x - y))) +
            3 * (y * u y * ((x - y) ^ 2 * u (x - y))) +
              u y * ((x - y) ^ 3 * u (x - y)) := by
        apply intervalIntegral.integral_congr
        intro y hy
        ring
      _ = (∫ y in (0 : ℝ)..x, y ^ 3 * u y * u (x - y)) +
          (∫ y in (0 : ℝ)..x, 3 * (y ^ 2 * u y * ((x - y) * u (x - y)))) +
          (∫ y in (0 : ℝ)..x, 3 * (y * u y * ((x - y) ^ 2 * u (x - y)))) +
          (∫ y in (0 : ℝ)..x, u y * ((x - y) ^ 3 * u (x - y))) := by
        rw [intervalIntegral.integral_add
              ((hi30.add (hi21.const_mul 3)).add (hi12.const_mul 3)) hi03,
          intervalIntegral.integral_add (hi30.add (hi21.const_mul 3)) (hi12.const_mul 3),
          intervalIntegral.integral_add hi30 (hi21.const_mul 3)]
      _ = positiveConvolutionMomentTerm u 3 0 x +
          3 * positiveConvolutionMomentTerm u 2 1 x +
          3 * positiveConvolutionMomentTerm u 1 2 x +
            positiveConvolutionMomentTerm u 0 3 x := by
        rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
        simp only [positiveConvolutionMomentTerm, pow_zero, one_mul, pow_one]
  rw [setIntegral_congr_fun measurableSet_Ici hpoint]
  have hsum1 :
      (∫ x in Ici (0 : ℝ), positiveConvolutionMomentTerm u 3 0 x +
        3 * positiveConvolutionMomentTerm u 2 1 x) =
        (∫ x in Ici (0 : ℝ), positiveConvolutionMomentTerm u 3 0 x) +
          (∫ x in Ici (0 : ℝ), 3 * positiveConvolutionMomentTerm u 2 1 x) := by
    simpa only [Pi.add_apply] using integral_add h30 (h21.const_mul 3)
  have hsum2 :
      (∫ x in Ici (0 : ℝ),
        (positiveConvolutionMomentTerm u 3 0 x +
          3 * positiveConvolutionMomentTerm u 2 1 x) +
            3 * positiveConvolutionMomentTerm u 1 2 x) =
        (∫ x in Ici (0 : ℝ), positiveConvolutionMomentTerm u 3 0 x +
          3 * positiveConvolutionMomentTerm u 2 1 x) +
          (∫ x in Ici (0 : ℝ), 3 * positiveConvolutionMomentTerm u 1 2 x) := by
    simpa only [Pi.add_apply] using
      integral_add (h30.add (h21.const_mul 3)) (h12.const_mul 3)
  have hsum3 :
      (∫ x in Ici (0 : ℝ),
        ((positiveConvolutionMomentTerm u 3 0 x +
          3 * positiveConvolutionMomentTerm u 2 1 x) +
            3 * positiveConvolutionMomentTerm u 1 2 x) +
              positiveConvolutionMomentTerm u 0 3 x) =
        (∫ x in Ici (0 : ℝ),
          (positiveConvolutionMomentTerm u 3 0 x +
            3 * positiveConvolutionMomentTerm u 2 1 x) +
              3 * positiveConvolutionMomentTerm u 1 2 x) +
          (∫ x in Ici (0 : ℝ), positiveConvolutionMomentTerm u 0 3 x) := by
    simpa only [Pi.add_apply] using
      integral_add ((h30.add (h21.const_mul 3)).add (h12.const_mul 3)) h03
  rw [hsum3, hsum2, hsum1, integral_const_mul, integral_const_mul,
    integral_positiveConvolutionMomentTerm u 3 0 h3 h0',
    integral_positiveConvolutionMomentTerm u 2 1 h2 h1',
    integral_positiveConvolutionMomentTerm u 1 2 h1' h2,
    integral_positiveConvolutionMomentTerm u 0 3 h0' h3]
  simp only [continuumMoment, pow_zero, one_mul, pow_one]
  ring

end

end DerridaRetaux
