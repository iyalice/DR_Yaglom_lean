import DerridaRetaux.Analysis.PositiveConvolutionMoments
import Mathlib.Tactic

set_option autoImplicit false

open MeasureTheory Set

namespace DerridaRetaux

noncomputable section

/-- A monomial term occurring in a moment of a positive convolution. -/
def positiveConvolutionMomentTerm
    (u : ℝ → ℝ) (a b : ℕ) (x : ℝ) : ℝ :=
  ∫ y in (0 : ℝ)..x,
    (y ^ a * u y) * ((x - y) ^ b * u (x - y))

/-- Each monomial term factors into the corresponding two half-line moments. -/
theorem integral_positiveConvolutionMomentTerm
    (u : ℝ → ℝ) (a b : ℕ)
    (ha : IntegrableOn (fun x : ℝ ↦ x ^ a * u x) (Ici 0))
    (hb : IntegrableOn (fun x : ℝ ↦ x ^ b * u x) (Ici 0)) :
    ∫ x in Ici (0 : ℝ), positiveConvolutionMomentTerm u a b x =
      continuumMoment u a * continuumMoment u b := by
  rw [integral_Ici_eq_integral_Ioi]
  have hconv := MeasureTheory.integral_posConvolution
    (integrableOn_Ici_iff_integrableOn_Ioi.mp ha)
    (integrableOn_Ici_iff_integrableOn_Ioi.mp hb)
    (ContinuousLinearMap.mul ℝ ℝ)
  simpa only [positiveConvolutionMomentTerm,
    ContinuousLinearMap.mul_apply, continuumMoment,
    integral_Ici_eq_integral_Ioi] using hconv

/-- The monomial convolution term is integrable in the output variable. -/
theorem integrableOn_positiveConvolutionMomentTerm
    (u : ℝ → ℝ) (a b : ℕ)
    (ha : IntegrableOn (fun x : ℝ ↦ x ^ a * u x) (Ici 0))
    (hb : IntegrableOn (fun x : ℝ ↦ x ^ b * u x) (Ici 0)) :
    IntegrableOn (positiveConvolutionMomentTerm u a b) (Ici 0) := by
  rw [integrableOn_Ici_iff_integrableOn_Ioi]
  have hconv := MeasureTheory.integrable_posConvolution
    (integrableOn_Ici_iff_integrableOn_Ioi.mp ha)
    (integrableOn_Ici_iff_integrableOn_Ioi.mp hb)
    (ContinuousLinearMap.mul ℝ ℝ)
  refine hconv.integrableOn.congr_fun ?_ measurableSet_Ioi
  intro x hx
  rw [MeasureTheory.posConvolution, Set.indicator_of_mem hx]
  rfl

/-- The second moment of the positive self-convolution. -/
theorem integral_pow_two_mul_positiveSelfConvolution
    (u : ℝ → ℝ) (hucont : ContinuousOn u (Ici (0 : ℝ)))
    (h0 : IntegrableOn u (Ici 0))
    (h1 : IntegrableOn (fun x : ℝ ↦ x * u x) (Ici 0))
    (h2 : IntegrableOn (fun x : ℝ ↦ x ^ 2 * u x) (Ici 0)) :
    ∫ x in Ici (0 : ℝ), x ^ 2 * positiveSelfConvolution u x =
      2 * continuumMoment u 0 * continuumMoment u 2 +
        2 * continuumMoment u 1 ^ 2 := by
  have h0' : IntegrableOn (fun x : ℝ ↦ x ^ 0 * u x) (Ici 0) := by
    simpa using h0
  have h1' : IntegrableOn (fun x : ℝ ↦ x ^ 1 * u x) (Ici 0) := by
    simpa using h1
  have h20 := integrableOn_positiveConvolutionMomentTerm u 2 0 h2 h0'
  have h11 := integrableOn_positiveConvolutionMomentTerm u 1 1 h1' h1'
  have h02 := integrableOn_positiveConvolutionMomentTerm u 0 2 h0' h2
  have hpoint : ∀ x ∈ Ici (0 : ℝ),
      x ^ 2 * positiveSelfConvolution u x =
        positiveConvolutionMomentTerm u 2 0 x +
          2 * positiveConvolutionMomentTerm u 1 1 x +
            positiveConvolutionMomentTerm u 0 2 x := by
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
    have hi20 : IntervalIntegrable
        (fun y : ℝ ↦ y ^ 2 * u y * u (x - y)) volume 0 x := by
      exact (((continuousOn_id.pow 2).mul huI).mul hrev).intervalIntegrable_of_Icc hx.le
    have hi11 : IntervalIntegrable
        (fun y : ℝ ↦ y * u y * ((x - y) * u (x - y))) volume 0 x := by
      exact ((continuousOn_id.mul huI).mul (hsub.mul hrev)).intervalIntegrable_of_Icc hx.le
    have hi02 : IntervalIntegrable
        (fun y : ℝ ↦ u y * ((x - y) ^ 2 * u (x - y))) volume 0 x := by
      exact (huI.mul ((hsub.pow 2).mul hrev)).intervalIntegrable_of_Icc hx.le
    calc
      x ^ 2 * positiveSelfConvolution u x =
          ∫ y in (0 : ℝ)..x, x ^ 2 * (u y * u (x - y)) := by
        rw [positiveSelfConvolution, intervalIntegral.integral_const_mul]
      _ = ∫ y in (0 : ℝ)..x,
          y ^ 2 * u y * u (x - y) +
            2 * (y * u y * ((x - y) * u (x - y))) +
              u y * ((x - y) ^ 2 * u (x - y)) := by
        apply intervalIntegral.integral_congr
        intro y hy
        ring
      _ = (∫ y in (0 : ℝ)..x, y ^ 2 * u y * u (x - y)) +
          (∫ y in (0 : ℝ)..x,
            2 * (y * u y * ((x - y) * u (x - y)))) +
          (∫ y in (0 : ℝ)..x, u y * ((x - y) ^ 2 * u (x - y))) := by
        rw [intervalIntegral.integral_add (hi20.add (hi11.const_mul 2)) hi02,
          intervalIntegral.integral_add hi20 (hi11.const_mul 2)]
      _ = positiveConvolutionMomentTerm u 2 0 x +
          2 * positiveConvolutionMomentTerm u 1 1 x +
            positiveConvolutionMomentTerm u 0 2 x := by
        rw [intervalIntegral.integral_const_mul]
        simp only [positiveConvolutionMomentTerm, pow_zero, one_mul, pow_one]
  rw [setIntegral_congr_fun measurableSet_Ici hpoint]
  have hsplit :
      (∫ x in Ici (0 : ℝ),
        positiveConvolutionMomentTerm u 2 0 x +
          2 * positiveConvolutionMomentTerm u 1 1 x +
            positiveConvolutionMomentTerm u 0 2 x) =
        (∫ x in Ici (0 : ℝ), positiveConvolutionMomentTerm u 2 0 x) +
          2 * (∫ x in Ici (0 : ℝ), positiveConvolutionMomentTerm u 1 1 x) +
            (∫ x in Ici (0 : ℝ), positiveConvolutionMomentTerm u 0 2 x) := by
    have hsum1 :
        (∫ x in Ici (0 : ℝ), positiveConvolutionMomentTerm u 2 0 x +
          2 * positiveConvolutionMomentTerm u 1 1 x) =
          (∫ x in Ici (0 : ℝ), positiveConvolutionMomentTerm u 2 0 x) +
            (∫ x in Ici (0 : ℝ), 2 * positiveConvolutionMomentTerm u 1 1 x) := by
      simpa only [Pi.add_apply] using integral_add h20 (h11.const_mul 2)
    have hsum2 :
        (∫ x in Ici (0 : ℝ),
          (positiveConvolutionMomentTerm u 2 0 x +
            2 * positiveConvolutionMomentTerm u 1 1 x) +
              positiveConvolutionMomentTerm u 0 2 x) =
          (∫ x in Ici (0 : ℝ), positiveConvolutionMomentTerm u 2 0 x +
            2 * positiveConvolutionMomentTerm u 1 1 x) +
              (∫ x in Ici (0 : ℝ), positiveConvolutionMomentTerm u 0 2 x) := by
      simpa only [Pi.add_apply] using
        integral_add (h20.add (h11.const_mul 2)) h02
    rw [hsum2, hsum1, integral_const_mul]
  rw [hsplit, integral_positiveConvolutionMomentTerm u 2 0 h2 h0',
    integral_positiveConvolutionMomentTerm u 1 1 h1' h1',
    integral_positiveConvolutionMomentTerm u 0 2 h0' h2]
  simp only [continuumMoment, pow_zero, one_mul, pow_one]
  ring

end

end DerridaRetaux
