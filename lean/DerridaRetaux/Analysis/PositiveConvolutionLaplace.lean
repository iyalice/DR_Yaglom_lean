import DerridaRetaux.Analysis.PositiveConvolutionMoments
import Mathlib.Tactic

set_option autoImplicit false

open MeasureTheory Set

namespace DerridaRetaux

noncomputable section

/-- Half-line Laplace transform of a density. -/
def continuumLaplace (u : ℝ → ℝ) (p : ℝ) : ℝ :=
  ∫ x in Ici (0 : ℝ), Real.exp (-(p * x)) * u x

/-- The Laplace transform turns positive self-convolution into multiplication. -/
theorem integral_exp_mul_positiveSelfConvolution
    (u : ℝ → ℝ) (p : ℝ)
    (hLap : IntegrableOn
      (fun x : ℝ ↦ Real.exp (-(p * x)) * u x) (Ici 0)) :
    ∫ x in Ici (0 : ℝ),
        Real.exp (-(p * x)) * positiveSelfConvolution u x =
      continuumLaplace u p ^ 2 := by
  rw [integral_Ici_eq_integral_Ioi]
  have hconv := MeasureTheory.integral_posConvolution
    (integrableOn_Ici_iff_integrableOn_Ioi.mp hLap)
    (integrableOn_Ici_iff_integrableOn_Ioi.mp hLap)
    (ContinuousLinearMap.mul ℝ ℝ)
  have hpoint : ∀ x ∈ Ioi (0 : ℝ),
      Real.exp (-(p * x)) * positiveSelfConvolution u x =
        ∫ y in (0 : ℝ)..x,
          (Real.exp (-(p * y)) * u y) *
            (Real.exp (-(p * (x - y))) * u (x - y)) := by
    intro x hx
    rw [positiveSelfConvolution, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro y hy
    rw [show -(p * x) = -(p * y) + -(p * (x - y)) by ring, Real.exp_add]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hpoint]
  simpa only [continuumLaplace, integral_Ici_eq_integral_Ioi,
    ContinuousLinearMap.mul_apply, pow_two] using hconv

end

end DerridaRetaux
