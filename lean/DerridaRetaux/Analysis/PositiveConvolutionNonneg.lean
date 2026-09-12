import DerridaRetaux.Analysis.QuadraticConvolutionLimit

set_option autoImplicit false

open MeasureTheory Set

namespace DerridaRetaux

noncomputable section

theorem positiveSelfConvolution_nonneg
    (u : ℝ → ℝ) (hu : ∀ x : ℝ, 0 ≤ x → 0 ≤ u x)
    {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ positiveSelfConvolution u x := by
  unfold positiveSelfConvolution
  apply intervalIntegral.integral_nonneg hx
  intro y hy
  exact mul_nonneg (hu y hy.1) (hu (x - y) (sub_nonneg.mpr hy.2))

end

end DerridaRetaux
