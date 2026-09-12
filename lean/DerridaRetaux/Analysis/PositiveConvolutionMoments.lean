import DerridaRetaux.Analysis.QuadraticConvolutionLimit
import DerridaRetaux.Analysis.MomentPassage
import Mathlib.Analysis.Convolution
import Mathlib.Tactic

set_option autoImplicit false

open MeasureTheory Set

namespace DerridaRetaux

noncomputable section

/-- The total mass of the positive half-line convolution is the square of the
total mass. -/
theorem integral_positiveSelfConvolution
    (u : ℝ → ℝ) (hu : IntegrableOn u (Ici (0 : ℝ))) :
    ∫ x in Ici (0 : ℝ), positiveSelfConvolution u x =
      (∫ x in Ici (0 : ℝ), u x) ^ 2 := by
  rw [integral_Ici_eq_integral_Ioi, integral_Ici_eq_integral_Ioi]
  have hconv := MeasureTheory.integral_posConvolution
    (integrableOn_Ici_iff_integrableOn_Ioi.mp hu)
    (integrableOn_Ici_iff_integrableOn_Ioi.mp hu)
    (ContinuousLinearMap.mul ℝ ℝ)
  simpa only [positiveSelfConvolution, ContinuousLinearMap.mul_apply,
    pow_two] using hconv

end

end DerridaRetaux
