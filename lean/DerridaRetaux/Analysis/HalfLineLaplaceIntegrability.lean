import DerridaRetaux.Analysis.PositiveConvolutionLaplace
import Mathlib.Tactic

set_option autoImplicit false

open MeasureTheory Set

namespace DerridaRetaux

noncomputable section

/-- For a nonnegative parameter, a half-line Laplace integrand is dominated
by the mass density. -/
theorem integrableOn_exp_neg_mul
    (u : ℝ → ℝ) (p : ℝ) (hp : 0 ≤ p)
    (hucont : ContinuousOn u (Ici (0 : ℝ)))
    (hunonneg : ∀ x : ℝ, 0 ≤ x → 0 ≤ u x)
    (h0 : IntegrableOn u (Ici 0)) :
    IntegrableOn (fun x : ℝ ↦ Real.exp (-(p * x)) * u x) (Ici 0) := by
  apply h0.mono'
  · exact ((by fun_prop : Continuous fun x : ℝ ↦ Real.exp (-(p * x))).continuousOn.mul
      hucont).aestronglyMeasurable measurableSet_Ici
  · filter_upwards [self_mem_ae_restrict measurableSet_Ici] with x hx
    have hx0 : 0 ≤ x := hx
    have hu0 := hunonneg x hx0
    have hexp0 := (Real.exp_pos (-(p * x))).le
    have hexp1 : Real.exp (-(p * x)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hp hx0))
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hexp0 hu0)]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hexp1 hu0

end

end DerridaRetaux
