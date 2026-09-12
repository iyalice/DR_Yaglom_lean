import DerridaRetaux.Analysis.QuadraticConvolutionLimit
import Mathlib.MeasureTheory.Integral.DominatedConvergence

set_option autoImplicit false

open MeasureTheory
open scoped Interval

namespace DerridaRetaux

noncomputable section

/-- The half-line self-convolution is jointly continuous in time and space
for a jointly continuous density. -/
theorem continuous_positiveSelfConvolution_uncurry
    (u : ℝ → ℝ → ℝ)
    (hu : Continuous (Function.uncurry u)) :
    Continuous (fun p : ℝ × ℝ ↦ positiveSelfConvolution (u p.1) p.2) := by
  let kernel : (ℝ × ℝ) → ℝ → ℝ := fun p z ↦
    u p.1 (p.2 * z) * u p.1 (p.2 - p.2 * z)
  have hkernel : Continuous (Function.uncurry kernel) := by
    dsimp only [kernel, Function.uncurry_apply_pair]
    have hfirst : Continuous
        (fun q : (ℝ × ℝ) × ℝ ↦ (q.1.1, q.1.2 * q.2)) :=
      (continuous_fst.comp continuous_fst).prodMk
        ((continuous_snd.comp continuous_fst).mul continuous_snd)
    have hsecond : Continuous
        (fun q : (ℝ × ℝ) × ℝ ↦
          (q.1.1, q.1.2 - q.1.2 * q.2)) :=
      (continuous_fst.comp continuous_fst).prodMk
        ((continuous_snd.comp continuous_fst).sub
          ((continuous_snd.comp continuous_fst).mul continuous_snd))
    exact (hu.comp hfirst).mul (hu.comp hsecond)
  have hintegral : Continuous
      (fun p : ℝ × ℝ ↦ ∫ z in (0 : ℝ)..1, kernel p z) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      hkernel 0 1
  have hproduct : Continuous
      (fun p : ℝ × ℝ ↦ p.2 * ∫ z in (0 : ℝ)..1, kernel p z) :=
    continuous_snd.mul hintegral
  apply hproduct.congr
  intro p
  exact positiveSelfConvolution_eq_unit (u p.1) p.2

end

end DerridaRetaux
