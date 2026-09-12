import DerridaRetaux.Analysis.ShiftedSpacetimeConvolution
import DerridaRetaux.Analysis.ShiftedConvolutionBound
import DerridaRetaux.Analysis.MildQuadraticCoefficient
import DerridaRetaux.Analysis.UniformProductHalf

set_option autoImplicit false

open Filter Set Topology

namespace DerridaRetaux

noncomputable section

/-- The complete rescaled quadratic Duhamel summand converges uniformly to
one half of the continuum self-convolution along every positive floor window. -/
theorem quadraticDuhamelIntegrand_floor_window_uniform_of_H1a
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p₀) (hthird : TiltSummable m 3 p₀)
    (hnonconstant : ¬ IsDirac p₀)
    (hExcess : CDHLSExcessFact m p₀ hm hcrit hthird hnonconstant)
    (scale : ℕ → ℕ) (u : ℝ → ℝ → ℝ)
    (t₀ t x : ℝ) (R : ℕ)
    (ht₀ : 0 < t₀) (ht : t₀ ≤ t) (hx : 0 < x)
    (hR : x + t + 1 ≤ (R : ℝ))
    (hscale : Tendsto scale atTop atTop)
    (hlocal : LocallyUniformSpacetimeLatticeDensity
      (fun _n s ↦ positiveTiltedDensity m (orbit m p₀ s)) scale u)
    (hu : ContinuousOn (Function.uncurry u)
      (Icc (t₀ / 2) (t + 1) ×ˢ Icc (0 : ℝ) (R : ℝ))) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      ∀ s ∈ Finset.Ico (gridIndex (scale n) t₀) (gridIndex (scale n) t),
        |densityQuadraticWeight m p₀ s (gridIndex (scale n) t) *
            ((scale n : ℝ) ^ 3 *
              conv (positiveTiltedDensity m (orbit m p₀ s))
                (positiveTiltedDensity m (orbit m p₀ s))
                (gridIndex (scale n) x +
                  (gridIndex (scale n) t - 1 - s))) -
          (1 / 2 : ℝ) * positiveSelfConvolution
            (u ((s : ℝ) / (scale n : ℝ)))
            (x + t - (s : ℝ) / (scale n : ℝ))| < ε := by
  let lo : ℕ → ℕ := fun n ↦ gridIndex (scale n) t₀
  let hi : ℕ → ℕ := fun n ↦ gridIndex (scale n) t
  let coeff : ℕ → ℕ → ℝ := fun n s ↦
    densityQuadraticWeight m p₀ s (gridIndex (scale n) t)
  let source : ℕ → ℕ → ℝ := fun n s ↦
    (scale n : ℝ) ^ 3 *
      conv (positiveTiltedDensity m (orbit m p₀ s))
        (positiveTiltedDensity m (orbit m p₀ s))
        (gridIndex (scale n) x + (gridIndex (scale n) t - 1 - s))
  let target : ℕ → ℕ → ℝ := fun n s ↦
    positiveSelfConvolution (u ((s : ℝ) / (scale n : ℝ)))
      (x + t - (s : ℝ) / (scale n : ℝ))
  have hcoeff : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      ∀ s ∈ Finset.Ico (lo n) (hi n),
        |coeff n s - (1 : ℝ) / 2| < ε := by
    intro ε hε
    have h := densityQuadraticWeight_natFloor_window_uniform_of_H1a
      m p₀ hm hcrit hthird hnonconstant hExcess scale hscale
      t₀ t ht₀ ht ε hε
    simpa only [lo, hi, coeff, gridIndex, max_eq_left ht₀.le,
      max_eq_left (ht₀.le.trans ht), mul_comm] using h
  have hsource : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      ∀ s ∈ Finset.Ico (lo n) (hi n),
        |source n s - target n s| < ε := by
    intro ε hε
    simpa only [lo, hi, source, target] using
      scaled_conv_shifted_floor_window_uniform
        (fun _n s ↦ positiveTiltedDensity m (orbit m p₀ s))
        scale u t₀ t x R ht₀ ht hx hR hscale hlocal hu ε hε
  obtain ⟨C, hC, htargetBound⟩ :=
    exists_bound_positiveSelfConvolution_shifted_floor_window
      u scale t₀ t x R ht₀ ht hx hR hscale hu
  have hbound : ∀ᶠ n : ℕ in atTop,
      ∀ s ∈ Finset.Ico (lo n) (hi n), |target n s| ≤ C := by
    simpa only [lo, hi, target] using htargetBound
  simpa only [lo, hi, coeff, source, target] using
    eventuallyUniform_mul_tendsto_half_mul lo hi coeff source target
      C hC hcoeff hsource hbound

end

end DerridaRetaux
