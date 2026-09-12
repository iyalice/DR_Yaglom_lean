import DerridaRetaux.Analysis.TimeRiemannLimit
import DerridaRetaux.Analysis.TruncatedTelescope
import Mathlib.Tactic

set_option autoImplicit false

open scoped BigOperators

namespace DerridaRetaux

noncomputable section

/-- Exact scaling identity between the triangular time array and the literal
quadratic Duhamel segment. -/
theorem gridTimeArraySum_quadratic_eq_scaled_segment
    (m : ℕ) (p₀ : ProbabilityMass) (N : ℕ)
    (t₀ t x : ℝ) (hN : 0 < N) (ht₀ : 0 ≤ t₀) (ht : 0 ≤ t) :
    let F : ℕ → ℕ → ℝ := fun _n s ↦
      densityQuadraticWeight m p₀ s (gridIndex N t) *
        ((N : ℝ) ^ 3 *
          conv (positiveTiltedDensity m (orbit m p₀ s))
            (positiveTiltedDensity m (orbit m p₀ s))
            (gridIndex N x + (gridIndex N t - 1 - s)))
    gridTimeArraySum F (fun _ ↦ N) 0 t₀ t =
      (N : ℝ) ^ 2 * densityQuadraticSegment m p₀
        (gridIndex N t₀) (gridIndex N t) (gridIndex N x) := by
  dsimp only
  rw [gridTimeArraySum]
  rw [densityQuadraticSegment_eq_weightedKernelSum]
  simp only [densityQuadraticKernel, shiftLeft_iterate_apply, densityB]
  rw [Finset.mul_sum]
  apply Finset.sum_congr
  · rfl
  intro s _hs
  have hNreal : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  field_simp [hNreal]
  ring

end

end DerridaRetaux
