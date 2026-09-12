import DerridaRetaux.Analysis.GridCompactness
import DerridaRetaux.Analysis.LogRate
import DerridaRetaux.Analysis.TemporalSmoothing

/-!
# Source-scale grid readout

This file supplies the concrete `O(log N / N)` adjacent-node error omitted
from the abstract compactness module.  It derives that error from the actual
orbit's weighted gradient estimate and connects it to the floor-grid readout.
-/

set_option autoImplicit false

namespace DerridaRetaux

noncomputable section

open Filter Set Topology

/-- The literal rescaled orbit array in `eq:rescaled`. -/
def orbitScaledGrid
    (m : ℕ) (p₀ : ProbabilityMass) (N n j : ℕ) : ℝ :=
  (N : ℝ) ^ 2 * positiveTiltedDensity m (orbit m p₀ n) j

/-- The adjacent-node error furnished by `eq:gradient` at the terminal time. -/
def orbitScaledGridStepError (C : ℝ) (N : ℕ) : ℝ :=
  (N : ℝ) ^ 2 *
    (C * Real.log ((N : ℝ) + 2) / profileScale N ^ 3)

/-- The weighted gradient estimate gives the source-specific adjacent-node
bound required by the floor-grid readout. -/
theorem orbitScaledGrid_adjacent_le_of_gradient
    (m : ℕ) (p₀ : ProbabilityMass) (C : ℝ)
    (hgradient : ∀ n : ℕ,
      WeightedSupThreeLE (profileScale n)
        (discreteDerivative (positiveTiltedDensity m (orbit m p₀ n)))
        (C * Real.log ((n : ℝ) + 2) / profileScale n ^ 3))
    (N : ℕ) (_hN : 0 < N) (j : ℕ) :
    |orbitScaledGrid m p₀ N N (j + 1) -
        orbitScaledGrid m p₀ N N j| ≤ orbitScaledGridStepError C N := by
  have hdelta := supLE_of_weightedSupThree
    (profileScale N)
    (C * Real.log ((N : ℝ) + 2) / profileScale N ^ 3)
    (profileScale_pos N)
    (discreteDerivative (positiveTiltedDensity m (orbit m p₀ N)))
    (hgradient N) j
  rw [discreteDerivative_apply] at hdelta
  have hNnonneg : 0 ≤ (N : ℝ) ^ 2 := sq_nonneg _
  calc
    |orbitScaledGrid m p₀ N N (j + 1) -
        orbitScaledGrid m p₀ N N j| =
        (N : ℝ) ^ 2 *
          |positiveTiltedDensity m (orbit m p₀ N) j -
            positiveTiltedDensity m (orbit m p₀ N) (j + 1)| := by
      rw [orbitScaledGrid, orbitScaledGrid, ← mul_sub, abs_mul,
        abs_of_nonneg hNnonneg, abs_sub_comm]
    _ ≤ (N : ℝ) ^ 2 *
        (C * Real.log ((N : ℝ) + 2) / profileScale N ^ 3) :=
      mul_le_mul_of_nonneg_left hdelta hNnonneg
    _ = orbitScaledGridStepError C N := rfl

/-- The concrete adjacent-node error tends to zero. -/
theorem orbitScaledGridStepError_tendsto_zero (C : ℝ) :
    Tendsto (orbitScaledGridStepError C) atTop (𝓝 0) := by
  change Tendsto
    (fun N : ℕ ↦ (N : ℝ) ^ 2 *
      (C * Real.log ((N : ℝ) + 2) / profileScale N ^ 3)) atTop (𝓝 0)
  simpa only [profileScale, Nat.cast_add, Nat.cast_one] using
    natSquare_mul_log_gradient_rate_tendsto_zero C

/-- Local uniform convergence of the interpolants transfers to the literal
floor-grid orbit readout, with no remaining interpolation-error premise. -/
theorem orbitScaledGrid_floor_readout_tendsto_of_gradient
    (m : ℕ) (p₀ : ProbabilityMass) (C : ℝ)
    (k : ℕ) (phi : ℕ → ℕ)
    (g : BoundedContinuousFunction (gridExhaustionRectangle k) ℝ)
    (x : ℝ) (hx : (1, x) ∈ gridExhaustionRectangle k)
    (hphi_cofinal : Tendsto phi atTop atTop)
    (huniform : TendstoUniformly
      (fun n (p : gridExhaustionRectangle k) ↦
        gridBilinearInterp (phi n) (orbitScaledGrid m p₀ (phi n))
          (p : ℝ × ℝ).1 (p : ℝ × ℝ).2)
      (fun p ↦ g p) atTop)
    (hgradient : ∀ n : ℕ,
      WeightedSupThreeLE (profileScale n)
        (discreteDerivative (positiveTiltedDensity m (orbit m p₀ n)))
        (C * Real.log ((n : ℝ) + 2) / profileScale n ^ 3)) :
    Tendsto
      (fun n ↦ orbitScaledGrid m p₀ (phi n) (phi n)
        (gridIndex (phi n) x)) atTop (𝓝 (g ⟨(1, x), hx⟩)) := by
  exact gridNodeReadout_tendsto_of_uniformOn_exhaustion
    k (orbitScaledGrid m p₀) phi g (orbitScaledGridStepError C) x hx
      hphi_cofinal huniform
      (orbitScaledGrid_adjacent_le_of_gradient m p₀ C hgradient)
      ((orbitScaledGridStepError_tendsto_zero C).comp hphi_cofinal)

/-- Combined U13 package: one cofinal diagonal subsequence converges uniformly
on every exhaustion rectangle, and all of its terminal floor-grid readouts
converge to the corresponding local limits. -/
theorem exists_orbitScaledGrid_diagonal_subsequence_and_readout
    (m : ℕ) (p₀ : ProbabilityMass) (C : ℝ)
    (hbound : ∀ k, EventuallyUniformlyBoundedOn
      (fun N p ↦ gridBilinearInterp N (orbitScaledGrid m p₀ N) p.1 p.2)
      (gridExhaustionRectangle k))
    (hequicontinuous : ∀ k, EventuallyEquicontinuousOnL1
      (fun N p ↦ gridBilinearInterp N (orbitScaledGrid m p₀ N) p.1 p.2)
      (gridExhaustionRectangle k))
    (hgradient : ∀ n : ℕ,
      WeightedSupThreeLE (profileScale n)
        (discreteDerivative (positiveTiltedDensity m (orbit m p₀ n)))
        (C * Real.log ((n : ℝ) + 2) / profileScale n ^ 3)) :
    ∃ g : ∀ k, BoundedContinuousFunction (gridExhaustionRectangle k) ℝ,
      ∃ phi : ℕ → ℕ,
        StrictMono phi ∧ Tendsto phi atTop atTop ∧
          (∀ k, TendstoUniformly
            (fun n (p : gridExhaustionRectangle k) ↦
              gridBilinearInterp (phi n) (orbitScaledGrid m p₀ (phi n))
                (p : ℝ × ℝ).1 (p : ℝ × ℝ).2)
            (fun p ↦ g k p) atTop) ∧
          ∀ k x (hx : (1, x) ∈ gridExhaustionRectangle k),
            Tendsto
              (fun n ↦ orbitScaledGrid m p₀ (phi n) (phi n)
                (gridIndex (phi n) x)) atTop (𝓝 (g k ⟨(1, x), hx⟩)) := by
  obtain ⟨g, phi, hmono, hcofinal, huniform⟩ :=
    exists_gridBilinearInterp_diagonal_subsequence
      (orbitScaledGrid m p₀) hbound hequicontinuous
  refine ⟨g, phi, hmono, hcofinal, huniform, ?_⟩
  intro k x hx
  exact orbitScaledGrid_floor_readout_tendsto_of_gradient
    m p₀ C k phi (g k) x hx hcofinal (huniform k) hgradient

end

end DerridaRetaux
