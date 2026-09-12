import DerridaRetaux.HumanInputs
import DerridaRetaux.Analysis.MildEquation
import DerridaRetaux.Analysis.PointwiseFromFar
import DerridaRetaux.Analysis.TruncatedSmoothingBounds
import DerridaRetaux.Prelim.WeightedMassOrbit

set_option autoImplicit false

open Filter Set Topology MeasureTheory

namespace DerridaRetaux.FixedArity

noncomputable section

/-- Source-facing equation `eq:mild` for an arbitrary glued subsequential
limit. All weighted bounds needed to remove the higher sources are discharged
from H1a and H1b inside the wrapper. -/
theorem subsequentialMildEquation
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p₀) (hthird : TiltSummable m 3 p₀)
    (hnotBinaryFixedPoint : ¬ (m = 2 ∧ p₀ = diracMass 1))
    (phi : ℕ → ℕ)
    (g : ∀ k, BoundedContinuousFunction (gridExhaustionRectangle k) ℝ)
    (hphi : Tendsto phi atTop atTop)
    (hlim : ∀ k, TendstoUniformly
      (fun n (p : gridExhaustionRectangle k) ↦
        gridBilinearInterp (phi n) (orbitScaledGrid m p₀ (phi n))
          (p : ℝ × ℝ).1 (p : ℝ × ℝ).2)
      (fun p ↦ g k p) atTop) :
    ∀ t₀ t x : ℝ, 0 < t₀ → t₀ ≤ t → 0 ≤ x →
      gluedExhaustionLimit g t x =
        gluedExhaustionLimit g t₀ (x + t - t₀) +
          ∫ s in t₀..t, (1 / 2 : ℝ) * positiveSelfConvolution
            (fun y ↦ gluedExhaustionLimit g s y) (x + t - s) := by
  have hnonconstant : ¬ IsDirac p₀ := by
    intro hdirac
    exact hnotBinaryFixedPoint
      (critical_isDirac_eq_binary m p₀ hm hcrit hdirac)
  let hExcess := HumanInputs.cdhls_excess_upper
    m p₀ hm hcrit hthird hnonconstant
  let hProduct := HumanInputs.cdhls_product_upper
    m p₀ hm hcrit hnonconstant
  obtain ⟨A, hA, hL1, _hfirst⟩ :=
    positiveTiltedDensity_weightedMass_orbit
      m p₀ hm hcrit hthird hnonconstant hExcess hProduct
  obtain ⟨B, hB, hpointwiseRaw⟩ :=
    positiveTiltedDensity_pointwise_of_H1
      m p₀ hm hcrit hthird hnonconstant hExcess hProduct
  have hpointwise : ∀ n j : ℕ,
      positiveTiltedDensity m (orbit m p₀ n) j ≤
        B * profileScale n / ((n + j + 1 : ℕ) : ℝ) ^ 3 := by
    simpa only [profileScale] using hpointwiseRaw
  have hSup : ∀ n : ℕ, WeightedSupThreeLE (profileScale n)
      (positiveTiltedDensity m (orbit m p₀ n))
      (B / profileScale n ^ 2) :=
    positiveTiltedDensity_weightedSup_of_pointwise
      m p₀ hm hcrit B hB.le hpointwise
  intro t₀ t x ht₀ ht hx
  exact gluedExhaustionLimit_mild_of_H1a
    m p₀ hm hcrit hthird hnonconstant hExcess
      A B hA.le hB.le hL1 hSup phi g t₀ t x ht₀ ht hx hphi hlim

end

end DerridaRetaux.FixedArity
