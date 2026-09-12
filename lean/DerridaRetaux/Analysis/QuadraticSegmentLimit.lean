import DerridaRetaux.Analysis.QuadraticDuhamelRiemann
import DerridaRetaux.Analysis.QuadraticDuhamelScaling

set_option autoImplicit false

open Filter Set Topology MeasureTheory

namespace DerridaRetaux

noncomputable section

/-- Source-facing limit of the rescaled quadratic Duhamel segment. -/
theorem scaled_densityQuadraticSegment_tendsto_of_H1a
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p₀) (hthird : TiltSummable m 3 p₀)
    (hnonconstant : ¬ IsDirac p₀)
    (hExcess : CDHLSExcessFact m p₀ hm hcrit hthird hnonconstant)
    (phi : ℕ → ℕ)
    (g : ∀ k, BoundedContinuousFunction (gridExhaustionRectangle k) ℝ)
    (t₀ t x : ℝ) (R : ℕ)
    (ht₀ : 0 < t₀) (ht : t₀ ≤ t) (hx : 0 < x)
    (hR : x + t + 1 ≤ (R : ℝ))
    (hphi : Tendsto phi atTop atTop)
    (hlim : ∀ k, TendstoUniformly
      (fun n (p : gridExhaustionRectangle k) ↦
        gridBilinearInterp (phi n) (orbitScaledGrid m p₀ (phi n))
          (p : ℝ × ℝ).1 (p : ℝ × ℝ).2)
      (fun p ↦ g k p) atTop) :
    Tendsto
      (fun n ↦ (phi n : ℝ) ^ 2 *
        densityQuadraticSegment m p₀
          (gridIndex (phi n) t₀) (gridIndex (phi n) t)
          (gridIndex (phi n) x))
      atTop
      (nhds (∫ s in t₀..t,
        (1 / 2 : ℝ) * positiveSelfConvolution
          (fun y ↦ gluedExhaustionLimit g s y) (x + t - s))) := by
  let F : ℕ → ℕ → ℝ := fun n s ↦
    densityQuadraticWeight m p₀ s (gridIndex (phi n) t) *
      ((phi n : ℝ) ^ 3 *
        conv (positiveTiltedDensity m (orbit m p₀ s))
          (positiveTiltedDensity m (orbit m p₀ s))
          (gridIndex (phi n) x + (gridIndex (phi n) t - 1 - s)))
  have hsum : Tendsto (fun n ↦ gridTimeArraySum F phi n t₀ t) atTop
      (nhds (∫ s in t₀..t,
        (1 / 2 : ℝ) * positiveSelfConvolution
          (fun y ↦ gluedExhaustionLimit g s y) (x + t - s))) := by
    simpa only [F] using quadraticDuhamelGridSum_tendsto_of_H1a
      m p₀ hm hcrit hthird hnonconstant hExcess phi g t₀ t x R
        ht₀ ht hx hR hphi hlim
  apply hsum.congr'
  have hphiPos : ∀ᶠ n : ℕ in atTop, 0 < phi n := by
    have hge := hphi.eventually_ge_atTop 1
    exact hge.mono fun _ hn ↦ by omega
  filter_upwards [hphiPos] with n hn
  symm
  simpa only [F, gridTimeArraySum] using
    (gridTimeArraySum_quadratic_eq_scaled_segment
      m p₀ (phi n) t₀ t x hn ht₀.le (ht₀.le.trans ht)).symm

end

end DerridaRetaux
