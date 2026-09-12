import DerridaRetaux.Analysis.MildEquationBoundary

set_option autoImplicit false

open Filter Set Topology MeasureTheory

namespace DerridaRetaux

noncomputable section

/-- Source-facing continuum mild equation for every nonnegative spatial
point. The compact truncation radius used in the proof is chosen internally. -/
theorem gluedExhaustionLimit_mild_of_H1a
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p₀) (hthird : TiltSummable m 3 p₀)
    (hnonconstant : ¬ IsDirac p₀)
    (hExcess : CDHLSExcessFact m p₀ hm hcrit hthird hnonconstant)
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hL1 : ∀ s : ℕ,
      weightedL1Three (profileScale s)
          (positiveTiltedDensity m (orbit m p₀ s)) ≤
        A / profileScale s)
    (hSup : ∀ s : ℕ,
      WeightedSupThreeLE (profileScale s)
        (positiveTiltedDensity m (orbit m p₀ s))
        (B / profileScale s ^ 2))
    (phi : ℕ → ℕ)
    (g : ∀ k, BoundedContinuousFunction (gridExhaustionRectangle k) ℝ)
    (t₀ t x : ℝ)
    (ht₀ : 0 < t₀) (ht : t₀ ≤ t) (hx : 0 ≤ x)
    (hphi : Tendsto phi atTop atTop)
    (hlim : ∀ k, TendstoUniformly
      (fun n (p : gridExhaustionRectangle k) ↦
        gridBilinearInterp (phi n) (orbitScaledGrid m p₀ (phi n))
          (p : ℝ × ℝ).1 (p : ℝ × ℝ).2)
      (fun p ↦ g k p) atTop) :
    gluedExhaustionLimit g t x =
      gluedExhaustionLimit g t₀ (x + t - t₀) +
        ∫ s in t₀..t, (1 / 2 : ℝ) * positiveSelfConvolution
          (fun y ↦ gluedExhaustionLimit g s y) (x + t - s) := by
  obtain ⟨R, hR⟩ := exists_nat_ge (x + t + 2)
  rcases eq_or_lt_of_le hx with hzero | hxpos
  · subst x
    simpa only [zero_add] using gluedExhaustionLimit_mild_zero_of_H1a
      m p₀ hm hcrit hthird hnonconstant hExcess
      A B hA hB hL1 hSup phi g t₀ t R ht₀ ht
        (by linarith [hR]) hphi hlim
  · exact gluedExhaustionLimit_mild_pos_of_H1a
      m p₀ hm hcrit hthird hnonconstant hExcess
      A B hA hB hL1 hSup phi g t₀ t x R ht₀ ht hxpos
        (by linarith [hR]) hphi hlim

end

end DerridaRetaux
