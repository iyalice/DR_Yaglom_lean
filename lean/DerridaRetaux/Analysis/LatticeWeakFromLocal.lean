import DerridaRetaux.Analysis.MomentConvergence

set_option autoImplicit false

open Filter Set Topology MeasureTheory
open scoped BoundedContinuousFunction

namespace DerridaRetaux

noncomputable section

/-- Local density convergence plus convergence of total mass gives weak
convergence of the associated scaled lattice measures to the density measure. -/
theorem scaledLatticeMeasuresAlong_tendsto_of_locallyUniform_and_mass
    (rho : ℕ → Seq) (scale : ℕ → ℕ) (u : ℝ → ℝ)
    (hscale : Tendsto scale atTop atTop)
    (hucont : ContinuousOn u (Ici (0 : ℝ)))
    (huneg : ∀ x : ℝ, x < 0 → u x = 0)
    (hu : ∀ x : ℝ, 0 ≤ u x)
    (hint : Integrable u volume)
    (hlocal : LocallyUniformLatticeDensity rho scale u)
    (hrho : ∀ n j : ℕ, 0 ≤ rho n j)
    (hsum : ∀ n : ℕ, Summable (rho n))
    (hmass : Tendsto
      (fun n : ℕ ↦ scaledDiscreteMoment (rho n) 0 (scale n))
      atTop (nhds (continuumMoment u 0))) :
    Tendsto (scaledLatticeMeasuresAlong rho scale hrho hsum) atTop
      (nhds (finiteDensityMeasure u hu hint)) := by
  have hcompact : ∀ test : ℝ →ᵇ ℝ, HasCompactSupport test →
      Tendsto
        (fun n : ℕ ↦ ∑' j : ℕ,
          (scale n : ℝ) * rho n j * test ((j : ℝ) / (scale n : ℝ)))
        atTop (nhds (∫ x, u x * test x)) := by
    intro test htest
    exact compact_lattice_sums_tendsto_of_locallyUniform
      rho scale u hscale hucont huneg hlocal test htest
  have hintegral : (∫ x, u x) = continuumMoment u 0 := by
    unfold continuumMoment
    rw [← integral_indicator measurableSet_Ici]
    apply integral_congr_ae
    filter_upwards with x
    by_cases hx : 0 ≤ x
    · have hxmem : x ∈ Ici (0 : ℝ) := hx
      rw [indicator_of_mem hxmem]
      simp
    · have hxneg : x < 0 := lt_of_not_ge hx
      have hxnot : x ∉ Ici (0 : ℝ) := hx
      rw [indicator_of_not_mem hxnot, huneg x hxneg]
  have hmass' : Tendsto
      (fun n : ℕ ↦ (scale n : ℝ) * ∑' j : ℕ, rho n j)
      atTop (nhds (∫ x, u x)) := by
    rw [hintegral]
    simpa only [scaledDiscreteMoment, pow_zero, div_one, one_mul] using hmass
  exact scaledLatticeMeasuresAlong_tendsto_finiteDensityMeasure
    rho scale u hrho hsum hu hint hcompact hmass'

end

end DerridaRetaux
