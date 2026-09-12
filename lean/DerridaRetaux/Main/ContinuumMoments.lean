import DerridaRetaux.HumanInputs
import DerridaRetaux.Analysis.GluedLimitProperties
import DerridaRetaux.Analysis.GluedTimeSliceOrbit
import DerridaRetaux.Analysis.HalfLineMomentTransfer
import DerridaRetaux.Analysis.OrbitMomentBound
import DerridaRetaux.Prelim.WeightedMassOrbit

set_option autoImplicit false

open Filter Set Topology MeasureTheory

namespace DerridaRetaux.FixedArity

noncomputable section

/-- Every moment of order at most three of a positive-time subsequential
continuum profile is finite.  The uniform discrete tail control is supplied
by H1a and H1b. -/
theorem subsequentialMoment_integrable
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
    ∀ t : ℝ, 0 < t → ∀ r : ℕ, r ≤ 3 →
      IntegrableOn
        (fun x : ℝ ↦ x ^ r * gluedExhaustionLimit g t x)
        (Ici (0 : ℝ)) := by
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
  let F : ℕ → (ℝ × ℝ) → ℝ := fun N p ↦
    gridBilinearInterp N (orbitScaledGrid m p₀ N) p.1 p.2
  have hcompat : ∀ {k l : ℕ}, ∀ hkl : k ≤ l,
      ∀ p : gridExhaustionRectangle k,
        g k p = g l ⟨(p : ℝ × ℝ),
          gridExhaustionRectangle_mono hkl p.property⟩ := by
    intro k l hkl p
    exact exhaustionLimits_compatible F phi g hlim hkl p
  intro t ht r hr
  let rhoN : ℕ → Seq := fun n ↦ positiveTiltedDensity m
    (orbit m p₀ (gridIndex (phi n) t))
  have hlocal : LocallyUniformLatticeDensity rhoN phi
      (fun x ↦ gluedExhaustionLimit g t x) := by
    exact locallyUniformLatticeDensity_orbit_of_gluedExhaustion_at_time
      m p₀ phi g t ht hphi hlim
  have hrho : ∀ n j : ℕ, 0 ≤ rhoN n j := by
    intro n j
    exact positiveTiltedDensity_nonneg m
      (orbit m p₀ (gridIndex (phi n) t)) (by omega)
      (orbit_critical m p₀ (by omega) hcrit _) j
  have hmoment : ∀ n : ℕ,
      Summable (fun j : ℕ ↦ (j : ℝ) ^ r * rhoN n j) := by
    intro n
    let s := gridIndex (phi n) t
    have hscrit := orbit_critical m p₀ (by omega) hcrit s
    have hsthird := orbit_tiltSummable_three
      m p₀ (by omega) hcrit hthird s
    have hzero := (positiveTiltedDensity_hasSum
      m (orbit m p₀ s) (by omega) hscrit).summable
    have hthree := positiveTiltedDensity_third_summable
      m (orbit m p₀ s) (by omega) hscrit hsthird
    simpa only [rhoN, s] using
      moment_summable_of_zero_and_third
        (positiveTiltedDensity m (orbit m p₀ s)) r hr
          (positiveTiltedDensity_nonneg m (orbit m p₀ s)
            (by omega) hscrit) hzero hthree
  obtain ⟨C, hbound⟩ :=
    orbit_scaledDiscreteMoment_eventually_bounded_of_weightedL1
      m p₀ hm hcrit hthird A hA.le hL1 phi hphi t ht r hr
  exact integrableOn_pow_mul_of_locallyUniform_and_momentBound_Ici
    rhoN phi (fun x ↦ gluedExhaustionLimit g t x) r hr C hphi
      (continuousOn_gluedExhaustionLimit_timeSlice_Ici g hcompat t ht)
      (fun x hx ↦ gluedExhaustionLimit_nonneg
        m p₀ hm hcrit phi g hphi hlim ht hx)
      hlocal hrho hmoment hbound

end

end DerridaRetaux.FixedArity
