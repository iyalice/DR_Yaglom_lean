import DerridaRetaux.Analysis.DensityMassFixedCutoff
import Mathlib.Tactic

set_option autoImplicit false

open Filter Topology

namespace DerridaRetaux

noncomputable section

/-!
# Total mass directly from compact profile convergence

This file completes the Riemann-sum and tail passage in unnumbered obligation
`U15`.  Compact-uniform profile convergence is kept as a literal family of
estimates.  For each fixed macroscopic cutoff `M`, it gives the prefix `l1`
error required by `DensityMassFixedCutoff`; the cubic weighted estimate controls
the remaining source tail uniformly in the generation.
-/

/-- Compact-uniform convergence supplies the integrated prefix error on every
fixed window `j < M(n+1)`. -/
theorem densityProfilePrefixL1Error_linearCutoff_tendsto_zero_of_compact
    (f : ℕ → Seq)
    (hprofile : ∀ R : ℝ, 0 ≤ R → ∃ error : ℕ → ℝ,
      Tendsto error atTop (nhds 0) ∧
        ∀ n : ℕ, 0 < n → ∀ x : ℝ, 0 ≤ x → x ≤ R →
          |(n : ℝ) ^ 2 * f n (gridIndex n x) -
            4 * Real.exp (-2 * x)| ≤ error n)
    (M : ℕ) :
    Tendsto
      (densityProfilePrefixL1Error f (linearProfileCutoff M))
      atTop (nhds 0) := by
  by_cases hM : M = 0
  · subst M
    have hzero :
        densityProfilePrefixL1Error f (linearProfileCutoff 0) =
          fun _n : ℕ ↦ 0 := by
      funext n
      simp [densityProfilePrefixL1Error, linearProfileCutoff]
    rw [hzero]
    exact tendsto_const_nhds
  · let R : ℝ := 2 * (M : ℝ)
    have hR : 0 ≤ R := by
      dsimp only [R]
      positivity
    obtain ⟨error, herror, hprofileR⟩ := hprofile R hR
    have hdiscrete : ∀ n : ℕ, 0 < n → ∀ j : ℕ,
        j < linearProfileCutoff M n →
          |(n : ℝ) ^ 2 * f n j -
            4 * Real.exp (-2 * ((j : ℝ) / (n : ℝ)))| ≤ error n := by
      intro n hn j hj
      have hnReal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      have hcutoffNat : linearProfileCutoff M n ≤ 2 * M * n := by
        dsimp only [linearProfileCutoff]
        have hsucc : n + 1 ≤ 2 * n := by omega
        nlinarith
      have hjNat : j ≤ 2 * M * n :=
        (Nat.le_of_lt hj).trans hcutoffNat
      have hjReal : (j : ℝ) ≤ 2 * (M : ℝ) * (n : ℝ) := by
        exact_mod_cast hjNat
      have hxnonneg : 0 ≤ (j : ℝ) / (n : ℝ) :=
        div_nonneg (Nat.cast_nonneg j) hnReal.le
      have hxR : (j : ℝ) / (n : ℝ) ≤ R := by
        rw [div_le_iff₀ hnReal]
        dsimp only [R]
        linarith
      have hbound := hprofileR n hn ((j : ℝ) / (n : ℝ)) hxnonneg hxR
      simpa only [gridIndex_at_node n j hn] using hbound
    have hintegrated : Tendsto
        (fun n : ℕ ↦
          ((linearProfileCutoff M n : ℝ) / (n : ℝ)) * error n)
        atTop (nhds 0) := by
      simpa only [mul_zero] using
        (linearProfileCutoff_ratio_tendsto M).mul herror
    exact densityProfilePrefixL1Error_tendsto_zero_of_uniform
      f (linearProfileCutoff M) error hdiscrete hintegrated

/-- Orbit specialization: compact profile convergence and the two approved H1
facts imply the total shifted-density mass limit, with no diagonal-rate premise. -/
theorem orbit_densityTotalMass_tendsto_two_of_compact_profile
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p₀) (hthird : TiltSummable m 3 p₀)
    (hnonconstant : ¬ IsDirac p₀)
    (hExcess : CDHLSExcessFact m p₀ hm hcrit hthird hnonconstant)
    (hProduct : CDHLSProductFact m p₀ hm hcrit hnonconstant)
    (hprofile : ∀ R : ℝ, 0 ≤ R → ∃ error : ℕ → ℝ,
      Tendsto error atTop (nhds 0) ∧
        ∀ n : ℕ, 0 < n → ∀ x : ℝ, 0 ≤ x → x ≤ R →
          |(n : ℝ) ^ 2 * rho m (orbit m p₀ n) (gridIndex n x) -
            4 * Real.exp (-2 * x)| ≤ error n) :
    Tendsto
      (fun n : ℕ ↦ (n : ℝ) * densityTotalMass m (orbit m p₀ n))
      atTop (nhds 2) := by
  apply orbit_densityTotalMass_tendsto_two_of_fixed_windows
    m p₀ hm hcrit hthird hnonconstant hExcess hProduct
  intro M
  exact densityProfilePrefixL1Error_linearCutoff_tendsto_zero_of_compact
    (fun n ↦ rho m (orbit m p₀ n)) hprofile M

/-- The same compact-profile bridge gives the normalization of the positive
tilted mass used in `eq:main1`. -/
theorem orbit_positiveTiltMass_tendsto_of_compact_profile
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p₀) (hthird : TiltSummable m 3 p₀)
    (hnonconstant : ¬ IsDirac p₀)
    (hExcess : CDHLSExcessFact m p₀ hm hcrit hthird hnonconstant)
    (hProduct : CDHLSProductFact m p₀ hm hcrit hnonconstant)
    (hprofile : ∀ R : ℝ, 0 ≤ R → ∃ error : ℕ → ℝ,
      Tendsto error atTop (nhds 0) ∧
        ∀ n : ℕ, 0 < n → ∀ x : ℝ, 0 ≤ x → x ≤ R →
          |(n : ℝ) ^ 2 * rho m (orbit m p₀ n) (gridIndex n x) -
            4 * Real.exp (-2 * x)| ≤ error n) :
    Tendsto
      (fun n : ℕ ↦ (n : ℝ) * positiveTiltMass m (orbit m p₀ n))
      atTop (nhds (2 / ((m : ℝ) - 1))) := by
  have horbitCrit : ∀ n : ℕ, Critical m (orbit m p₀ n) :=
    fun n ↦ orbit_critical m p₀ (by omega) hcrit n
  apply scaledPositiveTiltMass_tendsto_of_densityTotalMass
    m (orbit m p₀) hm horbitCrit 2
  exact orbit_densityTotalMass_tendsto_two_of_compact_profile
    m p₀ hm hcrit hthird hnonconstant hExcess hProduct hprofile

end

end DerridaRetaux
