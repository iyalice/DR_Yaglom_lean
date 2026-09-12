import DerridaRetaux.Analysis.ProfileConsequences
import Mathlib.Tactic

set_option autoImplicit false

open Filter Topology
open scoped BigOperators

namespace DerridaRetaux

/-!
# Total-density and excess consequences

These are the elementary limit passages after compact profile convergence.  The
global density-mass limit is kept explicit: proving it from local convergence and
the cubic tail estimate remains a separate compactness/uniform-integrability task.
-/

noncomputable section

/-- Total mass of the shifted tilted density. -/
def densityTotalMass (m : ℕ) (p : ProbabilityMass) : ℝ :=
  ∑' j : ℕ, rho m p j

/-- Exact normalization of the total shifted density. -/
theorem densityTotalMass_eq_tiltFactor_mul_positiveTiltMass
    (m : ℕ) (p : ProbabilityMass) (hm : 1 ≤ m)
    (hcrit : Critical m p) :
    densityTotalMass m p =
      ((m : ℝ) - 1) * positiveTiltMass m p := by
  exact (positiveTiltedDensity_hasSum m p hm hcrit).tsum_eq

/-- Rearranged form of the exact identity
`theta = (epsilon + p) / G`. -/
theorem excess_eq_partition_mul_positiveTiltMass_sub_survival
    (m : ℕ) (p : ProbabilityMass) (hm : 1 ≤ m)
    (hcrit : Critical m p) :
    excess m p =
      tiltedPartition m p * positiveTiltMass m p - survival p := by
  have hG := normalizedTilt_denominator_pos m p hm hcrit
  have htheta := positiveTiltMass_eq_excess_add_survival_div m p hm hcrit
  apply (eq_sub_iff_add_eq).2
  rw [htheta]
  field_simp only [hG.ne']
  ring

/-- A scaled total-density limit gives the corresponding scaled positive-tilt
mass limit. -/
theorem scaledPositiveTiltMass_tendsto_of_densityTotalMass
    (m : ℕ) (p : ℕ → ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : ∀ n : ℕ, Critical m (p n)) (c : ℝ)
    (hmass : Tendsto
      (fun n : ℕ ↦ (n : ℝ) * densityTotalMass m (p n)) atTop (𝓝 c)) :
    Tendsto
      (fun n : ℕ ↦ (n : ℝ) * positiveTiltMass m (p n)) atTop
      (𝓝 (c / ((m : ℝ) - 1))) := by
  have hfactor : (m : ℝ) - 1 ≠ 0 := by
    have hmReal : (1 : ℝ) < (m : ℝ) := by exact_mod_cast (show 1 < m by omega)
    linarith
  have hscaled := hmass.mul_const (((m : ℝ) - 1)⁻¹)
  convert hscaled using 1
  · funext n
    rw [densityTotalMass_eq_tiltFactor_mul_positiveTiltMass
      m (p n) (by omega) (hcrit n)]
    field_simp only [hfactor]
    ring

/-- Every finite quadratic-scale limit implies that the corresponding linear
scale vanishes. -/
theorem nat_mul_tendsto_zero_of_natSquare_mul_tendsto
    (u : ℕ → ℝ) (c : ℝ)
    (h : Tendsto (fun n : ℕ ↦ (n : ℝ) ^ 2 * u n) atTop (𝓝 c)) :
    Tendsto (fun n : ℕ ↦ (n : ℝ) * u n) atTop (𝓝 0) := by
  have hinv : Tendsto (fun n : ℕ ↦ ((n : ℝ))⁻¹) atTop (𝓝 0) := by
    simpa only [one_div] using tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)
  have hproduct :
      Tendsto
        (fun n : ℕ ↦ ((n : ℝ) ^ 2 * u n) * (n : ℝ)⁻¹)
        atTop (𝓝 0) := by
    simpa only [mul_zero] using h.mul hinv
  apply hproduct.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by
    exact_mod_cast (show n ≠ 0 by omega)
  field_simp only [hn0]
  ring

/-- The exact scalar identity transfers limits of `G_n`, `n theta_n`, and
`n p_n` to the first conclusion in `eq:main1`. -/
theorem scaledExcess_tendsto_of_partition_positiveTilt_survival
    (m : ℕ) (p : ℕ → ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : ∀ n : ℕ, Critical m (p n)) (c : ℝ)
    (hpartition : Tendsto
      (fun n : ℕ ↦ tiltedPartition m (p n)) atTop (𝓝 1))
    (htheta : Tendsto
      (fun n : ℕ ↦ (n : ℝ) * positiveTiltMass m (p n)) atTop (𝓝 c))
    (hsurvival : Tendsto
      (fun n : ℕ ↦ (n : ℝ) * survival (p n)) atTop (𝓝 0)) :
    Tendsto
      (fun n : ℕ ↦ (n : ℝ) * excess m (p n)) atTop (𝓝 c) := by
  have hproduct := hpartition.mul htheta
  have hdifference :
      Tendsto
        (fun n : ℕ ↦
          tiltedPartition m (p n) *
              ((n : ℝ) * positiveTiltMass m (p n)) -
            (n : ℝ) * survival (p n))
        atTop (𝓝 c) := by
    simpa only [one_mul, sub_zero] using hproduct.sub hsurvival
  convert hdifference using 1
  funext n
  rw [excess_eq_partition_mul_positiveTiltMass_sub_survival
    m (p n) (by omega) (hcrit n)]
  ring

/-- Combined orbit consequence: total tilted-density mass `2/n`, partition
convergence, and quadratic survival scaling imply
`n (G_n - 1) -> 2/(m-1)`. -/
theorem orbit_scaledExcess_tendsto_of_densityMass_and_survival
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p₀) (survivalLimit : ℝ)
    (hmass : Tendsto
      (fun n : ℕ ↦
        (n : ℝ) * densityTotalMass m (orbit m p₀ n)) atTop (𝓝 2))
    (hpartition : Tendsto
      (fun n : ℕ ↦ tiltedPartition m (orbit m p₀ n)) atTop (𝓝 1))
    (hsurvival : Tendsto
      (fun n : ℕ ↦
        (n : ℝ) ^ 2 * survival (orbit m p₀ n)) atTop
      (𝓝 survivalLimit)) :
    Tendsto
      (fun n : ℕ ↦ (n : ℝ) * excess m (orbit m p₀ n)) atTop
      (𝓝 (2 / ((m : ℝ) - 1))) := by
  have hcritOrbit : ∀ n : ℕ, Critical m (orbit m p₀ n) :=
    fun n ↦ orbit_critical m p₀ (by omega) hcrit n
  apply scaledExcess_tendsto_of_partition_positiveTilt_survival
    m (orbit m p₀) hm hcritOrbit (2 / ((m : ℝ) - 1)) hpartition
  · exact scaledPositiveTiltMass_tendsto_of_densityTotalMass
      m (orbit m p₀) hm hcritOrbit 2 hmass
  · exact nat_mul_tendsto_zero_of_natSquare_mul_tendsto
      (fun n ↦ survival (orbit m p₀ n)) survivalLimit hsurvival

end

end DerridaRetaux
