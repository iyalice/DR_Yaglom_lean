import DerridaRetaux.Analysis.ConditionalTV
import DerridaRetaux.Analysis.ProfileConsequences
import Mathlib.Tactic

set_option autoImplicit false

open Asymptotics Filter Topology

namespace DerridaRetaux

/-!
# Asymptotic readout normalization

This module turns the exact survival readout into the eventual denominator lower
bound needed for the conditional-law estimate.  It assumes only the already
separated partition, survival, and gradient conclusions.
-/

noncomputable section

/-- Exact survival and partition limits determine the scaled geometric readout. -/
theorem scaledSurvivalReadout_tendsto
    (m : ℕ) (p : ℕ → ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : ∀ n : ℕ, Critical m (p n)) (P : ℝ)
    (hpartition : Tendsto
      (fun n : ℕ ↦ tiltedPartition m (p n)) atTop (𝓝 1))
    (hsurvival : Tendsto
      (fun n : ℕ ↦ (n : ℝ) ^ 2 * survival (p n)) atTop (𝓝 P)) :
    Tendsto
      (fun n : ℕ ↦ (n : ℝ) ^ 2 * survivalReadout m (p n)) atTop
      (𝓝 (((m : ℝ) - 1) * P)) := by
  have hfactor : (m : ℝ) - 1 ≠ 0 := by
    have hmReal : (1 : ℝ) < (m : ℝ) := by exact_mod_cast (show 1 < m by omega)
    linarith
  have hconst :
      Tendsto (fun _ : ℕ ↦ (m : ℝ) - 1) atTop (𝓝 ((m : ℝ) - 1)) :=
    tendsto_const_nhds
  have hnumerator := hconst.mul hsurvival
  have hquotient := hnumerator.div hpartition one_ne_zero
  convert hquotient using 1
  · funext n
    have hG := normalizedTilt_denominator_pos m (p n) (by omega) (hcrit n)
    have hreadout := survival_eq_partition_mul_readout m (p n) hm (hcrit n)
    change
      (n : ℝ) ^ 2 * survivalReadout m (p n) =
        ((m : ℝ) - 1) * ((n : ℝ) ^ 2 * survival (p n)) /
          tiltedPartition m (p n)
    rw [hreadout]
    field_simp only [hG.ne', hfactor]
    ring
  · ring

/-- A positive limit of `n² a_n` gives an eventual lower bound on the source
normalization at the natural `(n+1)⁻²` scale. -/
theorem eventually_inverseSquare_lower_of_scaled_tendsto_pos
    (a : ℕ → ℝ) (c : ℝ) (hc : 0 < c)
    (h : Tendsto (fun n : ℕ ↦ (n : ℝ) ^ 2 * a n) atTop (𝓝 c)) :
    ∀ᶠ n : ℕ in atTop,
      (c / 2) / ((n + 1 : ℕ) : ℝ) ^ 2 ≤ a n := by
  have hlower :
      ∀ᶠ n : ℕ in atTop, c / 2 < (n : ℝ) ^ 2 * a n :=
    (tendsto_order.1 h).1 (c / 2) (by linarith)
  filter_upwards [hlower, eventually_ge_atTop (1 : ℕ)] with n hn hnOne
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast (show 0 < n by omega)
  have hsuccPos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have haPos : 0 < a n := by
    have hnSq : 0 < (n : ℝ) ^ 2 := sq_pos_of_pos hnpos
    nlinarith
  apply (div_le_iff₀ (sq_pos_of_pos hsuccPos)).2
  have hsquares : (n : ℝ) ^ 2 ≤ ((n + 1 : ℕ) : ℝ) ^ 2 := by
    norm_num only [Nat.cast_add, Nat.cast_one]
    nlinarith
  nlinarith [mul_le_mul_of_nonneg_right hsquares haPos.le]

/-- The exact `eq:tv` big-O consequence from a positive scaled-readout limit and
the logarithmic gradient estimate. -/
theorem conditionalPositiveL1Error_isBigO_of_scaled_readout_gradient
    (m : ℕ) (p : ℕ → ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : ∀ n : ℕ, Critical m (p n))
    (c D : ℝ) (hc : 0 < c) (hD : 0 ≤ D)
    (B : ℕ → ℝ)
    (hreadout : Tendsto
      (fun n : ℕ ↦ (n : ℝ) ^ 2 * survivalReadout m (p n)) atTop (𝓝 c))
    (hgradient : ∀ n : ℕ,
      B n ≤ D * Real.log ((n + 2 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 3)
    (hdelta : ∀ n : ℕ,
      SupLE (discreteDerivative (rho m (p n))) (B n)) :
    (fun n : ℕ ↦ conditionalPositiveL1Error m (p n)) =O[atTop]
      (fun n : ℕ ↦ Real.log ((n + 2 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ)) := by
  let K : ℝ := 2 * D / ((c / 2) * ((m : ℝ) - 1) ^ 2)
  refine isBigO_iff.mpr ⟨K, ?_⟩
  have hlower := eventually_inverseSquare_lower_of_scaled_tendsto_pos
    (fun n ↦ survivalReadout m (p n)) c hc hreadout
  filter_upwards [hlower] with n hn
  have hbound := conditionalPositiveL1Error_profile_scale_le
    m (p n) hm (hcrit n) n (c / 2) D (B n) (by linarith) hD
      hn (hgradient n) (hdelta n)
  have herrorNonneg := conditionalPositiveL1Error_nonneg m (p n)
  have hlog : 0 ≤ Real.log ((n + 2 : ℕ) : ℝ) := by
    apply Real.log_nonneg
    exact_mod_cast (show 1 ≤ n + 2 by omega)
  have hrate :
      0 ≤ Real.log ((n + 2 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ) :=
    div_nonneg hlog (Nat.cast_nonneg _)
  rw [Real.norm_eq_abs, abs_of_nonneg herrorNonneg,
    Real.norm_eq_abs, abs_of_nonneg hrate]
  simpa only [K, div_eq_mul_inv, mul_assoc] using hbound

/-- Orbit wrapper: the partition and survival limits make the readout positive at
scale `n⁻²`, so the gradient bound alone yields the conditional geometric rate. -/
theorem orbit_conditionalPositiveL1Error_isBigO
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p₀) (D : ℝ) (hD : 0 ≤ D)
    (B : ℕ → ℝ)
    (hpartition : Tendsto
      (fun n : ℕ ↦ tiltedPartition m (orbit m p₀ n)) atTop (𝓝 1))
    (hsurvival : Tendsto
      (fun n : ℕ ↦ (n : ℝ) ^ 2 * survival (orbit m p₀ n)) atTop
      (𝓝 (4 / ((m : ℝ) - 1) ^ 2)))
    (hgradient : ∀ n : ℕ,
      B n ≤ D * Real.log ((n + 2 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 3)
    (hdelta : ∀ n : ℕ,
      SupLE
        (discreteDerivative (rho m (orbit m p₀ n))) (B n)) :
    (fun n : ℕ ↦ conditionalPositiveL1Error m (orbit m p₀ n)) =O[atTop]
      (fun n : ℕ ↦ Real.log ((n + 2 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ)) := by
  have hfactor : 0 < (m : ℝ) - 1 := by
    have hmReal : (1 : ℝ) < (m : ℝ) := by exact_mod_cast (show 1 < m by omega)
    linarith
  have hreadout := scaledSurvivalReadout_tendsto
    m (orbit m p₀) hm
      (fun n ↦ orbit_critical m p₀ (by omega) hcrit n)
      (4 / ((m : ℝ) - 1) ^ 2) hpartition hsurvival
  have hreadoutValue :
      ((m : ℝ) - 1) * (4 / ((m : ℝ) - 1) ^ 2) =
        4 / ((m : ℝ) - 1) := by
    field_simp only [hfactor.ne']
    ring
  rw [hreadoutValue] at hreadout
  exact conditionalPositiveL1Error_isBigO_of_scaled_readout_gradient
    m (orbit m p₀) hm
      (fun n ↦ orbit_critical m p₀ (by omega) hcrit n)
      (4 / ((m : ℝ) - 1)) D (div_pos (by norm_num) hfactor) hD
      B hreadout hgradient hdelta

end

end DerridaRetaux
