import DerridaRetaux.Analysis.GridInterpolation
import DerridaRetaux.Analysis.LogRate
import DerridaRetaux.Analysis.ReadoutBounds
import Mathlib.Tactic

set_option autoImplicit false

open Filter Topology

namespace DerridaRetaux

/-!
# Consequences of an explicit compact profile error

This file does not assume or package the main profile theorem.  Instead, each
result takes the literal compact error estimate it needs as a theorem parameter.
It then records the elementary passage from the moving mesh point `j / n` to a
fixed density coefficient and the exact readout of a fixed original-law atom.
-/

noncomputable section

/-- If a sequence stays within an error tending to zero of a convergent comparison
sequence, then it has the same limit. -/
theorem tendsto_of_abs_sub_le_error
    {a b error : ℕ → ℝ} {c : ℝ}
    (hb : Tendsto b atTop (𝓝 c))
    (herror : Tendsto error atTop (𝓝 0))
    (hclose : ∀ᶠ n : ℕ in atTop, |a n - b n| ≤ error n) :
    Tendsto a atTop (𝓝 c) := by
  apply hb.congr_dist
  apply squeeze_zero' (Eventually.of_forall fun _ ↦ dist_nonneg) _ herror
  filter_upwards [hclose] with n hn
  simpa only [Real.dist_eq, abs_sub_comm] using hn

/-- A literal compact-uniform profile error bound, evaluated at the moving mesh
node `x = j / n`, yields the limit of the fixed coefficient `rho_n(j)`.

The compact estimate is intentionally exposed in the hypotheses rather than
hidden behind a proposition-valued definition. -/
theorem fixedDensity_tendsto_of_compact_profile_error
    (m : ℕ) (p₀ : ProbabilityMass) (R : ℝ) (error : ℕ → ℝ) (j : ℕ)
    (hjR : (j : ℝ) ≤ R)
    (herror : Tendsto error atTop (𝓝 0))
    (hprofile : ∀ n : ℕ, 0 < n → ∀ x : ℝ, 0 ≤ x → x ≤ R →
      |(n : ℝ) ^ 2 * rho m (orbit m p₀ n) (gridIndex n x) -
          4 * Real.exp (-2 * x)| ≤ error n) :
    Tendsto
      (fun n : ℕ ↦ (n : ℝ) ^ 2 * rho m (orbit m p₀ n) j)
      atTop (𝓝 4) := by
  let comparison : ℕ → ℝ :=
    fun n ↦ 4 * Real.exp (-2 * ((j : ℝ) / (n : ℝ)))
  have hmesh : Tendsto (fun n : ℕ ↦ (j : ℝ) / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat (j : ℝ)
  have harg :
      Tendsto (fun n : ℕ ↦ -2 * ((j : ℝ) / (n : ℝ))) atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_const_nhds.mul hmesh)
  have hexp :
      Tendsto (fun n : ℕ ↦ Real.exp (-2 * ((j : ℝ) / (n : ℝ))))
        atTop (𝓝 1) := by
    simpa only [Real.exp_zero] using (Real.continuous_exp.tendsto 0).comp harg
  have hcomparison : Tendsto comparison atTop (𝓝 4) := by
    simpa only [comparison, mul_one] using (tendsto_const_nhds.mul hexp)
  apply tendsto_of_abs_sub_le_error hcomparison herror
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hnpos : 0 < n := by omega
  have hnRpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnpos
  have hxnonneg : 0 ≤ (j : ℝ) / (n : ℝ) :=
    div_nonneg (Nat.cast_nonneg j) hnRpos.le
  have hxlej : (j : ℝ) / (n : ℝ) ≤ (j : ℝ) := by
    exact div_le_self (Nat.cast_nonneg j) (by exact_mod_cast hn)
  have hbound := hprofile n hnpos ((j : ℝ) / (n : ℝ)) hxnonneg
    (hxlej.trans hjR)
  simpa only [comparison, gridIndex_at_node n j hnpos] using hbound

/-- The boundary-value consequence of the compact profile estimate. -/
theorem boundaryDensity_tendsto_of_compact_profile_error
    (m : ℕ) (p₀ : ProbabilityMass) (R : ℝ) (error : ℕ → ℝ)
    (hR : 0 ≤ R)
    (herror : Tendsto error atTop (𝓝 0))
    (hprofile : ∀ n : ℕ, 0 < n → ∀ x : ℝ, 0 ≤ x → x ≤ R →
      |(n : ℝ) ^ 2 * rho m (orbit m p₀ n) (gridIndex n x) -
          4 * Real.exp (-2 * x)| ≤ error n) :
    Tendsto
      (fun n : ℕ ↦ (n : ℝ) ^ 2 * rho m (orbit m p₀ n) 0)
      atTop (𝓝 4) := by
  exact fixedDensity_tendsto_of_compact_profile_error
    m p₀ R error 0 (by simpa using hR) herror hprofile

/-- Exact atom readout transfers a fixed-density limit and `G_n → 1` to the
fixed positive-atom asymptotic in source equation `eq:atoms`. -/
theorem fixedAtom_tendsto_of_density_and_partition
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m) (hcrit : Critical m p₀)
    (k : ℕ) (hk : 1 ≤ k)
    (hdensity : Tendsto
      (fun n : ℕ ↦ (n : ℝ) ^ 2 * rho m (orbit m p₀ n) (k - 1))
      atTop (𝓝 4))
    (hpartition : Tendsto
      (fun n : ℕ ↦ tiltedPartition m (orbit m p₀ n)) atTop (𝓝 1)) :
    Tendsto
      (fun n : ℕ ↦ (n : ℝ) ^ 2 * orbit m p₀ n k)
      atTop (𝓝 (4 / (((m : ℝ) - 1) * (m : ℝ) ^ k))) := by
  have hfactor : (m : ℝ) - 1 ≠ 0 := by
    have hmReal : (1 : ℝ) < (m : ℝ) := by exact_mod_cast (show 1 < m by omega)
    linarith
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  have hconstant :
      Tendsto (fun _ : ℕ ↦ ((m : ℝ) ^ k)⁻¹) atTop
        (𝓝 (((m : ℝ) ^ k)⁻¹)) := tendsto_const_nhds
  have hfactorConstant :
      Tendsto (fun _ : ℕ ↦ (((m : ℝ) - 1)⁻¹)) atTop
        (𝓝 (((m : ℝ) - 1)⁻¹)) := tendsto_const_nhds
  have hcoeff :
      Tendsto
        (fun n : ℕ ↦
          tiltedPartition m (orbit m p₀ n) * ((m : ℝ) - 1)⁻¹ *
            ((m : ℝ) ^ k)⁻¹)
        atTop (𝓝 (1 * ((m : ℝ) - 1)⁻¹ * ((m : ℝ) ^ k)⁻¹)) :=
    (hpartition.mul hfactorConstant).mul hconstant
  have hproduct := hcoeff.mul hdensity
  have heq :
      (fun n : ℕ ↦
        (tiltedPartition m (orbit m p₀ n) * ((m : ℝ) - 1)⁻¹ *
            ((m : ℝ) ^ k)⁻¹) *
          ((n : ℝ) ^ 2 * rho m (orbit m p₀ n) (k - 1))) =
      fun n : ℕ ↦ (n : ℝ) ^ 2 * orbit m p₀ n k := by
    funext n
    rw [atom_eq_partition_mul_rho m (orbit m p₀ n) hm
      (orbit_critical m p₀ (by omega) hcrit n) k hk]
    ring
  rw [← heq]
  convert hproduct using 1
  field_simp only [hfactor, pow_ne_zero k hm0]
  ring

/-- Combining the literal compact-profile estimate with the partition limit gives
the full fixed-atom consequence without assuming a packaged profile theorem. -/
theorem fixedAtom_tendsto_of_compact_profile_error
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m) (hcrit : Critical m p₀)
    (R : ℝ) (error : ℕ → ℝ) (k : ℕ) (hk : 1 ≤ k)
    (hkR : ((k - 1 : ℕ) : ℝ) ≤ R)
    (herror : Tendsto error atTop (𝓝 0))
    (hprofile : ∀ n : ℕ, 0 < n → ∀ x : ℝ, 0 ≤ x → x ≤ R →
      |(n : ℝ) ^ 2 * rho m (orbit m p₀ n) (gridIndex n x) -
          4 * Real.exp (-2 * x)| ≤ error n)
    (hpartition : Tendsto
      (fun n : ℕ ↦ tiltedPartition m (orbit m p₀ n)) atTop (𝓝 1)) :
    Tendsto
      (fun n : ℕ ↦ (n : ℝ) ^ 2 * orbit m p₀ n k)
      atTop (𝓝 (4 / (((m : ℝ) - 1) * (m : ℝ) ^ k))) := by
  apply fixedAtom_tendsto_of_density_and_partition m p₀ hm hcrit k hk
  · exact fixedDensity_tendsto_of_compact_profile_error
      m p₀ R error (k - 1) hkR herror hprofile
  · exact hpartition

/-- Any finite limit of `n * (G_n - 1)` already forces `G_n → 1`.
The value of the scaled limit is deliberately left explicit. -/
theorem partition_tendsto_one_of_scaled_excess
    (G : ℕ → ℝ) (c : ℝ)
    (hscaled : Tendsto (fun n : ℕ ↦ (n : ℝ) * (G n - 1)) atTop (𝓝 c)) :
    Tendsto G atTop (𝓝 1) := by
  have hinv : Tendsto (fun n : ℕ ↦ ((n : ℝ))⁻¹) atTop (𝓝 0) := by
    simpa only [one_div] using tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)
  have hproduct :
      Tendsto
        (fun n : ℕ ↦ ((n : ℝ) * (G n - 1)) * ((n : ℝ))⁻¹)
        atTop (𝓝 0) := by
    simpa only [mul_zero] using hscaled.mul hinv
  have heq :
      (fun n : ℕ ↦ ((n : ℝ) * (G n - 1)) * ((n : ℝ))⁻¹) =ᶠ[atTop]
        (fun n : ℕ ↦ G n - 1) := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (by omega : 0 < n))
    field_simp only [hn0]
    ring
  have hsub : Tendsto (fun n : ℕ ↦ G n - 1) atTop (𝓝 0) :=
    Tendsto.congr' heq hproduct
  have hone : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  simpa only [sub_add_cancel, zero_add] using hsub.add hone

/-- Orbit form: a scaled excess limit implies convergence of the tilted partition
to one. -/
theorem orbitPartition_tendsto_one_of_scaled_excess
    (m : ℕ) (p₀ : ProbabilityMass) (c : ℝ)
    (hscaled : Tendsto
      (fun n : ℕ ↦ (n : ℝ) * excess m (orbit m p₀ n)) atTop (𝓝 c)) :
    Tendsto
      (fun n : ℕ ↦ tiltedPartition m (orbit m p₀ n)) atTop (𝓝 1) := by
  apply partition_tendsto_one_of_scaled_excess _ c
  simpa only [excess] using hscaled

/-- The exact geometric readout bound transfers the boundary density limit to the
survival constant.  The spatial-gradient input is exposed as `B_n`, with only the
precise vanishing condition `n² B_n → 0`. -/
theorem survival_tendsto_of_boundary_partition_gradient
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m) (hcrit : Critical m p₀)
    (B : ℕ → ℝ) (hB : ∀ n : ℕ, 0 ≤ B n)
    (hdelta : ∀ n : ℕ,
      SupLE (discreteDerivative (rho m (orbit m p₀ n))) (B n))
    (hscaledGradient : Tendsto
      (fun n : ℕ ↦ (n : ℝ) ^ 2 * B n) atTop (𝓝 0))
    (hboundary : Tendsto
      (fun n : ℕ ↦ (n : ℝ) ^ 2 * rho m (orbit m p₀ n) 0)
      atTop (𝓝 4))
    (hpartition : Tendsto
      (fun n : ℕ ↦ tiltedPartition m (orbit m p₀ n)) atTop (𝓝 1)) :
    Tendsto
      (fun n : ℕ ↦ (n : ℝ) ^ 2 * survival (orbit m p₀ n))
      atTop (𝓝 (4 / ((m : ℝ) - 1) ^ 2)) := by
  let comparison : ℕ → ℝ := fun n ↦
    tiltedPartition m (orbit m p₀ n) *
      ((n : ℝ) ^ 2 * rho m (orbit m p₀ n) 0) /
        ((m : ℝ) - 1) ^ 2
  let error : ℕ → ℝ := fun n ↦
    (n : ℝ) ^ 2 * tiltedPartition m (orbit m p₀ n) * B n /
      ((m : ℝ) - 1) ^ 3
  have hfactor : (m : ℝ) - 1 ≠ 0 := by
    have hmReal : (1 : ℝ) < (m : ℝ) := by exact_mod_cast (show 1 < m by omega)
    linarith
  have hconstantTwo :
      Tendsto (fun _ : ℕ ↦ (((m : ℝ) - 1) ^ 2)⁻¹) atTop
        (𝓝 ((((m : ℝ) - 1) ^ 2)⁻¹)) := tendsto_const_nhds
  have hcomparison :
      Tendsto comparison atTop (𝓝 (4 / ((m : ℝ) - 1) ^ 2)) := by
    have h := (hpartition.mul hboundary).mul hconstantTwo
    simpa only [comparison, div_eq_mul_inv, one_mul] using h
  have hconstantThree :
      Tendsto (fun _ : ℕ ↦ (((m : ℝ) - 1) ^ 3)⁻¹) atTop
        (𝓝 ((((m : ℝ) - 1) ^ 3)⁻¹)) := tendsto_const_nhds
  have herror : Tendsto error atTop (𝓝 0) := by
    have h := (hscaledGradient.mul hpartition).mul hconstantThree
    convert h using 1
    · funext n
      simp only [error, div_eq_mul_inv]
      ring
    · ring
  apply tendsto_of_abs_sub_le_error hcomparison herror
  filter_upwards with n
  have hnscale : 0 ≤ (n : ℝ) ^ 2 := sq_nonneg _
  have hncrit := orbit_critical m p₀ (by omega) hcrit n
  have hreadout := survival_sub_boundary_le
    m (orbit m p₀ n) hm hncrit (B n) (hB n) (hdelta n)
  have halgebra :
      (n : ℝ) ^ 2 * survival (orbit m p₀ n) - comparison n =
        (n : ℝ) ^ 2 *
          (survival (orbit m p₀ n) -
            tiltedPartition m (orbit m p₀ n) *
              rho m (orbit m p₀ n) 0 / ((m : ℝ) - 1) ^ 2) := by
    dsimp only [comparison]
    ring
  rw [halgebra, abs_mul, abs_of_nonneg hnscale]
  calc
    (n : ℝ) ^ 2 *
        |survival (orbit m p₀ n) -
          tiltedPartition m (orbit m p₀ n) *
            rho m (orbit m p₀ n) 0 / ((m : ℝ) - 1) ^ 2| ≤
        (n : ℝ) ^ 2 *
          (tiltedPartition m (orbit m p₀ n) * B n /
            ((m : ℝ) - 1) ^ 3) :=
      mul_le_mul_of_nonneg_left hreadout hnscale
    _ = error n := by
      dsimp only [error]
      ring

/- A fully explicit consequence wrapper: compact profile control gives the
boundary, the scaled excess gives `G_n → 1`, and the spatial-gradient rate gives
the survival asymptotic. -/
theorem survival_tendsto_of_compact_profile_excess_gradient
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m) (hcrit : Critical m p₀)
    (R : ℝ) (profileError B : ℕ → ℝ) (c : ℝ)
    (hR : 0 ≤ R)
    (hprofileError : Tendsto profileError atTop (𝓝 0))
    (hprofile : ∀ n : ℕ, 0 < n → ∀ x : ℝ, 0 ≤ x → x ≤ R →
      |(n : ℝ) ^ 2 * rho m (orbit m p₀ n) (gridIndex n x) -
          4 * Real.exp (-2 * x)| ≤ profileError n)
    (hscaledExcess : Tendsto
      (fun n : ℕ ↦ (n : ℝ) * excess m (orbit m p₀ n)) atTop (𝓝 c))
    (hB : ∀ n : ℕ, 0 ≤ B n)
    (hdelta : ∀ n : ℕ,
      SupLE (discreteDerivative (rho m (orbit m p₀ n))) (B n))
    (hscaledGradient : Tendsto
      (fun n : ℕ ↦ (n : ℝ) ^ 2 * B n) atTop (𝓝 0)) :
    Tendsto
      (fun n : ℕ ↦ (n : ℝ) ^ 2 * survival (orbit m p₀ n))
      atTop (𝓝 (4 / ((m : ℝ) - 1) ^ 2)) := by
  exact survival_tendsto_of_boundary_partition_gradient
    m p₀ hm hcrit B hB hdelta hscaledGradient
      (boundaryDensity_tendsto_of_compact_profile_error
        m p₀ R profileError hR hprofileError hprofile)
      (orbitPartition_tendsto_one_of_scaled_excess m p₀ c hscaledExcess)

/-- Direct specialization of the survival consequence to the logarithmic
gradient rate in source equation `eq:gradient`. -/
theorem survival_tendsto_of_boundary_partition_log_gradient
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m) (hcrit : Critical m p₀)
    (C : ℝ) (hC : 0 ≤ C)
    (hdelta : ∀ n : ℕ,
      SupLE (discreteDerivative (rho m (orbit m p₀ n)))
        (C * Real.log ((n : ℝ) + 2) / ((n : ℝ) + 1) ^ 3))
    (hboundary : Tendsto
      (fun n : ℕ ↦ (n : ℝ) ^ 2 * rho m (orbit m p₀ n) 0)
      atTop (𝓝 4))
    (hpartition : Tendsto
      (fun n : ℕ ↦ tiltedPartition m (orbit m p₀ n)) atTop (𝓝 1)) :
    Tendsto
      (fun n : ℕ ↦ (n : ℝ) ^ 2 * survival (orbit m p₀ n))
      atTop (𝓝 (4 / ((m : ℝ) - 1) ^ 2)) := by
  apply survival_tendsto_of_boundary_partition_gradient
    m p₀ hm hcrit
      (fun n : ℕ ↦
        C * Real.log ((n : ℝ) + 2) / ((n : ℝ) + 1) ^ 3)
  · intro n
    have hlogArg : (1 : ℝ) ≤ (n : ℝ) + 2 := by
      have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    exact div_nonneg
      (mul_nonneg hC (Real.log_nonneg hlogArg)) (by positivity)
  · exact hdelta
  · exact natSquare_mul_log_gradient_rate_tendsto_zero C
  · exact hboundary
  · exact hpartition

end

end DerridaRetaux
