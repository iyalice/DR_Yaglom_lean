import DerridaRetaux.Main.ProfileFinal
import DerridaRetaux.Analysis.AtomDomination
import DerridaRetaux.Analysis.DecrementLimit
import DerridaRetaux.Analysis.MeanConsequences
import DerridaRetaux.Analysis.ReadoutConsequences

set_option autoImplicit false

open Asymptotics Filter Topology

namespace DerridaRetaux.FixedArity

noncomputable section

/-- All conclusions of Theorem `thm:profile`, with compact-uniform convergence represented by
an explicit error modulus and the `eq:tv` convention equal to twice total variation. -/
theorem profile
    (m : ℕ) (data : ProfileInitialData m) :
    (∀ R : ℝ, 0 ≤ R → ∃ error : ℕ → ℝ,
      Tendsto error atTop (𝓝 0) ∧
        ∀ n : ℕ, 0 < n → ∀ x : ℝ, 0 ≤ x → x ≤ R →
          |(n : ℝ) ^ 2 * rho m (orbit m data.law n) (gridIndex n x) -
            4 * Real.exp (-2 * x)| ≤ error n) ∧
    Tendsto
      (fun n : ℕ ↦ (n : ℝ) * excess m (orbit m data.law n))
      atTop (𝓝 (2 / ((m : ℝ) - 1))) ∧
    Tendsto
      (fun n : ℕ ↦ (n : ℝ) ^ 2 * survival (orbit m data.law n))
      atTop (𝓝 (4 / ((m : ℝ) - 1) ^ 2)) ∧
    Tendsto
      (fun n : ℕ ↦ (n : ℝ) ^ 2 *
        (excess m (orbit m data.law n) - excess m (orbit m data.law (n + 1))))
      atTop (𝓝 (2 / ((m : ℝ) - 1))) ∧
    Tendsto
      (fun n : ℕ ↦ (n : ℝ) ^ 2 * probabilityFirstMoment (orbit m data.law n))
      atTop (𝓝 (4 * (m : ℝ) / ((m : ℝ) - 1) ^ 3)) ∧
    (∀ k : ℕ, 1 ≤ k →
      Tendsto
        (fun n : ℕ ↦ (n : ℝ) ^ 2 * orbit m data.law n k)
        atTop (𝓝 (4 / (((m : ℝ) - 1) * (m : ℝ) ^ k)))) ∧
    Tendsto
      (fun n : ℕ ↦ probabilityFirstMoment (orbit m data.law n) /
        survival (orbit m data.law n))
      atTop (𝓝 ((m : ℝ) / ((m : ℝ) - 1))) ∧
    (fun n : ℕ ↦ conditionalPositiveL1Error m (orbit m data.law n)) =O[atTop]
      (fun n : ℕ ↦ Real.log ((n + 2 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ)) := by
  have hnonconstant : ¬ IsDirac data.law := by
    intro hdirac
    exact data.notBinaryFixedPoint
      (critical_isDirac_eq_binary m data.law data.arity data.critical hdirac)
  have hExcess := HumanInputs.cdhls_excess_upper
    m data.law data.arity data.critical data.third hnonconstant
  have hProduct := HumanInputs.cdhls_product_upper
    m data.law data.arity data.critical hnonconstant
  obtain ⟨C, hC, hSup, hGradient, _hSpatial, _hTemporal⟩ :=
    smoothing m data.law data.arity data.critical data.third data.notBinaryFixedPoint
  have hprofile := profileDensity m data
  have hpartition := orbitPartition_tendsto_one_of_H1
    m data.law data.arity data.critical data.third hnonconstant hExcess
  obtain ⟨error0, herror0, hprofile0⟩ := hprofile 0 le_rfl
  have hboundary := boundaryDensity_tendsto_of_compact_profile_error
    m data.law 0 error0 le_rfl herror0 hprofile0
  have hGradientCast : ∀ n : ℕ,
      WeightedSupThreeLE (profileScale n)
        (discreteDerivative (rho m (orbit m data.law n)))
        (C * Real.log ((n : ℝ) + 2) / ((n : ℝ) + 1) ^ 3) := by
    intro n
    convert hGradient n using 1 <;> norm_num [profileScale]
  have hdelta : ∀ n : ℕ,
      SupLE (discreteDerivative (rho m (orbit m data.law n)))
        (C * Real.log ((n : ℝ) + 2) / ((n : ℝ) + 1) ^ 3) := by
    intro n
    exact supLE_of_weightedSupThree (profileScale n)
      (C * Real.log ((n : ℝ) + 2) / ((n : ℝ) + 1) ^ 3)
      (profileScale_pos n) _ (hGradientCast n)
  have hsurvival := survival_tendsto_of_boundary_partition_log_gradient
    m data.law data.arity data.critical C hC.le hdelta hboundary hpartition
  have hmass := orbit_densityTotalMass_tendsto_two_of_compact_profile
    m data.law data.arity data.critical data.third hnonconstant
      hExcess hProduct hprofile
  have hexcess := orbit_scaledExcess_tendsto_of_densityMass_and_survival
    m data.law data.arity data.critical (4 / ((m : ℝ) - 1) ^ 2)
      hmass hpartition hsurvival
  have hdecrement := excess_orbit_decrement_tendsto
    m data.law data.arity data.critical hsurvival hexcess
  have hfixed : ∀ k : ℕ, 1 ≤ k →
      Tendsto
        (fun n : ℕ ↦ (n : ℝ) ^ 2 * orbit m data.law n k)
        atTop (𝓝 (4 / (((m : ℝ) - 1) * (m : ℝ) ^ k))) := by
    intro k hk
    obtain ⟨error, herror, hprofileK⟩ :=
      hprofile (((k - 1 : ℕ) : ℝ)) (Nat.cast_nonneg _)
    exact fixedAtom_tendsto_of_compact_profile_error
      m data.law data.arity data.critical ((k - 1 : ℕ) : ℝ) error k hk
        le_rfl herror hprofileK hpartition
  obtain ⟨D, hD, hatom⟩ := orbit_fixedAtom_geometric_bound_of_H1_and_pointwise
    m data.law data.arity data.critical data.third hnonconstant hExcess
      C hC.le (by simpa only [profileScale] using hSup)
  have hmean := orbit_probabilityFirstMoment_tendsto_of_atom_limits_and_bound
    m data.law data.arity data.critical D hfixed hatom
  have hconditionalMean := conditionalFirstMoment_tendsto
    m (orbit m data.law) data.arity hmean hsurvival
  have htv := orbit_conditionalPositiveL1Error_isBigO
    m data.law data.arity data.critical C hC.le
      (fun n : ℕ ↦ C * Real.log ((n + 2 : ℕ) : ℝ) /
        ((n + 1 : ℕ) : ℝ) ^ 3)
      hpartition hsurvival (fun _ ↦ le_rfl) (by
        intro n
        exact supLE_of_weightedSupThree (profileScale n)
          (C * Real.log ((n + 2 : ℕ) : ℝ) / profileScale n ^ 3)
          (profileScale_pos n) _ (hGradient n))
  exact ⟨hprofile, hexcess, hsurvival, hdecrement, hmean, hfixed,
    hconditionalMean, htv⟩

end

end DerridaRetaux.FixedArity
