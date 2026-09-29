import DerridaRetaux.Main.ArrivalBounds
import DerridaRetaux.Main.DiscreteMoment
import DerridaRetaux.Arrival.MomentTail

set_option autoImplicit false

open Filter Topology
open scoped BigOperators

namespace DerridaRetaux.FixedArity

noncomputable section

/-- The current `prop:far`, absorbing the bounded error into a single constant. -/
theorem farArrivalBoundUniform
    (m : ℕ) (data : ProfileInitialData m) :
    ∃ C : ℝ, 0 < C ∧ ∀ s N : ℕ,
      s + SourceMonomialTag.sourceDifferenceCutoff m < N →
      arrivalCoeff m data.law s N ≤ C * ((s + 1 : ℕ) : ℝ) / (N : ℝ) ^ 3 := by
  obtain ⟨w, C, hC, hbound, _, hfar⟩ := farArrivalBound m data.law data.arity
    data.critical data.third data.notBinaryFixedPoint
  obtain ⟨W, hW⟩ := hbound.bddAbove
  refine ⟨|W| + C, by positivity, ?_⟩
  intro s N hN
  apply (hfar s N hN).trans
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hw : w N ≤ |W| := (hW ⟨N, rfl⟩).trans (le_abs_self W)
  have hs : (1 : ℝ) ≤ ((s + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ s + 1)
  nlinarith [abs_nonneg W]

/-- The probability-law mixture in current Lemma `lem:tiltedlaw`, coefficientwise.
`drStep` is the law of the positive-part recursion on independent copies. -/
theorem tiltedLawRecursion
    (m : ℕ) (p : ProbabilityMass) (hm : 2 ≤ m) (hcrit : Critical m p) (k : ℕ) :
    normalizedTilt m (drStep m p) k =
      (drStep m (normalizedTiltLaw m p (by omega) hcrit)) k / tiltDenom m p +
      (((m : ℝ) - 1) * zeroTilt m p ^ m / tiltDenom m p) * diracMass 0 k := by
  rw [drStep_eq_drStepProb, normalizedTilt_drStepProb_coeff m p (by omega) hcrit,
    drStep_eq_drStepProb, drStepProb_apply]
  have hq : (normalizedTiltLaw m p (by omega) hcrit : Seq) = normalizedTilt m p := rfl
  rw [hq]
  cases k with
  | zero =>
    simp only [drStepSeq_zero, convPow_apply_zero, diracMass_apply, if_pos rfl,
      zero_add, ite_true, mul_one]
    change (_ + (m : ℝ) * zeroTilt m p ^ m) / _ =
      (zeroTilt m p ^ m + _) / _ + ((m : ℝ) - 1) * zeroTilt m p ^ m / _
    ring
  | succ k =>
    simp [drStepSeq_succ, diracMass_apply]

/-- The weighted-mass lemma with the current manuscript's quantifiers. -/
theorem weightedMass
    (m : ℕ) (data : ProfileInitialData m) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ,
      weightedL1Three ((n + 1 : ℕ) : ℝ) (rho m (orbit m data.law n)) ≤
        C / ((n + 1 : ℕ) : ℝ) ∧
      (∑' j : ℕ, ((j + 1 : ℕ) : ℝ) * rho m (orbit m data.law n) j) = 1 := by
  have hnonconstant : ¬ IsDirac data.law := by
    intro h
    exact data.notBinaryFixedPoint
      (critical_isDirac_eq_binary m data.law data.arity data.critical h)
  obtain ⟨C, hC, hbound⟩ := weightedL1Three_orbit_bound m data.law data.arity
    data.critical data.third hnonconstant
    (HumanInputs.cdhls_excess_upper m data.law data.arity data.critical data.third hnonconstant)
    (HumanInputs.cdhls_product_upper m data.law data.arity data.critical hnonconstant)
  refine ⟨C, hC, fun n ↦ ⟨hbound n, ?_⟩⟩
  exact positiveTiltedDensity_firstShifted_tsum m (orbit m data.law n)
    (by have := data.arity; omega)
    (orbit_critical m data.law (by have := data.arity; omega) data.critical n)

/-- The current moment-and-tail lemma for transported generating functions. -/
theorem arrivalMomentTail
    (m : ℕ) (data : ProfileInitialData m) :
    ∃ C : ℝ, 0 < C ∧
      (∀ s : ℕ, arrivalValueAtOne m data.law s ≤ C / ((s + 1 : ℕ) : ℝ)) ∧
      ∀ r : ℕ, 1 ≤ r → r ≤ m ^ 2 →
        (∀ s : ℕ, shiftedCubicMoment r (convPow r (arrivalCoeff m data.law s)) ≤
          (r : ℝ) ^ 3 * C ^ r * (((s + 1 : ℕ) : ℝ) ^ ((3 : ℤ) - (r : ℤ)))) ∧
        ∀ s K : ℕ, 1 ≤ K → coefficientTail (convPow r (arrivalCoeff m data.law s)) K ≤
          ((r : ℝ) ^ 3 * C ^ r * (((s + 1 : ℕ) : ℝ) ^ ((3 : ℤ) - (r : ℤ)))) /
            (K : ℝ) ^ 3 := by
  have hnonconstant : ¬ IsDirac data.law := by
    intro h
    exact data.notBinaryFixedPoint
      (critical_isDirac_eq_binary m data.law data.arity data.critical h)
  exact arrivalMomentTail_bounds m data.law data.arity data.critical data.third hnonconstant
    (HumanInputs.cdhls_excess_upper m data.law data.arity data.critical data.third hnonconstant)
    (HumanInputs.cdhls_product_upper m data.law data.arity data.critical hnonconstant)

end
end DerridaRetaux.FixedArity
