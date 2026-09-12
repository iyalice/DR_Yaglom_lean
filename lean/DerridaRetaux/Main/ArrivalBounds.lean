import DerridaRetaux.HumanInputs
import DerridaRetaux.Arrival.SourceDifferenceBound
import DerridaRetaux.Analysis.PointwiseFromFar

set_option autoImplicit false

open Filter Topology Set

namespace DerridaRetaux.FixedArity

noncomputable section

/-!
# Source-facing source, far-arrival, and pointwise bounds

These wrappers invoke only H1a/H1b.  The finite source expansion, VisitOnce
argument, bounded-error conversion, and boundary completion are internal theorems.
-/

/-- Lemma `lem:sourcedifference` and equation `eq:sourcedifference`
(source lines 488--494). -/
theorem sourceDifference
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p₀) (hthird : TiltSummable m 3 p₀)
    (hnotBinaryFixedPoint : ¬ (m = 2 ∧ p₀ = diracMass 1)) :
    ∃ C : ℝ, 0 < C ∧ ∀ s N : ℕ,
      s + SourceMonomialTag.sourceDifferenceCutoff m < N →
        absoluteCoefficientTail
          (fun k : ℕ ↦ arrivalFormulaSource m p₀ (s + 1) k -
            arrivalFormulaSource m p₀ s k)
          (N + s) ≤
        C * (1 + arrivalBoundary m p₀ s * ((s + 1 : ℕ) : ℝ) ^ 2) /
          (N : ℝ) ^ 3 := by
  have hnonconstant : ¬ IsDirac p₀ := by
    intro hdirac
    exact hnotBinaryFixedPoint
      (critical_isDirac_eq_binary m p₀ hm hcrit hdirac)
  exact arrivalFormulaSource_sub_tail_bound_of_H1
    m p₀ hm hcrit hthird hnonconstant
      (HumanInputs.cdhls_excess_upper m p₀ hm hcrit hthird hnonconstant)
      (HumanInputs.cdhls_product_upper m p₀ hm hcrit hnonconstant)

/-- Proposition `prop:far` and equation `eq:far` (source lines 538--543). -/
theorem farArrivalBound
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p₀) (hthird : TiltSummable m 3 p₀)
    (hnotBinaryFixedPoint : ¬ (m = 2 ∧ p₀ = diracMass 1)) :
    ∃ omega : ℕ → ℝ, ∃ C : ℝ, 0 < C ∧
      Bornology.IsBounded (Set.range omega) ∧
      Tendsto omega atTop (nhds 0) ∧
      ∀ s N : ℕ, s + SourceMonomialTag.sourceDifferenceCutoff m < N →
        arrivalCoeff m p₀ s N ≤
          (omega N + C * ((s + 1 : ℕ) : ℝ)) / (N : ℝ) ^ 3 := by
  have hnonconstant : ¬ IsDirac p₀ := by
    intro hdirac
    exact hnotBinaryFixedPoint
      (critical_isDirac_eq_binary m p₀ hm hcrit hdirac)
  rcases arrivalCoeff_far_bound_of_H1
      m p₀ hm hcrit hthird hnonconstant
      (HumanInputs.cdhls_excess_upper m p₀ hm hcrit hthird hnonconstant)
      (HumanInputs.cdhls_product_upper m p₀ hm hcrit hnonconstant) with
    ⟨C, hC, hbounded, hlimit, hfar⟩
  exact ⟨arrivalFarOmega m p₀, C, hC, hbounded, hlimit, hfar⟩

/-- Proposition `prop:pointwise` and equation `eq:pointwise`
(source lines 415--421). -/
theorem pointwiseBound
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p₀) (hthird : TiltSummable m 3 p₀)
    (hnotBinaryFixedPoint : ¬ (m = 2 ∧ p₀ = diracMass 1)) :
    ∃ C : ℝ, 0 < C ∧ ∀ n j : ℕ,
      positiveTiltedDensity m (orbit m p₀ n) j ≤
        C * ((n + 1 : ℕ) : ℝ) / ((n + j + 1 : ℕ) : ℝ) ^ 3 := by
  have hnonconstant : ¬ IsDirac p₀ := by
    intro hdirac
    exact hnotBinaryFixedPoint
      (critical_isDirac_eq_binary m p₀ hm hcrit hdirac)
  exact positiveTiltedDensity_pointwise_of_H1
    m p₀ hm hcrit hthird hnonconstant
      (HumanInputs.cdhls_excess_upper m p₀ hm hcrit hthird hnonconstant)
      (HumanInputs.cdhls_product_upper m p₀ hm hcrit hnonconstant)

end

end DerridaRetaux.FixedArity
