import DerridaRetaux.HumanInputs
import DerridaRetaux.Prelim.CoarseMomentBounds

set_option autoImplicit false

open scoped BigOperators

namespace DerridaRetaux.FixedArity

noncomputable section

/-!
# Source-facing discrete moment lemmas

These wrappers invoke only the frozen published input attached to each source
result.  All recurrences, positivity statements, product conversions, and tail
arguments are proved in the axiom-free preliminary modules.
-/

/-- Lemma `lem:cubic` (source lines 256--267), including positivity, the exact
recurrence and product representation for `J_n`, and both low-moment bounds
with one enlarged positive constant. -/
theorem cubicMoment
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p₀) (hthird : TiltSummable m 3 p₀)
    (hnotBinaryFixedPoint : ¬ (m = 2 ∧ p₀ = diracMass 1)) :
    ∃ C : ℝ, 0 < C ∧
      (∀ n : ℕ, 0 < normalizedCubicMoment m (orbit m p₀ n)) ∧
      (∀ n : ℕ,
        tiltDenom m (orbit m p₀ n) *
            normalizedCubicMoment m (orbit m p₀ (n + 1)) =
          (m : ℝ) * normalizedCubicMoment m (orbit m p₀ n)) ∧
      (∀ n : ℕ,
        normalizedCubicMoment m (orbit m p₀ n) =
          normalizedCubicMoment m p₀ *
            (tiltedPartition m p₀ / tiltedPartition m (orbit m p₀ n)) *
              criticalProduct m p₀ n) ∧
      ∀ n : ℕ,
        normalizedCubicMoment m (orbit m p₀ n) ≤
            C * ((n + 1 : ℕ) : ℝ) ^ 2 ∧
          (∑' k : ℕ, (k : ℝ) ^ 3 * normalizedTilt m (orbit m p₀ n) k) ≤
            C * ((n + 1 : ℕ) : ℝ) ^ 2 ∧
          (∑' k : ℕ, (k : ℝ) ^ 2 * normalizedTilt m (orbit m p₀ n) k) ≤
            C * ((n + 1 : ℕ) : ℝ) := by
  have hnonconstant : ¬ IsDirac p₀ := by
    intro hdirac
    exact hnotBinaryFixedPoint (critical_isDirac_eq_binary m p₀ hm hcrit hdirac)
  have hProduct := HumanInputs.cdhls_product_upper m p₀ hm hcrit hnonconstant
  rcases normalizedCubicMoment_eqJ
      m p₀ hm hcrit hthird hnonconstant hProduct with
    ⟨C₁, hC₁, hpositive, hrecurrence, hproduct, hJ⟩
  rcases normalizedTilt_lowMoments_orbit
      m p₀ hm hcrit hthird hnonconstant hProduct with
    ⟨C₂, hC₂, hmoments⟩
  refine ⟨C₁ + C₂, add_pos hC₁ hC₂, hpositive, hrecurrence, hproduct, ?_⟩
  intro n
  have hL : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by positivity
  have hLtwo : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) ^ 2 := sq_nonneg _
  refine ⟨hJ n |>.trans ?_, (hmoments n).1 |>.trans ?_,
    (hmoments n).2 |>.trans ?_⟩
  · exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hC₂.le) hLtwo
  · exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hC₁.le) hLtwo
  · exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hC₁.le) hL

/-- Lemma `lem:atomtail` and equation `eq:atomtail` (source lines 294--299).
The only published input is H1a. -/
theorem firstTiltedAtomTail
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p₀) (hthird : TiltSummable m 3 p₀)
    (hnotBinaryFixedPoint : ¬ (m = 2 ∧ p₀ = diracMass 1)) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ,
      0 ≤ DerridaRetaux.firstTiltedAtomTail m p₀ n ∧
        DerridaRetaux.firstTiltedAtomTail m p₀ n ≤
          C / ((n + 1 : ℕ) : ℝ) := by
  have hnonconstant : ¬ IsDirac p₀ := by
    intro hdirac
    exact hnotBinaryFixedPoint (critical_isDirac_eq_binary m p₀ hm hcrit hdirac)
  exact DerridaRetaux.firstTiltedAtomTail_bound_all
    m p₀ hm hcrit hthird hnonconstant hnotBinaryFixedPoint
      (HumanInputs.cdhls_excess_upper m p₀ hm hcrit hthird hnonconstant)

end

end DerridaRetaux.FixedArity
