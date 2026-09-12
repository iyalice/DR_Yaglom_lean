import DerridaRetaux.Prelim.AtomTail
import DerridaRetaux.Prelim.CoarseMomentBounds
import DerridaRetaux.Prelim.WeightedMass
import Mathlib.Tactic

set_option autoImplicit false

open scoped BigOperators

namespace DerridaRetaux

noncomputable section

/-!
# Orbit-wide weighted mass bound

This file combines the two published coarse inputs, kept as separate explicit
theorem parameters, with the internal weighted-mass inequality.  It is the
source-shaped conditional core of `eq:weightedmass`.
-/

/-- The cubic weighted positive tilted density is `O(1/(n+1))`, with an
explicit positive constant and with H1a/H1b supplied separately. -/
theorem weightedL1Three_orbit_bound
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p₀) (hthird : TiltSummable m 3 p₀)
    (hnonconstant : ¬ IsDirac p₀)
    (hExcess : CDHLSExcessFact m p₀ hm hcrit hthird hnonconstant)
    (hProduct : CDHLSProductFact m p₀ hm hcrit hnonconstant) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ,
      weightedL1Three ((n + 1 : ℕ) : ℝ)
          (positiveTiltedDensity m (orbit m p₀ n)) ≤
        C / ((n + 1 : ℕ) : ℝ) := by
  rcases orbitPositiveTiltMass_bound_all
      m p₀ hm hcrit hthird hnonconstant hExcess with ⟨A, hA, hmass⟩
  rcases normalizedTilt_cube_orbit_bound
      m p₀ hm hcrit hthird hnonconstant hProduct with ⟨B, hB, hmoment⟩
  let C := 4 * ((m : ℝ) - 1) * (A + B)
  have hmReal : (1 : ℝ) < (m : ℝ) := by exact_mod_cast (show 1 < m by omega)
  have hC : 0 < C := by
    dsimp [C]
    exact mul_pos (mul_pos (by norm_num) (sub_pos.mpr hmReal)) (add_pos hA hB)
  refine ⟨C, hC, ?_⟩
  intro n
  have hncrit := orbit_critical m p₀ (by omega) hcrit n
  have hnthird := orbit_tiltSummable_three m p₀ (by omega) hcrit hthird n
  have hL : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
  exact weightedL1Three_positiveTiltedDensity_le
    m (orbit m p₀ n) ((n + 1 : ℕ) : ℝ) A B (by omega) hncrit hnthird hL
    (hmass n).2 (hmoment n)

/-- Complete source-shaped package for `eq:weightedmass`: its weighted `l1`
bound and the exact shifted first moment. -/
theorem positiveTiltedDensity_weightedMass_orbit
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p₀) (hthird : TiltSummable m 3 p₀)
    (hnonconstant : ¬ IsDirac p₀)
    (hExcess : CDHLSExcessFact m p₀ hm hcrit hthird hnonconstant)
    (hProduct : CDHLSProductFact m p₀ hm hcrit hnonconstant) :
    ∃ C : ℝ, 0 < C ∧
      (∀ n : ℕ,
        weightedL1Three ((n + 1 : ℕ) : ℝ)
            (positiveTiltedDensity m (orbit m p₀ n)) ≤
          C / ((n + 1 : ℕ) : ℝ)) ∧
      ∀ n : ℕ,
        ∑' j : ℕ, ((j + 1 : ℕ) : ℝ) *
            positiveTiltedDensity m (orbit m p₀ n) j = 1 := by
  rcases weightedL1Three_orbit_bound
      m p₀ hm hcrit hthird hnonconstant hExcess hProduct with ⟨C, hC, hbound⟩
  refine ⟨C, hC, hbound, ?_⟩
  intro n
  exact positiveTiltedDensity_firstShifted_tsum
    m (orbit m p₀ n) (by omega) (orbit_critical m p₀ (by omega) hcrit n)

end

end DerridaRetaux
