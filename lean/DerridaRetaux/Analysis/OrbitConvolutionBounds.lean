import DerridaRetaux.Analysis.ConvolutionNorms
import DerridaRetaux.Prelim.WeightedMassOrbit
import Mathlib.Tactic

set_option autoImplicit false

namespace DerridaRetaux

/-!
# Orbit convolution bounds

This file instantiates the deterministic weighted Young inequalities on the
critical orbit.  The pointwise estimate `eq:sup` remains a literal theorem
parameter; the weighted `l1` input can either be supplied directly or obtained
from the two approved CDHLS facts.
-/

noncomputable section

/-- Finite third tilted moment supplies the weighted summability needed by Young's
inequality at every finite generation. -/
theorem weightedAbs_positiveTiltedDensity_orbit_summable
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p₀) (hthird : TiltSummable m 3 p₀) (n : ℕ) :
    Summable
      (weightedAbs ((n + 1 : ℕ) : ℝ)
        (positiveTiltedDensity m (orbit m p₀ n))) := by
  have hncrit := orbit_critical m p₀ (by omega) hcrit n
  have hnthird := orbit_tiltSummable_three m p₀ (by omega) hcrit hthird n
  simpa only [weightedAbs, cubicWeight] using
    weightedL1Three_positiveTiltedDensity_summable
      m (orbit m p₀ n) ((n + 1 : ℕ) : ℝ) (by omega) hncrit hnthird (by positivity)

/-- Literal power bounds behind source equation `eq:convnorms`.

For `r+1` factors, the second estimate has size
`(B/L^2) * (A/L)^r`, i.e. exactly order `L^(-(r+2))`. -/
theorem weightedConvolutionPowers_orbit_bounds
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p₀) (hthird : TiltSummable m 3 p₀)
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hL1 : ∀ n : ℕ,
      weightedL1Three ((n + 1 : ℕ) : ℝ)
          (positiveTiltedDensity m (orbit m p₀ n)) ≤
        A / ((n + 1 : ℕ) : ℝ))
    (hSup : ∀ n : ℕ,
      WeightedSupThreeLE ((n + 1 : ℕ) : ℝ)
        (positiveTiltedDensity m (orbit m p₀ n))
        (B / ((n + 1 : ℕ) : ℝ) ^ 2)) :
    ∀ n r : ℕ,
      weightedL1Three ((n + 1 : ℕ) : ℝ)
          (convPow r (positiveTiltedDensity m (orbit m p₀ n))) ≤
        (A / ((n + 1 : ℕ) : ℝ)) ^ r ∧
      WeightedSupThreeLE ((n + 1 : ℕ) : ℝ)
        (convPow (r + 1) (positiveTiltedDensity m (orbit m p₀ n)))
        ((B / ((n + 1 : ℕ) : ℝ) ^ 2) *
          (A / ((n + 1 : ℕ) : ℝ)) ^ r) := by
  intro n r
  let L : ℝ := ((n + 1 : ℕ) : ℝ)
  let rhoN : Seq := positiveTiltedDensity m (orbit m p₀ n)
  have hL : 1 ≤ L := by
    dsimp [L]
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hsum : Summable (weightedAbs L rhoN) := by
    simpa only [L, rhoN] using
      weightedAbs_positiveTiltedDensity_orbit_summable m p₀ hm hcrit hthird n
  have hmassNonneg : 0 ≤ weightedL1Three L rhoN :=
    weightedL1Three_nonneg L hLpos rhoN
  have hratioNonneg : 0 ≤ A / L := div_nonneg hA hLpos.le
  have hmassBound : weightedL1Three L rhoN ≤ A / L := by
    simpa only [L, rhoN] using hL1 n
  have hpower : weightedL1Three L rhoN ^ r ≤ (A / L) ^ r :=
    pow_le_pow_left₀ hmassNonneg hmassBound r
  constructor
  · exact (weightedL1Three_convPow_le_pow L hL rhoN hsum r).trans hpower
  · have hbase : 0 ≤ B / L ^ 2 := div_nonneg hB (sq_nonneg L)
    have hconv := weightedSupThree_convPow_succ_le
      L (B / L ^ 2) hL hbase rhoN (by simpa only [L, rhoN] using hSup n) hsum r
    intro j
    calc
      cubicWeight L j * |convPow (r + 1) rhoN j| ≤
          (B / L ^ 2) * weightedL1Three L rhoN ^ r := hconv j
      _ ≤ (B / L ^ 2) * (A / L) ^ r :=
        mul_le_mul_of_nonneg_left hpower hbase

/-- Source-shaped `eq:convnorms`: H1a/H1b provide `A`, while the pointwise
The constant `B` is exposed as the still-separate input `eq:sup`. -/
theorem convolutionNorms_orbit_of_pointwise
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p₀) (hthird : TiltSummable m 3 p₀)
    (hnonconstant : ¬ IsDirac p₀)
    (hExcess : CDHLSExcessFact m p₀ hm hcrit hthird hnonconstant)
    (hProduct : CDHLSProductFact m p₀ hm hcrit hnonconstant)
    (B : ℝ) (hB : 0 ≤ B)
    (hSup : ∀ n : ℕ,
      WeightedSupThreeLE ((n + 1 : ℕ) : ℝ)
        (positiveTiltedDensity m (orbit m p₀ n))
        (B / ((n + 1 : ℕ) : ℝ) ^ 2)) :
    ∃ A : ℝ, 0 < A ∧ ∀ n r : ℕ,
      weightedL1Three ((n + 1 : ℕ) : ℝ)
          (convPow r (positiveTiltedDensity m (orbit m p₀ n))) ≤
        (A / ((n + 1 : ℕ) : ℝ)) ^ r ∧
      WeightedSupThreeLE ((n + 1 : ℕ) : ℝ)
        (convPow (r + 1) (positiveTiltedDensity m (orbit m p₀ n)))
        ((B / ((n + 1 : ℕ) : ℝ) ^ 2) *
          (A / ((n + 1 : ℕ) : ℝ)) ^ r) := by
  rcases weightedL1Three_orbit_bound
      m p₀ hm hcrit hthird hnonconstant hExcess hProduct with ⟨A, hA, hL1⟩
  refine ⟨A, hA, ?_⟩
  exact weightedConvolutionPowers_orbit_bounds
    m p₀ hm hcrit hthird A B hA.le hB hL1 hSup

end

end DerridaRetaux
