import DerridaRetaux.Analysis.MildCoefficientLimits
import DerridaRetaux.Analysis.TruncatedSmoothingBounds
import Mathlib.Tactic

set_option autoImplicit false

open Filter Topology

namespace DerridaRetaux

noncomputable section

/-- On a fixed positive macroscopic time window, the complete coefficient of
the quadratic Duhamel source converges uniformly to `1/2`. -/
theorem densityQuadraticWeight_natFloor_window_uniform_of_H1a
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p₀) (hthird : TiltSummable m 3 p₀)
    (hnonconstant : ¬ IsDirac p₀)
    (hExcess : CDHLSExcessFact m p₀ hm hcrit hthird hnonconstant)
    (scale : ℕ → ℕ) (hscale : Tendsto scale atTop atTop)
    (t₀ t : ℝ) (ht₀ : 0 < t₀) (ht : t₀ ≤ t) :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n : ℕ in atTop, ∀ s ∈
        Finset.Ico ⌊t₀ * (scale n : ℝ)⌋₊ ⌊t * (scale n : ℝ)⌋₊,
          |densityQuadraticWeight m p₀ s ⌊t * (scale n : ℝ)⌋₊ -
            (1 : ℝ) / 2| < ε := by
  intro ε hε
  have hP := terminalTransportWeight_orbit_natFloor_window_uniform_of_H1a
    m p₀ hm hcrit hthird hnonconstant hExcess scale hscale t₀ t ht₀ ht
    ε hε
  have hd := orbit_densityD_uniform_after_natFloor_of_H1a
    m p₀ hm hcrit hthird hnonconstant hExcess scale hscale t₀ ht₀
    (ε / 2) (half_pos hε)
  filter_upwards [hP, hd] with n hnP hnd
  intro s hs
  let P : ℝ := terminalTransportWeight
    (fun i ↦ transportCoeff m (orbit m p₀ i)) s ⌊t * (scale n : ℝ)⌋₊
  let d : ℝ := densityD m p₀ s
  have hPbound : |P| ≤ 1 := by
    dsimp only [P, terminalTransportWeight]
    exact abs_transportBetween_orbit_le_one m p₀ hm hcrit (s + 1)
      ⌊t * (scale n : ℝ)⌋₊
  have hPclose : |P - 1| < ε := hnP s hs
  have hdclose : |d - (1 : ℝ) / 2| < ε / 2 :=
    hnd s (Finset.mem_Ico.mp hs).1
  dsimp only [densityQuadraticWeight]
  change |P * d - (1 : ℝ) / 2| < ε
  rw [show P * d - (1 : ℝ) / 2 =
    P * (d - (1 : ℝ) / 2) + ((1 : ℝ) / 2) * (P - 1) by ring]
  calc
    |P * (d - (1 : ℝ) / 2) + ((1 : ℝ) / 2) * (P - 1)| ≤
        |P * (d - (1 : ℝ) / 2)| +
          |((1 : ℝ) / 2) * (P - 1)| := abs_add _ _
    _ = |P| * |d - (1 : ℝ) / 2| +
          ((1 : ℝ) / 2) * |P - 1| := by
      rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    _ < 1 * (ε / 2) + ((1 : ℝ) / 2) * ε := by
      apply add_lt_add
      · calc
          |P| * |d - (1 : ℝ) / 2| ≤ 1 * |d - (1 : ℝ) / 2| :=
            mul_le_mul_of_nonneg_right hPbound (abs_nonneg _)
          _ < 1 * (ε / 2) := mul_lt_mul_of_pos_left hdclose zero_lt_one
      · exact mul_lt_mul_of_pos_left hPclose (by norm_num)
    _ = ε := by ring

end

end DerridaRetaux
