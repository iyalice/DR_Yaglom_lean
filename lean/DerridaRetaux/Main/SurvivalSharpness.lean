import DerridaRetaux.Main.Sharpness
import DerridaRetaux.Sharpness.SurvivalToExcess

set_option autoImplicit false

open Filter Topology

namespace DerridaRetaux.FixedArity

/-- Current Appendix A, Theorem `thm:sharpness`: every smaller real tilted-moment
order admits a critical counterexample to the exact survival asymptotic. -/
theorem sharpnessSurvival
    (m : ℕ) (r : ℝ) (hm : 2 ≤ m) (hr₀ : 0 ≤ r) (hr₃ : r < 3) :
    ∃ p₀ : ProbabilityMass,
      Critical m p₀ ∧ ¬ IsDirac p₀ ∧ RealTiltSummable m r p₀ ∧
      ¬ TiltSummable m 3 p₀ ∧
      ¬ Tendsto (fun n : ℕ ↦ (n : ℝ) ^ 2 * survival (orbit m p₀ n))
        atTop (𝓝 (4 / ((m : ℝ) - 1) ^ 2)) := by
  obtain ⟨p₀, hcrit, hnonconstant, hr, hthird, hnot⟩ := sharpness m r hm hr₀ hr₃
  refine ⟨p₀, hcrit, hnonconstant, hr, hthird, ?_⟩
  intro hs
  exact hnot (excess_tendsto_of_survival_asymptotic m p₀ hm hcrit hs)

/-- Current Lemma `lem:productasymptotic`: the logarithmic product exponent,
under the survival assumption and criticality alone. -/
theorem productAsymptoticOfSurvival
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m) (hcrit : Critical m p₀)
    (hs : Tendsto (fun n : ℕ ↦ (n : ℝ) ^ 2 * survival (orbit m p₀ n)) atTop
      (𝓝 (4 / ((m : ℝ) - 1) ^ 2))) :
    Tendsto (fun n : ℕ ↦ Real.log (criticalProduct m p₀ n) / Real.log (n : ℝ))
      atTop (𝓝 2) :=
  criticalProduct_log_limit_of_survival m p₀ hm hcrit hs

end DerridaRetaux.FixedArity
