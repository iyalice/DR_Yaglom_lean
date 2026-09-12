import DerridaRetaux.Sharpness.ProductContradiction

set_option autoImplicit false

open Filter Topology

namespace DerridaRetaux.FixedArity

noncomputable section

/-!
# Axiom-free core of the sharpness theorem

This layer receives the frozen Chen--Shi statement as one explicit theorem
parameter.  It does not import `DerridaRetaux.HumanInputs`.
-/

/-- Core form of Theorem `thm:sharpness` (source lines 132--134).  For every
real tilted-moment order in `[0,3)`, the explicit critical non-Dirac law has
that moment finite, has infinite third tilted moment, and violates the
generating-function excess limit. -/
theorem sharpness_core
    (m : ℕ) (r : ℝ) (hm : 2 ≤ m) (hr₀ : 0 ≤ r) (hr₃ : r < 3)
    (hStable : ChenShiStableProductFact
      m (sharpnessPowerLaw m r hm hr₀ hr₃) (sharpPowerExponent r)
        (sharpNormalizingConstant m (sharpPowerExponent r) *
          sharpTailConstant m (sharpPowerExponent r)) hm
        (by
          exact ⟨by linarith [three_lt_sharpPowerExponent r hr₀],
            sharpPowerExponent_lt_four r hr₃⟩)
        (sharpnessStableTailConstant_pos m r hm hr₀)
        (sharpnessPowerLaw_critical m r hm hr₀ hr₃)
        (sharpOriginalLaw_stableTail_tendsto
          m (sharpPowerExponent r) hm
            (by linarith [three_lt_sharpPowerExponent r hr₀]))) :
    ∃ p₀ : ProbabilityMass,
      Critical m p₀ ∧
        ¬ IsDirac p₀ ∧
        RealTiltSummable m r p₀ ∧
        ¬ TiltSummable m 3 p₀ ∧
        ¬ Tendsto
          (fun n : ℕ ↦ (n : ℝ) * (tiltedPartition m (orbit m p₀ n) - 1))
          atTop (nhds (2 / ((m : ℝ) - 1))) :=
  exists_critical_law_with_finite_real_tilt_and_no_profile_excess_limit
    m r hm hr₀ hr₃ hStable

end

end DerridaRetaux.FixedArity
