import DerridaRetaux.HumanInputs
import DerridaRetaux.Main.SharpnessCore

set_option autoImplicit false

open Filter Topology

namespace DerridaRetaux.FixedArity

noncomputable section

/-!
# Source-facing sharpness theorem

This is the intentionally thin wrapper around the axiom-free core.  Its only
published input is the frozen Chen--Shi theorem `H3`.
-/

/-- Theorem `thm:sharpness` (source lines 132--134), with the source's real
moment order and its endpoint cases kept literal. -/
theorem sharpness
    (m : ℕ) (r : ℝ) (hm : 2 ≤ m) (hr₀ : 0 ≤ r) (hr₃ : r < 3) :
    ∃ p₀ : ProbabilityMass,
      Critical m p₀ ∧
        ¬ IsDirac p₀ ∧
        RealTiltSummable m r p₀ ∧
        ¬ TiltSummable m 3 p₀ ∧
        ¬ Tendsto
          (fun n : ℕ ↦ (n : ℝ) * (tiltedPartition m (orbit m p₀ n) - 1))
          atTop (nhds (2 / ((m : ℝ) - 1))) := by
  rcases sharpnessPowerLaw_stableProduct_parameters m r hm hr₀ hr₃ with
    ⟨halpha, hc₀, hcritical, htail⟩
  apply sharpness_core m r hm hr₀ hr₃
  exact HumanInputs.chenShi_stable_product
    m (sharpnessPowerLaw m r hm hr₀ hr₃) (sharpPowerExponent r)
      (sharpNormalizingConstant m (sharpPowerExponent r) *
        sharpTailConstant m (sharpPowerExponent r))
      hm halpha hc₀ hcritical htail

end

end DerridaRetaux.FixedArity
