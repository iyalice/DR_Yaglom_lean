import DerridaRetaux.HumanInputs
import DerridaRetaux.Main.SpineCore

/-!
# Source-facing third-moment tail corollary

Only the frozen H1b product estimate crosses the human-input boundary here;
the spine kernel, coupling, tail estimate, and all limit arithmetic are proved
in the imported core modules.
-/

set_option autoImplicit false

open Filter

namespace DerridaRetaux.FixedArity

noncomputable section

/-- Corollary `cor:thirdtail`, including `eq:thirdtail` and the literal
two-stage quantifier order of `eq:UI`. -/
theorem thirdMomentTail
    (m : ℕ) (data : ProfileInitialData m) :
    ∃ C : ℝ, 0 < C ∧
      (∀ (n : ℕ) (R : ℝ), 2 ≤ R →
        normalizedTiltThirdTail m (orbit m data.law n) R ≤
          C * ((n + 1 : ℕ) : ℝ) ^ 2 *
            (spineMarginalTail m data 0 (R / 2) + (n : ℝ) / R)) ∧
      ∀ (eta T : ℝ), 0 < eta → eta < T →
        ∀ epsilon : ℝ, 0 < epsilon →
          ∀ᶠ A : ℝ in atTop, ∀ᶠ N : ℕ in atTop, ∀ n : ℕ,
            eta * (N : ℝ) ≤ (n : ℝ) →
            (n : ℝ) ≤ T * (N : ℝ) →
            normalizedTiltThirdTail m (orbit m data.law n)
                (A * (N : ℝ)) / (N : ℝ) ^ 2 ≤ epsilon := by
  have hnonconstant : ¬ IsDirac data.law := by
    intro hdirac
    exact data.notBinaryFixedPoint
      (critical_isDirac_eq_binary m data.law data.arity data.critical hdirac)
  have hProduct := HumanInputs.cdhls_product_upper
    m data.law data.arity data.critical hnonconstant
  rcases profileThirdTail_quadratic_of_concreteSpine
      m data hnonconstant hProduct with ⟨C, hC, htail⟩
  refine ⟨C, hC, htail, ?_⟩
  exact profileThirdTail_uniform_integrability_of_concreteSpine
    m data hnonconstant hProduct

end

end DerridaRetaux.FixedArity
