import DerridaRetaux.Arrival.ArrivalRecursion

set_option autoImplicit false

namespace DerridaRetaux.FixedArity

/-!
# Manuscript-facing arrival recursion

The source writes the renewal identity in Laurent-series notation.  This
wrapper exposes the equivalent coefficientwise statement mandated by the
architecture, together with the exact kappa recursion and Duhamel formula.
-/

/-- Lemma `lem:arrival` (source lines 443--453). -/
theorem arrivalRecursion
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p₀)
    (hnotBinaryFixedPoint : ¬ (m = 2 ∧ p₀ = diracMass 1)) :
    (∀ s N : ℕ,
      arrivalCoeff m p₀ (s + 1) N =
        arrivalCoeff m p₀ s N -
            (if N = s then arrivalBoundary m p₀ s else 0) +
          shiftByInt (1 - (s : ℤ)) (arrivalFormulaSource m p₀ s) N) ∧
    (∀ s : ℕ,
      arrivalKappa m p₀ (s + 1) =
        arrivalKappa m p₀ s /
          (1 + arrivalKappa m p₀ s * arrivalBoundary m p₀ s)) ∧
    ∀ s N : ℕ, s ≤ N →
      arrivalCoeff m p₀ s N =
        arrivalCoeff m p₀ 0 N +
          ∑ j ∈ Finset.range s, arrivalFormulaSource m p₀ j (N + j - 1) := by
  exact ⟨arrivalCoeff_succ_eq_formulaSource m p₀ hm hcrit hnotBinaryFixedPoint,
    arrivalKappa_succ m p₀ hm hcrit hnotBinaryFixedPoint,
    arrivalCoeff_duhamel m p₀ hm hcrit hnotBinaryFixedPoint⟩

end DerridaRetaux.FixedArity
