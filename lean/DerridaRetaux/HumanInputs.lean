import DerridaRetaux.ExternalSignatures

set_option autoImplicit false

open Topology

namespace DerridaRetaux.HumanInputs

/-!
# Published human inputs

This is the complete primitive mathematical trust boundary.  The four declarations
below are the only nonstandard facts permitted by the handoff; no source theorem or
intermediate conclusion is hidden in another structure or predicate.
-/

/-- CDHLS Theorem 3, specialized to exactly the excess upper bound used here. -/
axiom cdhls_excess_upper
    (m : ℕ)
    (p₀ : ProbabilityMass)
    (hm : 2 ≤ m)
    (hcrit : Critical m p₀)
    (hthird : TiltSummable m 3 p₀)
    (hnonconstant : ¬ IsDirac p₀) :
    CDHLSExcessFact m p₀ hm hcrit hthird hnonconstant

/-- CDHLS Proposition 1; `n + 1` records the published inclusive endpoint. -/
axiom cdhls_product_upper
    (m : ℕ)
    (p₀ : ProbabilityMass)
    (hm : 2 ≤ m)
    (hcrit : Critical m p₀)
    (hnonconstant : ¬ IsDirac p₀) :
    CDHLSProductFact m p₀ hm hcrit hnonconstant

/--
Characteristic equality implies spectral equality and then translation equivalence,
in the one Kotani specialization fixed by the handoff.
-/
axiom kotani_characteristic_eq_implies_translate
    (M₁ M₂ : EntranceString)
    (h₁ h₂ : ℝ → ℝ)
    (hentrance₁ : IsEntranceType M₁)
    (hentrance₂ : IsEntranceType M₂)
    (hsecond₁ : HasSecondEntranceMoment M₁)
    (hsecond₂ : HasSecondEntranceMoment M₂)
    (hright₁ : HasRightEnd M₁ 0)
    (hright₂ : HasRightEnd M₂ 0)
    (hcharacteristic₁ : ∀ lambda : ℝ, lambda < 0 →
      HasSingularCharacteristic M₁ lambda (h₁ lambda))
    (hcharacteristic₂ : ∀ lambda : ℝ, lambda < 0 →
      HasSingularCharacteristic M₂ lambda (h₂ lambda))
    (hequal : ∀ lambda : ℝ, lambda < 0 → h₁ lambda = h₂ lambda) :
    KotaniCharacteristicFact M₁ M₂ h₁ h₂ hentrance₁ hentrance₂ hsecond₁ hsecond₂
      hright₁ hright₂ hcharacteristic₁ hcharacteristic₂ hequal

/-- Chen--Shi Theorem 1.1 for the original-law tail and half-open critical product. -/
axiom chenShi_stable_product
    (m : ℕ)
    (p₀ : ProbabilityMass)
    (alpha c₀ : ℝ)
    (hm : 2 ≤ m)
    (halpha : 2 < alpha ∧ alpha < 4)
    (hc₀ : 0 < c₀)
    (hcrit : Critical m p₀)
    (htail :
      Filter.Tendsto
        (fun k : ℕ ↦ p₀.mass k * (m : ℝ) ^ k * Real.rpow (k : ℝ) alpha)
        Filter.atTop (𝓝 c₀)) :
    ChenShiStableProductFact m p₀ alpha c₀ hm halpha hc₀ hcrit htail

end DerridaRetaux.HumanInputs
