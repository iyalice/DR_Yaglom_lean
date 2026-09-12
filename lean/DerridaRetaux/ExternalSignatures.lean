import DerridaRetaux.Model.Tilted
import DerridaRetaux.Rigidity.EntranceStringBase

set_option autoImplicit false

open Filter Topology

namespace DerridaRetaux

/-!
# Transparent types of the published inputs

This file introduces no primitive facts.  It freezes transparent proposition types
for exactly the four published inputs permitted by the handoff.  Proof-core modules
may accept these propositions as explicit theorem parameters without importing
`DerridaRetaux.HumanInputs`.
-/

/-- CDHLS Theorem 3, restricted to the excess upper bound used in the profile branch. -/
def CDHLSExcessFact
    (m : ℕ)
    (p₀ : ProbabilityMass)
    (_hm : 2 ≤ m)
    (_hcrit : Critical m p₀)
    (_hthird : TiltSummable m 3 p₀)
    (_hnonconstant : ¬ IsDirac p₀) : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ n : ℕ, 1 ≤ n →
      tiltedPartition m (orbit m p₀ n) - 1 ≤ C / (n : ℝ)

/-- CDHLS Proposition 1 with its published inclusive endpoint. -/
def CDHLSProductFact
    (m : ℕ)
    (p₀ : ProbabilityMass)
    (_hm : 2 ≤ m)
    (_hcrit : Critical m p₀)
    (_hnonconstant : ¬ IsDirac p₀) : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ n : ℕ, 1 ≤ n →
      criticalProduct m p₀ (n + 1) ≤ C * (n : ℝ) ^ 2

/--
Kotani's characteristic-to-spectral-to-translation specialization.  Endpoint
de-translation and every concrete-string conclusion remain internal obligations.
-/
def KotaniCharacteristicFact
    (M₁ M₂ : EntranceString)
    (h₁ h₂ : ℝ → ℝ)
    (_hentrance₁ : IsEntranceType M₁)
    (_hentrance₂ : IsEntranceType M₂)
    (_hsecond₁ : HasSecondEntranceMoment M₁)
    (_hsecond₂ : HasSecondEntranceMoment M₂)
    (_hright₁ : HasRightEnd M₁ 0)
    (_hright₂ : HasRightEnd M₂ 0)
    (_hcharacteristic₁ : ∀ lambda : ℝ, lambda < 0 →
      HasSingularCharacteristic M₁ lambda (h₁ lambda))
    (_hcharacteristic₂ : ∀ lambda : ℝ, lambda < 0 →
      HasSingularCharacteristic M₂ lambda (h₂ lambda))
    (_hequal : ∀ lambda : ℝ, lambda < 0 → h₁ lambda = h₂ lambda) : Prop :=
  ∃ c : ℝ, ∀ x : ℝ,
    stringCumulative M₁ (x + c) = stringCumulative M₂ x

/-- Chen--Shi Theorem 1.1 for the original-law tail and half-open product. -/
def ChenShiStableProductFact
    (m : ℕ)
    (p₀ : ProbabilityMass)
    (alpha c₀ : ℝ)
    (_hm : 2 ≤ m)
    (_halpha : 2 < alpha ∧ alpha < 4)
    (_hc₀ : 0 < c₀)
    (_hcrit : Critical m p₀)
    (_htail :
      Tendsto
        (fun k : ℕ ↦ p₀.mass k * (m : ℝ) ^ k * Real.rpow (k : ℝ) alpha)
        atTop (𝓝 c₀)) : Prop :=
  ∃ c₁ c₂ : ℝ,
    0 < c₁ ∧ c₁ ≤ c₂ ∧
      ∀ n : ℕ, 1 ≤ n →
        c₁ * Real.rpow (n : ℝ) (alpha - 2) ≤ criticalProduct m p₀ n ∧
          criticalProduct m p₀ n ≤ c₂ * Real.rpow (n : ℝ) (alpha - 2)

end DerridaRetaux
