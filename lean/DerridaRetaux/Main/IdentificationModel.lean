import DerridaRetaux.Main.Identification
import DerridaRetaux.Rigidity.ModelCharacteristicParameter

set_option autoImplicit false

open Filter Topology

namespace DerridaRetaux.FixedArity

noncomputable section

/-- The model-side characteristic is now discharged internally.  Only the
constructed-string characteristic remains as a premise of the H2 comparison. -/
theorem constructedModelCumulative_eq_of_constructed_characteristic
    {κ c C : ℝ} {A0 A2 A3 : ℝ → ℝ}
    (hκ : 0 < κ) (hc : 0 < c) (hC : 0 < C)
    (hA2 : ∀ s : ℝ, 0 < s →
      HasDerivAt A2 (A0 s * A2 s - 1) s)
    (hA3 : ∀ s : ℝ, 0 < s →
      HasDerivAt A3 (A0 s * A3 s) s)
    (hprodTop : Tendsto (stringA2Y κ A2 A3) atTop (𝓝 0))
    (hbounds : ∀ s : ℝ, 0 < s →
      c * s ^ 2 ≤ A3 s ∧ A3 s ≤ C * s ^ 2)
    (hconstructed : ∀ lambda : ℝ, lambda < 0 →
      HasSingularCharacteristic (constructedEntranceString κ A2 A3) lambda
        (-(2 * κ / 3) * Real.sqrt (-lambda))) :
    ∀ x : ℝ,
      stringCumulative (constructedEntranceString κ A2 A3) x =
        stringCumulative (modelEntranceString (2 * κ / 3)) x := by
  apply constructedModelCumulative_eq_of_characteristics
    hκ hc hC (d := 2 * κ / 3) (A0 := A0)
      (h := fun lambda ↦ -(2 * κ / 3) * Real.sqrt (-lambda))
      (by positivity) hA2 hA3 hprodTop hbounds hconstructed
  intro lambda hlambda
  exact sourceModelEntranceString_hasSingularCharacteristic hκ hlambda

end

end DerridaRetaux.FixedArity
