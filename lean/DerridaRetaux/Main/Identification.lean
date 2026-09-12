import DerridaRetaux.HumanInputs
import DerridaRetaux.Rigidity.ModelString
import DerridaRetaux.Rigidity.StringAdmissibility
import DerridaRetaux.Rigidity.Translation

set_option autoImplicit false

open Filter Topology

namespace DerridaRetaux.FixedArity

noncomputable section

/-!
# Source-facing Kotani comparison

This is the thin H2 crossing for the two concrete strings.  Both characteristic
witnesses remain explicit internal prerequisites.  Entrance type, second moments,
right endpoints, and removal of the translation are discharged by proved project
lemmas.
-/

/-- Once both concrete strings have the same singular characteristic on the whole
negative axis, the approved Kotani input and the common endpoint identify their
cumulative strings pointwise. -/
theorem constructedModelCumulative_eq_of_characteristics
    {κ c C d : ℝ} {A0 A2 A3 h : ℝ → ℝ}
    (hκ : 0 < κ) (hc : 0 < c) (hC : 0 < C) (hd : d ≠ 0)
    (hA2 : ∀ s : ℝ, 0 < s →
      HasDerivAt A2 (A0 s * A2 s - 1) s)
    (hA3 : ∀ s : ℝ, 0 < s →
      HasDerivAt A3 (A0 s * A3 s) s)
    (hprodTop : Tendsto (stringA2Y κ A2 A3) atTop (𝓝 0))
    (hbounds : ∀ s : ℝ, 0 < s →
      c * s ^ 2 ≤ A3 s ∧ A3 s ≤ C * s ^ 2)
    (hconstructed : ∀ lambda : ℝ, lambda < 0 →
      HasSingularCharacteristic
        (constructedEntranceString κ A2 A3) lambda (h lambda))
    (hmodel : ∀ lambda : ℝ, lambda < 0 →
      HasSingularCharacteristic (modelEntranceString d) lambda (h lambda)) :
    ∀ x : ℝ,
      stringCumulative (constructedEntranceString κ A2 A3) x =
        stringCumulative (modelEntranceString d) x := by
  have hentranceConstructed :=
    constructedEntranceString_isEntranceType
      hκ hc hC hA2 hA3 hprodTop hbounds
  have hentranceModel := modelEntranceString_isEntranceType hd
  have hsecondConstructed :=
    constructedEntranceString_hasSecondEntranceMoment
      hκ hc hC hA2 hA3 hprodTop hbounds
  have hsecondModel := modelEntranceString_hasSecondEntranceMoment d
  have hrightConstructed :=
    constructedEntranceString_hasRightEnd_zero
      hκ hc hC hA2 hA3 hprodTop hbounds
  have hrightModel := modelEntranceString_hasRightEnd_zero hd
  have hfact := HumanInputs.kotani_characteristic_eq_implies_translate
    (constructedEntranceString κ A2 A3) (modelEntranceString d) h h
      hentranceConstructed hentranceModel hsecondConstructed hsecondModel
      hrightConstructed hrightModel hconstructed hmodel (fun _ _ ↦ rfl)
  exact kotaniCharacteristicFact_imp_cumulative_eq
    (constructedEntranceString κ A2 A3) (modelEntranceString d) h h
      hentranceConstructed hentranceModel hsecondConstructed hsecondModel
      hrightConstructed hrightModel hconstructed hmodel (fun _ _ ↦ rfl) hfact

end

end DerridaRetaux.FixedArity
