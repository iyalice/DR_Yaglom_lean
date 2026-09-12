import DerridaRetaux.Rigidity.EntranceStringBase

set_option autoImplicit false

open Filter Topology

namespace DerridaRetaux

noncomputable section

/-- Once an endpoint solution has the normalized reduction-of-order
representation, its entrance expansion is exactly the singular characteristic. -/
theorem hasSingularCharacteristic_of_endpoint_representation
    {M : EntranceString} {lambda h : ℝ} {phi f : ℝ → ℝ}
    (hvolterra : IsEntranceNormalizedVolterraSolution M lambda phi)
    (hrepresentation : ∀ᶠ xi : ℝ in atBot,
      f xi = phi xi * ∫ v in xi..M.endpoint, ((phi v) ^ 2)⁻¹)
    (hexpansion : Tendsto (fun xi : ℝ ↦ f xi + xi) atBot (𝓝 h)) :
    HasSingularCharacteristic M lambda h := by
  refine ⟨phi, hvolterra, ?_⟩
  apply hexpansion.congr'
  filter_upwards [hrepresentation] with xi hxi
  rw [hxi]
  ring

end

end DerridaRetaux
