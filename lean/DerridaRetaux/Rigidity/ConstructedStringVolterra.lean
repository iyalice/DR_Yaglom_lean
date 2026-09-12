import DerridaRetaux.Rigidity.EndpointEntranceVolterra
import DerridaRetaux.Rigidity.ConstructedStringIntegralDensity

set_option autoImplicit false

open Filter Set Topology MeasureTheory

namespace DerridaRetaux

noncomputable section

/-- Abstract bridge from a positive endpoint solution of the constructed
string density equation to its entrance-normalized Volterra solution. -/
theorem entranceSolutionFromEndpoint_isVolterra_constructedString
    {κ c C a h : ℝ} {A0 A2 A3 f f' : ℝ → ℝ}
    (hκ : 0 < κ) (hc : 0 < c) (hC : 0 < C) (ha : 0 < a)
    (hA2 : ∀ s : ℝ, 0 < s → HasDerivAt A2 (A0 s * A2 s - 1) s)
    (hA3 : ∀ s : ℝ, 0 < s → HasDerivAt A3 (A0 s * A3 s) s)
    (hprodTop : Tendsto (stringA2Y κ A2 A3) atTop (𝓝 0))
    (hbounds : ∀ s : ℝ, 0 < s → c * s ^ 2 ≤ A3 s ∧ A3 s ≤ C * s ^ 2)
    (hmono : StrictMonoOn (stringXi κ A2 A3) (Ioi 0))
    (hbij : BijOn (stringXi κ A2 A3) (Ioi 0) (Iio 0))
    (hfcont : ContinuousOn f (Iio (0 : ℝ)))
    (hfpos : ∀ x : ℝ, x < 0 → 0 < f x)
    (hlimit : Tendsto (fun x : ℝ ↦ f x + x) atBot (𝓝 h))
    (hfderiv : ∀ x : ℝ, x < 0 → HasDerivAt f (f' x) x)
    (hfprimeNeg : ∀ x : ℝ, x < 0 → f' x < 0)
    (hfprimeMono : MonotoneOn f' (Iio (0 : ℝ)))
    (hfprimeLimit : Tendsto f' atBot (𝓝 (-1)))
    (hfend : Tendsto f (𝓝[<] (0 : ℝ)) (𝓝 0))
    (hfsecond : ∀ x : ℝ, x < 0 →
      HasDerivAt f'
        (a * constructedStringLebesgueDensity κ A2 A3 hmono hbij x * f x) x) :
    IsEntranceNormalizedVolterraSolution
      (constructedEntranceString κ A2 A3) (-a)
      (entranceSolutionFromEndpoint f) := by
  have hphiCont := continuousOn_entranceSolutionFromEndpoint
    hfcont hfpos hlimit hfderiv
  have hphiLim := tendsto_entranceSolutionFromEndpoint_atBot_one
    hfcont hfpos hlimit hfderiv hfprimeNeg hfprimeLimit
  refine ⟨hphiCont, hphiLim, ?_⟩
  intro xi hxi
  rw [constructedEntranceString_endpoint] at hxi
  let phi := entranceSolutionFromEndpoint f
  let psi := entranceSolutionFromEndpointSlope f f'
  let rho := constructedStringLebesgueDensity κ A2 A3 hmono hbij
  have hphiPos : ∀ y : ℝ, y < 0 → 0 < phi y := fun y hy ↦
    entranceSolutionFromEndpoint_pos hy hfcont hfpos hlimit
  have hphiDeriv : ∀ y : ℝ, y < 0 → HasDerivAt phi (psi y) y := fun y hy ↦
    hasDerivAt_entranceSolutionFromEndpoint hy hfcont hfpos hlimit
      (hfderiv y hy)
  have hpsiDeriv : ∀ y : ℝ, y < 0 →
      HasDerivAt psi (a * rho y * phi y) y := fun y hy ↦ by
    simpa only [psi, phi, rho] using
      hasDerivAt_entranceSolutionFromEndpointSlope
        (q := fun z ↦ a * constructedStringLebesgueDensity κ A2 A3 hmono hbij z)
        hy hfcont hfpos hlimit (hfderiv y hy) (hfsecond y hy)
  have hweighted := tendsto_endpoint_weighted_entranceSlope_atBot_zero
    (xi := xi) hfcont hfpos hlimit hfderiv hfprimeNeg hfprimeLimit
  obtain ⟨hLeb, hLebEq⟩ := integral_entranceVolterraKernel_density
    ha hxi hphiCont hphiPos hphiLim hphiDeriv hpsiDeriv
      (fun y hy ↦ sq_nonneg _) hweighted
  have hMass : IntegrableOn (fun y : ℝ ↦ (xi - y) * phi y) (Iic xi)
      (constructedStringMass κ A2 A3) := by
    apply integrableOn_constructedStringMass_of_density hκ hc hC hA2 hA3
      hprodTop hbounds hmono hbij hxi
    simpa only [phi, rho, mul_assoc] using hLeb
  refine ⟨hMass, ?_⟩
  have hMassEq := integral_constructedStringMass_eq_density
    (g := fun y : ℝ ↦ (xi - y) * phi y)
    hκ hc hC hA2 hA3 hprodTop hbounds hmono hbij hxi
  change phi xi = 1 - -a *
    ∫ y in Iic xi, (xi - y) * phi y ∂constructedStringMass κ A2 A3
  rw [hMassEq]
  change phi xi = 1 - -a *
    ∫ y in Iic xi, (xi - y) * phi y * rho y
  rw [hLebEq]
  field_simp [ha.ne']
  ring

end

end DerridaRetaux
