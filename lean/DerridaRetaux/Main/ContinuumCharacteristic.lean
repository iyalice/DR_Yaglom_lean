import DerridaRetaux.Main.ContinuumEndpointLimit
import DerridaRetaux.Main.ContinuumLaplaceGapRegularity

set_option autoImplicit false

open Filter Set Topology MeasureTheory

namespace DerridaRetaux.FixedArity

noncomputable section

/-- Every positive Laplace parameter produces the source singular
characteristic for the string extracted from a subsequential limit. -/
theorem subsequentialConstructedString_hasSingularCharacteristic
    (m : ℕ) (data : ProfileInitialData m)
    (phi : ℕ → ℕ)
    (g : ∀ k, BoundedContinuousFunction (gridExhaustionRectangle k) ℝ)
    (hphi : Tendsto phi atTop atTop)
    (hlim : ∀ k, TendstoUniformly
      (fun n (q : gridExhaustionRectangle k) ↦
        gridBilinearInterp (phi n) (orbitScaledGrid m data.law (phi n))
          (q : ℝ × ℝ).1 (q : ℝ × ℝ).2)
      (fun q ↦ g k q) atTop)
    {κ p : ℝ} (hκ : 0 < κ) (hp : 0 < p) :
    HasSingularCharacteristic
      (constructedEntranceString κ
        (fun t ↦ continuumMoment (fun x ↦ gluedExhaustionLimit g t x) 2)
        (fun t ↦ continuumMoment (fun x ↦ gluedExhaustionLimit g t x) 3))
      (-(p ^ 2 / 4)) (-κ * p / 3) := by
  let A0 : ℝ → ℝ := fun t ↦
    continuumMoment (fun x ↦ gluedExhaustionLimit g t x) 0
  let A2 : ℝ → ℝ := fun t ↦
    continuumMoment (fun x ↦ gluedExhaustionLimit g t x) 2
  let A3 : ℝ → ℝ := fun t ↦
    continuumMoment (fun x ↦ gluedExhaustionLimit g t x) 3
  let Z : ℝ → ℝ := fun t ↦ subsequentialLaplaceGap g t p
  obtain ⟨c, C, hc, hC, hbounds⟩ :=
    subsequentialMoment_rigidityBounds m data phi g hphi hlim
  have hmom := subsequentialMomentODE m data phi g hphi hlim
  have hA2 : ∀ s : ℝ, 0 < s → HasDerivAt A2 (A0 s * A2 s - 1) s := by
    simpa only [A0, A2] using hmom.2.1
  have hA3 : ∀ s : ℝ, 0 < s → HasDerivAt A3 (A0 s * A3 s) s := by
    simpa only [A0, A3] using hmom.2.2
  have hprodTop : Tendsto (stringA2Y κ A2 A3) atTop (𝓝 0) :=
    subsequential_stringA2Y_tendsto_atTop_zero
      m data phi g hphi hlim hκ hc hC hbounds
  have hPhi : Tendsto (constructedPhi Z) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    simpa only [Z] using
      tendsto_subsequentialConstructedPhi_one m data phi g hphi hlim p hp.le
  have hTime : Tendsto
      (fun t : ℝ ↦ constructedEndpointAtTime p (stringY κ A3) Z t +
        stringXi κ A2 A3 t)
      (𝓝[>] (0 : ℝ)) (𝓝 (-κ * p / 3)) := by
    simpa only [A2, A3, Z] using
      tendsto_subsequentialEndpoint_add_coordinate
        m data phi g hphi hlim hκ hc hC hp hA2 hA3 hprodTop hbounds
  have hEndpoint : Tendsto
      (constructedEndpointAtTime p (stringY κ A3) Z) atTop (𝓝 0) := by
    simpa only [A3, Z] using
      tendsto_subsequentialConstructedEndpoint_atTop_zero
        m data phi g hphi hlim hκ hc hC hp hbounds
  apply DerridaRetaux.constructedEntranceString_hasSingularCharacteristic
    hκ hc hC hp hA2 hA3 hprodTop
    (fun s hs ↦ ⟨(hbounds s hs).1, (hbounds s hs).2.1⟩)
  · intro s hs
    simpa only [A0, Z] using
      subsequentialLaplaceGap_hasDerivAt
        m data phi g hphi hlim p s hp.le hs
  · intro s hs
    simpa only [Z] using
      subsequentialLaplaceGap_intervalIntegrable
        m data phi g hphi hlim p s hp.le hs
  · intro s hs
    simpa only [Z] using
      subsequentialLaplaceGap_stronglyMeasurableAtFilter
        m data phi g hphi hlim p s hp.le hs
  · intro s hs
    simpa only [Z] using
      subsequentialLaplaceGap_continuousAt
        m data phi g hphi hlim p s hp.le hs
  · intro s hs
    simpa only [Z] using
      subsequentialLaplaceGap_pos m data phi g hphi hlim hs hp
  · exact hPhi
  · exact hTime
  · exact hEndpoint

end

end DerridaRetaux.FixedArity
