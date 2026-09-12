import DerridaRetaux.Main.ContinuumCharacteristic
import DerridaRetaux.Main.IdentificationModel

set_option autoImplicit false

open Filter Topology Real

namespace DerridaRetaux.FixedArity

noncomputable section

/-- The string extracted from every subsequential limit is the explicit model
string, with source normalization `d = 2κ/3`. -/
theorem subsequentialConstructedString_cumulative_eq_model
    (m : ℕ) (data : ProfileInitialData m)
    (phi : ℕ → ℕ)
    (g : ∀ k, BoundedContinuousFunction (gridExhaustionRectangle k) ℝ)
    (hphi : Tendsto phi atTop atTop)
    (hlim : ∀ k, TendstoUniformly
      (fun n (q : gridExhaustionRectangle k) ↦
        gridBilinearInterp (phi n) (orbitScaledGrid m data.law (phi n))
          (q : ℝ × ℝ).1 (q : ℝ × ℝ).2)
      (fun q ↦ g k q) atTop)
    {κ : ℝ} (hκ : 0 < κ) :
    ∀ x : ℝ,
      stringCumulative
        (constructedEntranceString κ
          (fun t ↦ continuumMoment (fun y ↦ gluedExhaustionLimit g t y) 2)
          (fun t ↦ continuumMoment (fun y ↦ gluedExhaustionLimit g t y) 3)) x =
      stringCumulative (modelEntranceString (2 * κ / 3)) x := by
  let A0 : ℝ → ℝ := fun t ↦
    continuumMoment (fun x ↦ gluedExhaustionLimit g t x) 0
  let A2 : ℝ → ℝ := fun t ↦
    continuumMoment (fun x ↦ gluedExhaustionLimit g t x) 2
  let A3 : ℝ → ℝ := fun t ↦
    continuumMoment (fun x ↦ gluedExhaustionLimit g t x) 3
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
  apply constructedModelCumulative_eq_of_constructed_characteristic
    hκ hc hC hA2 hA3 hprodTop
    (fun s hs ↦ ⟨(hbounds s hs).1, (hbounds s hs).2.1⟩)
  intro lambda hlambda
  let p : ℝ := 2 * Real.sqrt (-lambda)
  have hneg : 0 < -lambda := neg_pos.mpr hlambda
  have hp : 0 < p := mul_pos (by norm_num) (Real.sqrt_pos.2 hneg)
  have hlambdaEq : lambda = -(p ^ 2 / 4) := by
    have hsqrt : (Real.sqrt (-lambda)) ^ 2 = -lambda := Real.sq_sqrt hneg.le
    dsimp only [p]
    nlinarith
  have hchar := subsequentialConstructedString_hasSingularCharacteristic
    m data phi g hphi hlim hκ hp
  rw [← hlambdaEq] at hchar
  have hvalue : -κ * p / 3 = -(2 * κ / 3) * Real.sqrt (-lambda) := by
    dsimp only [p]
    ring
  rw [hvalue] at hchar
  exact hchar

end

end DerridaRetaux.FixedArity
