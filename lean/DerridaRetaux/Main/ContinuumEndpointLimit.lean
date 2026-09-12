import DerridaRetaux.Main.ContinuumEndpointExpansion

set_option autoImplicit false

open Filter Set Topology MeasureTheory

namespace DerridaRetaux.FixedArity

noncomputable section

theorem tendsto_subsequentialConstructedEndpoint_atTop_zero
    (m : ℕ) (data : ProfileInitialData m)
    (phi : ℕ → ℕ)
    (g : ∀ k, BoundedContinuousFunction (gridExhaustionRectangle k) ℝ)
    (hphi : Tendsto phi atTop atTop)
    (hlim : ∀ k, TendstoUniformly
      (fun n (q : gridExhaustionRectangle k) ↦
        gridBilinearInterp (phi n) (orbitScaledGrid m data.law (phi n))
          (q : ℝ × ℝ).1 (q : ℝ × ℝ).2)
      (fun q ↦ g k q) atTop)
    {κ c C p : ℝ} (hκ : 0 < κ) (hc : 0 < c) (hC : 0 < C)
    (hp : 0 < p)
    (hbounds : ∀ t : ℝ, 0 < t →
      c * t ^ 2 ≤ continuumMoment (fun x ↦ gluedExhaustionLimit g t x) 3 ∧
      continuumMoment (fun x ↦ gluedExhaustionLimit g t x) 3 ≤ C * t ^ 2 ∧
      0 ≤ continuumMoment (fun x ↦ gluedExhaustionLimit g t x) 2 ∧
      continuumMoment (fun x ↦ gluedExhaustionLimit g t x) 2 ≤ C * t) :
    Tendsto
      (constructedEndpointAtTime p
        (stringY κ (fun t ↦ continuumMoment
          (fun x ↦ gluedExhaustionLimit g t x) 3))
        (fun t ↦ subsequentialLaplaceGap g t p))
      atTop (𝓝 0) := by
  let A2 : ℝ → ℝ := fun t ↦
    continuumMoment (fun x ↦ gluedExhaustionLimit g t x) 2
  let A3 : ℝ → ℝ := fun t ↦
    continuumMoment (fun x ↦ gluedExhaustionLimit g t x) 3
  let Y : ℝ → ℝ := stringY κ A3
  let Z : ℝ → ℝ := fun t ↦ subsequentialLaplaceGap g t p
  have hA2Y : Tendsto (fun t : ℝ ↦ Y t * A2 t) atTop (𝓝 0) := by
    have hprod := subsequential_stringA2Y_tendsto_atTop_zero
      m data phi g hphi hlim hκ hc hC hbounds
    simpa only [Y, stringA2Y, mul_comm] using hprod
  apply squeeze_zero' _ _ hA2Y
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    have hA3pos : 0 < A3 t :=
      (mul_pos hc (sq_pos_of_pos ht)).trans_le (hbounds t ht).1
    apply constructedEndpointAtTime_nonneg
    · exact div_nonneg hκ.le hA3pos.le
    · exact (subsequentialLaplaceGap_nonneg_and_le
        m data phi g hphi hlim ht hp.le).1
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    have hA3pos : 0 < A3 t :=
      (mul_pos hc (sq_pos_of_pos ht)).trans_le (hbounds t ht).1
    apply constructedEndpointAtTime_le_Y_mul_A2 p A2 Y Z t hp
    · exact (hbounds t ht).2.2.1
    · exact div_nonneg hκ.le hA3pos.le
    · exact (subsequentialLaplaceGap_nonneg_and_le
        m data phi g hphi hlim ht hp.le).2
    · exact (subsequentialLaplaceGap_integral_bounds
        m data phi g hphi hlim hC hp.le ht
        (fun s hs ↦ (hbounds s hs).2.2.2)).1

end

end DerridaRetaux.FixedArity
