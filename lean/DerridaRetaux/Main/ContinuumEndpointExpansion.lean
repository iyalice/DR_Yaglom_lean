import DerridaRetaux.Main.ContinuumConstructedPhiBounds
import DerridaRetaux.Main.ContinuumRemainder
import DerridaRetaux.Rigidity.ConstructedCharacteristic

set_option autoImplicit false

open Filter Set Topology MeasureTheory

namespace DerridaRetaux.FixedArity

noncomputable section

theorem subsequential_firstEndpointTerm_tendsto_zero
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
    (hp : 0 ≤ p)
    (hA2 : ∀ s : ℝ, 0 < s →
      HasDerivAt
        (fun t ↦ continuumMoment (fun x ↦ gluedExhaustionLimit g t x) 2)
        (continuumMoment (fun x ↦ gluedExhaustionLimit g s x) 0 *
          continuumMoment (fun x ↦ gluedExhaustionLimit g s x) 2 - 1) s)
    (hA3 : ∀ s : ℝ, 0 < s →
      HasDerivAt
        (fun t ↦ continuumMoment (fun x ↦ gluedExhaustionLimit g t x) 3)
        (continuumMoment (fun x ↦ gluedExhaustionLimit g s x) 0 *
          continuumMoment (fun x ↦ gluedExhaustionLimit g s x) 3) s)
    (hprodTop : Tendsto
      (stringA2Y κ
        (fun t ↦ continuumMoment (fun x ↦ gluedExhaustionLimit g t x) 2)
        (fun t ↦ continuumMoment (fun x ↦ gluedExhaustionLimit g t x) 3))
      atTop (𝓝 0))
    (hbounds : ∀ t : ℝ, 0 < t →
      c * t ^ 2 ≤ continuumMoment (fun x ↦ gluedExhaustionLimit g t x) 3 ∧
      continuumMoment (fun x ↦ gluedExhaustionLimit g t x) 3 ≤ C * t ^ 2 ∧
      0 ≤ continuumMoment (fun x ↦ gluedExhaustionLimit g t x) 2 ∧
      continuumMoment (fun x ↦ gluedExhaustionLimit g t x) 2 ≤ C * t) :
    Tendsto
      (fun t : ℝ ↦
        stringA2Y κ
          (fun s ↦ continuumMoment (fun x ↦ gluedExhaustionLimit g s x) 2)
          (fun s ↦ continuumMoment (fun x ↦ gluedExhaustionLimit g s x) 3) t *
        (constructedPhi (fun s ↦ subsequentialLaplaceGap g s p) t - 1))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  let K : ℝ := (κ / c) * (p ^ 2 * C / 8)
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hlinear : Tendsto (fun t : ℝ ↦ K * t) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hid : Tendsto (fun t : ℝ ↦ t) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
      tendsto_id.mono_left inf_le_left
    convert tendsto_const_nhds.mul hid using 1 <;> ring
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero' _ _ hlinear
  · exact Eventually.of_forall fun t ↦ norm_nonneg _
  · filter_upwards [self_mem_nhdsWithin] with t ht
    have hA3pos : 0 < continuumMoment
        (fun x ↦ gluedExhaustionLimit g t x) 3 :=
      (mul_pos hc (sq_pos_of_pos ht)).trans_le (hbounds t ht).1
    have hprod := (stringA2Y_two_sided hκ hc hC ht hA2 hA3 hprodTop
      (fun s hs ↦ ⟨(hbounds s hs).1, (hbounds s hs).2.1⟩)).2
    have hprodNonneg : 0 ≤ stringA2Y κ
        (fun s ↦ continuumMoment (fun x ↦ gluedExhaustionLimit g s x) 2)
        (fun s ↦ continuumMoment (fun x ↦ gluedExhaustionLimit g s x) 3) t := by
      unfold stringA2Y stringY
      exact mul_nonneg (hbounds t ht).2.2.1 (div_nonneg hκ.le hA3pos.le)
    have hdev := subsequentialConstructedPhi_deviation_bound
      m data phi g hphi hlim hC hp ht (fun s hs ↦ (hbounds s hs).2.2.2)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hprodNonneg,
      abs_sub_comm, abs_of_nonneg hdev.1]
    calc
      stringA2Y κ
            (fun s ↦ continuumMoment (fun x ↦ gluedExhaustionLimit g s x) 2)
            (fun s ↦ continuumMoment (fun x ↦ gluedExhaustionLimit g s x) 3) t *
          (1 - constructedPhi (fun s ↦ subsequentialLaplaceGap g s p) t) ≤
          ((κ / c) * t⁻¹) * ((p ^ 2 * C / 8) * t ^ 2) := by
        exact mul_le_mul hprod hdev.2 hdev.1 (mul_nonneg (div_nonneg hκ.le hc.le) (inv_nonneg.mpr ht.le))
      _ = K * t := by
        have htpos : 0 < t := ht
        dsimp only [K]
        rw [inv_eq_one_div]
        field_simp [ne_of_gt htpos, ne_of_gt hc]
        ring

theorem tendsto_subsequentialEndpoint_add_coordinate
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
    (hA2 : ∀ s : ℝ, 0 < s →
      HasDerivAt
        (fun t ↦ continuumMoment (fun x ↦ gluedExhaustionLimit g t x) 2)
        (continuumMoment (fun x ↦ gluedExhaustionLimit g s x) 0 *
          continuumMoment (fun x ↦ gluedExhaustionLimit g s x) 2 - 1) s)
    (hA3 : ∀ s : ℝ, 0 < s →
      HasDerivAt
        (fun t ↦ continuumMoment (fun x ↦ gluedExhaustionLimit g t x) 3)
        (continuumMoment (fun x ↦ gluedExhaustionLimit g s x) 0 *
          continuumMoment (fun x ↦ gluedExhaustionLimit g s x) 3) s)
    (hprodTop : Tendsto
      (stringA2Y κ
        (fun t ↦ continuumMoment (fun x ↦ gluedExhaustionLimit g t x) 2)
        (fun t ↦ continuumMoment (fun x ↦ gluedExhaustionLimit g t x) 3))
      atTop (𝓝 0))
    (hbounds : ∀ t : ℝ, 0 < t →
      c * t ^ 2 ≤ continuumMoment (fun x ↦ gluedExhaustionLimit g t x) 3 ∧
      continuumMoment (fun x ↦ gluedExhaustionLimit g t x) 3 ≤ C * t ^ 2 ∧
      0 ≤ continuumMoment (fun x ↦ gluedExhaustionLimit g t x) 2 ∧
      continuumMoment (fun x ↦ gluedExhaustionLimit g t x) 2 ≤ C * t) :
    Tendsto
      (fun t : ℝ ↦
        constructedEndpointAtTime p
          (stringY κ (fun s ↦ continuumMoment
            (fun x ↦ gluedExhaustionLimit g s x) 3))
          (fun s ↦ subsequentialLaplaceGap g s p) t +
        stringXi κ
          (fun s ↦ continuumMoment (fun x ↦ gluedExhaustionLimit g s x) 2)
          (fun s ↦ continuumMoment (fun x ↦ gluedExhaustionLimit g s x) 3) t)
      (𝓝[>] (0 : ℝ)) (𝓝 (-κ * p / 3)) := by
  let A2 : ℝ → ℝ := fun t ↦
    continuumMoment (fun x ↦ gluedExhaustionLimit g t x) 2
  let A3 : ℝ → ℝ := fun t ↦
    continuumMoment (fun x ↦ gluedExhaustionLimit g t x) 3
  let Z : ℝ → ℝ := fun t ↦ subsequentialLaplaceGap g t p
  let Phi := constructedPhi Z
  let R : ℝ → ℝ := fun t ↦ subsequentialThirdRemainder g t p
  have hPhi := tendsto_subsequentialConstructedPhi_one
    m data phi g hphi hlim p hp.le
  have hfirst : Tendsto (fun t : ℝ ↦ stringA2Y κ A2 A3 t * (Phi t - 1))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [A2, A3, Z, Phi] using
      subsequential_firstEndpointTerm_tendsto_zero m data phi g hphi hlim
        hκ hc hC hp.le hA2 hA3 hprodTop hbounds
  have hRnorm : Tendsto (fun t : ℝ ↦ R t / A3 t)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [R, A3] using
      subsequentialThirdRemainder_normalized_tendsto_zero
        m data phi g hphi hlim p hp.le
  have hremBase : Tendsto
      (fun t : ℝ ↦ (2 * κ / p ^ 2) * Phi t * (R t / A3 t))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    convert (tendsto_const_nhds.mul hPhi).mul hRnorm using 1 <;> ring
  have hrem : Tendsto
      (fun t : ℝ ↦ (2 / p ^ 2) * stringY κ A3 t * Phi t * R t)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    apply hremBase.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    have hA3pos : 0 < A3 t :=
      (mul_pos hc (sq_pos_of_pos ht)).trans_le (hbounds t ht).1
    unfold stringY
    field_simp [hp.ne', hA3pos.ne']
  have hexpansion : ∀ t : ℝ, 0 < t →
      constructedEndpointAtTime p (stringY κ A3) Z t +
          stringXi κ A2 A3 t =
        stringA2Y κ A2 A3 t * (Phi t - 1) -
          (κ * p / 3) * Phi t +
          (2 / p ^ 2) * stringY κ A3 t * Phi t * R t := by
    intro t ht
    have hTaylor := subsequentialLaplaceGap_taylor
      m data phi g hphi hlim ht hp.le
    have hA3pos : 0 < A3 t :=
      (mul_pos hc (sq_pos_of_pos ht)).trans_le (hbounds t ht).1
    have halg := constructedEndpointAtTime_add_coordinate_eq p κ (A2 t) (A3 t)
      (stringY κ A3 t) (Z t) (R t) (stringXi κ A2 A3 t) (Phi t)
      hp.ne'
      (by simpa only [A2, A3, Z, R] using hTaylor)
      (by unfold stringY; field_simp [hA3pos.ne'])
      (by simp only [stringXi, stringA2Y]; ring)
    simpa only [Phi, constructedEndpointAtTime, stringA2Y,
      mul_comm (A2 t) (stringY κ A3 t)] using halg
  simpa only [A2, A3, Z, Phi, R] using
    tendsto_constructedEndpoint_add_coordinate_at_zero p κ
      (constructedEndpointAtTime p (stringY κ A3) Z)
      (stringXi κ A2 A3) (fun t ↦ stringA2Y κ A2 A3 t * (Phi t - 1))
      Phi (fun t ↦ (2 / p ^ 2) * stringY κ A3 t * Phi t * R t)
      hexpansion hfirst hPhi hrem

end

end DerridaRetaux.FixedArity
