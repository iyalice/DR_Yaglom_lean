import DerridaRetaux.Main.ContinuumIdentification
import DerridaRetaux.Rigidity.CumulativeToPhysicalTime
import DerridaRetaux.Rigidity.PhysicalTime

set_option autoImplicit false

open Filter Set Topology

namespace DerridaRetaux.FixedArity

noncomputable section

/-- String identification fixes the source coordinate, scale, and zeroth
moment in physical time. -/
theorem subsequential_physicalTime_identification
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
    (∀ t : ℝ, 0 < t →
      stringXi κ
          (fun s ↦ continuumMoment (fun x ↦ gluedExhaustionLimit g s x) 2)
          (fun s ↦ continuumMoment (fun x ↦ gluedExhaustionLimit g s x) 3) t =
        -(2 * κ / 3) / t) ∧
    (∀ t : ℝ, 0 < t →
      stringY κ
          (fun s ↦ continuumMoment (fun x ↦ gluedExhaustionLimit g s x) 3) t =
        (2 * κ / 3) / t ^ 2) ∧
    (∀ t : ℝ, 0 < t →
      continuumMoment (fun x ↦ gluedExhaustionLimit g t x) 0 = 2 / t) := by
  let A0 : ℝ → ℝ := fun t ↦
    continuumMoment (fun x ↦ gluedExhaustionLimit g t x) 0
  let A2 : ℝ → ℝ := fun t ↦
    continuumMoment (fun x ↦ gluedExhaustionLimit g t x) 2
  let A3 : ℝ → ℝ := fun t ↦
    continuumMoment (fun x ↦ gluedExhaustionLimit g t x) 3
  let xi : ℝ → ℝ := stringXi κ A2 A3
  let Y : ℝ → ℝ := stringY κ A3
  let d : ℝ := 2 * κ / 3
  have hd : 0 < d := by dsimp only [d]; positivity
  obtain ⟨c, C, hc, hC, hbounds⟩ :=
    subsequentialMoment_rigidityBounds m data phi g hphi hlim
  have hmom := subsequentialMomentODE m data phi g hphi hlim
  have hA2 : ∀ s : ℝ, 0 < s → HasDerivAt A2 (A0 s * A2 s - 1) s := by
    simpa only [A0, A2] using hmom.2.1
  have hA3 : ∀ s : ℝ, 0 < s → HasDerivAt A3 (A0 s * A3 s) s := by
    simpa only [A0, A3] using hmom.2.2
  have hA3pos : ∀ s : ℝ, 0 < s → 0 < A3 s := fun s hs ↦
    (mul_pos hc (sq_pos_of_pos hs)).trans_le (hbounds s hs).1
  have hprodTop : Tendsto (stringA2Y κ A2 A3) atTop (𝓝 0) :=
    subsequential_stringA2Y_tendsto_atTop_zero
      m data phi g hphi hlim hκ hc hC hbounds
  have hcum : ∀ x : ℝ,
      stringCumulative (constructedEntranceString κ A2 A3) x =
        stringCumulative (modelEntranceString d) x := by
    simpa only [A2, A3, d] using
      subsequentialConstructedString_cumulative_eq_model
        m data phi g hphi hlim hκ
  have hYxi : ∀ t : ℝ, 0 < t → Y t = xi t ^ 2 / d := by
    simpa only [Y, xi] using
      stringY_eq_stringXi_sq_div_of_cumulative_eq_model
        hκ hc hC hd hA2 hA3 hprodTop
          (fun s hs ↦ ⟨(hbounds s hs).1, (hbounds s hs).2.1⟩) hcum
  let hmono := strictMonoOn_stringXi hκ hA2 hA3 hA3pos
  let hbij := stringXi_bijOn hκ hc hC hA2 hA3 hprodTop
    (fun s hs ↦ ⟨(hbounds s hs).1, (hbounds s hs).2.1⟩)
  have hxiNeg : ∀ t : ℝ, 0 < t → xi t < 0 := fun t ht ↦ hbij.1 ht
  have hxiDeriv : ∀ t : ℝ, 0 < t → HasDerivAt xi (xi t ^ 2 / d) t := by
    intro t ht
    have hbase := hasDerivAt_stringXi κ A0 A2 A3
      (hA2 t ht) (hA3 t ht) (hA3pos t ht).ne'
    simpa only [xi, Y, hYxi t ht] using hbase
  have hxiZero : Tendsto xi (𝓝[>] (0 : ℝ)) atBot := by
    simpa only [xi] using tendsto_stringXi_nhdsGT_zero_atBot
      hκ hc hC hA2 hA3 hprodTop
        (fun s hs ↦ ⟨(hbounds s hs).1, (hbounds s hs).2.1⟩)
  have hxi : ∀ t : ℝ, 0 < t → xi t = -d / t :=
    physicalTimeCoordinate_eq_neg_div d xi hd hxiNeg hxiDeriv hxiZero
  have hY : ∀ t : ℝ, 0 < t → Y t = d / t ^ 2 :=
    physicalTimeScale_eq d xi Y hd hxi hYxi
  have hYDeriv : ∀ t : ℝ, 0 < t →
      HasDerivAt Y (-A0 t * Y t) t := by
    intro t ht
    simpa only [Y] using
      hasDerivAt_stringY κ A0 A3 (hA3 t ht) (hA3pos t ht).ne'
  have hA0 : ∀ t : ℝ, 0 < t → A0 t = 2 / t :=
    physicalTimeZerothMoment_eq d Y A0 hd hY hYDeriv
  exact ⟨by simpa only [A2, A3, xi, d] using hxi,
    by simpa only [A3, Y, d] using hY,
    by simpa only [A0] using hA0⟩

end

end DerridaRetaux.FixedArity
