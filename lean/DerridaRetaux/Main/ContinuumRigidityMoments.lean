import DerridaRetaux.Main.ContinuumMomentODE
import DerridaRetaux.Analysis.HalfLineDensityMeasure
import DerridaRetaux.Rigidity.StringCoordinates
import Mathlib.Tactic

set_option autoImplicit false

open Filter Set Topology MeasureTheory

namespace DerridaRetaux.FixedArity

noncomputable section

/-- The moment data needed by the string construction: a uniform quadratic
two-sided bound for `A₃`, together with positivity and the linear `A₂` bound. -/
theorem subsequentialMoment_rigidityBounds
    (m : ℕ) (data : ProfileInitialData m)
    (phi : ℕ → ℕ)
    (g : ∀ k, BoundedContinuousFunction (gridExhaustionRectangle k) ℝ)
    (hphi : Tendsto phi atTop atTop)
    (hlim : ∀ k, TendstoUniformly
      (fun n (q : gridExhaustionRectangle k) ↦
        gridBilinearInterp (phi n) (orbitScaledGrid m data.law (phi n))
          (q : ℝ × ℝ).1 (q : ℝ × ℝ).2)
      (fun q ↦ g k q) atTop) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ t : ℝ, 0 < t →
      c * t ^ 2 ≤ continuumMoment
          (fun x ↦ gluedExhaustionLimit g t x) 3 ∧
      continuumMoment (fun x ↦ gluedExhaustionLimit g t x) 3 ≤ C * t ^ 2 ∧
      0 ≤ continuumMoment (fun x ↦ gluedExhaustionLimit g t x) 2 ∧
      continuumMoment (fun x ↦ gluedExhaustionLimit g t x) 2 ≤ C * t := by
  obtain ⟨C, hC, hb⟩ := subsequentialMoment_bounds
    m data phi g hphi hlim
  refine ⟨1 / C ^ 2, C, by positivity, hC, ?_⟩
  intro t ht
  let u : ℝ → ℝ := fun x ↦ gluedExhaustionLimit g t x
  have huFull := subsequentialDensity_continuousOn_positiveHalfStrip
    m data phi g hlim t ht
  have hucont : ContinuousOn u (Ici (0 : ℝ)) := by
    let emb : ℝ → ℝ × ℝ := fun x ↦ (t, x)
    change ContinuousOn
      ((fun q : ℝ × ℝ ↦ gluedExhaustionLimit g q.1 q.2) ∘ emb)
        (Ici (0 : ℝ))
    exact huFull.comp (by dsimp only [emb]; fun_prop) (fun x hx ↦ by
      dsimp only [emb]
      change t ≤ t ∧ (0 : ℝ) ≤ x
      exact ⟨le_rfl, hx⟩)
  have hunonneg : ∀ x : ℝ, 0 ≤ x → 0 ≤ u x := by
    intro x hx
    exact gluedExhaustionLimit_nonneg m data.law data.arity data.critical
      phi g hphi hlim ht hx
  have hi : ∀ r : ℕ, r ≤ 3 →
      IntegrableOn (fun x : ℝ ↦ x ^ r * u x) (Ici 0) := by
    intro r hr
    simpa only [u] using subsequentialMoment_integrable
      m data.law data.arity data.critical data.third data.notBinaryFixedPoint
        phi g hphi hlim t ht r hr
  let μ : Measure ℝ := halfLineDensityMeasure u
  have hiμ : ∀ r : ℕ, r ≤ 3 →
      IntegrableOn (fun x : ℝ ↦ x ^ r) (Ici 0) μ := by
    intro r hr
    rw [integrableOn_halfLineDensityMeasure_iff u (fun x : ℝ ↦ x ^ r)
      hucont hunonneg]
    exact hi r hr
  have hA1 : positiveHalfLineMoment 1 μ = 1 := by
    rw [positiveHalfLineMoment_halfLineDensityMeasure u 1 hucont hunonneg]
    simpa only [u] using (hb t ht).2.1
  have hlowerRaw := (positiveHalfLineMoment_A3_lower μ
    (hiμ 0 (by norm_num)) (by simpa only [pow_one] using hiμ 1 (by norm_num))
    (hiμ 2 (by norm_num)) (hiμ 3 (by norm_num)) hA1).1
  rw [positiveHalfLineMoment_halfLineDensityMeasure u 0 hucont hunonneg,
    positiveHalfLineMoment_halfLineDensityMeasure u 3 hucont hunonneg]
    at hlowerRaw
  have hA0nonneg : 0 ≤ continuumMoment u 0 := by
    unfold continuumMoment
    apply integral_nonneg_of_ae
    filter_upwards [self_mem_ae_restrict measurableSet_Ici] with x hx
    exact mul_nonneg (pow_nonneg hx 0) (hunonneg x hx)
  have hA2nonneg : 0 ≤ continuumMoment u 2 := by
    unfold continuumMoment
    apply integral_nonneg_of_ae
    filter_upwards [self_mem_ae_restrict measurableSet_Ici] with x hx
    exact mul_nonneg (pow_nonneg hx 2) (hunonneg x hx)
  have hA3nonneg : 0 ≤ continuumMoment u 3 := by
    unfold continuumMoment
    apply integral_nonneg_of_ae
    filter_upwards [self_mem_ae_restrict measurableSet_Ici] with x hx
    exact mul_nonneg (pow_nonneg hx 3) (hunonneg x hx)
  have hA0upper : continuumMoment u 0 ≤ C / t := by
    simpa only [u] using (hb t ht).1
  have hA0sq : continuumMoment u 0 ^ 2 ≤ (C / t) ^ 2 :=
    (sq_le_sq₀ hA0nonneg (div_nonneg hC.le ht.le)).2 hA0upper
  have hprod : 1 ≤ (C / t) ^ 2 * continuumMoment u 3 :=
    hlowerRaw.trans (mul_le_mul_of_nonneg_right hA0sq hA3nonneg)
  have hlower : (1 / C ^ 2) * t ^ 2 ≤ continuumMoment u 3 := by
    have hscale : 0 ≤ t ^ 2 / C ^ 2 := by positivity
    have hscaled := mul_le_mul_of_nonneg_left hprod hscale
    calc
      (1 / C ^ 2) * t ^ 2 = (t ^ 2 / C ^ 2) * 1 := by ring
      _ ≤ (t ^ 2 / C ^ 2) * ((C / t) ^ 2 * continuumMoment u 3) := hscaled
      _ = continuumMoment u 3 := by field_simp [hC.ne', ht.ne']; ring
  exact ⟨by simpa only [u] using hlower,
    (hb t ht).2.2.2,
    by simpa only [u] using hA2nonneg,
    (hb t ht).2.2.1⟩

/-- The product `A₂Y` vanishes at large time, as required to integrate the
coordinate ODE from infinity. -/
theorem subsequential_stringA2Y_tendsto_atTop_zero
    (m : ℕ) (data : ProfileInitialData m)
    (phi : ℕ → ℕ)
    (g : ∀ k, BoundedContinuousFunction (gridExhaustionRectangle k) ℝ)
    (hphi : Tendsto phi atTop atTop)
    (hlim : ∀ k, TendstoUniformly
      (fun n (q : gridExhaustionRectangle k) ↦
        gridBilinearInterp (phi n) (orbitScaledGrid m data.law (phi n))
          (q : ℝ × ℝ).1 (q : ℝ × ℝ).2)
      (fun q ↦ g k q) atTop)
    {κ c C : ℝ} (hκ : 0 < κ) (hc : 0 < c) (hC : 0 < C)
    (hbounds : ∀ t : ℝ, 0 < t →
      c * t ^ 2 ≤ continuumMoment
          (fun x ↦ gluedExhaustionLimit g t x) 3 ∧
      continuumMoment (fun x ↦ gluedExhaustionLimit g t x) 3 ≤ C * t ^ 2 ∧
      0 ≤ continuumMoment (fun x ↦ gluedExhaustionLimit g t x) 2 ∧
      continuumMoment (fun x ↦ gluedExhaustionLimit g t x) 2 ≤ C * t) :
    Tendsto
      (stringA2Y κ
        (fun t ↦ continuumMoment (fun x ↦ gluedExhaustionLimit g t x) 2)
        (fun t ↦ continuumMoment (fun x ↦ gluedExhaustionLimit g t x) 3))
      atTop (𝓝 0) := by
  let A2 : ℝ → ℝ := fun t ↦
    continuumMoment (fun x ↦ gluedExhaustionLimit g t x) 2
  let A3 : ℝ → ℝ := fun t ↦
    continuumMoment (fun x ↦ gluedExhaustionLimit g t x) 3
  let upper : ℝ → ℝ := fun t ↦ (C * κ / c) / t
  have hupperZero : Tendsto upper atTop (𝓝 0) := by
    have hcst : Tendsto (fun _ : ℝ ↦ C * κ / c) atTop (𝓝 (C * κ / c)) :=
      tendsto_const_nhds
    have h := hcst.mul (tendsto_inv_atTop_zero :
      Tendsto (fun t : ℝ ↦ t⁻¹) atTop (𝓝 0))
    convert h using 1 <;> ring
  apply squeeze_zero' _ _ hupperZero
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    unfold stringA2Y stringY
    exact mul_nonneg (hbounds t ht).2.2.1
      (div_nonneg hκ.le ((hbounds t ht).1.trans' (by positivity)))
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    have hA3pos : 0 < A3 t :=
      (mul_pos hc (sq_pos_of_pos ht)).trans_le (hbounds t ht).1
    unfold stringA2Y stringY
    dsimp only [A2, A3]
    change continuumMoment (fun x ↦ gluedExhaustionLimit g t x) 2 *
      (κ / continuumMoment (fun x ↦ gluedExhaustionLimit g t x) 3) ≤
        (C * κ / c) / t
    calc
      continuumMoment (fun x ↦ gluedExhaustionLimit g t x) 2 *
          (κ / continuumMoment (fun x ↦ gluedExhaustionLimit g t x) 3) =
          (continuumMoment (fun x ↦ gluedExhaustionLimit g t x) 2 * κ) /
            continuumMoment (fun x ↦ gluedExhaustionLimit g t x) 3 := by ring
      _ ≤ (C * κ / c) / t := by
        apply (div_le_iff₀ hA3pos).2
        have hA2upper := (hbounds t ht).2.2.2
        have hscaled := mul_le_mul_of_nonneg_right hA2upper hκ.le
        calc
          continuumMoment (fun x ↦ gluedExhaustionLimit g t x) 2 * κ ≤
              (C * t) * κ := hscaled
          _ = ((C * κ / c) / t) * (c * t ^ 2) := by
            field_simp [hc.ne', ht.ne']
            ring
          _ ≤ ((C * κ / c) / t) *
              continuumMoment (fun x ↦ gluedExhaustionLimit g t x) 3 := by
            exact mul_le_mul_of_nonneg_left (hbounds t ht).1 (by positivity)

end

end DerridaRetaux.FixedArity
