import DerridaRetaux.Main.ContinuumPhysicalTime
import DerridaRetaux.Main.ContinuumRemainder
import DerridaRetaux.Rigidity.RiccatiPhysicalTime
import DerridaRetaux.Analysis.LaplaceUniqueness

set_option autoImplicit false

open Filter Set Topology MeasureTheory

namespace DerridaRetaux.FixedArity

noncomputable section

/-- Every subsequential continuum limit is the explicit Yaglom density. -/
theorem subsequentialDensity_eq_yaglom
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
    ∀ t x : ℝ, 0 < t → 0 ≤ x →
      gluedExhaustionLimit g t x =
        4 / t ^ 2 * Real.exp (-2 * x / t) := by
  let A0 : ℝ → ℝ := fun t ↦
    continuumMoment (fun x ↦ gluedExhaustionLimit g t x) 0
  let A2 : ℝ → ℝ := fun t ↦
    continuumMoment (fun x ↦ gluedExhaustionLimit g t x) 2
  let A3 : ℝ → ℝ := fun t ↦
    continuumMoment (fun x ↦ gluedExhaustionLimit g t x) 3
  let d : ℝ := 2 * κ / 3
  obtain ⟨c, C, hc, hC, hbounds⟩ :=
    subsequentialMoment_rigidityBounds m data phi g hphi hlim
  have hphysical := subsequential_physicalTime_identification
    m data phi g hphi hlim hκ
  have hxi : ∀ t : ℝ, 0 < t → stringXi κ A2 A3 t = -d / t := by
    simpa only [A2, A3, d] using hphysical.1
  have hY : ∀ t : ℝ, 0 < t → stringY κ A3 t = d / t ^ 2 := by
    simpa only [A3, d] using hphysical.2.1
  have hA0 : ∀ t : ℝ, 0 < t → A0 t = 2 / t := by
    simpa only [A0] using hphysical.2.2
  have hA3pos : ∀ t : ℝ, 0 < t → 0 < A3 t := fun t ht ↦
    (mul_pos hc (sq_pos_of_pos ht)).trans_le (hbounds t ht).1
  have hA2eq : ∀ t : ℝ, 0 < t → A2 t = t := by
    intro t ht
    have hx := hxi t ht
    have hy := hY t ht
    simp only [stringXi, stringA2Y] at hx
    rw [hy] at hx
    dsimp only [d] at hx
    field_simp [hκ.ne', ht.ne'] at hx
    have hfactorNe : (2 * κ) * (3 * t) ≠ 0 := by positivity
    apply mul_right_cancel₀ hfactorNe
    calc
      A2 t * ((2 * κ) * (3 * t)) = A2 t * (2 * κ) * (3 * t) := by ring
      _ = 2 * κ * (3 * t ^ 2) := hx
      _ = t * ((2 * κ) * (3 * t)) := by ring
  have hA3eq : ∀ t : ℝ, 0 < t → A3 t = (3 / 2 : ℝ) * t ^ 2 := by
    intro t ht
    have hy := hY t ht
    simp only [stringY] at hy
    dsimp only [d] at hy
    field_simp [hκ.ne', (hA3pos t ht).ne', ht.ne'] at hy
    nlinarith
  have hgap : ∀ p : ℝ, 0 < p → ∀ t : ℝ, 0 < t →
      subsequentialLaplaceGap g t p = t * p ^ 2 / (t * p + 2) := by
    intro p hp
    let Z : ℝ → ℝ := fun t ↦ subsequentialLaplaceGap g t p
    let R : ℝ → ℝ := fun t ↦ subsequentialThirdRemainder g t p
    have hRnorm : Tendsto (fun t : ℝ ↦ R t / A3 t)
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      simpa only [R, A3] using
        subsequentialThirdRemainder_normalized_tendsto_zero
          m data phi g hphi hlim p hp.le
    have hRover : Tendsto (fun t : ℝ ↦ R t / t ^ 2)
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have hscaled : Tendsto (fun t : ℝ ↦ (3 / 2 : ℝ) * (R t / A3 t))
          (𝓝[>] (0 : ℝ)) (𝓝 0) := by
        simpa only [mul_zero] using tendsto_const_nhds.mul hRnorm
      apply hscaled.congr'
      filter_upwards [self_mem_nhdsWithin] with t ht
      have htpos : 0 < t := ht
      rw [hA3eq t htpos]
      field_simp [htpos.ne']
      ring
    have hlin : Tendsto (fun t : ℝ ↦ -(p ^ 4 / 4) * t)
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have hid : Tendsto (fun t : ℝ ↦ t) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
        tendsto_id.mono_left inf_le_left
      simpa only [mul_zero] using tendsto_const_nhds.mul hid
    have hfactor : Tendsto (fun t : ℝ ↦ t * p + 2)
        (𝓝[>] (0 : ℝ)) (𝓝 2) := by
      have hid : Tendsto (fun t : ℝ ↦ t) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
        tendsto_id.mono_left inf_le_left
      convert (hid.mul_const p).add_const 2 using 1 <;> ring
    have hResidual : Tendsto (riccatiResidualNormalized p Z)
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have hbase : Tendsto
          (fun t : ℝ ↦ -(p ^ 4 / 4) * t + (t * p + 2) * (R t / t ^ 2))
          (𝓝[>] (0 : ℝ)) (𝓝 0) := by
        simpa only [add_zero, mul_zero] using hlin.add (hfactor.mul hRover)
      apply hbase.congr'
      filter_upwards [self_mem_nhdsWithin] with t ht
      have htpos : 0 < t := ht
      have hTaylor := subsequentialLaplaceGap_taylor
        m data phi g hphi hlim htpos hp.le
      have hA2t := hA2eq t htpos
      have hA3t := hA3eq t htpos
      dsimp only [A2] at hA2t
      dsimp only [A3] at hA3t
      dsimp only [Z, R, riccatiResidualNormalized]
      rw [hTaylor, hA2t, hA3t]
      field_simp [htpos.ne']
      ring
    have hZderiv : ∀ t : ℝ, 0 < t → HasDerivAt Z
        ((2 / t) * Z t + (1 / 2 : ℝ) * (Z t ^ 2 - p ^ 2)) t := by
      intro t ht
      have hsource := subsequentialLaplaceGap_hasDerivAt
        m data phi g hphi hlim p t hp.le ht
      have hA0t : continuumMoment (fun x ↦ gluedExhaustionLimit g t x) 0 =
          2 / t := by simpa only [A0] using hA0 t ht
      rw [hA0t] at hsource
      simpa only [Z] using hsource
    have hInt : ∀ t : ℝ, 0 < t → IntervalIntegrable Z volume 0 t := by
      intro t ht
      simpa only [Z] using subsequentialLaplaceGap_intervalIntegrable
        m data phi g hphi hlim p t hp.le ht
    have hPhi : Tendsto (constructedPhi Z) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
      simpa only [Z] using tendsto_subsequentialConstructedPhi_one
        m data phi g hphi hlim p hp.le
    simpa only [Z] using riccati_eq_physicalTime_of_entrance
      p Z hp.le hZderiv hInt hPhi hResidual
  intro t x ht hx
  let u : ℝ → ℝ := fun y ↦ gluedExhaustionLimit g t y
  have hucont : ContinuousOn u (Ici (0 : ℝ)) := by
    simpa only [u] using subsequential_slice_continuous_for_gap
      m data phi g hlim ht
  have hunonneg : ∀ y ∈ Ici (0 : ℝ), 0 ≤ u y := by
    intro y hy
    exact gluedExhaustionLimit_nonneg m data.law data.arity data.critical
      phi g hphi hlim ht hy
  have huint : IntegrableOn u (Ici (0 : ℝ)) := by
    simpa only [u, pow_zero, one_mul] using subsequentialMoment_integrable
      m data.law data.arity data.critical data.third data.notBinaryFixedPoint
        phi g hphi hlim t ht 0 (by norm_num)
  refine yaglomDensity_eq_of_laplace ht hucont hunonneg huint ?_ x hx
  intro p hp
  have hZvalue := hgap p hp t ht
  have hU : continuumLaplace u p = 4 / (t * (t * p + 2)) := by
    apply physicalTimeLaplaceTransform_eq t p (A0 t)
      (subsequentialLaplaceGap g t p) (continuumLaplace u p) ht hp.le
    · exact hA0 t ht
    · exact hZvalue
    · dsimp only [u, A0, subsequentialLaplaceGap]
      ring
  simpa only [continuumLaplace, u, neg_mul] using hU

end

end DerridaRetaux.FixedArity
