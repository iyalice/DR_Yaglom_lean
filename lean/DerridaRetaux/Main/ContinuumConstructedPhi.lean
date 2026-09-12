import DerridaRetaux.Main.ContinuumLaplaceGapRegularity
import DerridaRetaux.Rigidity.ConstructedSolution

set_option autoImplicit false

open Filter Set Topology MeasureTheory

namespace DerridaRetaux.FixedArity

noncomputable section

theorem subsequentialLaplaceGap_integral_tendsto_zero
    (m : ℕ) (data : ProfileInitialData m)
    (phi : ℕ → ℕ)
    (g : ∀ k, BoundedContinuousFunction (gridExhaustionRectangle k) ℝ)
    (hphi : Tendsto phi atTop atTop)
    (hlim : ∀ k, TendstoUniformly
      (fun n (q : gridExhaustionRectangle k) ↦
        gridBilinearInterp (phi n) (orbitScaledGrid m data.law (phi n))
          (q : ℝ × ℝ).1 (q : ℝ × ℝ).2)
      (fun q ↦ g k q) atTop)
    (p : ℝ) (hp : 0 ≤ p) :
    Tendsto (fun t : ℝ ↦ ∫ s in (0 : ℝ)..t, subsequentialLaplaceGap g s p)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  obtain ⟨C, hC, hb⟩ := subsequentialMoment_bounds m data phi g hphi hlim
  let K : ℝ := (p ^ 2 / 2) * C
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hupperLim : Tendsto (fun t : ℝ ↦ K * (t ^ 2 / 2))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hid : Tendsto (fun t : ℝ ↦ t) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
      tendsto_id.mono_left inf_le_left
    have hconst : Tendsto (fun _ : ℝ ↦ K) (𝓝[>] (0 : ℝ)) (𝓝 K) :=
      tendsto_const_nhds
    convert hconst.mul ((hid.pow 2).div_const (2 : ℝ)) using 1 <;> ring
  apply squeeze_zero' _ _ hupperLim
  · filter_upwards [self_mem_nhdsWithin] with t ht
    have hInt := subsequentialLaplaceGap_intervalIntegrable
      m data phi g hphi hlim p t hp ht
    rw [intervalIntegral.integral_of_le ht.le]
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    exact (subsequentialLaplaceGap_nonneg_and_le
      m data phi g hphi hlim hs.1 hp).1
  · filter_upwards [self_mem_nhdsWithin] with t ht
    have hInt := subsequentialLaplaceGap_intervalIntegrable
      m data phi g hphi hlim p t hp ht
    have hUpperInt : IntervalIntegrable (fun s : ℝ ↦ K * s) volume 0 t :=
      (continuous_const.mul continuous_id).intervalIntegrable 0 t
    calc
      (∫ s in (0 : ℝ)..t, subsequentialLaplaceGap g s p) ≤
          ∫ s in (0 : ℝ)..t, K * s := by
        apply intervalIntegral.integral_mono_on_of_le_Ioo ht.le hInt hUpperInt
        intro s hs
        calc
          subsequentialLaplaceGap g s p ≤ (p ^ 2 / 2) *
              continuumMoment (fun x ↦ gluedExhaustionLimit g s x) 2 :=
            (subsequentialLaplaceGap_nonneg_and_le
              m data phi g hphi hlim hs.1 hp).2
          _ ≤ (p ^ 2 / 2) * (C * s) := by
            gcongr
            exact (hb s hs.1).2.2.1
          _ = K * s := by simp only [K]; ring
      _ = K * (t ^ 2 / 2) := by
        rw [intervalIntegral.integral_const_mul, integral_id]
        ring

theorem tendsto_subsequentialConstructedPhi_one
    (m : ℕ) (data : ProfileInitialData m)
    (phi : ℕ → ℕ)
    (g : ∀ k, BoundedContinuousFunction (gridExhaustionRectangle k) ℝ)
    (hphi : Tendsto phi atTop atTop)
    (hlim : ∀ k, TendstoUniformly
      (fun n (q : gridExhaustionRectangle k) ↦
        gridBilinearInterp (phi n) (orbitScaledGrid m data.law (phi n))
          (q : ℝ × ℝ).1 (q : ℝ × ℝ).2)
      (fun q ↦ g k q) atTop)
    (p : ℝ) (hp : 0 ≤ p) :
    Tendsto (constructedPhi (fun t ↦ subsequentialLaplaceGap g t p))
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  have hI := subsequentialLaplaceGap_integral_tendsto_zero
    m data phi g hphi hlim p hp
  have hscaled : Tendsto
      (fun t : ℝ ↦ -(1 / 2 : ℝ) *
        ∫ s in (0 : ℝ)..t, subsequentialLaplaceGap g s p)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    convert tendsto_const_nhds.mul hI using 1 <;> ring
  simpa only [constructedPhi, Real.exp_zero] using
    Real.continuous_exp.continuousAt.tendsto.comp hscaled

end

end DerridaRetaux.FixedArity
