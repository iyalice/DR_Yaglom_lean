import DerridaRetaux.Main.ContinuumLaplaceGap

set_option autoImplicit false

open Filter Set Topology MeasureTheory

namespace DerridaRetaux.FixedArity

noncomputable section

theorem subsequentialLaplaceGap_continuousAt
    (m : ℕ) (data : ProfileInitialData m)
    (phi : ℕ → ℕ)
    (g : ∀ k, BoundedContinuousFunction (gridExhaustionRectangle k) ℝ)
    (hphi : Tendsto phi atTop atTop)
    (hlim : ∀ k, TendstoUniformly
      (fun n (q : gridExhaustionRectangle k) ↦
        gridBilinearInterp (phi n) (orbitScaledGrid m data.law (phi n))
          (q : ℝ × ℝ).1 (q : ℝ × ℝ).2)
      (fun q ↦ g k q) atTop)
    (p t : ℝ) (hp : 0 ≤ p) (ht : 0 < t) :
    ContinuousAt (fun s ↦ subsequentialLaplaceGap g s p) t :=
  (subsequentialLaplaceGap_hasDerivAt
    m data phi g hphi hlim p t hp ht).continuousAt

theorem subsequentialLaplaceGap_stronglyMeasurableAtFilter
    (m : ℕ) (data : ProfileInitialData m)
    (phi : ℕ → ℕ)
    (g : ∀ k, BoundedContinuousFunction (gridExhaustionRectangle k) ℝ)
    (hphi : Tendsto phi atTop atTop)
    (hlim : ∀ k, TendstoUniformly
      (fun n (q : gridExhaustionRectangle k) ↦
        gridBilinearInterp (phi n) (orbitScaledGrid m data.law (phi n))
          (q : ℝ × ℝ).1 (q : ℝ × ℝ).2)
      (fun q ↦ g k q) atTop)
    (p t : ℝ) (hp : 0 ≤ p) (ht : 0 < t) :
    StronglyMeasurableAtFilter (fun s ↦ subsequentialLaplaceGap g s p)
      (𝓝 t) volume := by
  apply ContinuousAt.stronglyMeasurableAtFilter (μ := volume) isOpen_Ioi
  · intro s hs
    exact subsequentialLaplaceGap_continuousAt
      m data phi g hphi hlim p s hp hs
  · exact ht

/-- The gap is interval-integrable down to the entrance time; its linear upper
bound removes any issue at the endpoint `0`. -/
theorem subsequentialLaplaceGap_intervalIntegrable
    (m : ℕ) (data : ProfileInitialData m)
    (phi : ℕ → ℕ)
    (g : ∀ k, BoundedContinuousFunction (gridExhaustionRectangle k) ℝ)
    (hphi : Tendsto phi atTop atTop)
    (hlim : ∀ k, TendstoUniformly
      (fun n (q : gridExhaustionRectangle k) ↦
        gridBilinearInterp (phi n) (orbitScaledGrid m data.law (phi n))
          (q : ℝ × ℝ).1 (q : ℝ × ℝ).2)
      (fun q ↦ g k q) atTop)
    (p t : ℝ) (hp : 0 ≤ p) (ht : 0 < t) :
    IntervalIntegrable (fun s ↦ subsequentialLaplaceGap g s p)
      volume 0 t := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ht.le]
  obtain ⟨C, hC, hb⟩ := subsequentialMoment_bounds m data phi g hphi hlim
  have hcont : ContinuousOn (fun s ↦ subsequentialLaplaceGap g s p)
      (Ioc (0 : ℝ) t) := by
    intro s hs
    exact (subsequentialLaplaceGap_continuousAt
      m data phi g hphi hlim p s hp hs.1).continuousWithinAt
  have hmeas : AEStronglyMeasurable (fun s ↦ subsequentialLaplaceGap g s p)
      (volume.restrict (Ioc (0 : ℝ) t)) :=
    (hcont.aemeasurable measurableSet_Ioc).aestronglyMeasurable
  have hconst : Integrable (fun _ : ℝ ↦ (p ^ 2 / 2) * (C * t))
      (volume.restrict (Ioc (0 : ℝ) t)) := by
    exact integrableOn_const.2 (.inr measure_Ioc_lt_top)
  apply hconst.mono' hmeas
  filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with s hs
  have hgap := subsequentialLaplaceGap_nonneg_and_le
    m data phi g hphi hlim hs.1 hp
  rw [Real.norm_eq_abs, abs_of_nonneg hgap.1]
  calc
    subsequentialLaplaceGap g s p ≤ (p ^ 2 / 2) *
        continuumMoment (fun x ↦ gluedExhaustionLimit g s x) 2 := hgap.2
    _ ≤ (p ^ 2 / 2) * (C * s) := by
      exact mul_le_mul_of_nonneg_left (hb s hs.1).2.2.1 (by positivity)
    _ ≤ (p ^ 2 / 2) * (C * t) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hs.2 hC.le) (by positivity)

end

end DerridaRetaux.FixedArity
