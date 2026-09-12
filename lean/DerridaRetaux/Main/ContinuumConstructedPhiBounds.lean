import DerridaRetaux.Main.ContinuumConstructedPhi

set_option autoImplicit false

open Filter Set Topology MeasureTheory

namespace DerridaRetaux.FixedArity

noncomputable section

theorem subsequentialLaplaceGap_integral_bounds
    (m : ℕ) (data : ProfileInitialData m)
    (phi : ℕ → ℕ)
    (g : ∀ k, BoundedContinuousFunction (gridExhaustionRectangle k) ℝ)
    (hphi : Tendsto phi atTop atTop)
    (hlim : ∀ k, TendstoUniformly
      (fun n (q : gridExhaustionRectangle k) ↦
        gridBilinearInterp (phi n) (orbitScaledGrid m data.law (phi n))
          (q : ℝ × ℝ).1 (q : ℝ × ℝ).2)
      (fun q ↦ g k q) atTop)
    {C p t : ℝ} (hC : 0 < C) (hp : 0 ≤ p) (ht : 0 < t)
    (hA2upper : ∀ s : ℝ, 0 < s →
      continuumMoment (fun x ↦ gluedExhaustionLimit g s x) 2 ≤ C * s) :
    0 ≤ ∫ s in (0 : ℝ)..t, subsequentialLaplaceGap g s p ∧
      (∫ s in (0 : ℝ)..t, subsequentialLaplaceGap g s p) ≤
        (p ^ 2 * C / 4) * t ^ 2 := by
  have hInt := subsequentialLaplaceGap_intervalIntegrable
    m data phi g hphi hlim p t hp ht
  constructor
  · rw [intervalIntegral.integral_of_le ht.le]
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    exact (subsequentialLaplaceGap_nonneg_and_le
      m data phi g hphi hlim hs.1 hp).1
  · have hUpperInt : IntervalIntegrable
        (fun s : ℝ ↦ ((p ^ 2 / 2) * C) * s) volume 0 t :=
      (continuous_const.mul continuous_id).intervalIntegrable 0 t
    calc
      (∫ s in (0 : ℝ)..t, subsequentialLaplaceGap g s p) ≤
          ∫ s in (0 : ℝ)..t, ((p ^ 2 / 2) * C) * s := by
        apply intervalIntegral.integral_mono_on_of_le_Ioo ht.le hInt hUpperInt
        intro s hs
        calc
          subsequentialLaplaceGap g s p ≤ (p ^ 2 / 2) *
              continuumMoment (fun x ↦ gluedExhaustionLimit g s x) 2 :=
            (subsequentialLaplaceGap_nonneg_and_le
              m data phi g hphi hlim hs.1 hp).2
          _ ≤ (p ^ 2 / 2) * (C * s) := by
            gcongr
            exact hA2upper s hs.1
          _ = ((p ^ 2 / 2) * C) * s := by ring
      _ = (p ^ 2 * C / 4) * t ^ 2 := by
        rw [intervalIntegral.integral_const_mul, integral_id]
        ring

theorem subsequentialConstructedPhi_deviation_bound
    (m : ℕ) (data : ProfileInitialData m)
    (phi : ℕ → ℕ)
    (g : ∀ k, BoundedContinuousFunction (gridExhaustionRectangle k) ℝ)
    (hphi : Tendsto phi atTop atTop)
    (hlim : ∀ k, TendstoUniformly
      (fun n (q : gridExhaustionRectangle k) ↦
        gridBilinearInterp (phi n) (orbitScaledGrid m data.law (phi n))
          (q : ℝ × ℝ).1 (q : ℝ × ℝ).2)
      (fun q ↦ g k q) atTop)
    {C p t : ℝ} (hC : 0 < C) (hp : 0 ≤ p) (ht : 0 < t)
    (hA2upper : ∀ s : ℝ, 0 < s →
      continuumMoment (fun x ↦ gluedExhaustionLimit g s x) 2 ≤ C * s) :
    0 ≤ 1 - constructedPhi (fun s ↦ subsequentialLaplaceGap g s p) t ∧
      1 - constructedPhi (fun s ↦ subsequentialLaplaceGap g s p) t ≤
        (p ^ 2 * C / 8) * t ^ 2 := by
  let I : ℝ := ∫ s in (0 : ℝ)..t, subsequentialLaplaceGap g s p
  obtain ⟨hInonneg, hIupper⟩ := subsequentialLaplaceGap_integral_bounds
    m data phi g hphi hlim hC hp ht hA2upper
  have hPhiOne : constructedPhi (fun s ↦ subsequentialLaplaceGap g s p) t ≤ 1 :=
    constructedPhi_le_one _ _ hInonneg
  constructor
  · linarith
  · have hexp := Real.add_one_le_exp (-(1 / 2 : ℝ) * I)
    change 1 - Real.exp (-(1 / 2 : ℝ) * I) ≤ (p ^ 2 * C / 8) * t ^ 2
    have hfirst : 1 - Real.exp (-(1 / 2 : ℝ) * I) ≤ (1 / 2 : ℝ) * I := by
      linarith
    calc
      1 - Real.exp (-(1 / 2 : ℝ) * I) ≤ (1 / 2 : ℝ) * I := hfirst
      _ ≤ (1 / 2 : ℝ) * ((p ^ 2 * C / 4) * t ^ 2) := by gcongr
      _ = (p ^ 2 * C / 8) * t ^ 2 := by ring

end

end DerridaRetaux.FixedArity
