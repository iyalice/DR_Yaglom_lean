import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

set_option autoImplicit false

open Filter Set Topology MeasureTheory

namespace DerridaRetaux

noncomputable section

/-- A jointly continuous-on-the-relevant-triangle integrand integrated over
`[t,t+h]` has right derivative equal to its value at the collapsed endpoint.
No derivative of the integrand with respect to the parameter is needed. -/
theorem hasDerivWithinAt_shrinkingInterval
    (G : ℝ → ℝ → ℝ) (t : ℝ)
    (hG : ContinuousWithinAt (fun z : ℝ × ℝ ↦ G z.1 z.2)
      {z : ℝ × ℝ | 0 ≤ z.1 ∧ t ≤ z.2 ∧ z.2 ≤ t + z.1} (0, t))
    (hInt : ∀ h : ℝ, 0 ≤ h → IntervalIntegrable (G h) volume t (t + h)) :
    HasDerivWithinAt (fun h ↦ ∫ s in t..t + h, G h s)
      (G 0 t) (Ici 0) 0 := by
  rw [hasDerivWithinAt_iff_tendsto_slope,
    Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  obtain ⟨δ, hδ, hclose⟩ :=
    (Metric.continuousWithinAt_iff.mp hG) (ε / 2) (half_pos hε)
  refine ⟨min δ 1, lt_min hδ zero_lt_one, ?_⟩
  intro h hhmem hhdist
  have hh0 : 0 ≤ h := hhmem.1
  have hhne : h ≠ 0 := by
    intro heq
    exact hhmem.2 (by simpa [heq])
  have hhpos : 0 < h := lt_of_le_of_ne hh0 (Ne.symm hhne)
  have hhδ : h < δ := by
    have habs : |h| < min δ 1 := by simpa [Real.dist_eq] using hhdist
    exact lt_of_le_of_lt (le_abs_self h) (habs.trans_le (min_le_left _ _))
  have hbound : ∀ s ∈ uIoc t (t + h),
      ‖G h s - G 0 t‖ ≤ ε / 2 := by
    intro s hs
    rw [uIoc_of_le (by linarith : t ≤ t + h)] at hs
    have hsδ : |s - t| < δ := by
      rw [abs_of_nonneg (sub_nonneg.mpr hs.1.le)]
      linarith [hs.2]
    have hpair : dist (h, s) (0, t) < δ := by
      rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq, sub_zero,
        max_lt_iff]
      exact ⟨by simpa [abs_of_pos hhpos] using hhδ, hsδ⟩
    have hpairMem : (h, s) ∈ {z : ℝ × ℝ | 0 ≤ z.1 ∧ t ≤ z.2 ∧ z.2 ≤ t + z.1} :=
      ⟨hh0, hs.1.le, hs.2⟩
    exact (hclose hpairMem hpair).le
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  have hslope :
      slope (fun q ↦ ∫ s in t..t + q, G q s) 0 h - G 0 t =
        h⁻¹ * ∫ s in t..t + h, (G h s - G 0 t) := by
    rw [intervalIntegral.integral_sub (hInt h hh0)
      (continuous_const.intervalIntegrable _ _)]
    simp only [slope, sub_zero, intervalIntegral.integral_same,
      intervalIntegral.integral_const, zero_smul, sub_zero, smul_eq_mul]
    field_simp [hhne]
  rw [Real.dist_eq, hslope, abs_mul, abs_inv, abs_of_pos hhpos]
  calc
    h⁻¹ * |∫ s in t..t + h, G h s - G 0 t| ≤
        h⁻¹ * ((ε / 2) * |t + h - t|) := by
      gcongr
      simpa only [Real.norm_eq_abs] using hnorm
    _ = ε / 2 := by rw [show t + h - t = h by ring, abs_of_pos hhpos]; field_simp [hhne]
    _ < ε := half_lt_self hε

end

end DerridaRetaux
