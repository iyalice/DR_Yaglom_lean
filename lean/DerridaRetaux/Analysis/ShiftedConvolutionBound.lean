import DerridaRetaux.Analysis.ConvolutionContinuityOn
import DerridaRetaux.Analysis.FloorTransportBoxGeometry

set_option autoImplicit false

open Filter Set Topology

namespace DerridaRetaux

noncomputable section

/-- The continuum convolution evaluated along the transported floor window is
uniformly bounded, as a consequence of continuity on one compact box. -/
theorem exists_bound_positiveSelfConvolution_shifted_floor_window
    (u : ℝ → ℝ → ℝ) (scale : ℕ → ℕ)
    (t₀ t x : ℝ) (R : ℕ)
    (ht₀ : 0 < t₀) (ht : t₀ ≤ t) (hx : 0 < x)
    (hR : x + t + 1 ≤ (R : ℝ))
    (hscale : Tendsto scale atTop atTop)
    (hu : ContinuousOn (Function.uncurry u)
      (Icc (t₀ / 2) (t + 1) ×ˢ Icc (0 : ℝ) (R : ℝ))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n : ℕ in atTop,
      ∀ s ∈ Finset.Ico (gridIndex (scale n) t₀) (gridIndex (scale n) t),
        |positiveSelfConvolution
          (u ((s : ℝ) / (scale n : ℝ)))
          (x + t - (s : ℝ) / (scale n : ℝ))| ≤ C := by
  have hetaT : t₀ / 2 ≤ t + 1 := by linarith
  have hconvCont : ContinuousOn
      (fun p : ℝ × ℝ ↦ positiveSelfConvolution (u p.1) p.2)
      (Icc (t₀ / 2) (t + 1) ×ˢ Icc (0 : ℝ) (R : ℝ)) :=
    continuousOn_positiveSelfConvolution_uncurry u (t₀ / 2) (t + 1)
      (R : ℝ) hetaT (Nat.cast_nonneg R) hu
  obtain ⟨C, hC⟩ :=
    (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hconvCont
  have hCnonneg : 0 ≤ C := by
    have hp : (t₀, 0) ∈
        Icc (t₀ / 2) (t + 1) ×ˢ Icc (0 : ℝ) (R : ℝ) := by
      exact ⟨⟨by linarith, by linarith⟩, le_rfl, Nat.cast_nonneg R⟩
    exact (norm_nonneg (positiveSelfConvolution (u t₀) 0)).trans
      (hC (t₀, 0) hp)
  refine ⟨C, hCnonneg, ?_⟩
  have hinv : Tendsto (fun n : ℕ ↦ (scale n : ℝ)⁻¹) atTop (nhds 0) := by
    simpa only [Function.comp_apply] using
      tendsto_inverse_atTop_nhds_zero_nat.comp hscale
  have hthreshold : 0 < min (t₀ / 2) (min (x / 2) ((1 : ℝ) / 3)) := by
    positivity
  have hinvSmall : ∀ᶠ n : ℕ in atTop,
      (scale n : ℝ)⁻¹ < min (t₀ / 2) (min (x / 2) ((1 : ℝ) / 3)) :=
    hinv (Iio_mem_nhds hthreshold)
  have hscalePos : ∀ᶠ n : ℕ in atTop, 0 < scale n := by
    have hge := hscale.eventually_ge_atTop 1
    exact hge.mono fun _ hn ↦ by omega
  filter_upwards [hinvSmall, hscalePos] with n hninv hnpos
  intro s hs
  have hinvT : (scale n : ℝ)⁻¹ < t₀ / 2 :=
    hninv.trans_le (min_le_left _ _)
  have hinvX : (scale n : ℝ)⁻¹ < x / 2 :=
    hninv.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hinvOne : (scale n : ℝ)⁻¹ < (1 : ℝ) / 3 :=
    hninv.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨_hpNow, hpTarget, _hpdist, _hsLower, _hsUpper,
      _hkLower, _hkUpper⟩ :=
    floorTransportBoxGeometry (scale n) s t₀ t x 1 R hnpos
      ht₀ ht hx hR hinvT hinvX hinvOne hs
  simpa only [Real.norm_eq_abs] using hC _ hpTarget

end

end DerridaRetaux
