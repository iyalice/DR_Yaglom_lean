import DerridaRetaux.Analysis.SpacetimeConvolutionLimit
import DerridaRetaux.Analysis.ConvolutionContinuityOn
import DerridaRetaux.Analysis.FloorTransportBoxGeometry
import DerridaRetaux.Analysis.ConvolutionTriangle

set_option autoImplicit false

open Filter Set Topology

namespace DerridaRetaux

noncomputable section

/-- Uniform convolution limit at the transported spatial index appearing in
the discrete Duhamel sum, for a strictly positive target point. -/
theorem scaled_conv_shifted_floor_window_uniform
    (rho : ℕ → ℕ → Seq) (scale : ℕ → ℕ) (u : ℝ → ℝ → ℝ)
    (t₀ t x : ℝ) (R : ℕ)
    (ht₀ : 0 < t₀) (ht : t₀ ≤ t) (hx : 0 < x)
    (hR : x + t + 1 ≤ (R : ℝ))
    (hscale : Tendsto scale atTop atTop)
    (hlocal : LocallyUniformSpacetimeLatticeDensity rho scale u)
    (hu : ContinuousOn (Function.uncurry u)
      (Icc (t₀ / 2) (t + 1) ×ˢ Icc (0 : ℝ) (R : ℝ))) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      ∀ s ∈ Finset.Ico (gridIndex (scale n) t₀) (gridIndex (scale n) t),
        |(scale n : ℝ) ^ 3 * conv (rho n s) (rho n s)
            (gridIndex (scale n) x + (gridIndex (scale n) t - 1 - s)) -
          positiveSelfConvolution
            (u ((s : ℝ) / (scale n : ℝ)))
            (x + t - (s : ℝ) / (scale n : ℝ))| < ε := by
  intro ε hε
  have heta : 0 < t₀ / 2 := half_pos ht₀
  have hetaT : t₀ / 2 ≤ t + 1 := by linarith
  have hhalfX : 0 < x / 2 := half_pos hx
  have hconv := scaled_conv_uniform_on_spacetime_away_zero
    rho scale u (t₀ / 2) (t + 1) (x / 2) R hscale
      heta hetaT hhalfX hu hlocal (ε / 2) (half_pos hε)
  have hconvCont : ContinuousOn
      (fun p : ℝ × ℝ ↦ positiveSelfConvolution (u p.1) p.2)
      (Icc (t₀ / 2) (t + 1) ×ˢ Icc (0 : ℝ) (R : ℝ)) :=
    continuousOn_positiveSelfConvolution_uncurry u (t₀ / 2) (t + 1)
      (R : ℝ) hetaT (Nat.cast_nonneg R) hu
  have hconvUniform :=
    (isCompact_Icc.prod isCompact_Icc).uniformContinuousOn_of_continuous hconvCont
  obtain ⟨δ, hδ, hmod⟩ :=
    Metric.uniformContinuousOn_iff.mp hconvUniform (ε / 2) (half_pos hε)
  have hinv : Tendsto (fun n : ℕ ↦ (scale n : ℝ)⁻¹) atTop (nhds 0) := by
    simpa only [Function.comp_apply] using
      tendsto_inverse_atTop_nhds_zero_nat.comp hscale
  have hthreshold : 0 < min (t₀ / 2) (min (x / 2) (δ / 3)) := by positivity
  have hinvSmall : ∀ᶠ n : ℕ in atTop,
      (scale n : ℝ)⁻¹ < min (t₀ / 2) (min (x / 2) (δ / 3)) :=
    hinv (Iio_mem_nhds hthreshold)
  have hscalePos : ∀ᶠ n : ℕ in atTop, 0 < scale n := by
    have hge := hscale.eventually_ge_atTop 1
    exact hge.mono fun _ hn ↦ by omega
  filter_upwards [hconv, hinvSmall, hscalePos] with n hnconv hninv hnpos
  intro s hs
  have hinvT : (scale n : ℝ)⁻¹ < t₀ / 2 :=
    hninv.trans_le (min_le_left _ _)
  have hinvX : (scale n : ℝ)⁻¹ < x / 2 :=
    hninv.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hinvδ : (scale n : ℝ)⁻¹ < δ / 3 :=
    hninv.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨hpNow, hpTarget, hpdist, hsLower, hsUpper,
      hkLower, hkUpper⟩ :=
    floorTransportBoxGeometry (scale n) s t₀ t x δ R hnpos
      ht₀ ht hx hR hinvT hinvX hinvδ hs
  have hdiscrete := hnconv s hsLower hsUpper
    (gridIndex (scale n) x + (gridIndex (scale n) t - 1 - s))
    hkLower hkUpper
  have hcontinuous := hmod _ hpNow _ hpTarget hpdist
  exact convolution_triangle_lt
    ((scale n : ℝ) ^ 3 * conv (rho n s) (rho n s)
      (gridIndex (scale n) x + (gridIndex (scale n) t - 1 - s)))
    u ((s : ℝ) / (scale n : ℝ))
    (((gridIndex (scale n) x +
      (gridIndex (scale n) t - 1 - s) : ℕ) : ℝ) / (scale n : ℝ))
    (x + t - (s : ℝ) / (scale n : ℝ)) ε hdiscrete hcontinuous

end

end DerridaRetaux
