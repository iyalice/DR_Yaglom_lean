import DerridaRetaux.Analysis.SpacetimeLatticeDensity
import DerridaRetaux.Analysis.SpacetimeConvolutionRiemann
import Mathlib.Tactic

set_option autoImplicit false

open Filter Set Topology

namespace DerridaRetaux

noncomputable section

/-- Spacetime local-uniform convergence of the rescaled lattice density may
be multiplied inside every finite convolution triangle, uniformly throughout
a compact positive-time box and a compact spatial annulus. -/
theorem scaled_conv_uniform_on_spacetime_away_zero
    (rho : ℕ → ℕ → Seq) (scale : ℕ → ℕ) (u : ℝ → ℝ → ℝ)
    (eta T δ : ℝ) (R : ℕ)
    (hscale : Tendsto scale atTop atTop)
    (heta : 0 < eta) (hetaT : eta ≤ T) (hδ : 0 < δ)
    (hu : ContinuousOn (fun p : ℝ × ℝ ↦ u p.1 p.2)
      (Icc eta T ×ˢ Icc (0 : ℝ) (R : ℝ)))
    (hlocal : LocallyUniformSpacetimeLatticeDensity rho scale u) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      ∀ s : ℕ, eta * (scale n : ℝ) ≤ (s : ℝ) →
        (s : ℝ) ≤ T * (scale n : ℝ) →
      ∀ k : ℕ, δ * (scale n : ℝ) ≤ (k : ℝ) →
        k ≤ R * scale n →
        |(scale n : ℝ) ^ 3 * conv (rho n s) (rho n s) k -
          positiveSelfConvolution
            (u ((s : ℝ) / (scale n : ℝ)))
            ((k : ℝ) / (scale n : ℝ))| < ε := by
  intro ε hε
  obtain ⟨Mprofile, hprofile⟩ :=
    latticeSelfConvolutionSum_uniform_on_spacetime_away_zero
      u eta T δ R hetaT hδ hu (ε / 2) (half_pos hε)
  obtain ⟨error, herror, hlocalBox⟩ := hlocal eta T R heta hetaT
  obtain ⟨C, hC⟩ :=
    (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hu
  have hCnonneg : 0 ≤ C := by
    have hpoint := hC (eta, 0)
      ⟨⟨le_rfl, hetaT⟩, le_rfl, Nat.cast_nonneg R⟩
    exact (norm_nonneg (u eta 0)).trans hpoint
  let coeffError : ℕ → ℝ := fun n ↦
    ((R : ℝ) + 1) *
      (|error n| * (|error n| + C) + C * |error n|)
  have habs : Tendsto (fun n ↦ |error n|) atTop (nhds 0) := by
    simpa only [abs_zero] using herror.abs
  have hcoeffError : Tendsto coeffError atTop (nhds 0) := by
    have hfirst := habs.mul (habs.add
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ C) atTop (nhds C)))
    have hsecond :=
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ C) atTop (nhds C)).mul habs
    have hinner := hfirst.add hsecond
    have htotal :=
      (tendsto_const_nhds : Tendsto
        (fun _ : ℕ ↦ (R : ℝ) + 1) atTop (nhds ((R : ℝ) + 1))).mul hinner
    simpa only [coeffError, zero_add, add_zero, mul_zero, zero_mul] using htotal
  have hcoeffSmall : ∀ᶠ n : ℕ in atTop, coeffError n < ε / 2 :=
    hcoeffError (Iio_mem_nhds (half_pos hε))
  have hscaleLarge : ∀ᶠ n : ℕ in atTop, Mprofile ≤ scale n :=
    hscale.eventually_ge_atTop Mprofile
  have hscalePos : ∀ᶠ n : ℕ in atTop, 0 < scale n := by
    have hge := hscale.eventually_ge_atTop 1
    exact hge.mono fun _ hn ↦ by omega
  filter_upwards [hcoeffSmall, hscaleLarge, hscalePos] with
      n hnsmall hnlarge hnpos
  intro s hsLower hsUpper k hkLower hkUpper
  have hNreal : (0 : ℝ) < (scale n : ℝ) := by exact_mod_cast hnpos
  let st : ℝ := (s : ℝ) / (scale n : ℝ)
  have hst : st ∈ Icc eta T := by
    constructor
    · dsimp only [st]
      exact (le_div_iff₀ hNreal).2 (by simpa only [mul_comm] using hsLower)
    · dsimp only [st]
      exact (div_le_iff₀ hNreal).2 (by simpa only [mul_comm] using hsUpper)
  have huBound : ∀ j : ℕ, j ≤ R * scale n →
      |u st ((j : ℝ) / (scale n : ℝ))| ≤ C := by
    intro j hj
    have hxj : (j : ℝ) / (scale n : ℝ) ∈ Icc (0 : ℝ) (R : ℝ) := by
      constructor
      · exact div_nonneg (Nat.cast_nonneg j) hNreal.le
      · rw [div_le_iff₀ hNreal]
        exact_mod_cast hj
    simpa only [Real.norm_eq_abs] using hC (st, (j : ℝ) / (scale n : ℝ))
      ⟨hst, hxj⟩
  have hcompare : dist
      (scaledLatticeSelfConvolutionSum (rho n s) (scale n) k)
      (latticeSelfConvolutionSum (u st) (scale n) k) < ε / 2 := by
    calc
      dist (scaledLatticeSelfConvolutionSum (rho n s) (scale n) k)
          (latticeSelfConvolutionSum (u st) (scale n) k) ≤
          ((R : ℝ) + 1) *
            (|error n| * (|error n| + C) + C * |error n|) :=
        scaledLatticeSelfConvolutionSum_dist_le
          (rho n s) (u st) (scale n) k R |error n| C hnpos hkUpper
          (abs_nonneg _) hCnonneg
          (fun j hj ↦ (hlocalBox n hnpos s hsLower hsUpper j hj).trans
            (le_abs_self (error n))) huBound
      _ = coeffError n := rfl
      _ < ε / 2 := hnsmall
  have hprofileSmall := hprofile (scale n) hnlarge st hst k hkLower hkUpper
  have hidentity :
      (scale n : ℝ) ^ 3 * conv (rho n s) (rho n s) k =
        scaledLatticeSelfConvolutionSum (rho n s) (scale n) k := by
    simpa only [scaledLatticeSelfConvolutionSum] using
      scaled_conv_eq_lattice_product_sum (rho n s) (scale n) k hnpos
  rw [hidentity]
  calc
    |scaledLatticeSelfConvolutionSum (rho n s) (scale n) k -
        positiveSelfConvolution (u st) ((k : ℝ) / (scale n : ℝ))| =
      dist (scaledLatticeSelfConvolutionSum (rho n s) (scale n) k)
        (positiveSelfConvolution (u st) ((k : ℝ) / (scale n : ℝ))) := by
      rw [Real.dist_eq]
    _ ≤ dist (scaledLatticeSelfConvolutionSum (rho n s) (scale n) k)
          (latticeSelfConvolutionSum (u st) (scale n) k) +
        dist (latticeSelfConvolutionSum (u st) (scale n) k)
          (positiveSelfConvolution (u st) ((k : ℝ) / (scale n : ℝ))) :=
      dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := by
      apply add_lt_add hcompare
      simpa only [Real.dist_eq] using hprofileSmall
    _ = ε := by ring

end

end DerridaRetaux
