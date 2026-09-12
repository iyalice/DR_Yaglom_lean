import DerridaRetaux.Analysis.UniformParameterizedRiemann
import DerridaRetaux.Analysis.QuadraticConvolutionLimit
import Mathlib.Tactic

set_option autoImplicit false

open Filter Set Topology
open scoped Interval

namespace DerridaRetaux

noncomputable section

/-- The profile convolution Riemann sums converge uniformly in both a compact
positive-time parameter and a compact spatial annulus. -/
theorem latticeSelfConvolutionSum_uniform_on_spacetime_away_zero
    (u : ℝ → ℝ → ℝ) (eta T δ : ℝ) (R : ℕ)
    (hetaT : eta ≤ T) (hδ : 0 < δ)
    (hu : ContinuousOn (fun p : ℝ × ℝ ↦ u p.1 p.2)
      (Icc eta T ×ˢ Icc (0 : ℝ) (R : ℝ))) :
    ∀ ε : ℝ, 0 < ε → ∃ M : ℕ, ∀ N : ℕ, M ≤ N →
      ∀ s : ℝ, s ∈ Icc eta T →
      ∀ k : ℕ, δ * (N : ℝ) ≤ (k : ℝ) → k ≤ R * N →
        |latticeSelfConvolutionSum (u s) N k -
          positiveSelfConvolution (u s) ((k : ℝ) / (N : ℝ))| < ε := by
  intro ε hε
  let P : Set (ℝ × ℝ) := Icc eta T ×ˢ Icc (0 : ℝ) (R : ℝ)
  let G : (ℝ × ℝ) × ℝ → ℝ := fun q ↦
    u q.1.1 (q.1.2 * q.2) * u q.1.1 (q.1.2 - q.1.2 * q.2)
  have hargOne : ContinuousOn
      (fun q : (ℝ × ℝ) × ℝ ↦ (q.1.1, q.1.2 * q.2))
      (P ×ˢ Icc (0 : ℝ) 1) :=
    (continuous_fst.comp continuous_fst).prodMk
      ((continuous_snd.comp continuous_fst).mul continuous_snd) |>.continuousOn
  have hargTwo : ContinuousOn
      (fun q : (ℝ × ℝ) × ℝ ↦
        (q.1.1, q.1.2 - q.1.2 * q.2))
      (P ×ˢ Icc (0 : ℝ) 1) :=
    (continuous_fst.comp continuous_fst).prodMk
      ((continuous_snd.comp continuous_fst).sub
        ((continuous_snd.comp continuous_fst).mul continuous_snd)) |>.continuousOn
  have hG : ContinuousOn G (P ×ˢ Icc (0 : ℝ) 1) := by
    apply (hu.comp hargOne ?_).mul (hu.comp hargTwo ?_)
    · intro q hq
      exact ⟨hq.1.1, mul_nonneg hq.1.2.1 hq.2.1,
        (mul_le_of_le_one_right hq.1.2.1 hq.2.2).trans hq.1.2.2⟩
    · intro q hq
      exact ⟨hq.1.1, sub_nonneg.mpr
        (mul_le_of_le_one_right hq.1.2.1 hq.2.2),
        (sub_le_self _ (mul_nonneg hq.1.2.1 hq.2.1)).trans hq.1.2.2⟩
  have hPcompact : IsCompact P := isCompact_Icc.prod isCompact_Icc
  obtain ⟨C, hC⟩ := hPcompact.exists_bound_of_continuousOn hu
  have hCnonneg : 0 ≤ C := by
    have hpoint : (eta, 0) ∈ P :=
      ⟨⟨le_rfl, hetaT⟩, le_rfl, Nat.cast_nonneg R⟩
    exact (norm_nonneg (u eta 0)).trans (hC (eta, 0) hpoint)
  let tolerance : ℝ := ε / (4 * ((R : ℝ) + 1))
  have htolerance : 0 < tolerance := by
    dsimp only [tolerance]
    positivity
  obtain ⟨Kmesh, hKmesh⟩ :=
    latticeLeftRiemannSum_unit_uniform_on_compact_parameter
      P hPcompact G hG tolerance htolerance
  obtain ⟨Mgrid, hMgrid⟩ := exists_nat_gt ((Kmesh : ℝ) / δ)
  have hendpointLim : Tendsto
      (fun N : ℕ ↦ (N : ℝ)⁻¹ * C * C) atTop (nhds 0) := by
    simpa only [zero_mul] using
      (tendsto_inverse_atTop_nhds_zero_nat.mul
        (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ C) atTop (nhds C))).mul
          (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ C) atTop (nhds C))
  have hendpointEventually : ∀ᶠ N : ℕ in atTop,
      (N : ℝ)⁻¹ * C * C < ε / 4 :=
    hendpointLim (Iio_mem_nhds (by linarith))
  rcases eventually_atTop.1 hendpointEventually with ⟨Mend, hMend⟩
  refine ⟨max (max Mgrid Mend) 1, ?_⟩
  intro N hMN s hs k hlower hkR
  have hMgridN : Mgrid ≤ N :=
    (le_max_left Mgrid Mend).trans
      ((le_max_left (max Mgrid Mend) 1).trans hMN)
  have hMendN : Mend ≤ N :=
    (le_max_right Mgrid Mend).trans
      ((le_max_left (max Mgrid Mend) 1).trans hMN)
  have hNpos : 0 < N := (le_max_right (max Mgrid Mend) 1).trans hMN
  have hNreal : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNpos
  have hKreal : (Kmesh : ℝ) < δ * (N : ℝ) := by
    have hKM : (Kmesh : ℝ) < (Mgrid : ℝ) * δ :=
      (div_lt_iff₀ hδ).mp hMgrid
    calc
      (Kmesh : ℝ) < (Mgrid : ℝ) * δ := hKM
      _ ≤ (N : ℝ) * δ := by
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hMgridN) hδ.le
      _ = δ * (N : ℝ) := mul_comm _ _
  have hKk : Kmesh ≤ k := by
    exact_mod_cast (le_of_lt (hKreal.trans_le hlower))
  have hkpos : 0 < k := by
    have : (0 : ℝ) < (k : ℝ) :=
      (mul_pos hδ hNreal).trans_le hlower
    exact_mod_cast this
  let x : ℝ := (k : ℝ) / (N : ℝ)
  have hxR : x ∈ Icc (0 : ℝ) (R : ℝ) := by
    constructor
    · exact div_nonneg (Nat.cast_nonneg k) hNreal.le
    · rw [div_le_iff₀ hNreal]
      exact_mod_cast hkR
  have hp : (s, x) ∈ P := ⟨hs, hxR⟩
  have hriemann := hKmesh k hKk (s, x) hp
  have hsplit := latticeSelfConvolutionSum_eq_unit_add_endpoint
    (u s) N k hNpos hkpos
  have huX : |u s x| ≤ C := by
    simpa only [Real.norm_eq_abs] using hC (s, x) hp
  have huZero : |u s 0| ≤ C := by
    simpa only [Real.norm_eq_abs] using hC (s, 0)
      ⟨hs, le_rfl, Nat.cast_nonneg R⟩
  have hendpoint : |(N : ℝ)⁻¹ * u s x * u s 0| < ε / 4 := by
    calc
      |(N : ℝ)⁻¹ * u s x * u s 0| =
          (N : ℝ)⁻¹ * |u s x| * |u s 0| := by
        rw [abs_mul, abs_mul, abs_of_pos (inv_pos.mpr hNreal)]
      _ ≤ (N : ℝ)⁻¹ * C * C := by gcongr
      _ < ε / 4 := hMend N hMendN
  change |latticeSelfConvolutionSum (u s) N k -
    positiveSelfConvolution (u s) x| < ε
  rw [hsplit, ← positiveSelfConvolution_eq_unit (u s) x]
  rw [show x * latticeLeftRiemannSum
      (unitSelfConvolutionKernel (u s) x) 1 k +
        (N : ℝ)⁻¹ * u s x * u s 0 -
      x * ∫ z in (0 : ℝ)..1, unitSelfConvolutionKernel (u s) x z =
      x * (latticeLeftRiemannSum
        (unitSelfConvolutionKernel (u s) x) 1 k -
          ∫ z in (0 : ℝ)..1, unitSelfConvolutionKernel (u s) x z) +
        (N : ℝ)⁻¹ * u s x * u s 0 by ring]
  calc
    |x * (latticeLeftRiemannSum
          (unitSelfConvolutionKernel (u s) x) 1 k -
        ∫ z in (0 : ℝ)..1, unitSelfConvolutionKernel (u s) x z) +
      (N : ℝ)⁻¹ * u s x * u s 0| ≤
        |x * (latticeLeftRiemannSum
          (unitSelfConvolutionKernel (u s) x) 1 k -
            ∫ z in (0 : ℝ)..1, unitSelfConvolutionKernel (u s) x z)| +
          |(N : ℝ)⁻¹ * u s x * u s 0| := abs_add _ _
    _ = x * |latticeLeftRiemannSum
          (unitSelfConvolutionKernel (u s) x) 1 k -
            ∫ z in (0 : ℝ)..1, unitSelfConvolutionKernel (u s) x z| +
          |(N : ℝ)⁻¹ * u s x * u s 0| := by
      rw [abs_mul, abs_of_nonneg hxR.1]
    _ < (R : ℝ) * tolerance + ε / 4 := by
      apply add_lt_add_of_le_of_lt _ hendpoint
      exact mul_le_mul hxR.2 hriemann.le (abs_nonneg _) (Nat.cast_nonneg R)
    _ ≤ ε / 4 + ε / 4 := by
      apply add_le_add_right
      have hRle : (R : ℝ) ≤ (R : ℝ) + 1 := by linarith
      calc
        (R : ℝ) * tolerance ≤ ((R : ℝ) + 1) * tolerance :=
          mul_le_mul_of_nonneg_right hRle htolerance.le
        _ = ε / 4 := by
          dsimp only [tolerance]
          field_simp
          ring
    _ < ε := by linarith

end

end DerridaRetaux
