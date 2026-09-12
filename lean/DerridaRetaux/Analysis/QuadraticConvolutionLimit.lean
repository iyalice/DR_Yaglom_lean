import DerridaRetaux.Analysis.LatticeRiemannLimit
import DerridaRetaux.Basic.Convolution
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Tactic

set_option autoImplicit false

open Filter Topology MeasureTheory Set
open scoped BigOperators Interval

namespace DerridaRetaux

noncomputable section

/-!
# The spatial quadratic-convolution limit

The discrete Cauchy convolution at coefficient `k` only sees indices
`0 ≤ i ≤ k`.  Consequently local-uniform convergence of the quadratically
rescaled lattice density on compact windows is already enough for the spatial
convolution limit; no tail or tightness input is used here.
-/

/-- The continuous half-line self-convolution.  It is the convolution of the
zero extension from `ℝ≥0`: for `x ≥ 0` only `0 ≤ y ≤ x` contributes. -/
def positiveSelfConvolution (u : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ y in (0 : ℝ)..x, u y * u (x - y)

/-- The profile-valued lattice Riemann sum which appears after quadratic
rescaling of a Cauchy convolution. -/
def latticeSelfConvolutionSum (u : ℝ → ℝ) (N k : ℕ) : ℝ :=
  (N : ℝ)⁻¹ * ∑ i ∈ Finset.range (k + 1),
    u ((i : ℝ) / (N : ℝ)) * u (((k - i : ℕ) : ℝ) / (N : ℝ))

/-- The literal product sum on the right-hand side of the source scaling
identity. -/
def scaledLatticeSelfConvolutionSum (rho : Seq) (N k : ℕ) : ℝ :=
  (N : ℝ)⁻¹ * ∑ i ∈ Finset.range (k + 1),
    ((N : ℝ) ^ 2 * rho i) * ((N : ℝ) ^ 2 * rho (k - i))

/-- Pull the half-line convolution kernel back to the unit interval. -/
def unitSelfConvolutionKernel (u : ℝ → ℝ) (x z : ℝ) : ℝ :=
  u (x * z) * u (x - x * z)

/-- The unit-interval and half-line presentations of the continuous
convolution agree, including at the boundary `x = 0`. -/
theorem positiveSelfConvolution_eq_unit
    (u : ℝ → ℝ) (x : ℝ) :
    x * ∫ z in (0 : ℝ)..1, unitSelfConvolutionKernel u x z =
      positiveSelfConvolution u x := by
  simpa only [unitSelfConvolutionKernel, positiveSelfConvolution,
    mul_zero, mul_one] using
    (intervalIntegral.mul_integral_comp_mul_left
      (a := (0 : ℝ)) (b := 1)
      (f := fun y : ℝ ↦ u y * u (x - y)) x)

/-- A uniform perturbation of the integrand on `[0,1]` may be combined with
an arbitrary cofinal choice of the mesh. -/
theorem latticeLeftRiemannSum_unit_tendsto_of_uniform
    (f : ℕ → ℝ → ℝ) (g : ℝ → ℝ) (mesh : ℕ → ℕ)
    (hmesh : Tendsto mesh atTop atTop)
    (huniform : TendstoUniformlyOn f g atTop (Icc (0 : ℝ) 1))
    (hg : ContinuousOn g (Icc (0 : ℝ) 1)) :
    Tendsto (fun n ↦ latticeLeftRiemannSum (f n) 1 (mesh n))
      atTop (nhds (∫ z in (0 : ℝ)..1, g z)) := by
  have hfixed : Tendsto
      (fun n ↦ latticeLeftRiemannSum g 1 (mesh n)) atTop
      (nhds (∫ z in (0 : ℝ)..1, g z)) := by
    simpa only [Nat.cast_one] using
      (latticeLeftRiemannSum_tendsto_intervalIntegral g 1
        (by simpa only [Nat.cast_one] using hg)).comp hmesh
  have hdiff : Tendsto
      (fun n ↦ latticeLeftRiemannSum (f n) 1 (mesh n) -
        latticeLeftRiemannSum g 1 (mesh n)) atTop (nhds 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    have hεhalf : 0 < ε / 2 := half_pos hε
    have hclose :=
      (Metric.tendstoUniformlyOn_iff.mp huniform) (ε / 2) hεhalf
    have hmeshPos : ∀ᶠ n : ℕ in atTop, 0 < mesh n := by
      have hge : ∀ᶠ n : ℕ in atTop, 1 ≤ mesh n :=
        hmesh (eventually_ge_atTop (1 : ℕ))
      exact hge.mono fun _ hn ↦ by omega
    filter_upwards [hclose, hmeshPos] with n hnclose hnpos
    have hmeshReal : (0 : ℝ) < (mesh n : ℝ) := by exact_mod_cast hnpos
    have hmeshNe : (mesh n : ℝ) ≠ 0 := hmeshReal.ne'
    rw [Real.dist_eq, sub_zero, latticeLeftRiemannSum,
      latticeLeftRiemannSum, ← Finset.sum_sub_distrib]
    calc
      |∑ j ∈ Finset.range (1 * mesh n),
          ((mesh n : ℝ)⁻¹ * f n ((j : ℝ) / (mesh n : ℝ)) -
            (mesh n : ℝ)⁻¹ * g ((j : ℝ) / (mesh n : ℝ)))| ≤
          ∑ _j ∈ Finset.range (1 * mesh n),
            (mesh n : ℝ)⁻¹ * (ε / 2) := by
        calc
          |∑ j ∈ Finset.range (1 * mesh n),
              ((mesh n : ℝ)⁻¹ * f n ((j : ℝ) / (mesh n : ℝ)) -
                (mesh n : ℝ)⁻¹ * g ((j : ℝ) / (mesh n : ℝ)))| ≤
              ∑ j ∈ Finset.range (1 * mesh n),
                |(mesh n : ℝ)⁻¹ * f n ((j : ℝ) / (mesh n : ℝ)) -
                  (mesh n : ℝ)⁻¹ * g ((j : ℝ) / (mesh n : ℝ))| :=
            Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ _j ∈ Finset.range (1 * mesh n),
                (mesh n : ℝ)⁻¹ * (ε / 2) := by
            apply Finset.sum_le_sum
            intro j hj
            have hjlt : j < mesh n := by
              simpa only [one_mul] using Finset.mem_range.mp hj
            have hz : (j : ℝ) / (mesh n : ℝ) ∈ Icc (0 : ℝ) 1 := by
              constructor
              · exact div_nonneg (Nat.cast_nonneg j) hmeshReal.le
              · rw [div_le_one hmeshReal]
                exact_mod_cast (Nat.le_of_lt hjlt)
            have hpoint := hnclose _ hz
            rw [Real.dist_eq, abs_sub_comm] at hpoint
            rw [← mul_sub, abs_mul, abs_of_pos (inv_pos.mpr hmeshReal)]
            exact mul_le_mul_of_nonneg_left hpoint.le
              (inv_nonneg.mpr hmeshReal.le)
      _ = ε / 2 := by
        simp only [one_mul, Finset.sum_const, Finset.card_range,
          nsmul_eq_mul]
        field_simp only [hmeshNe]
        ring
      _ < ε := half_lt_self hε
  simpa only [sub_add_cancel, zero_add] using hdiff.add hfixed

/-- Joint continuity on a compact parameter rectangle gives one Riemann-mesh
threshold valid for every parameter in that rectangle. -/
theorem latticeLeftRiemannSum_unit_uniform_in_parameter
    (G : ℝ × ℝ → ℝ) (R : ℝ)
    (hG : ContinuousOn G (Icc (0 : ℝ) R ×ˢ Icc (0 : ℝ) 1)) :
    ∀ ε : ℝ, 0 < ε → ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
      ∀ x ∈ Icc (0 : ℝ) R,
        |latticeLeftRiemannSum (fun z ↦ G (x, z)) 1 k -
          ∫ z in (0 : ℝ)..1, G (x, z)| < ε := by
  intro ε hε
  let η : ℝ := ε / 2
  have hη : 0 < η := half_pos hε
  have hGuniform : UniformContinuousOn G
      (Icc (0 : ℝ) R ×ˢ Icc (0 : ℝ) 1) :=
    (isCompact_Icc.prod isCompact_Icc).uniformContinuousOn_of_continuous hG
  obtain ⟨δ, hδ, hmod⟩ :=
    Metric.uniformContinuousOn_iff.mp hGuniform η hη
  obtain ⟨K₀, hK₀⟩ := exists_nat_gt δ⁻¹
  refine ⟨max K₀ 1, ?_⟩
  intro k hk x hx
  have hK₀k : K₀ ≤ k := (le_max_left K₀ 1).trans hk
  have hkpos : 0 < k := (le_max_right K₀ 1).trans hk
  have hkreal : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hkpos
  have hkne : (k : ℝ) ≠ 0 := hkreal.ne'
  have hinvlt : (k : ℝ)⁻¹ < δ := by
    apply (inv_lt_comm₀ hkreal hδ).2
    exact hK₀.trans_le (by exact_mod_cast hK₀k)
  let a : ℕ → ℝ := fun j ↦ (j : ℝ) / (k : ℝ)
  have ha_mono : ∀ j : ℕ, a j ≤ a (j + 1) := by
    intro j
    dsimp only [a]
    apply div_le_div_of_nonneg_right _ hkreal.le
    exact_mod_cast Nat.le_succ j
  have ha_unit : ∀ {j : ℕ}, j ≤ k → a j ∈ Icc (0 : ℝ) 1 := by
    intro j hj
    constructor
    · exact div_nonneg (Nat.cast_nonneg j) hkreal.le
    · rw [div_le_one hkreal]
      exact_mod_cast hj
  have hslice : ContinuousOn (fun z : ℝ ↦ G (x, z))
      (Icc (0 : ℝ) 1) := by
    apply hG.comp (continuous_const.prodMk continuous_id).continuousOn
    intro z hz
    exact ⟨hx, hz⟩
  have hpartition :
      ∑ j ∈ Finset.range k,
          ∫ z in a j..a (j + 1), G (x, z) =
        ∫ z in (0 : ℝ)..1, G (x, z) := by
    have hsum := intervalIntegral.sum_integral_adjacent_intervals
      (f := fun z : ℝ ↦ G (x, z)) (a := a) (n := k) (μ := volume)
      (fun j hj ↦
        (hslice.mono fun z hz ↦
          ⟨(ha_unit (Nat.le_of_lt hj)).1.trans hz.1,
            hz.2.trans (ha_unit (Nat.succ_le_iff.mpr hj)).2⟩).intervalIntegrable_of_Icc
          (ha_mono j))
    simpa only [a, Nat.cast_zero, zero_div, Nat.cast_add,
      Nat.cast_one, add_div, div_self hkne] using hsum
  have hcell : ∀ j < k,
      |(k : ℝ)⁻¹ * G (x, a j) -
        ∫ z in a j..a (j + 1), G (x, z)| ≤
        η * (k : ℝ)⁻¹ := by
    intro j hj
    have hstep : a (j + 1) - a j = (k : ℝ)⁻¹ := by
      dsimp only [a]
      push_cast
      field_simp only [hkne]
      ring
    have hconst : (k : ℝ)⁻¹ * G (x, a j) =
        ∫ _z in a j..a (j + 1), G (x, a j) := by
      rw [intervalIntegral.integral_const]
      simp only [smul_eq_mul, hstep]
    have hconstInt : IntervalIntegrable (fun _z : ℝ ↦ G (x, a j))
        volume (a j) (a (j + 1)) := continuous_const.intervalIntegrable _ _
    have hcellSubset : Icc (a j) (a (j + 1)) ⊆ Icc (0 : ℝ) 1 := by
      intro z hz
      exact ⟨(ha_unit (Nat.le_of_lt hj)).1.trans hz.1,
        hz.2.trans (ha_unit (Nat.succ_le_iff.mpr hj)).2⟩
    have hsliceInt : IntervalIntegrable (fun z : ℝ ↦ G (x, z))
        volume (a j) (a (j + 1)) :=
      (hslice.mono hcellSubset).intervalIntegrable_of_Icc (ha_mono j)
    rw [hconst, ← intervalIntegral.integral_sub hconstInt hsliceInt]
    calc
      |∫ z in a j..a (j + 1), G (x, a j) - G (x, z)| =
          ‖∫ z in a j..a (j + 1), G (x, a j) - G (x, z)‖ := by
        rw [Real.norm_eq_abs]
      _ ≤ η * |a (j + 1) - a j| := by
        apply intervalIntegral.norm_integral_le_of_norm_le_const
        intro z hz
        rw [Set.uIoc_of_le (ha_mono j)] at hz
        have hzUnit : z ∈ Icc (0 : ℝ) 1 :=
          hcellSubset ⟨hz.1.le, hz.2⟩
        have hd : dist (x, a j) (x, z) < δ := by
          rw [Prod.dist_eq, dist_self, max_eq_right dist_nonneg]
          rw [Real.dist_eq, abs_sub_comm,
            abs_of_nonneg (sub_nonneg.mpr hz.1.le)]
          calc
            z - a j ≤ a (j + 1) - a j := sub_le_sub_right hz.2 _
            _ = (k : ℝ)⁻¹ := hstep
            _ < δ := hinvlt
        have hpj : (x, a j) ∈
            Icc (0 : ℝ) R ×ˢ Icc (0 : ℝ) 1 :=
          ⟨hx, ha_unit (Nat.le_of_lt hj)⟩
        have hpz : (x, z) ∈ Icc (0 : ℝ) R ×ˢ Icc (0 : ℝ) 1 :=
          ⟨hx, hzUnit⟩
        simpa only [Real.norm_eq_abs, Real.dist_eq] using
          (le_of_lt (hmod (x, a j) hpj (x, z) hpz hd))
      _ = η * (k : ℝ)⁻¹ := by
        congr 1
        rw [hstep, abs_of_pos (inv_pos.mpr hkreal)]
  rw [latticeLeftRiemannSum, one_mul, ← hpartition,
    ← Finset.sum_sub_distrib]
  calc
    |∑ j ∈ Finset.range k,
        ((k : ℝ)⁻¹ * G (x, (j : ℝ) / (k : ℝ)) -
          ∫ z in a j..a (j + 1), G (x, z))| ≤
        ∑ j ∈ Finset.range k,
          |(k : ℝ)⁻¹ * G (x, (j : ℝ) / (k : ℝ)) -
            ∫ z in a j..a (j + 1), G (x, z)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ Finset.range k, η * (k : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro j hj
      simpa only [a] using hcell j (Finset.mem_range.mp hj)
    _ = η := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      field_simp only [hkne]
      ring
    _ < ε := half_lt_self hε

/-- Continuity of `u` on the nonnegative half-line makes the pulled-back
convolution kernel continuous on the unit interval. -/
theorem continuousOn_unitSelfConvolutionKernel
    (u : ℝ → ℝ) (hu : ContinuousOn u (Ici (0 : ℝ)))
    (x : ℝ) (hx : 0 ≤ x) :
    ContinuousOn (unitSelfConvolutionKernel u x) (Icc (0 : ℝ) 1) := by
  have hfirst : ContinuousOn (fun z : ℝ ↦ x * z) (Icc (0 : ℝ) 1) :=
    continuous_const.mul continuous_id |>.continuousOn
  have hsecond : ContinuousOn (fun z : ℝ ↦ x - x * z)
      (Icc (0 : ℝ) 1) :=
    continuous_const.sub (continuous_const.mul continuous_id) |>.continuousOn
  apply (hu.comp hfirst ?_).mul (hu.comp hsecond ?_)
  · intro z hz
    exact mul_nonneg hx hz.1
  · intro z hz
    exact sub_nonneg.mpr (mul_le_of_le_one_right hx hz.2)

/-- If the macroscopic target `x_n` converges to `x`, then the corresponding
unit-interval convolution kernels converge uniformly. -/
theorem unitSelfConvolutionKernel_tendstoUniformlyOn
    (u : ℝ → ℝ) (hu : ContinuousOn u (Ici (0 : ℝ)))
    (xseq : ℕ → ℝ) (x R : ℝ)
    (hx : Tendsto xseq atTop (nhds x))
    (hxR : x ∈ Icc (0 : ℝ) R)
    (hseqR : ∀ᶠ n : ℕ in atTop, xseq n ∈ Icc (0 : ℝ) R) :
    TendstoUniformlyOn
      (fun n ↦ unitSelfConvolutionKernel u (xseq n))
      (unitSelfConvolutionKernel u x) atTop (Icc (0 : ℝ) 1) := by
  let K : Set (ℝ × ℝ) := Icc (0 : ℝ) R ×ˢ Icc (0 : ℝ) 1
  let G : ℝ × ℝ → ℝ := fun p ↦ unitSelfConvolutionKernel u p.1 p.2
  have hargOne : ContinuousOn (fun p : ℝ × ℝ ↦ p.1 * p.2) K :=
    (continuous_fst.mul continuous_snd).continuousOn
  have hargTwo : ContinuousOn (fun p : ℝ × ℝ ↦ p.1 - p.1 * p.2) K :=
    (continuous_fst.sub (continuous_fst.mul continuous_snd)).continuousOn
  have hGcont : ContinuousOn G K := by
    apply (hu.comp hargOne ?_).mul (hu.comp hargTwo ?_)
    · intro p hp
      exact mul_nonneg hp.1.1 hp.2.1
    · intro p hp
      exact sub_nonneg.mpr (mul_le_of_le_one_right hp.1.1 hp.2.2)
  have hGuniform : UniformContinuousOn G K :=
    (isCompact_Icc.prod isCompact_Icc).uniformContinuousOn_of_continuous hGcont
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  obtain ⟨δ, hδ, hmod⟩ :=
    Metric.uniformContinuousOn_iff.mp hGuniform ε hε
  have hxclose : ∀ᶠ n : ℕ in atTop, dist (xseq n) x < δ :=
    (Metric.tendsto_nhds.mp hx) δ hδ
  filter_upwards [hxclose, hseqR] with n hnclose hnR
  intro z hz
  have hp : (x, z) ∈ K := ⟨hxR, hz⟩
  have hpn : (xseq n, z) ∈ K := ⟨hnR, hz⟩
  have hpair : dist (x, z) (xseq n, z) < δ := by
    simpa only [Prod.dist_eq, dist_self, max_eq_left, dist_nonneg,
      dist_comm] using hnclose
  simpa only [G] using hmod (x, z) hp (xseq n, z) hpn hpair

/-- Elementary product perturbation used to integrate the two pointwise
lattice-density errors across the finite convolution triangle. -/
theorem abs_mul_sub_mul_le_of_two_errors
    (A B a b error bound : ℝ)
    (herror : 0 ≤ error) (hbound : 0 ≤ bound)
    (hAa : |A - a| ≤ error) (hBb : |B - b| ≤ error)
    (ha : |a| ≤ bound) (hb : |b| ≤ bound) :
    |A * B - a * b| ≤
      error * (error + bound) + bound * error := by
  have hB : |B| ≤ error + bound := by
    calc
      |B| = |(B - b) + b| := by ring_nf
      _ ≤ |B - b| + |b| := abs_add _ _
      _ ≤ error + bound := add_le_add hBb hb
  rw [show A * B - a * b = (A - a) * B + a * (B - b) by ring]
  calc
    |(A - a) * B + a * (B - b)| ≤
        |(A - a) * B| + |a * (B - b)| := abs_add _ _
    _ = |A - a| * |B| + |a| * |B - b| := by
      rw [abs_mul, abs_mul]
    _ ≤ error * (error + bound) + bound * error := by
      apply add_le_add
      · exact mul_le_mul hAa hB (abs_nonneg _) herror
      · exact mul_le_mul ha hBb (abs_nonneg _) hbound

/-- Quantitative finite-triangle form of the local-density product estimate.
It is uniform in every output coefficient `k ≤ R*N`. -/
theorem scaledLatticeSelfConvolutionSum_dist_le
    (rho : Seq) (u : ℝ → ℝ) (N k R : ℕ) (error bound : ℝ)
    (hN : 0 < N) (hk : k ≤ R * N)
    (herror : 0 ≤ error) (hbound : 0 ≤ bound)
    (hlocal : ∀ j : ℕ, j ≤ R * N →
      |(N : ℝ) ^ 2 * rho j - u ((j : ℝ) / (N : ℝ))| ≤ error)
    (huBound : ∀ j : ℕ, j ≤ R * N →
      |u ((j : ℝ) / (N : ℝ))| ≤ bound) :
    dist (scaledLatticeSelfConvolutionSum rho N k)
      (latticeSelfConvolutionSum u N k) ≤
        ((R : ℝ) + 1) *
          (error * (error + bound) + bound * error) := by
  have hNreal : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hNne : (N : ℝ) ≠ 0 := hNreal.ne'
  let q : ℝ := error * (error + bound) + bound * error
  have hq : 0 ≤ q := by
    dsimp only [q]
    positivity
  have hterm : ∀ i ∈ Finset.range (k + 1),
      |(((N : ℝ) ^ 2 * rho i) * ((N : ℝ) ^ 2 * rho (k - i))) -
        u ((i : ℝ) / (N : ℝ)) *
          u (((k - i : ℕ) : ℝ) / (N : ℝ))| ≤ q := by
    intro i hi
    have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hsub : k - i ≤ k := Nat.sub_le k i
    apply abs_mul_sub_mul_le_of_two_errors
      ((N : ℝ) ^ 2 * rho i) ((N : ℝ) ^ 2 * rho (k - i))
      (u ((i : ℝ) / (N : ℝ)))
      (u (((k - i : ℕ) : ℝ) / (N : ℝ))) error bound
      herror hbound
    · exact hlocal i (hik.trans hk)
    · exact hlocal (k - i) (hsub.trans hk)
    · exact huBound i (hik.trans hk)
    · exact huBound (k - i) (hsub.trans hk)
  have hcard : k + 1 ≤ (R + 1) * N := by
    calc
      k + 1 ≤ R * N + N := Nat.add_le_add hk hN
      _ = (R + 1) * N := by rw [Nat.add_mul, one_mul]
  have hratio : ((k + 1 : ℕ) : ℝ) / (N : ℝ) ≤ (R : ℝ) + 1 := by
    rw [div_le_iff₀ hNreal]
    norm_num only [Nat.cast_add, Nat.cast_one, Nat.cast_mul]
    exact_mod_cast hcard
  rw [Real.dist_eq, scaledLatticeSelfConvolutionSum,
    latticeSelfConvolutionSum, ← mul_sub, ← Finset.sum_sub_distrib,
    abs_mul, abs_of_pos (inv_pos.mpr hNreal)]
  calc
    (N : ℝ)⁻¹ *
        |∑ i ∈ Finset.range (k + 1),
          (((N : ℝ) ^ 2 * rho i) * ((N : ℝ) ^ 2 * rho (k - i)) -
            u ((i : ℝ) / (N : ℝ)) *
              u (((k - i : ℕ) : ℝ) / (N : ℝ)))| ≤
        (N : ℝ)⁻¹ * ∑ i ∈ Finset.range (k + 1),
          |(((N : ℝ) ^ 2 * rho i) * ((N : ℝ) ^ 2 * rho (k - i)) -
            u ((i : ℝ) / (N : ℝ)) *
              u (((k - i : ℕ) : ℝ) / (N : ℝ)))| := by
      exact mul_le_mul_of_nonneg_left
        (Finset.abs_sum_le_sum_abs _ _) (inv_nonneg.mpr hNreal.le)
    _ ≤ (N : ℝ)⁻¹ * ∑ _i ∈ Finset.range (k + 1), q := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hNreal.le)
      apply Finset.sum_le_sum
      intro i hi
      exact hterm i hi
    _ = (((k + 1 : ℕ) : ℝ) / (N : ℝ)) * q := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      rw [div_eq_mul_inv]
      ring
    _ ≤ ((R : ℝ) + 1) * q := mul_le_mul_of_nonneg_right hratio hq
    _ = ((R : ℝ) + 1) *
        (error * (error + bound) + bound * error) := rfl

/-- Exact source normalization
`N³ (rho * rho)(k) = N⁻¹ ∑ᵢ [N² rho(i)] [N² rho(k-i)]`.
The positivity hypothesis only excludes the meaningless zero mesh. -/
theorem scaled_conv_eq_lattice_product_sum
    (rho : Seq) (N k : ℕ) (hN : 0 < N) :
    (N : ℝ) ^ 3 * conv rho rho k =
      (N : ℝ)⁻¹ * ∑ i ∈ Finset.range (k + 1),
        ((N : ℝ) ^ 2 * rho i) * ((N : ℝ) ^ 2 * rho (k - i)) := by
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [conv]
  calc
    (N : ℝ) ^ 3 * ∑ i ∈ Finset.range (k + 1), rho i * rho (k - i) =
        ∑ i ∈ Finset.range (k + 1),
          (N : ℝ) ^ 3 * (rho i * rho (k - i)) := by
      rw [Finset.mul_sum]
    _ = ∑ i ∈ Finset.range (k + 1),
          (N : ℝ)⁻¹ *
            (((N : ℝ) ^ 2 * rho i) * ((N : ℝ) ^ 2 * rho (k - i))) := by
      apply Finset.sum_congr rfl
      intro i _hi
      field_simp only [hN0]
      ring
    _ = (N : ℝ)⁻¹ * ∑ i ∈ Finset.range (k + 1),
          ((N : ℝ) ^ 2 * rho i) * ((N : ℝ) ^ 2 * rho (k - i)) := by
      rw [Finset.mul_sum]

/-- Split the closed Cauchy sum into a unit-interval left Riemann sum and its
single right-endpoint atom.  The endpoint term is displayed explicitly; this
is the discrete trace of the zero-extension boundary. -/
theorem latticeSelfConvolutionSum_eq_unit_add_endpoint
    (u : ℝ → ℝ) (N k : ℕ) (hN : 0 < N) (hk : 0 < k) :
    latticeSelfConvolutionSum u N k =
      ((k : ℝ) / (N : ℝ)) *
        latticeLeftRiemannSum
          (unitSelfConvolutionKernel u ((k : ℝ) / (N : ℝ))) 1 k +
      (N : ℝ)⁻¹ * u ((k : ℝ) / (N : ℝ)) * u 0 := by
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  rw [latticeSelfConvolutionSum, Finset.sum_range_succ, mul_add,
    latticeLeftRiemannSum, one_mul]
  congr 1
  · rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    have hik : i ≤ k := Nat.le_of_lt (Finset.mem_range.mp hi)
    have hfirst : (i : ℝ) / (N : ℝ) =
        ((k : ℝ) / (N : ℝ)) * ((i : ℝ) / (k : ℝ)) := by
      field_simp only [hN0, hk0]
      ring
    have hsecond : ((k - i : ℕ) : ℝ) / (N : ℝ) =
        (k : ℝ) / (N : ℝ) -
          (k : ℝ) / (N : ℝ) * ((i : ℝ) / (k : ℝ)) := by
      rw [Nat.cast_sub hik]
      field_simp only [hN0, hk0]
      ring
    rw [hfirst, hsecond]
    dsimp only [unitSelfConvolutionKernel]
    field_simp only [hN0, hk0]
    ring
  · simp only [Nat.sub_self, Nat.cast_zero, zero_div]
    ring

/-- Moving-target spatial Riemann theorem away from the degenerate endpoint.
Both the lattice scale and the target index may be selected independently;
only their ratio is prescribed. -/
theorem latticeSelfConvolutionSum_tendsto_moving
    (u : ℝ → ℝ) (scale target : ℕ → ℕ) (x : ℝ)
    (hu : ContinuousOn u (Ici (0 : ℝ)))
    (hscale : Tendsto scale atTop atTop)
    (htarget : Tendsto target atTop atTop)
    (hratio : Tendsto
      (fun n : ℕ ↦ (target n : ℝ) / (scale n : ℝ))
      atTop (nhds x))
    (hx : 0 < x) :
    Tendsto
      (fun n : ℕ ↦ latticeSelfConvolutionSum u (scale n) (target n))
      atTop (nhds (positiveSelfConvolution u x)) := by
  let xseq : ℕ → ℝ := fun n ↦ (target n : ℝ) / (scale n : ℝ)
  let R : ℝ := x + 1
  have hxR : x ∈ Icc (0 : ℝ) R := by
    exact ⟨hx.le, by dsimp only [R]; linarith⟩
  have hseqR : ∀ᶠ n : ℕ in atTop, xseq n ∈ Icc (0 : ℝ) R := by
    have hupper : ∀ᶠ n : ℕ in atTop, xseq n < R := by
      exact hratio (Iio_mem_nhds (by dsimp only [R]; linarith))
    filter_upwards [hupper] with n hn
    exact ⟨div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _), hn.le⟩
  have huniform : TendstoUniformlyOn
      (fun n ↦ unitSelfConvolutionKernel u (xseq n))
      (unitSelfConvolutionKernel u x) atTop (Icc (0 : ℝ) 1) :=
    unitSelfConvolutionKernel_tendstoUniformlyOn
      u hu xseq x R hratio hxR hseqR
  have hkernel : ContinuousOn (unitSelfConvolutionKernel u x)
      (Icc (0 : ℝ) 1) :=
    continuousOn_unitSelfConvolutionKernel u hu x hx.le
  have hriemann : Tendsto
      (fun n ↦ latticeLeftRiemannSum
        (unitSelfConvolutionKernel u (xseq n)) 1 (target n))
      atTop
      (nhds (∫ z in (0 : ℝ)..1, unitSelfConvolutionKernel u x z)) :=
    latticeLeftRiemannSum_unit_tendsto_of_uniform
      (fun n ↦ unitSelfConvolutionKernel u (xseq n))
      (unitSelfConvolutionKernel u x) target htarget huniform hkernel
  have hmain : Tendsto
      (fun n ↦ xseq n * latticeLeftRiemannSum
        (unitSelfConvolutionKernel u (xseq n)) 1 (target n))
      atTop (nhds (positiveSelfConvolution u x)) := by
    rw [← positiveSelfConvolution_eq_unit u x]
    exact hratio.mul hriemann
  have hscaleInv : Tendsto (fun n : ℕ ↦ (scale n : ℝ)⁻¹)
      atTop (nhds 0) := by
    simpa only [Function.comp_apply] using
      tendsto_inverse_atTop_nhds_zero_nat.comp hscale
  have hpoint : Tendsto (fun n ↦ u (xseq n)) atTop (nhds (u x)) := by
    exact (hu.continuousAt (Ici_mem_nhds hx)).tendsto.comp hratio
  have hendpoint : Tendsto
      (fun n ↦ (scale n : ℝ)⁻¹ * u (xseq n) * u 0)
      atTop (nhds 0) := by
    simpa only [zero_mul] using (hscaleInv.mul hpoint).mul tendsto_const_nhds
  have hscalePos : ∀ᶠ n : ℕ in atTop, 0 < scale n := by
    have hge : ∀ᶠ n : ℕ in atTop, 1 ≤ scale n :=
      hscale (eventually_ge_atTop (1 : ℕ))
    exact hge.mono fun _ hn ↦ by omega
  have htargetPos : ∀ᶠ n : ℕ in atTop, 0 < target n := by
    have hge : ∀ᶠ n : ℕ in atTop, 1 ≤ target n :=
      htarget (eventually_ge_atTop (1 : ℕ))
    exact hge.mono fun _ hn ↦ by omega
  have heq : ∀ᶠ n : ℕ in atTop,
      latticeSelfConvolutionSum u (scale n) (target n) =
        xseq n * latticeLeftRiemannSum
          (unitSelfConvolutionKernel u (xseq n)) 1 (target n) +
        (scale n : ℝ)⁻¹ * u (xseq n) * u 0 := by
    filter_upwards [hscalePos, htargetPos] with n hn hkn
    simpa only [xseq] using
      latticeSelfConvolutionSum_eq_unit_add_endpoint
        u (scale n) (target n) hn hkn
  have hsum := (hmain.add hendpoint).congr'
    (heq.mono fun _ hn ↦ hn.symm)
  simpa only [add_zero] using hsum

/-- Local-uniform convergence of the quadratically rescaled coefficients can
be multiplied inside the finite Cauchy triangle.  This is the coefficient-to-
profile bridge for a moving positive macroscopic target. -/
theorem scaledLatticeSelfConvolutionSum_tendsto_moving_of_locallyUniform
    (rho : ℕ → Seq) (scale target : ℕ → ℕ) (u : ℝ → ℝ) (x : ℝ)
    (hscale : Tendsto scale atTop atTop)
    (htarget : Tendsto target atTop atTop)
    (hratio : Tendsto
      (fun n : ℕ ↦ (target n : ℝ) / (scale n : ℝ))
      atTop (nhds x))
    (hu : ContinuousOn u (Ici (0 : ℝ)))
    (hlocal : LocallyUniformLatticeDensity rho scale u)
    (hx : 0 < x) :
    Tendsto
      (fun n : ℕ ↦
        scaledLatticeSelfConvolutionSum (rho n) (scale n) (target n))
      atTop (nhds (positiveSelfConvolution u x)) := by
  have hprofile := latticeSelfConvolutionSum_tendsto_moving
    u scale target x hu hscale htarget hratio hx
  obtain ⟨R : ℕ, hR⟩ := exists_nat_gt (x + 1)
  have hxR : x < (R : ℝ) := lt_trans (by linarith) hR
  obtain ⟨error, herror, hlocalR⟩ := hlocal R
  have huR : ContinuousOn u (Icc (0 : ℝ) (R : ℝ)) :=
    hu.mono fun _ hy ↦ hy.1
  obtain ⟨C, hC⟩ :=
    isCompact_Icc.exists_bound_of_continuousOn huR
  have hCnonneg : 0 ≤ C := by
    have hCzero := hC 0 ⟨le_rfl, Nat.cast_nonneg R⟩
    exact (norm_nonneg (u 0)).trans hCzero
  let errorBound : ℕ → ℝ := fun n ↦
    ((R : ℝ) + 1) *
      (|error n| * (|error n| + C) + C * |error n|)
  have habs : Tendsto (fun n ↦ |error n|) atTop (nhds 0) := by
    simpa only [abs_zero] using herror.abs
  have herrorBound : Tendsto errorBound atTop (nhds 0) := by
    have hfirst := habs.mul (habs.add
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ C) atTop (nhds C)))
    have hsecond :=
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ C) atTop (nhds C)).mul habs
    have hinner := hfirst.add hsecond
    have htotal :=
      (tendsto_const_nhds : Tendsto
        (fun _ : ℕ ↦ (R : ℝ) + 1) atTop (nhds ((R : ℝ) + 1))).mul hinner
    simpa only [errorBound, zero_add, add_zero, mul_zero, zero_mul] using htotal
  have hscalePos : ∀ᶠ n : ℕ in atTop, 0 < scale n := by
    have hge : ∀ᶠ n : ℕ in atTop, 1 ≤ scale n :=
      hscale (eventually_ge_atTop (1 : ℕ))
    exact hge.mono fun _ hn ↦ by omega
  have htargetLe : ∀ᶠ n : ℕ in atTop, target n ≤ R * scale n := by
    have hratioLt : ∀ᶠ n : ℕ in atTop,
        (target n : ℝ) / (scale n : ℝ) < (R : ℝ) :=
      hratio (Iio_mem_nhds hxR)
    filter_upwards [hratioLt, hscalePos] with n hn hnpos
    have hNreal : (0 : ℝ) < (scale n : ℝ) := by exact_mod_cast hnpos
    have hlt : (target n : ℝ) < (R : ℝ) * (scale n : ℝ) :=
      (div_lt_iff₀ hNreal).mp hn
    have hltNat : target n < R * scale n := by exact_mod_cast hlt
    exact hltNat.le
  apply hprofile.congr_dist
  apply squeeze_zero' (Eventually.of_forall fun _ ↦ dist_nonneg) _ herrorBound
  filter_upwards [hscalePos, htargetLe] with n hnpos hkn
  let N : ℕ := scale n
  let k : ℕ := target n
  have hNpos : 0 < N := by simpa only [N] using hnpos
  have hNreal : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNpos
  have hNne : (N : ℝ) ≠ 0 := hNreal.ne'
  have hkN : k ≤ R * N := by simpa only [k, N] using hkn
  let q : ℝ := |error n| * (|error n| + C) + C * |error n|
  have hqnonneg : 0 ≤ q := by
    dsimp only [q]
    positivity
  have hterm : ∀ i ∈ Finset.range (k + 1),
      |(((N : ℝ) ^ 2 * rho n i) *
          ((N : ℝ) ^ 2 * rho n (k - i))) -
        (u ((i : ℝ) / (N : ℝ)) *
          u (((k - i : ℕ) : ℝ) / (N : ℝ)))| ≤ q := by
    intro i hi
    have hik : i ≤ k :=
      Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hsubk : k - i ≤ k := Nat.sub_le k i
    have hiRN : i ≤ R * scale n := by
      simpa only [N] using hik.trans hkN
    have hsubRN : k - i ≤ R * scale n := by
      simpa only [N] using hsubk.trans hkN
    have hiR : (i : ℝ) / (N : ℝ) ∈ Icc (0 : ℝ) (R : ℝ) := by
      constructor
      · exact div_nonneg (Nat.cast_nonneg i) hNreal.le
      · rw [div_le_iff₀ hNreal]
        exact_mod_cast (hik.trans hkN)
    have hsubR : ((k - i : ℕ) : ℝ) / (N : ℝ) ∈
        Icc (0 : ℝ) (R : ℝ) := by
      constructor
      · exact div_nonneg (Nat.cast_nonneg _) hNreal.le
      · rw [div_le_iff₀ hNreal]
        exact_mod_cast (hsubk.trans hkN)
    apply abs_mul_sub_mul_le_of_two_errors
      ((N : ℝ) ^ 2 * rho n i)
      ((N : ℝ) ^ 2 * rho n (k - i))
      (u ((i : ℝ) / (N : ℝ)))
      (u (((k - i : ℕ) : ℝ) / (N : ℝ)))
      |error n| C (abs_nonneg _) hCnonneg
    · exact (hlocalR n hnpos i hiRN).trans (le_abs_self (error n))
    · exact (hlocalR n hnpos (k - i) hsubRN).trans
        (le_abs_self (error n))
    · simpa only [Real.norm_eq_abs] using hC _ hiR
    · simpa only [Real.norm_eq_abs] using hC _ hsubR
  have hcard : k + 1 ≤ (R + 1) * N := by
    calc
      k + 1 ≤ R * N + N := Nat.add_le_add hkN hNpos
      _ = (R + 1) * N := by rw [Nat.add_mul, one_mul]
  have hratioCard : ((k + 1 : ℕ) : ℝ) / (N : ℝ) ≤ (R : ℝ) + 1 := by
    rw [div_le_iff₀ hNreal]
    norm_num only [Nat.cast_add, Nat.cast_one, Nat.cast_mul]
    exact_mod_cast hcard
  rw [dist_comm, Real.dist_eq, scaledLatticeSelfConvolutionSum,
    latticeSelfConvolutionSum, show scale n = N from rfl,
    show target n = k from rfl, ← mul_sub, ← Finset.sum_sub_distrib,
    abs_mul, abs_of_pos (inv_pos.mpr hNreal)]
  calc
    (N : ℝ)⁻¹ *
        |∑ i ∈ Finset.range (k + 1),
          (((N : ℝ) ^ 2 * rho n i) *
              ((N : ℝ) ^ 2 * rho n (k - i)) -
            u ((i : ℝ) / (N : ℝ)) *
              u (((k - i : ℕ) : ℝ) / (N : ℝ)))| ≤
        (N : ℝ)⁻¹ * ∑ i ∈ Finset.range (k + 1),
          |(((N : ℝ) ^ 2 * rho n i) *
              ((N : ℝ) ^ 2 * rho n (k - i)) -
            u ((i : ℝ) / (N : ℝ)) *
              u (((k - i : ℕ) : ℝ) / (N : ℝ)))| := by
      exact mul_le_mul_of_nonneg_left
        (Finset.abs_sum_le_sum_abs _ _) (inv_nonneg.mpr hNreal.le)
    _ ≤ (N : ℝ)⁻¹ * ∑ _i ∈ Finset.range (k + 1), q := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hNreal.le)
      apply Finset.sum_le_sum
      intro i hi
      exact hterm i hi
    _ = (((k + 1 : ℕ) : ℝ) / (N : ℝ)) * q := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      rw [div_eq_mul_inv]
      ring
    _ ≤ ((R : ℝ) + 1) * q :=
      mul_le_mul_of_nonneg_right hratioCard hqnonneg
    _ = errorBound n := by
      rfl

/-- Source-facing moving-point theorem for the actual Cauchy convolution.
The proof uses the exact `conv` definition, rather than an abstract quadratic
source or an assumed convolution limit. -/
theorem scaled_conv_tendsto_moving_of_locallyUniform
    (rho : ℕ → Seq) (scale target : ℕ → ℕ) (u : ℝ → ℝ) (x : ℝ)
    (hscale : Tendsto scale atTop atTop)
    (htarget : Tendsto target atTop atTop)
    (hratio : Tendsto
      (fun n : ℕ ↦ (target n : ℝ) / (scale n : ℝ))
      atTop (nhds x))
    (hu : ContinuousOn u (Ici (0 : ℝ)))
    (hlocal : LocallyUniformLatticeDensity rho scale u)
    (hx : 0 < x) :
    Tendsto
      (fun n : ℕ ↦
        (scale n : ℝ) ^ 3 * conv (rho n) (rho n) (target n))
      atTop (nhds (positiveSelfConvolution u x)) := by
  have hsum :=
    scaledLatticeSelfConvolutionSum_tendsto_moving_of_locallyUniform
      rho scale target u x hscale htarget hratio hu hlocal hx
  have hscalePos : ∀ᶠ n : ℕ in atTop, 0 < scale n := by
    have hge : ∀ᶠ n : ℕ in atTop, 1 ≤ scale n :=
      hscale (eventually_ge_atTop (1 : ℕ))
    exact hge.mono fun _ hn ↦ by omega
  apply hsum.congr'
  filter_upwards [hscalePos] with n hn
  have hidentity :
      (scale n : ℝ) ^ 3 * conv (rho n) (rho n) (target n) =
        scaledLatticeSelfConvolutionSum (rho n) (scale n) (target n) := by
    simpa only [scaledLatticeSelfConvolutionSum] using
      scaled_conv_eq_lattice_product_sum
        (rho n) (scale n) (target n) hn
  exact hidentity.symm

/-! ## Fixed nodes, the hard boundary, and fixed index shifts -/

/-- Adding a fixed index to a cofinal moving target preserves both cofinality
and its macroscopic location. -/
theorem target_add_const_limits
    (scale target : ℕ → ℕ) (x : ℝ) (q : ℕ)
    (hscale : Tendsto scale atTop atTop)
    (htarget : Tendsto target atTop atTop)
    (hratio : Tendsto
      (fun n : ℕ ↦ (target n : ℝ) / (scale n : ℝ))
      atTop (nhds x)) :
    Tendsto (fun n ↦ target n + q) atTop atTop ∧
      Tendsto
        (fun n : ℕ ↦ ((target n + q : ℕ) : ℝ) / (scale n : ℝ))
        atTop (nhds x) := by
  have hq : Tendsto (fun n : ℕ ↦ (q : ℝ) / (scale n : ℝ))
      atTop (nhds 0) :=
    (tendsto_const_div_atTop_nhds_zero_nat (q : ℝ)).comp hscale
  constructor
  · exact (tendsto_add_atTop_nat q).comp htarget
  · simpa only [Nat.cast_add, add_div, add_zero] using hratio.add hq

/-- Subtracting a fixed index has the same two invariance properties.  The
proof makes the eventual absence of boundary truncation explicit. -/
theorem target_sub_const_limits
    (scale target : ℕ → ℕ) (x : ℝ) (q : ℕ)
    (hscale : Tendsto scale atTop atTop)
    (htarget : Tendsto target atTop atTop)
    (hratio : Tendsto
      (fun n : ℕ ↦ (target n : ℝ) / (scale n : ℝ))
      atTop (nhds x)) :
    Tendsto (fun n ↦ target n - q) atTop atTop ∧
      Tendsto
        (fun n : ℕ ↦ ((target n - q : ℕ) : ℝ) / (scale n : ℝ))
        atTop (nhds x) := by
  have hsubTop : Tendsto (fun n ↦ target n - q) atTop atTop := by
    rw [tendsto_atTop]
    intro b
    filter_upwards [htarget.eventually_ge_atTop (b + q)] with n hn
    omega
  have hq : Tendsto (fun n : ℕ ↦ (q : ℝ) / (scale n : ℝ))
      atTop (nhds 0) :=
    (tendsto_const_div_atTop_nhds_zero_nat (q : ℝ)).comp hscale
  have hraw : Tendsto
      (fun n : ℕ ↦ (target n : ℝ) / (scale n : ℝ) -
        (q : ℝ) / (scale n : ℝ)) atTop (nhds x) := by
    simpa only [sub_zero] using hratio.sub hq
  refine ⟨hsubTop, hraw.congr' ?_⟩
  filter_upwards [htarget.eventually_ge_atTop q] with n hn
  rw [Nat.cast_sub hn]
  ring

/-- The natural-floor grid point has the expected positive macroscopic
location along every cofinal scale. -/
theorem gridIndex_cofinal_and_ratio
    (scale : ℕ → ℕ) (hscale : Tendsto scale atTop atTop)
    (x : ℝ) (hx : 0 < x) :
    Tendsto (fun n ↦ gridIndex (scale n) x) atTop atTop ∧
      Tendsto
        (fun n : ℕ ↦ (gridIndex (scale n) x : ℝ) / (scale n : ℝ))
        atTop (nhds x) := by
  have hscaleReal : Tendsto (fun n : ℕ ↦ (scale n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hscale
  constructor
  · simpa only [gridIndex, max_eq_left hx.le, mul_comm] using
      (tendsto_nat_floor_mul_atTop x hx).comp hscale
  · simpa only [gridIndex, max_eq_left hx.le, mul_comm,
      Function.comp_apply] using
      (tendsto_nat_floor_mul_div_atTop (R := ℝ) hx.le).comp hscaleReal

/-- Fixed positive spatial point, read at the actual source floor node. -/
theorem scaled_conv_gridIndex_tendsto_of_locallyUniform
    (rho : ℕ → Seq) (scale : ℕ → ℕ) (u : ℝ → ℝ) (x : ℝ)
    (hscale : Tendsto scale atTop atTop)
    (hu : ContinuousOn u (Ici (0 : ℝ)))
    (hlocal : LocallyUniformLatticeDensity rho scale u)
    (hx : 0 < x) :
    Tendsto
      (fun n : ℕ ↦ (scale n : ℝ) ^ 3 *
        conv (rho n) (rho n) (gridIndex (scale n) x))
      atTop (nhds (positiveSelfConvolution u x)) := by
  obtain ⟨htarget, hratio⟩ := gridIndex_cofinal_and_ratio scale hscale x hx
  exact scaled_conv_tendsto_moving_of_locallyUniform
    rho scale (fun n ↦ gridIndex (scale n) x) u x
    hscale htarget hratio hu hlocal hx

/-- At the zero spatial boundary the Cauchy sum consists of one atom.  Its
extra factor `1/N` forces the rescaled convolution to zero, exactly matching
the zero-length continuous convolution interval. -/
theorem scaled_conv_zero_tendsto_of_locallyUniform
    (rho : ℕ → Seq) (scale : ℕ → ℕ) (u : ℝ → ℝ)
    (hscale : Tendsto scale atTop atTop)
    (hlocal : LocallyUniformLatticeDensity rho scale u) :
    Tendsto
      (fun n : ℕ ↦ (scale n : ℝ) ^ 3 * conv (rho n) (rho n) 0)
      atTop (nhds (positiveSelfConvolution u 0)) := by
  obtain ⟨error, herror, hlocalZero⟩ := hlocal 0
  have hscalePos : ∀ᶠ n : ℕ in atTop, 0 < scale n := by
    have hge : ∀ᶠ n : ℕ in atTop, 1 ≤ scale n :=
      hscale (eventually_ge_atTop (1 : ℕ))
    exact hge.mono fun _ hn ↦ by omega
  let atom : ℕ → ℝ := fun n ↦ (scale n : ℝ) ^ 2 * rho n 0
  have hatom : Tendsto atom atTop (nhds (u 0)) := by
    apply tendsto_const_nhds.congr_dist
    apply squeeze_zero' (Eventually.of_forall fun _ ↦ dist_nonneg) _ herror
    filter_upwards [hscalePos] with n hn
    have hpoint := hlocalZero n hn 0 (by simp)
    simpa only [atom, Real.dist_eq, Nat.cast_zero, zero_div,
      abs_sub_comm] using hpoint
  have hinv : Tendsto (fun n : ℕ ↦ (scale n : ℝ)⁻¹)
      atTop (nhds 0) := by
    simpa only [Function.comp_apply] using
      tendsto_inverse_atTop_nhds_zero_nat.comp hscale
  have hproduct : Tendsto (fun n ↦ (scale n : ℝ)⁻¹ * atom n * atom n)
      atTop (nhds 0) := by
    simpa only [zero_mul] using (hinv.mul hatom).mul hatom
  have heq : ∀ᶠ n : ℕ in atTop,
      (scale n : ℝ) ^ 3 * conv (rho n) (rho n) 0 =
        (scale n : ℝ)⁻¹ * atom n * atom n := by
    filter_upwards [hscalePos] with n hn
    have hidentity :=
      scaled_conv_eq_lattice_product_sum (rho n) (scale n) 0 hn
    simpa [atom, mul_assoc] using hidentity
  have hconv := hproduct.congr' (heq.mono fun _ hn ↦ hn.symm)
  simpa only [positiveSelfConvolution, intervalIntegral.integral_same] using hconv

/-- Fixed nonnegative spatial point, including the hard boundary `x=0`. -/
theorem scaled_conv_gridIndex_tendsto_of_locallyUniform_of_nonneg
    (rho : ℕ → Seq) (scale : ℕ → ℕ) (u : ℝ → ℝ) (x : ℝ)
    (hscale : Tendsto scale atTop atTop)
    (hu : ContinuousOn u (Ici (0 : ℝ)))
    (hlocal : LocallyUniformLatticeDensity rho scale u)
    (hx : 0 ≤ x) :
    Tendsto
      (fun n : ℕ ↦ (scale n : ℝ) ^ 3 *
        conv (rho n) (rho n) (gridIndex (scale n) x))
      atTop (nhds (positiveSelfConvolution u x)) := by
  rcases hx.eq_or_lt with rfl | hxpos
  · simpa only [gridIndex_at_zero] using
      scaled_conv_zero_tendsto_of_locallyUniform rho scale u hscale hlocal
  · exact scaled_conv_gridIndex_tendsto_of_locallyUniform
      rho scale u x hscale hu hlocal hxpos

/-- Pointwise formula for a finite right shift, including its literal zero
extension on `k < q`. -/
theorem shiftRightPow_apply_eq_ite
    (q : ℕ) (f : Seq) (k : ℕ) :
    shiftRightPow q f k = if q ≤ k then f (k - q) else 0 := by
  induction q generalizing f k with
  | zero => simp only [shiftRightPow_zero, Nat.zero_le, ↓reduceIte, Nat.sub_zero]
  | succ q ih =>
      rw [shiftRightPow_succ]
      simp only [ih]
      by_cases hqk : q + 1 ≤ k
      · have hqk' : q ≤ k := by omega
        rw [if_pos hqk, if_pos hqk']
        have hsub : k - q = (k - (q + 1)) + 1 := by omega
        rw [hsub, shiftRight_succ]
      · rw [if_neg hqk]
        by_cases hqk' : q ≤ k
        · rw [if_pos hqk']
          have hkq : k = q := by omega
          subst k
          simp only [Nat.sub_self, shiftRight_zero]
        · rw [if_neg hqk']

/-- Above the boundary, `shiftRightPow q` is exactly subtraction of `q` from
the readout index. -/
theorem shiftRightPow_apply_of_le
    (q : ℕ) (f : Seq) (k : ℕ) (hqk : q ≤ k) :
    shiftRightPow q f k = f (k - q) := by
  simp only [shiftRightPow_apply_eq_ite, hqk, ↓reduceIte]

/-- Below the boundary, the same right shift is exactly zero. -/
theorem shiftRightPow_apply_of_lt
    (q : ℕ) (f : Seq) (k : ℕ) (hkq : k < q) :
    shiftRightPow q f k = 0 := by
  simp only [shiftRightPow_apply_eq_ite, if_neg (Nat.not_le.mpr hkq)]

/-- A fixed positive right shift of the actual discrete quadratic convolution
does not change its positive macroscopic spatial limit. -/
theorem scaled_shiftRightPow_conv_gridIndex_tendsto_of_locallyUniform
    (rho : ℕ → Seq) (scale : ℕ → ℕ) (u : ℝ → ℝ)
    (q : ℕ) (x : ℝ)
    (hscale : Tendsto scale atTop atTop)
    (hu : ContinuousOn u (Ici (0 : ℝ)))
    (hlocal : LocallyUniformLatticeDensity rho scale u)
    (hx : 0 < x) :
    Tendsto
      (fun n : ℕ ↦ (scale n : ℝ) ^ 3 *
        shiftRightPow q (conv (rho n) (rho n)) (gridIndex (scale n) x))
      atTop (nhds (positiveSelfConvolution u x)) := by
  let target : ℕ → ℕ := fun n ↦ gridIndex (scale n) x
  obtain ⟨htarget, hratio⟩ := gridIndex_cofinal_and_ratio scale hscale x hx
  obtain ⟨hsubTop, hsubRatio⟩ :=
    target_sub_const_limits scale target x q hscale htarget hratio
  have hconv := scaled_conv_tendsto_moving_of_locallyUniform
    rho scale (fun n ↦ target n - q) u x
    hscale hsubTop hsubRatio hu hlocal hx
  apply hconv.congr'
  filter_upwards [htarget.eventually_ge_atTop q] with n hn
  rw [shiftRightPow_apply_of_le q (conv (rho n) (rho n)) (target n) hn]

/-- The fixed-right-shift result including `x=0`.  When `q>0`, the boundary
readout is identically zero by the preceding zero-extension formula. -/
theorem scaled_shiftRightPow_conv_gridIndex_tendsto_of_nonneg
    (rho : ℕ → Seq) (scale : ℕ → ℕ) (u : ℝ → ℝ)
    (q : ℕ) (x : ℝ)
    (hscale : Tendsto scale atTop atTop)
    (hu : ContinuousOn u (Ici (0 : ℝ)))
    (hlocal : LocallyUniformLatticeDensity rho scale u)
    (hx : 0 ≤ x) :
    Tendsto
      (fun n : ℕ ↦ (scale n : ℝ) ^ 3 *
        shiftRightPow q (conv (rho n) (rho n)) (gridIndex (scale n) x))
      atTop (nhds (positiveSelfConvolution u x)) := by
  rcases hx.eq_or_lt with rfl | hxpos
  · cases q with
    | zero =>
        simpa only [shiftRightPow_zero, gridIndex_at_zero] using
          scaled_conv_zero_tendsto_of_locallyUniform rho scale u hscale hlocal
    | succ q =>
        have hzero : (fun n : ℕ ↦ (scale n : ℝ) ^ 3 *
            shiftRightPow (q + 1) (conv (rho n) (rho n))
              (gridIndex (scale n) 0)) = fun _ ↦ (0 : ℝ) := by
          funext n
          rw [gridIndex_at_zero,
            shiftRightPow_apply_of_lt (q + 1) _ 0 (by omega), mul_zero]
        rw [hzero]
        simpa only [positiveSelfConvolution,
          intervalIntegral.integral_same] using
          (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (0 : ℝ)) atTop (nhds 0))
  · exact scaled_shiftRightPow_conv_gridIndex_tendsto_of_locallyUniform
      rho scale u q x hscale hu hlocal hxpos

/-! ## A genuinely local-uniform positive-space version -/

/-- The profile convolution Riemann sums converge uniformly when the output
grid point stays in a compact annulus `δ ≤ k/N ≤ R`. -/
theorem latticeSelfConvolutionSum_uniform_on_compact_away_zero
    (u : ℝ → ℝ) (hu : ContinuousOn u (Ici (0 : ℝ)))
    (δ : ℝ) (R : ℕ) (hδ : 0 < δ) :
    ∀ ε : ℝ, 0 < ε → ∃ M : ℕ, ∀ N : ℕ, M ≤ N →
      ∀ k : ℕ, δ * (N : ℝ) ≤ (k : ℝ) → k ≤ R * N →
        |latticeSelfConvolutionSum u N k -
          positiveSelfConvolution u ((k : ℝ) / (N : ℝ))| < ε := by
  intro ε hε
  let G : ℝ × ℝ → ℝ := fun p ↦ unitSelfConvolutionKernel u p.1 p.2
  have hargOne : ContinuousOn (fun p : ℝ × ℝ ↦ p.1 * p.2)
      (Icc (0 : ℝ) (R : ℝ) ×ˢ Icc (0 : ℝ) 1) :=
    (continuous_fst.mul continuous_snd).continuousOn
  have hargTwo : ContinuousOn (fun p : ℝ × ℝ ↦ p.1 - p.1 * p.2)
      (Icc (0 : ℝ) (R : ℝ) ×ˢ Icc (0 : ℝ) 1) :=
    (continuous_fst.sub (continuous_fst.mul continuous_snd)).continuousOn
  have hG : ContinuousOn G
      (Icc (0 : ℝ) (R : ℝ) ×ˢ Icc (0 : ℝ) 1) := by
    apply (hu.comp hargOne ?_).mul (hu.comp hargTwo ?_)
    · intro p hp
      exact mul_nonneg hp.1.1 hp.2.1
    · intro p hp
      exact sub_nonneg.mpr (mul_le_of_le_one_right hp.1.1 hp.2.2)
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hu.mono fun _ hy ↦ hy.1 : ContinuousOn u
      (Icc (0 : ℝ) (R : ℝ)))
  have hCnonneg : 0 ≤ C := by
    have hCzero := hC 0 ⟨le_rfl, Nat.cast_nonneg R⟩
    exact (norm_nonneg (u 0)).trans hCzero
  let η : ℝ := ε / (4 * ((R : ℝ) + 1))
  have hη : 0 < η := by
    dsimp only [η]
    positivity
  obtain ⟨K, hK⟩ :=
    latticeLeftRiemannSum_unit_uniform_in_parameter G (R : ℝ) hG η hη
  obtain ⟨Mgrid, hMgrid⟩ := exists_nat_gt ((K : ℝ) / δ)
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
  intro N hMN k hlower hkR
  have hMgridN : Mgrid ≤ N :=
    (le_max_left Mgrid Mend).trans
      ((le_max_left (max Mgrid Mend) 1).trans hMN)
  have hMendN : Mend ≤ N :=
    (le_max_right Mgrid Mend).trans
      ((le_max_left (max Mgrid Mend) 1).trans hMN)
  have hNpos : 0 < N := (le_max_right (max Mgrid Mend) 1).trans hMN
  have hNreal : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNpos
  have hKreal : (K : ℝ) < δ * (N : ℝ) := by
    have hKM : (K : ℝ) < (Mgrid : ℝ) * δ :=
      (div_lt_iff₀ hδ).mp hMgrid
    calc
      (K : ℝ) < (Mgrid : ℝ) * δ := hKM
      _ ≤ (N : ℝ) * δ := by
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hMgridN) hδ.le
      _ = δ * (N : ℝ) := mul_comm _ _
  have hKk : K ≤ k := by
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
  have hriemann := hK k hKk x hxR
  have hsplit := latticeSelfConvolutionSum_eq_unit_add_endpoint
    u N k hNpos hkpos
  have huX : |u x| ≤ C := by
    simpa only [Real.norm_eq_abs] using hC x hxR
  have huZero : |u 0| ≤ C := by
    simpa only [Real.norm_eq_abs] using
      hC 0 ⟨le_rfl, Nat.cast_nonneg R⟩
  have hendpoint :
      |(N : ℝ)⁻¹ * u x * u 0| < ε / 4 := by
    calc
      |(N : ℝ)⁻¹ * u x * u 0| =
          (N : ℝ)⁻¹ * |u x| * |u 0| := by
        rw [abs_mul, abs_mul, abs_of_pos (inv_pos.mpr hNreal)]
      _ ≤ (N : ℝ)⁻¹ * C * C := by
        gcongr
      _ < ε / 4 := hMend N hMendN
  rw [hsplit, ← positiveSelfConvolution_eq_unit u x]
  rw [show x * latticeLeftRiemannSum
      (unitSelfConvolutionKernel u x) 1 k +
        (N : ℝ)⁻¹ * u x * u 0 -
      x * ∫ z in (0 : ℝ)..1, unitSelfConvolutionKernel u x z =
      x * (latticeLeftRiemannSum
        (unitSelfConvolutionKernel u x) 1 k -
          ∫ z in (0 : ℝ)..1, unitSelfConvolutionKernel u x z) +
        (N : ℝ)⁻¹ * u x * u 0 by ring]
  calc
    |x * (latticeLeftRiemannSum
          (unitSelfConvolutionKernel u x) 1 k -
        ∫ z in (0 : ℝ)..1, unitSelfConvolutionKernel u x z) +
      (N : ℝ)⁻¹ * u x * u 0| ≤
        |x * (latticeLeftRiemannSum
          (unitSelfConvolutionKernel u x) 1 k -
            ∫ z in (0 : ℝ)..1, unitSelfConvolutionKernel u x z)| +
          |(N : ℝ)⁻¹ * u x * u 0| := by
      exact abs_add _ _
    _ = x * |latticeLeftRiemannSum
          (unitSelfConvolutionKernel u x) 1 k -
            ∫ z in (0 : ℝ)..1, unitSelfConvolutionKernel u x z| +
          |(N : ℝ)⁻¹ * u x * u 0| := by
      rw [abs_mul, abs_of_nonneg hxR.1]
    _ < (R : ℝ) * η + ε / 4 := by
      apply add_lt_add_of_le_of_lt _ hendpoint
      exact mul_le_mul hxR.2 hriemann.le (abs_nonneg _) (Nat.cast_nonneg R)
    _ ≤ ε / 4 + ε / 4 := by
      apply add_le_add_right
      have hRle : (R : ℝ) ≤ (R : ℝ) + 1 := by linarith
      calc
        (R : ℝ) * η ≤ ((R : ℝ) + 1) * η :=
          mul_le_mul_of_nonneg_right hRle hη.le
        _ = ε / 4 := by
          dsimp only [η]
          field_simp
          ring
    _ < ε := by linarith

/-- Local-uniform spatial convergence of the actual discrete quadratic
convolution on every compact annulus `δ ≤ k/N ≤ R`.  The conclusion is a
single eventual statement uniform over all eligible output nodes. -/
theorem scaled_conv_uniform_on_compact_away_zero_of_locallyUniform
    (rho : ℕ → Seq) (scale : ℕ → ℕ) (u : ℝ → ℝ)
    (δ : ℝ) (R : ℕ)
    (hscale : Tendsto scale atTop atTop)
    (hu : ContinuousOn u (Ici (0 : ℝ)))
    (hlocal : LocallyUniformLatticeDensity rho scale u)
    (hδ : 0 < δ) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ k : ℕ,
      δ * (scale n : ℝ) ≤ (k : ℝ) → k ≤ R * scale n →
        |(scale n : ℝ) ^ 3 * conv (rho n) (rho n) k -
          positiveSelfConvolution u ((k : ℝ) / (scale n : ℝ))| < ε := by
  intro ε hε
  obtain ⟨Mprofile, hprofile⟩ :=
    latticeSelfConvolutionSum_uniform_on_compact_away_zero
      u hu δ R hδ (ε / 2) (half_pos hε)
  obtain ⟨error, herror, hlocalR⟩ := hlocal R
  have huR : ContinuousOn u (Icc (0 : ℝ) (R : ℝ)) :=
    hu.mono fun _ hy ↦ hy.1
  obtain ⟨C, hC⟩ :=
    isCompact_Icc.exists_bound_of_continuousOn huR
  have hCnonneg : 0 ≤ C := by
    have hCzero := hC 0 ⟨le_rfl, Nat.cast_nonneg R⟩
    exact (norm_nonneg (u 0)).trans hCzero
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
    have hge : ∀ᶠ n : ℕ in atTop, 1 ≤ scale n :=
      hscale.eventually_ge_atTop 1
    exact hge.mono fun _ hn ↦ by omega
  filter_upwards [hcoeffSmall, hscaleLarge, hscalePos] with
      n hnsmall hnlarge hnpos
  intro k hlower hkR
  have hNreal : (0 : ℝ) < (scale n : ℝ) := by exact_mod_cast hnpos
  have huBound : ∀ j : ℕ, j ≤ R * scale n →
      |u ((j : ℝ) / (scale n : ℝ))| ≤ C := by
    intro j hj
    have hxj : (j : ℝ) / (scale n : ℝ) ∈
        Icc (0 : ℝ) (R : ℝ) := by
      constructor
      · exact div_nonneg (Nat.cast_nonneg j) hNreal.le
      · rw [div_le_iff₀ hNreal]
        exact_mod_cast hj
    simpa only [Real.norm_eq_abs] using hC _ hxj
  have hcompare : dist
      (scaledLatticeSelfConvolutionSum (rho n) (scale n) k)
      (latticeSelfConvolutionSum u (scale n) k) < ε / 2 := by
    calc
      dist (scaledLatticeSelfConvolutionSum (rho n) (scale n) k)
          (latticeSelfConvolutionSum u (scale n) k) ≤
          ((R : ℝ) + 1) *
            (|error n| * (|error n| + C) + C * |error n|) :=
        scaledLatticeSelfConvolutionSum_dist_le
          (rho n) u (scale n) k R |error n| C hnpos hkR
          (abs_nonneg _) hCnonneg
          (fun j hj ↦ (hlocalR n hnpos j hj).trans
            (le_abs_self (error n))) huBound
      _ = coeffError n := rfl
      _ < ε / 2 := hnsmall
  have hprofileSmall := hprofile (scale n) hnlarge k hlower hkR
  have hidentity :
      (scale n : ℝ) ^ 3 * conv (rho n) (rho n) k =
        scaledLatticeSelfConvolutionSum (rho n) (scale n) k := by
    simpa only [scaledLatticeSelfConvolutionSum] using
      scaled_conv_eq_lattice_product_sum (rho n) (scale n) k hnpos
  rw [hidentity]
  calc
    |scaledLatticeSelfConvolutionSum (rho n) (scale n) k -
        positiveSelfConvolution u ((k : ℝ) / (scale n : ℝ))| =
        dist (scaledLatticeSelfConvolutionSum (rho n) (scale n) k)
          (positiveSelfConvolution u ((k : ℝ) / (scale n : ℝ))) := by
      rw [Real.dist_eq]
    _ ≤ dist (scaledLatticeSelfConvolutionSum (rho n) (scale n) k)
          (latticeSelfConvolutionSum u (scale n) k) +
        dist (latticeSelfConvolutionSum u (scale n) k)
          (positiveSelfConvolution u ((k : ℝ) / (scale n : ℝ))) :=
      dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := by
      apply add_lt_add hcompare
      simpa only [Real.dist_eq] using hprofileSmall
    _ = ε := by ring

/-! ## Source-notation wrappers -/

/-- Fixed-point version with the literal orbit density `rho m (orbit ...)`.
The selected generation may represent any positive macroscopic time slice;
all analytic content is in its stated local-uniform lattice hypothesis. -/
theorem orbit_rho_scaled_conv_gridIndex_tendsto
    (m : ℕ) (p₀ : ProbabilityMass) (generation scale : ℕ → ℕ)
    (u : ℝ → ℝ) (x : ℝ)
    (hscale : Tendsto scale atTop atTop)
    (hu : ContinuousOn u (Ici (0 : ℝ)))
    (hlocal : LocallyUniformLatticeDensity
      (fun n ↦ rho m (orbit m p₀ (generation n))) scale u)
    (hx : 0 ≤ x) :
    Tendsto
      (fun n : ℕ ↦ (scale n : ℝ) ^ 3 *
        conv (rho m (orbit m p₀ (generation n)))
          (rho m (orbit m p₀ (generation n))) (gridIndex (scale n) x))
      atTop (nhds (positiveSelfConvolution u x)) := by
  exact scaled_conv_gridIndex_tendsto_of_locallyUniform_of_nonneg
    (fun n ↦ rho m (orbit m p₀ (generation n))) scale u x
    hscale hu hlocal hx

/-- Compact-annulus local-uniform version for the same literal orbit density. -/
theorem orbit_rho_scaled_conv_uniform_on_compact_away_zero
    (m : ℕ) (p₀ : ProbabilityMass) (generation scale : ℕ → ℕ)
    (u : ℝ → ℝ) (δ : ℝ) (R : ℕ)
    (hscale : Tendsto scale atTop atTop)
    (hu : ContinuousOn u (Ici (0 : ℝ)))
    (hlocal : LocallyUniformLatticeDensity
      (fun n ↦ rho m (orbit m p₀ (generation n))) scale u)
    (hδ : 0 < δ) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ k : ℕ,
      δ * (scale n : ℝ) ≤ (k : ℝ) → k ≤ R * scale n →
        |(scale n : ℝ) ^ 3 *
            conv (rho m (orbit m p₀ (generation n)))
              (rho m (orbit m p₀ (generation n))) k -
          positiveSelfConvolution u ((k : ℝ) / (scale n : ℝ))| < ε := by
  exact scaled_conv_uniform_on_compact_away_zero_of_locallyUniform
    (fun n ↦ rho m (orbit m p₀ (generation n))) scale u δ R
    hscale hu hlocal hδ

end

end DerridaRetaux
