import DerridaRetaux.Analysis.QuadraticConvolutionLimit
import Mathlib.Tactic

set_option autoImplicit false

open Filter Topology MeasureTheory Set
open scoped BigOperators Interval

namespace DerridaRetaux

noncomputable section

/-!
# Time Riemann sums with source floor endpoints

This file handles the time-mesh passage left open after the coefficient and
spatial-convolution limits.  The sums use the same half-open natural interval
as the exact discrete Duhamel formula.
-/

/-- The source-shaped left time sum: the lower floor is included and the
upper floor is excluded, exactly as in the discrete Duhamel `Finset.Ico`. -/
def gridTimeLeftRiemannSum (f : ℝ → ℝ) (N : ℕ) (a b : ℝ) : ℝ :=
  ∑ s ∈ Finset.Ico (gridIndex N a) (gridIndex N b),
    (N : ℝ)⁻¹ * f ((s : ℝ) / (N : ℝ))

/-- Prefix form used to expose both floor endpoints algebraically. -/
def gridTimePrefixRiemannSum (f : ℝ → ℝ) (N : ℕ) (x : ℝ) : ℝ :=
  ∑ s ∈ Finset.range (gridIndex N x),
    (N : ℝ)⁻¹ * f ((s : ℝ) / (N : ℝ))

/-- Triangular-array version of the same source-shaped time sum. -/
def gridTimeArraySum (F : ℕ → ℕ → ℝ) (scale : ℕ → ℕ)
    (n : ℕ) (a b : ℝ) : ℝ :=
  ∑ s ∈ Finset.Ico (gridIndex (scale n) a) (gridIndex (scale n) b),
    (scale n : ℝ)⁻¹ * F n s

/-- Monotonicity of the actual natural-floor grid readout on the nonnegative
half-line. -/
theorem gridIndex_mono_of_nonneg
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (N : ℕ) :
    gridIndex N a ≤ gridIndex N b := by
  rw [gridIndex, gridIndex, max_eq_left ha,
    max_eq_left (ha.trans hab)]
  apply Nat.floor_mono
  exact mul_le_mul_of_nonneg_left hab (Nat.cast_nonneg N)

/-- The floor node lies at most one mesh cell below its spatial argument. -/
theorem gridIndex_div_floor_bounds
    (N : ℕ) (x : ℝ) (hN : 0 < N) (hx : 0 ≤ x) :
    (gridIndex N x : ℝ) / (N : ℝ) ≤ x ∧
      x < (gridIndex N x : ℝ) / (N : ℝ) + (N : ℝ)⁻¹ := by
  have hNreal : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  constructor
  · rw [div_le_iff₀ hNreal]
    simpa only [mul_comm] using gridIndex_cast_le N x hx
  · have hsplit :
        (gridIndex N x : ℝ) / (N : ℝ) + (N : ℝ)⁻¹ =
          ((gridIndex N x : ℝ) + 1) / (N : ℝ) := by
      rw [add_div]
      simp only [one_div]
    rw [hsplit, lt_div_iff₀ hNreal]
    simpa only [mul_comm] using mul_lt_gridIndex_add_one N x hx

/-- In particular, the normalized actual floor node converges to its fixed
nonnegative target. -/
theorem gridIndex_div_tendsto
    (x : ℝ) (hx : 0 ≤ x) :
    Tendsto (fun N : ℕ ↦ (gridIndex N x : ℝ) / (N : ℝ))
      atTop (nhds x) := by
  have hscaleReal : Tendsto (fun N : ℕ ↦ (N : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  simpa only [gridIndex, max_eq_left hx, mul_comm, Function.comp_apply] using
    (tendsto_nat_floor_mul_div_atTop (R := ℝ) hx).comp hscaleReal

/-- A half-open floor interval is exactly the difference of its two floor
prefixes. -/
theorem gridTimeLeftRiemannSum_eq_prefix_sub
    (f : ℝ → ℝ) (N : ℕ) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) :
    gridTimeLeftRiemannSum f N a b =
      gridTimePrefixRiemannSum f N b -
        gridTimePrefixRiemannSum f N a := by
  rw [gridTimeLeftRiemannSum, gridTimePrefixRiemannSum,
    gridTimePrefixRiemannSum]
  exact Finset.sum_Ico_eq_sub _ (gridIndex_mono_of_nonneg ha hab N)

/-- Exact rescaling of a mesh prefix to a unit-interval left Riemann sum. -/
theorem gridTimePrefixRiemannSum_eq_unit
    (f : ℝ → ℝ) (N k : ℕ) (hN : 0 < N) (hk : 0 < k) :
    (∑ s ∈ Finset.range k,
      (N : ℝ)⁻¹ * f ((s : ℝ) / (N : ℝ))) =
      ((k : ℝ) / (N : ℝ)) *
        latticeLeftRiemannSum
          (fun z ↦ f (((k : ℝ) / (N : ℝ)) * z)) 1 k := by
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  rw [latticeLeftRiemannSum, one_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _hs
  have harg : (s : ℝ) / (N : ℝ) =
      ((k : ℝ) / (N : ℝ)) * ((s : ℝ) / (k : ℝ)) := by
    field_simp only [hN0, hk0]
    ring
  rw [harg]
  field_simp only [hN0, hk0]
  ring

/-- Continuous rescaling parameters give uniform convergence of the pulled-
back integrands on the unit interval. -/
theorem timeUnitKernel_tendstoUniformlyOn
    (f : ℝ → ℝ) (hf : Continuous f)
    (xseq : ℕ → ℝ) (x R : ℝ)
    (hx : Tendsto xseq atTop (nhds x))
    (hxR : x ∈ Icc (0 : ℝ) R)
    (hseqR : ∀ᶠ n : ℕ in atTop, xseq n ∈ Icc (0 : ℝ) R) :
    TendstoUniformlyOn
      (fun n z ↦ f (xseq n * z)) (fun z ↦ f (x * z))
      atTop (Icc (0 : ℝ) 1) := by
  let K : Set (ℝ × ℝ) := Icc (0 : ℝ) R ×ˢ Icc (0 : ℝ) 1
  let G : ℝ × ℝ → ℝ := fun p ↦ f (p.1 * p.2)
  have hG : Continuous G := hf.comp (continuous_fst.mul continuous_snd)
  have hGuniform : UniformContinuousOn G K :=
    (isCompact_Icc.prod isCompact_Icc).uniformContinuousOn_of_continuous
      hG.continuousOn
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

/-- Every positive floor prefix converges to the corresponding integral from
zero.  The proof displays the moving floor ratio and uses the exact unit-
interval rescaling above. -/
theorem gridTimePrefixRiemannSum_tendsto
    (f : ℝ → ℝ) (hf : Continuous f) (x : ℝ) (hx : 0 < x) :
    Tendsto (fun N : ℕ ↦ gridTimePrefixRiemannSum f N x)
      atTop (nhds (∫ t in (0 : ℝ)..x, f t)) := by
  let target : ℕ → ℕ := fun N ↦ gridIndex N x
  let xseq : ℕ → ℝ := fun N ↦ (target N : ℝ) / (N : ℝ)
  have htarget : Tendsto target atTop atTop := by
    simpa only [target, gridIndex, max_eq_left hx.le, mul_comm] using
      tendsto_nat_floor_mul_atTop x hx
  have hratio : Tendsto xseq atTop (nhds x) := by
    simpa only [xseq, target] using gridIndex_div_tendsto x hx.le
  let R : ℝ := x + 1
  have hxR : x ∈ Icc (0 : ℝ) R := by
    exact ⟨hx.le, by dsimp only [R]; linarith⟩
  have hseqR : ∀ᶠ N : ℕ in atTop, xseq N ∈ Icc (0 : ℝ) R := by
    have hupper : ∀ᶠ N : ℕ in atTop, xseq N < R :=
      hratio (Iio_mem_nhds (by dsimp only [R]; linarith))
    filter_upwards [hupper] with N hN
    exact ⟨div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _), hN.le⟩
  have huniform : TendstoUniformlyOn
      (fun N z ↦ f (xseq N * z)) (fun z ↦ f (x * z))
      atTop (Icc (0 : ℝ) 1) :=
    timeUnitKernel_tendstoUniformlyOn f hf xseq x R
      hratio hxR hseqR
  have hkernel : ContinuousOn (fun z : ℝ ↦ f (x * z))
      (Icc (0 : ℝ) 1) :=
    (hf.comp (continuous_const.mul continuous_id)).continuousOn
  have hriemann : Tendsto
      (fun N ↦ latticeLeftRiemannSum
        (fun z ↦ f (xseq N * z)) 1 (target N))
      atTop (nhds (∫ z in (0 : ℝ)..1, f (x * z))) :=
    latticeLeftRiemannSum_unit_tendsto_of_uniform
      (fun N z ↦ f (xseq N * z)) (fun z ↦ f (x * z))
      target htarget huniform hkernel
  have hmain : Tendsto
      (fun N ↦ xseq N * latticeLeftRiemannSum
        (fun z ↦ f (xseq N * z)) 1 (target N))
      atTop (nhds (x * ∫ z in (0 : ℝ)..1, f (x * z))) :=
    hratio.mul hriemann
  have hNpos : ∀ᶠ N : ℕ in atTop, 0 < N := by
    exact eventually_gt_atTop 0
  have htargetPos : ∀ᶠ N : ℕ in atTop, 0 < target N := by
    have hge : ∀ᶠ N : ℕ in atTop, 1 ≤ target N :=
      htarget (eventually_ge_atTop (1 : ℕ))
    exact hge.mono fun _ hN ↦ by omega
  have heq : ∀ᶠ N : ℕ in atTop,
      gridTimePrefixRiemannSum f N x =
        xseq N * latticeLeftRiemannSum
          (fun z ↦ f (xseq N * z)) 1 (target N) := by
    filter_upwards [hNpos, htargetPos] with N hN hk
    simpa only [gridTimePrefixRiemannSum, xseq, target] using
      gridTimePrefixRiemannSum_eq_unit f N (target N) hN hk
  have hprefix := hmain.congr' (heq.mono fun _ hN ↦ hN.symm)
  have hchange :
      x * ∫ z in (0 : ℝ)..1, f (x * z) =
        ∫ t in (0 : ℝ)..x, f t := by
    simpa only [mul_zero, mul_one] using
      (intervalIntegral.mul_integral_comp_mul_left
        (a := (0 : ℝ)) (b := 1) (f := f) x)
  rw [← hchange]
  exact hprefix

/-- Source-floor left sums on a fixed positive time window converge to the
corresponding interval integral.  Both floor endpoints are handled through
the exact prefix-difference identity, not replaced by idealized endpoints. -/
theorem gridTimeLeftRiemannSum_tendsto
    (f : ℝ → ℝ) (hf : Continuous f)
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    Tendsto (fun N : ℕ ↦ gridTimeLeftRiemannSum f N a b)
      atTop (nhds (∫ t in a..b, f t)) := by
  have hb : 0 < b := ha.trans_le hab
  have hprefixB := gridTimePrefixRiemannSum_tendsto f hf b hb
  have hprefixA := gridTimePrefixRiemannSum_tendsto f hf a ha
  have hdiff := hprefixB.sub hprefixA
  have hzeroA : IntervalIntegrable f volume (0 : ℝ) a :=
    hf.intervalIntegrable 0 a
  have habInt : IntervalIntegrable f volume a b :=
    hf.intervalIntegrable a b
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    hzeroA habInt
  have hintegral :
      (∫ t in (0 : ℝ)..b, f t) - (∫ t in (0 : ℝ)..a, f t) =
        ∫ t in a..b, f t := by
    linarith
  rw [← hintegral]
  apply hdiff.congr'
  filter_upwards [] with N
  exact (gridTimeLeftRiemannSum_eq_prefix_sub f N ha.le hab).symm

/-- Positive-time version: continuity is needed only on `(0,∞)`.  The proof
clamps the integrand to a compact interval below `a`, then shows that every
actual floor-window node eventually lies where the clamp is inactive. -/
theorem gridTimeLeftRiemannSum_tendsto_of_continuousOn_Ioi
    (f : ℝ → ℝ) (hf : ContinuousOn f (Ioi (0 : ℝ)))
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    Tendsto (fun N : ℕ ↦ gridTimeLeftRiemannSum f N a b)
      atTop (nhds (∫ t in a..b, f t)) := by
  let c : ℝ := a / 2
  have hc : 0 < c := half_pos ha
  have hcb : c ≤ b := by
    dsimp only [c]
    linarith
  let clamp : ℝ → ℝ := fun t ↦ max c (min b t)
  let g : ℝ → ℝ := fun t ↦ f (clamp t)
  have hclamp : Continuous clamp := by
    exact continuous_const.max (continuous_const.min continuous_id)
  have hclampMem : ∀ t : ℝ, clamp t ∈ Icc c b := by
    intro t
    constructor
    · exact le_max_left _ _
    · exact max_le hcb (min_le_left _ _)
  have hfcb : ContinuousOn f (Icc c b) := by
    apply hf.mono
    intro t ht
    exact hc.trans_le ht.1
  have hg : Continuous g := by
    have hcomp := hfcb.comp_continuous hclamp hclampMem
    simpa only [g, Function.comp_apply] using hcomp
  have hagree : ∀ t ∈ Icc c b, g t = f t := by
    intro t ht
    simp only [g, clamp, min_eq_right ht.2, max_eq_right ht.1]
  have hintegral : (∫ t in a..b, g t) = ∫ t in a..b, f t := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hab] at ht
    apply hagree t
    exact ⟨(by dsimp only [c]; linarith [ht.1]), ht.2⟩
  have hglobal := gridTimeLeftRiemannSum_tendsto g hg a b ha hab
  rw [hintegral] at hglobal
  apply hglobal.congr'
  have hNpos : ∀ᶠ N : ℕ in atTop, 0 < N := eventually_gt_atTop 0
  have hinv : Tendsto (fun N : ℕ ↦ (N : ℝ)⁻¹) atTop (nhds 0) :=
    tendsto_inverse_atTop_nhds_zero_nat
  have hinvSmall : ∀ᶠ N : ℕ in atTop, (N : ℝ)⁻¹ < c :=
    hinv (Iio_mem_nhds hc)
  filter_upwards [hNpos, hinvSmall] with N hN hsmall
  rw [gridTimeLeftRiemannSum, gridTimeLeftRiemannSum]
  apply Finset.sum_congr rfl
  intro s hs
  have hNreal : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hfloorA := gridIndex_div_floor_bounds N a hN ha.le
  have hfloorB := gridIndex_div_floor_bounds N b hN (ha.le.trans hab)
  have hsBounds := Finset.mem_Ico.mp hs
  have hsLower : (gridIndex N a : ℝ) / (N : ℝ) ≤
      (s : ℝ) / (N : ℝ) := by
    apply div_le_div_of_nonneg_right _ hNreal.le
    exact_mod_cast hsBounds.1
  have hsUpper : (s : ℝ) / (N : ℝ) ≤ b := by
    have hsHi : s ≤ gridIndex N b := Nat.le_of_lt hsBounds.2
    exact (div_le_div_of_nonneg_right (by exact_mod_cast hsHi) hNreal.le).trans
      hfloorB.1
  have hsMem : (s : ℝ) / (N : ℝ) ∈ Icc c b := by
    constructor
    · have hcFloor : c ≤ (gridIndex N a : ℝ) / (N : ℝ) := by
        dsimp only [c] at hsmall ⊢
        linarith [hfloorA.2]
      exact hcFloor.trans hsLower
    · exact hsUpper
  rw [hagree _ hsMem]

/-- The same floor-endpoint Riemann theorem along an arbitrary cofinal mesh
selection. -/
theorem gridTimeLeftRiemannSum_along_scale_tendsto
    (f : ℝ → ℝ) (hf : Continuous f)
    (scale : ℕ → ℕ) (hscale : Tendsto scale atTop atTop)
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    Tendsto
      (fun n : ℕ ↦ gridTimeLeftRiemannSum f (scale n) a b)
      atTop (nhds (∫ t in a..b, f t)) :=
  (gridTimeLeftRiemannSum_tendsto f hf a b ha hab).comp hscale

/-- Cofinal-scale form requiring continuity only at positive times. -/
theorem gridTimeLeftRiemannSum_along_scale_tendsto_of_continuousOn_Ioi
    (f : ℝ → ℝ) (hf : ContinuousOn f (Ioi (0 : ℝ)))
    (scale : ℕ → ℕ) (hscale : Tendsto scale atTop atTop)
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    Tendsto
      (fun n : ℕ ↦ gridTimeLeftRiemannSum f (scale n) a b)
      atTop (nhds (∫ t in a..b, f t)) :=
  (gridTimeLeftRiemannSum_tendsto_of_continuousOn_Ioi
    f hf a b ha hab).comp hscale

/-- Abstract perturbation bridge from a proved source-floor Riemann limit to a
triangular array with one uniform pointwise error on that floor window. -/
theorem gridTimeArraySum_tendsto_of_uniform_approximation_of_base
    (F : ℕ → ℕ → ℝ) (f : ℝ → ℝ)
    (scale : ℕ → ℕ) (hscale : Tendsto scale atTop atTop)
    (a b : ℝ) (hb : 0 ≤ b)
    (hbase : Tendsto
      (fun n : ℕ ↦ gridTimeLeftRiemannSum f (scale n) a b)
      atTop (nhds (∫ t in a..b, f t)))
    (error : ℕ → ℝ) (herror : Tendsto error atTop (nhds 0))
    (happrox : ∀ n : ℕ, 0 < scale n →
      ∀ s ∈ Finset.Ico (gridIndex (scale n) a) (gridIndex (scale n) b),
        |F n s - f ((s : ℝ) / (scale n : ℝ))| ≤ error n) :
    Tendsto (fun n : ℕ ↦ gridTimeArraySum F scale n a b)
      atTop (nhds (∫ t in a..b, f t)) := by
  have hvanish : Tendsto (fun n : ℕ ↦ b * |error n|)
      atTop (nhds 0) := by
    simpa only [abs_zero, mul_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ b) atTop (nhds b)).mul
        herror.abs
  have hscalePos : ∀ᶠ n : ℕ in atTop, 0 < scale n := by
    have hge : ∀ᶠ n : ℕ in atTop, 1 ≤ scale n :=
      hscale (eventually_ge_atTop (1 : ℕ))
    exact hge.mono fun _ hn ↦ by omega
  apply hbase.congr_dist
  apply squeeze_zero' (Eventually.of_forall fun _ ↦ dist_nonneg) _ hvanish
  filter_upwards [hscalePos] with n hnpos
  let N : ℕ := scale n
  let lo : ℕ := gridIndex N a
  let hi : ℕ := gridIndex N b
  have hNpos : 0 < N := by simpa only [N] using hnpos
  have hNreal : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNpos
  have hcard : (Finset.Ico lo hi).card ≤ hi := by
    simp only [Nat.card_Ico]
    omega
  have hhi : (hi : ℝ) ≤ (N : ℝ) * b := by
    simpa only [hi] using gridIndex_cast_le N b hb
  have hcardRatio : ((Finset.Ico lo hi).card : ℝ) / (N : ℝ) ≤ b := by
    rw [div_le_iff₀ hNreal]
    have hcardCast : ((Finset.Ico lo hi).card : ℝ) ≤ (hi : ℝ) := by
      exact_mod_cast hcard
    exact hcardCast.trans (by simpa only [mul_comm] using hhi)
  have hterm : ∀ s ∈ Finset.Ico lo hi,
      |(N : ℝ)⁻¹ * F n s -
        (N : ℝ)⁻¹ * f ((s : ℝ) / (N : ℝ))| ≤
        (N : ℝ)⁻¹ * |error n| := by
    intro s hs
    rw [← mul_sub, abs_mul, abs_of_pos (inv_pos.mpr hNreal)]
    apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hNreal.le)
    have hs' : s ∈ Finset.Ico
        (gridIndex (scale n) a) (gridIndex (scale n) b) := by
      simpa only [lo, hi, N] using hs
    exact (happrox n hnpos s hs').trans (le_abs_self (error n))
  rw [dist_comm, Real.dist_eq, gridTimeArraySum,
    gridTimeLeftRiemannSum, show scale n = N from rfl,
    show gridIndex N a = lo from rfl, show gridIndex N b = hi from rfl,
    ← Finset.sum_sub_distrib]
  calc
    |∑ s ∈ Finset.Ico lo hi,
        ((N : ℝ)⁻¹ * F n s -
          (N : ℝ)⁻¹ * f ((s : ℝ) / (N : ℝ)))| ≤
        ∑ s ∈ Finset.Ico lo hi,
          |(N : ℝ)⁻¹ * F n s -
            (N : ℝ)⁻¹ * f ((s : ℝ) / (N : ℝ))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _s ∈ Finset.Ico lo hi, (N : ℝ)⁻¹ * |error n| := by
      apply Finset.sum_le_sum
      intro s hs
      exact hterm s hs
    _ = (((Finset.Ico lo hi).card : ℕ) : ℝ) /
        (N : ℝ) * |error n| := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      rw [div_eq_mul_inv]
      ring
    _ ≤ b * |error n| :=
      mul_le_mul_of_nonneg_right hcardRatio (abs_nonneg _)

/-- Uniform lattice perturbations of a globally continuous time integrand
have the same interval-integral limit. -/
theorem gridTimeArraySum_tendsto_of_uniform_approximation
    (F : ℕ → ℕ → ℝ) (f : ℝ → ℝ) (hf : Continuous f)
    (scale : ℕ → ℕ) (hscale : Tendsto scale atTop atTop)
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (error : ℕ → ℝ) (herror : Tendsto error atTop (nhds 0))
    (happrox : ∀ n : ℕ, 0 < scale n →
      ∀ s ∈ Finset.Ico (gridIndex (scale n) a) (gridIndex (scale n) b),
        |F n s - f ((s : ℝ) / (scale n : ℝ))| ≤ error n) :
    Tendsto (fun n : ℕ ↦ gridTimeArraySum F scale n a b)
      atTop (nhds (∫ t in a..b, f t)) := by
  apply gridTimeArraySum_tendsto_of_uniform_approximation_of_base
    F f scale hscale a b (ha.le.trans hab)
    (gridTimeLeftRiemannSum_along_scale_tendsto
      f hf scale hscale a b ha hab)
    error herror happrox

/-- Positive-time triangular-array interface.  This is the form suited to
the mild Duhamel passage, whose limiting integrand need only be continuous
away from the singular initial time. -/
theorem gridTimeArraySum_tendsto_of_uniform_approximation_on_Ioi
    (F : ℕ → ℕ → ℝ) (f : ℝ → ℝ)
    (hf : ContinuousOn f (Ioi (0 : ℝ)))
    (scale : ℕ → ℕ) (hscale : Tendsto scale atTop atTop)
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (error : ℕ → ℝ) (herror : Tendsto error atTop (nhds 0))
    (happrox : ∀ n : ℕ, 0 < scale n →
      ∀ s ∈ Finset.Ico (gridIndex (scale n) a) (gridIndex (scale n) b),
        |F n s - f ((s : ℝ) / (scale n : ℝ))| ≤ error n) :
    Tendsto (fun n : ℕ ↦ gridTimeArraySum F scale n a b)
      atTop (nhds (∫ t in a..b, f t)) := by
  apply gridTimeArraySum_tendsto_of_uniform_approximation_of_base
    F f scale hscale a b (ha.le.trans hab)
    (gridTimeLeftRiemannSum_along_scale_tendsto_of_continuousOn_Ioi
      f hf scale hscale a b ha hab)
    error herror happrox

end

end DerridaRetaux
