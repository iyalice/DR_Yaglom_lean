import DerridaRetaux.Analysis.MomentPassage
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.Topology.Semicontinuous
import Mathlib.Tactic

set_option autoImplicit false

open Filter Topology MeasureTheory Set
open scoped BoundedContinuousFunction

namespace DerridaRetaux

noncomputable section

/-!
# Lower-semicontinuous passage of the limiting cubic tail

The source uses bounded lower-semicontinuous truncations before monotone
convergence.  Here we make that approximation explicit with continuous ramps,
so the only measure-convergence input is Mathlib's weak topology on finite
measures.
-/

/-- Nonnegative cubic tail integrand, extended by zero off `x > delta`. -/
def cubicTailIntegrand (delta x : ℝ) : ℝ :=
  if delta < x then (max x 0) ^ 3 else 0

theorem cubicTailIntegrand_nonneg (delta x : ℝ) :
    0 ≤ cubicTailIntegrand delta x := by
  unfold cubicTailIntegrand
  split_ifs <;> positivity

/-- The strict cubic tail is lower semicontinuous when the cutoff is
nonnegative.  At the boundary its value is zero, so the upward jump is allowed. -/
theorem cubicTailIntegrand_lowerSemicontinuous
    (delta : ℝ) :
    LowerSemicontinuous (cubicTailIntegrand delta) := by
  intro x y hy
  by_cases hx : delta < x
  · have hcont : ContinuousAt (fun z : ℝ ↦ (max z 0) ^ 3) x :=
      ((continuous_id.max continuous_const).pow 3).continuousAt
    have hy' : y < (max x 0) ^ 3 := by
      simpa [cubicTailIntegrand, hx] using hy
    filter_upwards [isOpen_Ioi.mem_nhds hx, hcont (Ioi_mem_nhds hy')] with z hz hzy
    have hz' : delta < z := hz
    rw [cubicTailIntegrand, if_pos hz']
    exact hzy
  · have hyzero : y < 0 := by
      simpa [cubicTailIntegrand, hx] using hy
    exact Eventually.of_forall fun z ↦
      hyzero.trans_le (cubicTailIntegrand_nonneg delta z)

theorem cubicTailIntegrand_eq_indicator
    (delta : ℝ) (hdelta : 0 ≤ delta) :
    cubicTailIntegrand delta = (Ioi delta).indicator (fun x : ℝ ↦ x ^ 3) := by
  funext x
  by_cases hx : delta < x
  · have hx0 : 0 ≤ x := hdelta.trans hx.le
    simp [cubicTailIntegrand, hx, max_eq_left hx0]
  · simp [cubicTailIntegrand, hx]

/-- Cubic tail capped at height `M`. -/
def cappedCubicTailIntegrand (delta M x : ℝ) : ℝ :=
  if delta < x then min M ((max x 0) ^ 3) else 0

/-- Continuous ramp approximation to the capped strict tail. -/
def cubicTailContinuousApprox (delta M : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  min M ((max x 0) ^ 3) *
    min 1 ((n : ℝ) * max (x - delta) 0)

theorem continuous_cubicTailContinuousApprox (delta M : ℝ) (n : ℕ) :
    Continuous (cubicTailContinuousApprox delta M n) := by
  unfold cubicTailContinuousApprox
  fun_prop

theorem cubicTailContinuousApprox_nonneg
    (delta M : ℝ) (n : ℕ) (hM : 0 ≤ M) (x : ℝ) :
    0 ≤ cubicTailContinuousApprox delta M n x := by
  unfold cubicTailContinuousApprox
  apply mul_nonneg
  · exact le_min hM (by positivity)
  · exact le_min (by norm_num) (mul_nonneg (by positivity) (by positivity))

theorem cubicTailContinuousApprox_le_cap
    (delta M : ℝ) (n : ℕ) (hM : 0 ≤ M) (x : ℝ) :
    cubicTailContinuousApprox delta M n x ≤ M := by
  have hcapNonneg : 0 ≤ min M ((max x 0) ^ 3) := le_min hM (by positivity)
  have hrampNonneg : 0 ≤ min 1 ((n : ℝ) * max (x - delta) 0) :=
    le_min (by norm_num) (mul_nonneg (by positivity) (by positivity))
  have hrampLe : min 1 ((n : ℝ) * max (x - delta) 0) ≤ 1 := min_le_left _ _
  calc
    cubicTailContinuousApprox delta M n x ≤
        min M ((max x 0) ^ 3) * 1 := by
      exact mul_le_mul_of_nonneg_left hrampLe hcapNonneg
    _ = min M ((max x 0) ^ 3) := by ring
    _ ≤ M := min_le_left _ _

theorem cubicTailContinuousApprox_le_tail
    (delta M : ℝ) (n : ℕ) (hM : 0 ≤ M) (x : ℝ) :
    cubicTailContinuousApprox delta M n x ≤ cubicTailIntegrand delta x := by
  unfold cubicTailContinuousApprox cubicTailIntegrand
  by_cases hx : delta < x
  · rw [if_pos hx]
    have hcapNonneg : 0 ≤ min M ((max x 0) ^ 3) := le_min hM (by positivity)
    have hrampNonneg : 0 ≤ min 1 ((n : ℝ) * max (x - delta) 0) :=
      le_min (by norm_num) (mul_nonneg (by positivity) (by positivity))
    have hrampLe : min 1 ((n : ℝ) * max (x - delta) 0) ≤ 1 := min_le_left _ _
    calc
      min M ((max x 0) ^ 3) * min 1 ((n : ℝ) * max (x - delta) 0) ≤
          min M ((max x 0) ^ 3) := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hrampLe hcapNonneg
      _ ≤ (max x 0) ^ 3 := min_le_right _ _
  · rw [if_neg hx]
    have hxle : x ≤ delta := le_of_not_gt hx
    have hzero : max (x - delta) 0 = 0 := max_eq_right (sub_nonpos.mpr hxle)
    simp [hzero]

theorem cubicTailContinuousApprox_tendsto_capped
    (delta M x : ℝ) :
    Tendsto (fun n : ℕ ↦ cubicTailContinuousApprox delta M n x)
      atTop (nhds (cappedCubicTailIntegrand delta M x)) := by
  by_cases hx : delta < x
  · have hxd : 0 < max (x - delta) 0 := by
      rw [max_eq_left (sub_nonneg.mpr hx.le)]
      linarith
    have hgrow : Tendsto (fun n : ℕ ↦ (n : ℝ) * max (x - delta) 0)
        atTop atTop := by
      convert tendsto_natCast_atTop_atTop.const_mul_atTop hxd using 1
      funext n
      ring
    obtain ⟨N, hN⟩ := eventually_atTop.1 (tendsto_atTop.1 hgrow 1)
    apply tendsto_atTop_of_eventually_const (i₀ := N)
    intro n hn
    have hone : 1 ≤ (n : ℝ) * max (x - delta) 0 := hN n hn
    simp [cubicTailContinuousApprox, cappedCubicTailIntegrand, hx,
      min_eq_left hone]
  · have hxle : x ≤ delta := le_of_not_gt hx
    have hzero : max (x - delta) 0 = 0 := max_eq_right (sub_nonpos.mpr hxle)
    simpa [cubicTailContinuousApprox, cappedCubicTailIntegrand, hx, hzero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (0 : ℝ)) atTop (nhds 0))

/-- The continuous approximation packaged as a bounded continuous test
function for weak convergence of finite measures. -/
def cubicTailApproxBCF (delta M : ℝ) (n : ℕ) (hM : 0 ≤ M) : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfBound
    ⟨cubicTailContinuousApprox delta M n,
      continuous_cubicTailContinuousApprox delta M n⟩
    (2 * M) (by
      intro x y
      rw [Real.dist_eq]
      have hx0 := cubicTailContinuousApprox_nonneg delta M n hM x
      have hy0 := cubicTailContinuousApprox_nonneg delta M n hM y
      have hxM := cubicTailContinuousApprox_le_cap delta M n hM x
      have hyM := cubicTailContinuousApprox_le_cap delta M n hM y
      calc
        |cubicTailContinuousApprox delta M n x -
            cubicTailContinuousApprox delta M n y| ≤
          |cubicTailContinuousApprox delta M n x| +
            |cubicTailContinuousApprox delta M n y| := abs_sub _ _
        _ = cubicTailContinuousApprox delta M n x +
            cubicTailContinuousApprox delta M n y := by
          rw [abs_of_nonneg hx0, abs_of_nonneg hy0]
        _ ≤ M + M := add_le_add hxM hyM
        _ = 2 * M := by ring)

@[simp]
theorem cubicTailApproxBCF_apply
    (delta M : ℝ) (n : ℕ) (hM : 0 ≤ M) (x : ℝ) :
    cubicTailApproxBCF delta M n hM x =
      cubicTailContinuousApprox delta M n x := rfl

/-- For a finite measure, continuous ramps converge in integral to the capped
strict cubic tail. -/
theorem integral_cubicTailContinuousApprox_tendsto_capped
    (mu : Measure ℝ) [IsFiniteMeasure mu]
    (delta M : ℝ) (hM : 0 ≤ M) :
    Tendsto (fun n : ℕ ↦ ∫ x, cubicTailContinuousApprox delta M n x ∂mu)
      atTop (nhds (∫ x, cappedCubicTailIntegrand delta M x ∂mu)) := by
  apply tendsto_integral_of_dominated_convergence (fun _ : ℝ ↦ M)
  · intro n
    exact (continuous_cubicTailContinuousApprox delta M n).aestronglyMeasurable
  · exact integrable_const M
  · intro n
    exact Eventually.of_forall fun x ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg
        (cubicTailContinuousApprox_nonneg delta M n hM x)]
      exact cubicTailContinuousApprox_le_cap delta M n hM x
  · exact Eventually.of_forall fun x ↦
      cubicTailContinuousApprox_tendsto_capped delta M x

theorem cappedCubicTailIntegrand_nonneg
    (delta M x : ℝ) (hM : 0 ≤ M) :
    0 ≤ cappedCubicTailIntegrand delta M x := by
  unfold cappedCubicTailIntegrand
  split_ifs
  · exact le_min hM (by positivity)
  · norm_num

theorem cappedCubicTailIntegrand_le_tail
    (delta M x : ℝ) :
    cappedCubicTailIntegrand delta M x ≤ cubicTailIntegrand delta x := by
  unfold cappedCubicTailIntegrand cubicTailIntegrand
  by_cases hx : delta < x
  · rw [if_pos hx, if_pos hx]
    exact min_le_right _ _
  · rw [if_neg hx, if_neg hx]

theorem measurable_cappedCubicTailIntegrand (delta M : ℝ) :
    Measurable (cappedCubicTailIntegrand delta M) := by
  unfold cappedCubicTailIntegrand
  apply Measurable.ite measurableSet_Ioi
  · fun_prop
  · exact measurable_const

theorem cappedCubicTailIntegrand_tendsto_tail (delta x : ℝ) :
    Tendsto (fun n : ℕ ↦ cappedCubicTailIntegrand delta (n : ℝ) x)
      atTop (nhds (cubicTailIntegrand delta x)) := by
  by_cases hx : delta < x
  · have hgrow : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop
    obtain ⟨N, hN⟩ := eventually_atTop.1
      (tendsto_atTop.1 hgrow ((max x 0) ^ 3))
    apply tendsto_atTop_of_eventually_const (i₀ := N)
    intro n hn
    have hcube : (max x 0) ^ 3 ≤ (n : ℝ) := hN n hn
    simp [cappedCubicTailIntegrand, cubicTailIntegrand, hx,
      min_eq_right hcube]
  · simpa [cappedCubicTailIntegrand, cubicTailIntegrand, hx] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (0 : ℝ)) atTop (nhds 0))

/-- Removing the cap is justified by dominated convergence once the limiting
cubic tail is integrable. -/
theorem integral_cappedCubicTailIntegrand_tendsto_tail
    (mu : Measure ℝ) (delta : ℝ)
    (hint : Integrable (cubicTailIntegrand delta) mu) :
    Tendsto
      (fun n : ℕ ↦ ∫ x, cappedCubicTailIntegrand delta (n : ℝ) x ∂mu)
      atTop (nhds (∫ x, cubicTailIntegrand delta x ∂mu)) := by
  apply tendsto_integral_of_dominated_convergence (cubicTailIntegrand delta)
  · intro n
    exact (measurable_cappedCubicTailIntegrand delta (n : ℝ)).aestronglyMeasurable
  · exact hint
  · intro n
    exact Eventually.of_forall fun x ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg
        (cappedCubicTailIntegrand_nonneg delta (n : ℝ) x (by positivity))]
      exact cappedCubicTailIntegrand_le_tail delta (n : ℝ) x
  · exact Eventually.of_forall fun x ↦
      cappedCubicTailIntegrand_tendsto_tail delta x

/-- Specific Portmanteau passage used for `eq:limitthirdtail`: a uniform bound
on the exact cubic tails of weakly convergent finite measures passes to the
limit.  Continuous ramps make the lower-semicontinuous step explicit. -/
theorem integral_cubicTail_le_of_finiteMeasure_tendsto
    (mus : ℕ → FiniteMeasure ℝ) (mu : FiniteMeasure ℝ)
    (hmu : Tendsto mus atTop (nhds mu))
    (delta B : ℝ)
    (hmusIntegrable : ∀ N : ℕ,
      Integrable (cubicTailIntegrand delta) (mus N : Measure ℝ))
    (hmuIntegrable : Integrable (cubicTailIntegrand delta) (mu : Measure ℝ))
    (hbound : ∀ N : ℕ,
      (∫ x, cubicTailIntegrand delta x ∂(mus N : Measure ℝ)) ≤ B) :
    (∫ x, cubicTailIntegrand delta x ∂(mu : Measure ℝ)) ≤ B := by
  have hweak := FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp hmu
  have hcapBound : ∀ M : ℝ, 0 ≤ M →
      (∫ x, cappedCubicTailIntegrand delta M x ∂(mu : Measure ℝ)) ≤ B := by
    intro M hM
    have happBound : ∀ n : ℕ,
        (∫ x, cubicTailContinuousApprox delta M n x ∂(mu : Measure ℝ)) ≤ B := by
      intro n
      have htest := hweak (cubicTailApproxBCF delta M n hM)
      have hboundN : ∀ N : ℕ,
          (∫ x, cubicTailContinuousApprox delta M n x ∂(mus N : Measure ℝ)) ≤ B := by
        intro N
        have happIntegrable :
            Integrable (cubicTailContinuousApprox delta M n)
              (mus N : Measure ℝ) := by
          simpa only [cubicTailApproxBCF_apply] using
            (cubicTailApproxBCF delta M n hM).integrable (mus N : Measure ℝ)
        calc
          (∫ x, cubicTailContinuousApprox delta M n x ∂(mus N : Measure ℝ)) ≤
              ∫ x, cubicTailIntegrand delta x ∂(mus N : Measure ℝ) := by
            apply integral_mono
              happIntegrable
              (hmusIntegrable N)
            intro x
            exact cubicTailContinuousApprox_le_tail delta M n hM x
          _ ≤ B := hbound N
      apply le_of_tendsto' (by
        simpa only [cubicTailApproxBCF_apply] using htest)
      exact hboundN
    apply le_of_tendsto'
      (integral_cubicTailContinuousApprox_tendsto_capped
        (mu : Measure ℝ) delta M hM)
    exact happBound
  apply le_of_tendsto'
    (integral_cappedCubicTailIntegrand_tendsto_tail
      (mu : Measure ℝ) delta hmuIntegrable)
  intro n
  exact hcapBound (n : ℝ) (by positivity)

/-- Eventual form of the Portmanteau tail bound.  A finite prefix of lattice
scales is irrelevant to weak convergence and therefore need not satisfy the
asymptotic estimate. -/
theorem integral_cubicTail_le_of_finiteMeasure_tendsto_eventually
    (mus : ℕ → FiniteMeasure ℝ) (mu : FiniteMeasure ℝ)
    (hmu : Tendsto mus atTop (nhds mu))
    (delta B : ℝ)
    (hmusIntegrable : ∀ N : ℕ,
      Integrable (cubicTailIntegrand delta) (mus N : Measure ℝ))
    (hmuIntegrable : Integrable (cubicTailIntegrand delta) (mu : Measure ℝ))
    (hbound : ∀ᶠ N : ℕ in atTop,
      (∫ x, cubicTailIntegrand delta x ∂(mus N : Measure ℝ)) ≤ B) :
    (∫ x, cubicTailIntegrand delta x ∂(mu : Measure ℝ)) ≤ B := by
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 hbound
  apply integral_cubicTail_le_of_finiteMeasure_tendsto
    (fun k ↦ mus (k + N₀)) mu
    (hmu.comp (tendsto_add_atTop_nat N₀)) delta B
  · intro k
    exact hmusIntegrable (k + N₀)
  · exact hmuIntegrable
  · intro k
    exact hN₀ (k + N₀) (by omega)

/-- Set-integral form of the preceding result, matching the manuscript's
`x > delta` notation. -/
theorem setIntegral_cube_Ioi_le_of_finiteMeasure_tendsto
    (mus : ℕ → FiniteMeasure ℝ) (mu : FiniteMeasure ℝ)
    (hmu : Tendsto mus atTop (nhds mu))
    (delta B : ℝ) (hdelta : 0 ≤ delta)
    (hmusIntegrable : ∀ N : ℕ,
      IntegrableOn (fun x : ℝ ↦ x ^ 3) (Ioi delta) (mus N : Measure ℝ))
    (hmuIntegrable :
      IntegrableOn (fun x : ℝ ↦ x ^ 3) (Ioi delta) (mu : Measure ℝ))
    (hbound : ∀ N : ℕ,
      (∫ x in Ioi delta, x ^ 3 ∂(mus N : Measure ℝ)) ≤ B) :
    (∫ x in Ioi delta, x ^ 3 ∂(mu : Measure ℝ)) ≤ B := by
  have heq := cubicTailIntegrand_eq_indicator delta hdelta
  have hmain := integral_cubicTail_le_of_finiteMeasure_tendsto
    mus mu hmu delta B
      (fun N ↦ by
        rw [heq]
        exact (hmusIntegrable N).integrable_indicator measurableSet_Ioi)
      (by
        rw [heq]
        exact hmuIntegrable.integrable_indicator measurableSet_Ioi)
      (fun N ↦ by
        rw [heq, integral_indicator measurableSet_Ioi]
        exact hbound N)
  rw [heq, integral_indicator measurableSet_Ioi] at hmain
  exact hmain

end

end DerridaRetaux
