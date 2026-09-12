import DerridaRetaux.Analysis.IntegratedRemainder
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.Tactic

/-!
# The positive Laplace gap and its exact ODE

This file formalizes the nonnegative integral `Z(t,p)` and the cancellation
which turns the mass and Laplace equations into `eq:ZODE`.  The moment and
Laplace ODEs themselves remain the preceding internal premise.
-/

set_option autoImplicit false

namespace DerridaRetaux

noncomputable section

open MeasureTheory Set

/-- Cauchy--Schwarz for nonnegative real functions, in the integral form used
for the continuum moment inequalities. -/
theorem integral_mul_sq_le_integral_sq_mul_integral_sq
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (f g : α → ℝ)
    (hf0 : 0 ≤ᵐ[μ] f) (hg0 : 0 ≤ᵐ[μ] g)
    (hf2 : Integrable (fun x ↦ f x ^ 2) μ)
    (hg2 : Integrable (fun x ↦ g x ^ 2) μ)
    (hfmeas : AEStronglyMeasurable f μ)
    (hgmeas : AEStronglyMeasurable g μ) :
    (∫ x, f x * g x ∂μ) ^ 2 ≤
      (∫ x, f x ^ 2 ∂μ) * (∫ x, g x ^ 2 ∂μ) := by
  have hpq : (2 : ℝ).HolderConjugate 2 := by
    rw [Real.holderConjugate_iff]
    norm_num
  have hfLp : MemLp f (ENNReal.ofReal (2 : ℝ)) μ := by
    simpa using (memLp_two_iff_integrable_sq hfmeas).2 hf2
  have hgLp : MemLp g (ENNReal.ofReal (2 : ℝ)) μ := by
    simpa using (memLp_two_iff_integrable_sq hgmeas).2 hg2
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg hpq hf0 hg0 hfLp hgLp
  have hprod : 0 ≤ᵐ[μ] fun x ↦ f x * g x := by
    filter_upwards [hf0, hg0] with x hfx hgx
    exact mul_nonneg hfx hgx
  have hleft : 0 ≤ ∫ x, f x * g x ∂μ := integral_nonneg_of_ae hprod
  have hF : 0 ≤ ∫ x, f x ^ 2 ∂μ :=
    integral_nonneg_of_ae (ae_of_all μ fun x ↦ sq_nonneg (f x))
  have hG : 0 ≤ ∫ x, g x ^ 2 ∂μ :=
    integral_nonneg_of_ae (ae_of_all μ fun x ↦ sq_nonneg (g x))
  simp only [Real.rpow_two] at h
  rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at h
  have hsqrtprod :
      0 ≤ Real.sqrt (∫ x, f x ^ 2 ∂μ) *
        Real.sqrt (∫ x, g x ^ 2 ∂μ) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  calc
    (∫ x, f x * g x ∂μ) ^ 2 ≤
        (Real.sqrt (∫ x, f x ^ 2 ∂μ) *
          Real.sqrt (∫ x, g x ^ 2 ∂μ)) ^ 2 :=
      (sq_le_sq₀ hleft hsqrtprod).2 h
    _ = (∫ x, f x ^ 2 ∂μ) * (∫ x, g x ^ 2 ∂μ) := by
      rw [mul_pow, Real.sq_sqrt hF, Real.sq_sqrt hG]

/-- The first Cauchy--Schwarz moment inequality `A₁² ≤ A₀ A₂`. -/
theorem positiveHalfLineMoment_one_sq_le_zero_mul_two
    (μ : Measure ℝ)
    (hzero : IntegrableOn (fun x : ℝ ↦ x ^ 0) (Ici 0) μ)
    (hsecond : IntegrableOn (fun x : ℝ ↦ x ^ 2) (Ici 0) μ) :
    positiveHalfLineMoment 1 μ ^ 2 ≤
      positiveHalfLineMoment 0 μ * positiveHalfLineMoment 2 μ := by
  let ν := μ.restrict (Ici (0 : ℝ))
  have hone : Integrable (fun _ : ℝ ↦ (1 : ℝ) ^ 2) ν := by
    change IntegrableOn (fun _ : ℝ ↦ (1 : ℝ) ^ 2) (Ici 0) μ
    simpa only [one_pow, pow_zero] using hzero
  have hx2 : Integrable (fun x : ℝ ↦ x ^ 2) ν := by
    change IntegrableOn (fun x : ℝ ↦ x ^ 2) (Ici 0) μ
    exact hsecond
  have hnonneg : 0 ≤ᵐ[ν] fun x : ℝ ↦ x := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ici] with x hx
    exact hx
  have hcs := integral_mul_sq_le_integral_sq_mul_integral_sq ν
    (fun _ : ℝ ↦ 1) (fun x : ℝ ↦ x)
    (ae_of_all ν fun _ ↦ zero_le_one) hnonneg hone hx2
    aestronglyMeasurable_const continuous_id.aestronglyMeasurable
  simpa [positiveHalfLineMoment, ν] using hcs

/-- The second Cauchy--Schwarz moment inequality `A₂² ≤ A₁ A₃`. -/
theorem positiveHalfLineMoment_two_sq_le_one_mul_three
    (μ : Measure ℝ)
    (hfirst : IntegrableOn (fun x : ℝ ↦ x) (Ici 0) μ)
    (hthird : IntegrableOn (fun x : ℝ ↦ x ^ 3) (Ici 0) μ) :
    positiveHalfLineMoment 2 μ ^ 2 ≤
      positiveHalfLineMoment 1 μ * positiveHalfLineMoment 3 μ := by
  let ν := μ.restrict (Ici (0 : ℝ))
  have hxnonneg : 0 ≤ᵐ[ν] fun x : ℝ ↦ x := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ici] with x hx
    exact hx
  have hsqrtnonneg : 0 ≤ᵐ[ν] fun x : ℝ ↦ Real.sqrt x :=
    ae_of_all ν fun x ↦ Real.sqrt_nonneg x
  have hxsqrtnonneg : 0 ≤ᵐ[ν] fun x : ℝ ↦ x * Real.sqrt x := by
    filter_upwards [hxnonneg, hsqrtnonneg] with x hx hsqrt
    exact mul_nonneg hx hsqrt
  have hsqrt2 : Integrable (fun x : ℝ ↦ Real.sqrt x ^ 2) ν := by
    change IntegrableOn (fun x : ℝ ↦ Real.sqrt x ^ 2) (Ici 0) μ
    refine hfirst.congr_fun_ae ?_
    filter_upwards [self_mem_ae_restrict measurableSet_Ici] with x hx
    exact (Real.sq_sqrt hx).symm
  have hxsqrt2 : Integrable (fun x : ℝ ↦ (x * Real.sqrt x) ^ 2) ν := by
    change IntegrableOn (fun x : ℝ ↦ (x * Real.sqrt x) ^ 2) (Ici 0) μ
    refine hthird.congr_fun_ae ?_
    filter_upwards [self_mem_ae_restrict measurableSet_Ici] with x hx
    calc
      x ^ 3 = x ^ 2 * x := by ring
      _ = x ^ 2 * Real.sqrt x ^ 2 := by rw [Real.sq_sqrt hx]
      _ = (x * Real.sqrt x) ^ 2 := by ring
  have hcs := integral_mul_sq_le_integral_sq_mul_integral_sq ν
    (fun x : ℝ ↦ Real.sqrt x) (fun x : ℝ ↦ x * Real.sqrt x)
    hsqrtnonneg hxsqrtnonneg hsqrt2 hxsqrt2
    Real.continuous_sqrt.aestronglyMeasurable
    (continuous_id.mul Real.continuous_sqrt).aestronglyMeasurable
  have hprodEq :
      (∫ x, Real.sqrt x * (x * Real.sqrt x) ∂ν) =
        positiveHalfLineMoment 2 μ := by
    change (∫ x in Ici (0 : ℝ), Real.sqrt x * (x * Real.sqrt x) ∂μ) =
      ∫ x in Ici (0 : ℝ), x ^ 2 ∂μ
    apply integral_congr_ae
    filter_upwards [self_mem_ae_restrict measurableSet_Ici] with x hx
    rw [show Real.sqrt x * (x * Real.sqrt x) =
      x * Real.sqrt x ^ 2 by ring, Real.sq_sqrt hx]
    ring
  have hsqrtEq :
      (∫ x, Real.sqrt x ^ 2 ∂ν) = positiveHalfLineMoment 1 μ := by
    change (∫ x in Ici (0 : ℝ), Real.sqrt x ^ 2 ∂μ) =
      ∫ x in Ici (0 : ℝ), x ^ 1 ∂μ
    apply integral_congr_ae
    filter_upwards [self_mem_ae_restrict measurableSet_Ici] with x hx
    rw [Real.sq_sqrt hx]
    simp
  have hxsqrtEq :
      (∫ x, (x * Real.sqrt x) ^ 2 ∂ν) =
        positiveHalfLineMoment 3 μ := by
    change (∫ x in Ici (0 : ℝ), (x * Real.sqrt x) ^ 2 ∂μ) =
      ∫ x in Ici (0 : ℝ), x ^ 3 ∂μ
    apply integral_congr_ae
    filter_upwards [self_mem_ae_restrict measurableSet_Ici] with x hx
    rw [show (x * Real.sqrt x) ^ 2 =
      x ^ 2 * Real.sqrt x ^ 2 by ring, Real.sq_sqrt hx]
    ring
  rwa [hprodEq, hsqrtEq, hxsqrtEq] at hcs

/-- The pair of lower moment estimates in `eq:A3lower`, normalized by `A₁=1`. -/
theorem positiveHalfLineMoment_A3_lower
    (μ : Measure ℝ)
    (hzero : IntegrableOn (fun x : ℝ ↦ x ^ 0) (Ici 0) μ)
    (hfirst : IntegrableOn (fun x : ℝ ↦ x) (Ici 0) μ)
    (hsecond : IntegrableOn (fun x : ℝ ↦ x ^ 2) (Ici 0) μ)
    (hthird : IntegrableOn (fun x : ℝ ↦ x ^ 3) (Ici 0) μ)
    (hA1 : positiveHalfLineMoment 1 μ = 1) :
    1 ≤ positiveHalfLineMoment 0 μ ^ 2 * positiveHalfLineMoment 3 μ ∧
      positiveHalfLineMoment 2 μ ^ 2 ≤ positiveHalfLineMoment 3 μ := by
  have h12 := positiveHalfLineMoment_one_sq_le_zero_mul_two μ hzero hsecond
  have h23 := positiveHalfLineMoment_two_sq_le_one_mul_three μ hfirst hthird
  have h12' :
      1 ≤ positiveHalfLineMoment 0 μ * positiveHalfLineMoment 2 μ := by
    simpa [hA1] using h12
  have h23' :
      positiveHalfLineMoment 2 μ ^ 2 ≤ positiveHalfLineMoment 3 μ := by
    simpa [hA1] using h23
  constructor
  · calc
      1 ≤ (positiveHalfLineMoment 0 μ *
          positiveHalfLineMoment 2 μ) ^ 2 := by
        nlinarith [sq_nonneg (positiveHalfLineMoment 0 μ *
          positiveHalfLineMoment 2 μ - 1)]
      _ = positiveHalfLineMoment 0 μ ^ 2 *
          positiveHalfLineMoment 2 μ ^ 2 := by ring
      _ ≤ positiveHalfLineMoment 0 μ ^ 2 *
          positiveHalfLineMoment 3 μ :=
        mul_le_mul_of_nonneg_left h23' (sq_nonneg _)
  · exact h23'

/-- Every nonnegative-half-line moment is nonnegative. -/
theorem positiveHalfLineMoment_nonneg (r : ℕ) (μ : Measure ℝ) :
    0 ≤ positiveHalfLineMoment r μ := by
  unfold positiveHalfLineMoment
  apply integral_nonneg_of_ae
  filter_upwards [self_mem_ae_restrict measurableSet_Ici] with x hx
  exact pow_nonneg hx r

/-- Unit first moment and finite moments force the strict positivity of `A₀`
and `A₃` used at the start of the rigidity argument. -/
theorem positiveHalfLineMoment_zero_and_three_pos
    (μ : Measure ℝ)
    (hzero : IntegrableOn (fun x : ℝ ↦ x ^ 0) (Ici 0) μ)
    (hfirst : IntegrableOn (fun x : ℝ ↦ x) (Ici 0) μ)
    (hsecond : IntegrableOn (fun x : ℝ ↦ x ^ 2) (Ici 0) μ)
    (hthird : IntegrableOn (fun x : ℝ ↦ x ^ 3) (Ici 0) μ)
    (hA1 : positiveHalfLineMoment 1 μ = 1) :
    0 < positiveHalfLineMoment 0 μ ∧ 0 < positiveHalfLineMoment 3 μ := by
  have h12 := positiveHalfLineMoment_one_sq_le_zero_mul_two μ hzero hsecond
  have h12' :
      1 ≤ positiveHalfLineMoment 0 μ * positiveHalfLineMoment 2 μ := by
    simpa [hA1] using h12
  have hA2nonneg := positiveHalfLineMoment_nonneg 2 μ
  have hlower :=
    (positiveHalfLineMoment_A3_lower μ hzero hfirst hsecond hthird hA1).1
  constructor
  · by_contra hnot
    have hA0nonpos : positiveHalfLineMoment 0 μ ≤ 0 := le_of_not_gt hnot
    have hproduct :
        positiveHalfLineMoment 0 μ * positiveHalfLineMoment 2 μ ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hA0nonpos hA2nonneg
    linarith
  · by_contra hnot
    have hA3nonpos : positiveHalfLineMoment 3 μ ≤ 0 := le_of_not_gt hnot
    have hproduct :
        positiveHalfLineMoment 0 μ ^ 2 * positiveHalfLineMoment 3 μ ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) hA3nonpos
    linarith

/-- Pointwise integrand of the source quantity `Z(t,p)`. -/
def laplaceSecondGapIntegrand (p x : ℝ) : ℝ :=
  Real.exp (-(p * x)) - 1 + p * x

/-- The Laplace second gap is nonnegative for nonnegative arguments. -/
theorem laplaceSecondGapIntegrand_nonneg
    (p x : ℝ) :
    0 ≤ laplaceSecondGapIntegrand p x := by
  have h := Real.add_one_le_exp (-(p * x))
  dsimp [laplaceSecondGapIntegrand]
  linarith

/-- It is strictly positive away from the origin when `p>0`. -/
theorem laplaceSecondGapIntegrand_pos
    {p x : ℝ} (hp : 0 < p) (hx : 0 < x) :
    0 < laplaceSecondGapIntegrand p x := by
  have hne : -(p * x) ≠ 0 := neg_ne_zero.mpr (mul_ne_zero hp.ne' hx.ne')
  have h := Real.add_one_lt_exp hne
  dsimp [laplaceSecondGapIntegrand]
  linarith

/-- The elementary quadratic upper bound used before integrating `Z`. -/
theorem laplaceSecondGapIntegrand_le_quadratic
    {p x : ℝ} (hp : 0 ≤ p) (hx : 0 ≤ x) :
    laplaceSecondGapIntegrand p x ≤ p ^ 2 * x ^ 2 / 2 := by
  let y := p * x
  have hy : 0 ≤ y := mul_nonneg hp hx
  have hrem := expThirdRemainderCore_le_cubic hy
  dsimp [expThirdRemainderCore, y] at hrem
  dsimp [laplaceSecondGapIntegrand]
  nlinarith [show (p * x) ^ 2 = p ^ 2 * x ^ 2 by ring,
    show (p * x) ^ 3 = p ^ 3 * x ^ 3 by ring]

/-- A finite second moment makes the Laplace gap integrable. -/
theorem integrableOn_laplaceSecondGapIntegrand_of_secondMoment
    (μ : Measure ℝ) {p : ℝ} (hp : 0 ≤ p)
    (hsecond : IntegrableOn (fun x : ℝ ↦ x ^ 2) (Ici 0) μ) :
    IntegrableOn (laplaceSecondGapIntegrand p) (Ici 0) μ := by
  have hdom : IntegrableOn (fun x : ℝ ↦ (p ^ 2 / 2) * x ^ 2) (Ici 0) μ :=
    hsecond.const_mul (p ^ 2 / 2)
  have hcontinuous : Continuous (laplaceSecondGapIntegrand p) := by
    unfold laplaceSecondGapIntegrand
    fun_prop
  refine hdom.mono' hcontinuous.aestronglyMeasurable.restrict ?_
  filter_upwards [self_mem_ae_restrict measurableSet_Ici] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (laplaceSecondGapIntegrand_nonneg p x)]
  simpa [mul_assoc, div_mul_eq_mul_div] using
    laplaceSecondGapIntegrand_le_quadratic hp hx

/-- Integral form of `0 ≤ Z ≤ p² A₂/2`. -/
theorem integratedLaplaceSecondGap_nonneg_and_le
    (μ : Measure ℝ) {p : ℝ} (hp : 0 ≤ p)
    (hsecond : IntegrableOn (fun x : ℝ ↦ x ^ 2) (Ici 0) μ) :
    0 ≤ integratedLaplaceSecondGap μ p ∧
      integratedLaplaceSecondGap μ p ≤
        (p ^ 2 / 2) * positiveHalfLineMoment 2 μ := by
  have hgap := integrableOn_laplaceSecondGapIntegrand_of_secondMoment μ hp hsecond
  have hquad : IntegrableOn (fun x : ℝ ↦ (p ^ 2 / 2) * x ^ 2) (Ici 0) μ :=
    hsecond.const_mul (p ^ 2 / 2)
  constructor
  · change 0 ≤ ∫ x in Ici (0 : ℝ), laplaceSecondGapIntegrand p x ∂μ
    apply integral_nonneg_of_ae
    filter_upwards [self_mem_ae_restrict measurableSet_Ici] with x hx
    exact laplaceSecondGapIntegrand_nonneg p x
  · calc
      integratedLaplaceSecondGap μ p =
          ∫ x in Ici (0 : ℝ), laplaceSecondGapIntegrand p x ∂μ := by rfl
      _ ≤ ∫ x in Ici (0 : ℝ), (p ^ 2 / 2) * x ^ 2 ∂μ := by
        exact setIntegral_mono_on hgap hquad measurableSet_Ici
          (fun x hx ↦ by
            simpa [mul_assoc, div_mul_eq_mul_div] using
              laplaceSecondGapIntegrand_le_quadratic hp hx)
      _ = (p ^ 2 / 2) * positiveHalfLineMoment 2 μ := by
        rw [integral_const_mul]
        rfl

/-- A unit first moment forces positive mass away from the origin. -/
theorem measure_Ioi_zero_pos_of_firstMoment_eq_one
    (μ : Measure ℝ)
    (hfirst : IntegrableOn (fun x : ℝ ↦ x) (Ici 0) μ)
    (hA1 : positiveHalfLineMoment 1 μ = 1) :
    0 < μ (Ioi (0 : ℝ)) := by
  have hfirstPos : 0 < ∫ x in Ici (0 : ℝ), x ∂μ := by
    have hmoment : (∫ x in Ici (0 : ℝ), x ∂μ) = 1 := by
      simpa [positiveHalfLineMoment] using hA1
    rw [hmoment]
    norm_num
  have hnonneg : 0 ≤ᵐ[μ.restrict (Ici (0 : ℝ))] fun x : ℝ ↦ x := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ici] with x hx
    exact hx
  have hsupport :=
    (setIntegral_pos_iff_support_of_nonneg_ae hnonneg hfirst).1 hfirstPos
  have hset : Function.support (fun x : ℝ ↦ x) ∩ Ici (0 : ℝ) = Ioi 0 := by
    ext x
    simp only [Function.mem_support, ne_eq, mem_inter_iff, mem_Ici, mem_Ioi]
    constructor
    · rintro ⟨hxne, hx⟩
      exact lt_of_le_of_ne hx (Ne.symm hxne)
    · intro hx
      exact ⟨ne_of_gt hx, hx.le⟩
  rwa [hset] at hsupport

/-- With unit first moment, `Z(t,p)` is strictly positive for every `p>0`. -/
theorem integratedLaplaceSecondGap_pos
    (μ : Measure ℝ) {p : ℝ} (hp : 0 < p)
    (hfirst : IntegrableOn (fun x : ℝ ↦ x) (Ici 0) μ)
    (hsecond : IntegrableOn (fun x : ℝ ↦ x ^ 2) (Ici 0) μ)
    (hA1 : positiveHalfLineMoment 1 μ = 1) :
    0 < integratedLaplaceSecondGap μ p := by
  have hgap := integrableOn_laplaceSecondGapIntegrand_of_secondMoment μ hp.le hsecond
  have hnonneg :
      0 ≤ᵐ[μ.restrict (Ici (0 : ℝ))] laplaceSecondGapIntegrand p := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ici] with x hx
    exact laplaceSecondGapIntegrand_nonneg p x
  rw [show integratedLaplaceSecondGap μ p =
      ∫ x in Ici (0 : ℝ), laplaceSecondGapIntegrand p x ∂μ by rfl]
  apply (setIntegral_pos_iff_support_of_nonneg_ae hnonneg hgap).2
  have hmass := measure_Ioi_zero_pos_of_firstMoment_eq_one μ hfirst hA1
  apply lt_of_lt_of_le hmass
  apply measure_mono
  intro x hx
  change laplaceSecondGapIntegrand p x ≠ 0 ∧ 0 ≤ x
  exact ⟨ne_of_gt (laplaceSecondGapIntegrand_pos hp hx), le_of_lt hx⟩

/-- Algebraic source definition `Z = p - A₀ + U`. -/
def momentLaplaceGap (A0 : ℝ → ℝ) (U : ℝ → ℝ → ℝ) (t p : ℝ) : ℝ :=
  p - A0 t + U t p

/-- Exact cancellation of the common boundary trace gives `eq:ZODE`. -/
theorem hasDerivAt_momentLaplaceGap
    (A0 beta : ℝ → ℝ) (U : ℝ → ℝ → ℝ) (t p : ℝ)
    (hA0 : HasDerivAt A0 (-beta t + (1 / 2 : ℝ) * A0 t ^ 2) t)
    (hU : HasDerivAt (fun s ↦ U s p)
      (p * U t p + (1 / 2 : ℝ) * U t p ^ 2 - beta t) t) :
    HasDerivAt (fun s ↦ momentLaplaceGap A0 U s p)
      (A0 t * momentLaplaceGap A0 U t p +
        (1 / 2 : ℝ) * (momentLaplaceGap A0 U t p ^ 2 - p ^ 2)) t := by
  have hderiv := ((hasDerivAt_const t p).sub hA0).add hU
  convert hderiv using 1
  all_goals simp only [momentLaplaceGap]
  all_goals ring

/-- Pointwise derivative wrapper for `eq:ZODE`. -/
theorem deriv_momentLaplaceGap_eq
    (A0 beta : ℝ → ℝ) (U : ℝ → ℝ → ℝ) (t p : ℝ)
    (hA0 : HasDerivAt A0 (-beta t + (1 / 2 : ℝ) * A0 t ^ 2) t)
    (hU : HasDerivAt (fun s ↦ U s p)
      (p * U t p + (1 / 2 : ℝ) * U t p ^ 2 - beta t) t) :
    deriv (fun s ↦ momentLaplaceGap A0 U s p) t =
      A0 t * momentLaplaceGap A0 U t p +
        (1 / 2 : ℝ) * (momentLaplaceGap A0 U t p ^ 2 - p ^ 2) :=
  (hasDerivAt_momentLaplaceGap A0 beta U t p hA0 hU).deriv

end

end DerridaRetaux
