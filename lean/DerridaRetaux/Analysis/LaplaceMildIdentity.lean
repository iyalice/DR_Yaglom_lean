import DerridaRetaux.Analysis.LaplaceDuhamelIntegrability
import Mathlib.Tactic

set_option autoImplicit false

open Filter Topology MeasureTheory Set

namespace DerridaRetaux

noncomputable section

/-- Fubini turns a pointwise mild equation into its exact Laplace-valued
counterpart. -/
theorem laplaceMildIdentity_of_pointwise
    (u : ℝ → ℝ → ℝ) (p t h : ℝ) (hh : 0 ≤ h)
    (hmild : ∀ x : ℝ, 0 ≤ x →
      u (t + h) x = u t (x + h) +
        ∫ s in t..t + h, (1 / 2 : ℝ) *
          positiveSelfConvolution (u s) (x + t + h - s))
    (hbase : IntegrableOn
      (fun x : ℝ ↦ Real.exp (-(p * x)) * u t (x + h)) (Ici 0))
    (hspaceTime : Integrable
      (laplaceDuhamelIntegrand
        (fun s ↦ positiveSelfConvolution (u s)) p t h)
      ((volume.restrict (Ici (0 : ℝ))).prod
        (volume.restrict (Ioc t (t + h))))) :
    continuumLaplace (u (t + h)) p =
      shiftedHalfLineLaplace (u t) p h +
        ∫ s in t..t + h, (1 / 2 : ℝ) *
          shiftedHalfLineLaplace (positiveSelfConvolution (u s)) p
            (t + h - s) := by
  have htime : t ≤ t + h := by linarith
  have hduhInt : IntegrableOn
      (fun x : ℝ ↦ ∫ s in t..t + h,
        laplaceDuhamelIntegrand
          (fun q ↦ positiveSelfConvolution (u q)) p t h (x, s))
      (Ici 0) := by
    simpa only [intervalIntegral.integral_of_le htime] using
      hspaceTime.integral_prod_left
  have hsum :
      continuumLaplace (u (t + h)) p =
        (∫ x in Ici (0 : ℝ), Real.exp (-(p * x)) * u t (x + h)) +
          ∫ x in Ici (0 : ℝ), ∫ s in t..t + h,
            laplaceDuhamelIntegrand
              (fun q ↦ positiveSelfConvolution (u q)) p t h (x, s) := by
    unfold continuumLaplace
    have hpoint : ∀ x ∈ Ici (0 : ℝ),
        Real.exp (-(p * x)) * u (t + h) x =
          Real.exp (-(p * x)) * u t (x + h) +
            ∫ s in t..t + h,
              laplaceDuhamelIntegrand
                (fun q ↦ positiveSelfConvolution (u q)) p t h (x, s) := by
      intro x hx
      rw [hmild x hx, mul_add, ← intervalIntegral.integral_const_mul]
      congr 1
    rw [setIntegral_congr_fun measurableSet_Ici hpoint]
    simpa only [Pi.add_apply] using integral_add hbase hduhInt
  rw [hsum]
  congr 1
  have hspaceTime' : Integrable
      (Function.uncurry (fun x s ↦
        laplaceDuhamelIntegrand
          (fun q ↦ positiveSelfConvolution (u q)) p t h (x, s)))
      ((volume.restrict (Ici (0 : ℝ))).prod
        (volume.restrict (Ioc t (t + h)))) := by
    simpa only [Function.uncurry_apply_pair] using hspaceTime
  have hswap := integral_integral_swap hspaceTime'
  calc
    (∫ x in Ici (0 : ℝ), ∫ s in t..t + h,
        laplaceDuhamelIntegrand
          (fun q ↦ positiveSelfConvolution (u q)) p t h (x, s)) =
        ∫ x in Ici (0 : ℝ), ∫ s in Ioc t (t + h),
          laplaceDuhamelIntegrand
            (fun q ↦ positiveSelfConvolution (u q)) p t h (x, s) := by
      apply setIntegral_congr_fun measurableSet_Ici
      intro x hx
      exact intervalIntegral.integral_of_le htime
    _ = ∫ s in Ioc t (t + h), ∫ x in Ici (0 : ℝ),
        laplaceDuhamelIntegrand
          (fun q ↦ positiveSelfConvolution (u q)) p t h (x, s) := hswap
    _ = ∫ s in Ioc t (t + h), (1 / 2 : ℝ) *
        shiftedHalfLineLaplace (positiveSelfConvolution (u s)) p
          (t + h - s) := by
      apply setIntegral_congr_fun measurableSet_Ioc
      intro s hs
      unfold shiftedHalfLineLaplace
      change (∫ x in Ici (0 : ℝ),
        laplaceDuhamelIntegrand
          (fun q ↦ positiveSelfConvolution (u q)) p t h (x, s)) =
        (1 / 2 : ℝ) * ∫ x in Ici (0 : ℝ),
          Real.exp (-(p * x)) *
            positiveSelfConvolution (u s) (x + (t + h - s))
      rw [← integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ici
      intro x hx
      unfold laplaceDuhamelIntegrand
      ring
    _ = ∫ s in t..t + h, (1 / 2 : ℝ) *
        shiftedHalfLineLaplace (positiveSelfConvolution (u s)) p
          (t + h - s) := (intervalIntegral.integral_of_le htime).symm

end

end DerridaRetaux
