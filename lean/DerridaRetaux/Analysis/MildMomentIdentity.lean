import DerridaRetaux.Analysis.MomentMildDerivative
import Mathlib.Tactic

set_option autoImplicit false

open Filter Topology MeasureTheory Set

namespace DerridaRetaux

noncomputable section

/-- The space-time integrand obtained by testing a mild Duhamel term with
the monomial `x^r`. -/
def momentDuhamelIntegrand
    (u : ℝ → ℝ → ℝ) (r : ℕ) (t h : ℝ) (z : ℝ × ℝ) : ℝ :=
  z.1 ^ r * ((1 / 2 : ℝ) *
    positiveSelfConvolution (u z.2) (z.1 + t + h - z.2))

/-- Fubini turns the pointwise mild equation into its exact moment-valued
counterpart.  Integrability of the displayed space-time integrand is kept
explicit so this lemma can be reused for polynomial and Laplace tests. -/
theorem momentMildIdentity_of_pointwise
    (u : ℝ → ℝ → ℝ) (r : ℕ) (t h : ℝ) (hh : 0 ≤ h)
    (hmild : ∀ x : ℝ, 0 ≤ x →
      u (t + h) x = u t (x + h) +
        ∫ s in t..t + h, (1 / 2 : ℝ) *
          positiveSelfConvolution (u s) (x + t + h - s))
    (hbase : IntegrableOn (fun x : ℝ ↦ x ^ r * u t (x + h)) (Ici 0))
    (hspaceTime : Integrable (momentDuhamelIntegrand u r t h)
      ((volume.restrict (Ici (0 : ℝ))).prod
        (volume.restrict (Ioc t (t + h))))) :
    continuumMoment (u (t + h)) r =
      shiftedHalfLineMoment (u t) r h +
        ∫ s in t..t + h, (1 / 2 : ℝ) *
          shiftedHalfLineMoment (positiveSelfConvolution (u s)) r
            (t + h - s) := by
  have htime : t ≤ t + h := by linarith
  have hduhInt : IntegrableOn
      (fun x : ℝ ↦ ∫ s in t..t + h,
        momentDuhamelIntegrand u r t h (x, s)) (Ici 0) := by
    simpa only [intervalIntegral.integral_of_le htime] using
      hspaceTime.integral_prod_left
  have hsum :
      continuumMoment (u (t + h)) r =
        (∫ x in Ici (0 : ℝ), x ^ r * u t (x + h)) +
          ∫ x in Ici (0 : ℝ), ∫ s in t..t + h,
            momentDuhamelIntegrand u r t h (x, s) := by
    unfold continuumMoment
    have hpoint : ∀ x ∈ Ici (0 : ℝ),
        x ^ r * u (t + h) x =
          x ^ r * u t (x + h) +
            ∫ s in t..t + h, momentDuhamelIntegrand u r t h (x, s) := by
      intro x hx
      rw [hmild x hx, mul_add, ← intervalIntegral.integral_const_mul]
      rfl
    rw [setIntegral_congr_fun measurableSet_Ici hpoint]
    simpa only [Pi.add_apply] using integral_add hbase hduhInt
  rw [hsum]
  congr 1
  have hspaceTime' : Integrable
      (Function.uncurry (fun x s ↦ momentDuhamelIntegrand u r t h (x, s)))
      ((volume.restrict (Ici (0 : ℝ))).prod
        (volume.restrict (Ioc t (t + h)))) := by
    simpa only [Function.uncurry_apply_pair] using hspaceTime
  have hswap := integral_integral_swap hspaceTime'
  calc
    (∫ x in Ici (0 : ℝ), ∫ s in t..t + h,
        momentDuhamelIntegrand u r t h (x, s)) =
        ∫ x in Ici (0 : ℝ), ∫ s in Ioc t (t + h),
          momentDuhamelIntegrand u r t h (x, s) := by
      apply setIntegral_congr_fun measurableSet_Ici
      intro x hx
      exact intervalIntegral.integral_of_le htime
    _ = ∫ s in Ioc t (t + h), ∫ x in Ici (0 : ℝ),
        momentDuhamelIntegrand u r t h (x, s) := hswap
    _ = ∫ s in Ioc t (t + h), (1 / 2 : ℝ) *
        shiftedHalfLineMoment (positiveSelfConvolution (u s)) r
          (t + h - s) := by
      apply setIntegral_congr_fun measurableSet_Ioc
      intro s hs
      change (∫ x in Ici (0 : ℝ), momentDuhamelIntegrand u r t h (x, s)) = _
      have heq :
          (∫ x in Ici (0 : ℝ), momentDuhamelIntegrand u r t h (x, s)) =
            ∫ x in Ici (0 : ℝ), (1 / 2 : ℝ) *
              (x ^ r * positiveSelfConvolution (u s) (x + (t + h - s))) := by
        apply setIntegral_congr_fun measurableSet_Ici
        intro x hx
        unfold momentDuhamelIntegrand
        ring
      rw [heq, integral_const_mul]
      rfl
    _ = ∫ s in t..t + h, (1 / 2 : ℝ) *
        shiftedHalfLineMoment (positiveSelfConvolution (u s)) r
          (t + h - s) := (intervalIntegral.integral_of_le htime).symm

end

end DerridaRetaux
