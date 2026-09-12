import DerridaRetaux.Analysis.HalfLineShiftDerivatives
import Mathlib.Tactic

set_option autoImplicit false

open Filter Topology MeasureTheory Set

namespace DerridaRetaux

noncomputable section

/-- Laplace pairing after translating a half-line density to the left. -/
def shiftedHalfLineLaplace (u : ℝ → ℝ) (p h : ℝ) : ℝ :=
  ∫ x in Ici (0 : ℝ), Real.exp (-(p * x)) * u (x + h)

theorem shiftedHalfLineLaplace_eq_integral_Ici
    (u : ℝ → ℝ) (p : ℝ) {h : ℝ} :
    shiftedHalfLineLaplace u p h =
      ∫ y in Ici h, Real.exp (-(p * (y - h))) * u y := by
  rw [shiftedHalfLineLaplace, ← integral_indicator measurableSet_Ici,
    ← integral_indicator measurableSet_Ici]
  rw [← MeasureTheory.integral_add_right_eq_self
    (fun y : ℝ ↦ (Ici h).indicator
      (fun z ↦ Real.exp (-(p * (z - h))) * u z) y) h]
  apply integral_congr_ae
  filter_upwards with x
  simp only [Set.indicator]
  by_cases hx : x ∈ Ici (0 : ℝ)
  · rw [if_pos hx, if_pos]
    · ring_nf
    · have hx0 : 0 ≤ x := hx
      exact show h ≤ x + h by linarith
  · rw [if_neg hx, if_neg]
    intro hxh
    have hle : h ≤ x + h := hxh
    have hx0 : 0 ≤ x := by linarith
    exact hx hx0

/-- Exact translated Laplace identity. -/
theorem shiftedHalfLineLaplace_eq
    (u : ℝ → ℝ) (p : ℝ) {h : ℝ} (hh : 0 ≤ h)
    (hLap : IntegrableOn
      (fun x : ℝ ↦ Real.exp (-(p * x)) * u x) (Ici 0)) :
    shiftedHalfLineLaplace u p h =
      Real.exp (p * h) *
        (continuumLaplace u p -
          ∫ y in (0 : ℝ)..h, Real.exp (-(p * y)) * u y) := by
  rw [shiftedHalfLineLaplace_eq_integral_Ici]
  have htail := integral_Ici_eq_interval_add_Ici
    (fun y : ℝ ↦ Real.exp (-(p * y)) * u y) hh hLap
  have hfactor : ∀ y : ℝ,
      Real.exp (-(p * (y - h))) * u y =
        Real.exp (p * h) * (Real.exp (-(p * y)) * u y) := by
    intro y
    rw [show -(p * (y - h)) = p * h + -(p * y) by ring, Real.exp_add]
    ring
  rw [setIntegral_congr_fun measurableSet_Ici (fun y _ ↦ hfactor y),
    integral_const_mul]
  have htailEq :
      (∫ y in Ici h, Real.exp (-(p * y)) * u y) =
        (∫ y in Ici (0 : ℝ), Real.exp (-(p * y)) * u y) -
          ∫ y in (0 : ℝ)..h, Real.exp (-(p * y)) * u y := by
    linarith [htail]
  rw [htailEq]
  rfl

/-- Right derivative at zero of the translated Laplace pairing. -/
theorem hasDerivWithinAt_shiftedHalfLineLaplace_zero
    (u : ℝ → ℝ) (p : ℝ)
    (hucont : ContinuousOn u (Ici 0))
    (hLap : IntegrableOn
      (fun x : ℝ ↦ Real.exp (-(p * x)) * u x) (Ici 0)) :
    HasDerivWithinAt (shiftedHalfLineLaplace u p)
      (p * continuumLaplace u p - u 0) (Ici 0) 0 := by
  let f : ℝ → ℝ := fun x ↦ Real.exp (-(p * x)) * u x
  have hexpCont : Continuous (fun x : ℝ ↦ Real.exp (-(p * x))) := by fun_prop
  have hfcont : ContinuousOn f (Ici 0) :=
    hexpCont.continuousOn.mul hucont
  have htail := hasDerivWithinAt_halfLineTailMoment_zero f 0 (by
    simpa only [pow_zero, one_mul] using hfcont)
  change HasDerivWithinAt
      (fun h ↦ (∫ x in Ici (0 : ℝ), x ^ 0 * f x) -
        ∫ y in (0 : ℝ)..h, y ^ 0 * f y) (-(0 ^ 0 * f 0))
        (Ici 0) 0 at htail
  have htail' : HasDerivWithinAt
      (fun h ↦ continuumLaplace u p - ∫ y in (0 : ℝ)..h, f y)
      (-u 0) (Ici 0) 0 := by
    simpa only [pow_zero, one_mul, f, continuumLaplace, Real.exp_zero,
      neg_zero, mul_zero] using htail
  have hinner : HasDerivAt (fun h : ℝ ↦ p * h) p 0 := by
    convert (hasDerivAt_const 0 p).mul (hasDerivAt_id 0) using 1 <;> ring
  have hexp : HasDerivAt (fun h : ℝ ↦ Real.exp (p * h)) p 0 := by
    convert (Real.hasDerivAt_exp (p * 0)).comp 0 hinner using 1 <;> simp
  have hformula := hexp.hasDerivWithinAt.mul htail'
  have hformula' : HasDerivWithinAt
      (fun h ↦ Real.exp (p * h) *
        (continuumLaplace u p - ∫ y in (0 : ℝ)..h,
          Real.exp (-(p * y)) * u y))
      (p * continuumLaplace u p - u 0) (Ici 0) 0 := by
    convert hformula using 1 <;> simp [f] <;> ring
  apply hformula'.congr_of_eventuallyEq
  · filter_upwards [self_mem_nhdsWithin] with h hh
    exact shiftedHalfLineLaplace_eq u p hh hLap
  · simp [shiftedHalfLineLaplace, continuumLaplace]

end

end DerridaRetaux
