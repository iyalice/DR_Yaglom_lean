import DerridaRetaux.Analysis.LaplaceGap
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Tactic
import Mathlib.Topology.Order.MonotoneContinuity

/-!
# The time and mass coordinates of the manuscript string

This file isolates the string-coordinate construction in `DR_Yaglom.tex`,
equations `eq:Y`, `eq:stringcoordinates`, and `eq:stringdensity`.  The moment
ODEs, their two-sided estimates, and the endpoint decay of `A₂Y` are explicit
premises: they belong to the preceding continuum analysis, not to the
definition of the string coordinates.
-/

set_option autoImplicit false

namespace DerridaRetaux

noncomputable section

open Filter MeasureTheory Set Topology
open scoped Interval

/-- The source normalization `Y(t) = κ / A₃(t)`. -/
def stringY (κ : ℝ) (A3 : ℝ → ℝ) (t : ℝ) : ℝ :=
  κ / A3 t

/-- The product whose derivative is `-Y` in the moment ODE. -/
def stringA2Y (κ : ℝ) (A2 A3 : ℝ → ℝ) (t : ℝ) : ℝ :=
  A2 t * stringY κ A3 t

/-- The manuscript coordinate `ξ(t) = -A₂(t)Y(t)`. -/
def stringXi (κ : ℝ) (A2 A3 : ℝ → ℝ) (t : ℝ) : ℝ :=
  -stringA2Y κ A2 A3 t

/-- The cumulative mass along the time coordinate.

The integrand is written as `A₃/κ`; `stringMassPrimitive_eq_integral_inv_Y`
below proves that this is exactly `Y⁻¹`, including at zeros under `κ ≠ 0`.
-/
def stringMassPrimitive (κ : ℝ) (A3 : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..t, A3 s / κ

/-- The mass integrand is literally the reciprocal of `Y`. -/
theorem inv_stringY (κ : ℝ) (A3 : ℝ → ℝ) (t : ℝ) :
    (stringY κ A3 t)⁻¹ = A3 t / κ := by
  simp [stringY]

/-- Integral form of the second identity in `eq:stringcoordinates`. -/
theorem stringMassPrimitive_eq_integral_inv_Y
    (κ : ℝ) (A3 : ℝ → ℝ) (t : ℝ) :
    stringMassPrimitive κ A3 t =
      ∫ s in (0 : ℝ)..t, (stringY κ A3 s)⁻¹ := by
  apply intervalIntegral.integral_congr
  intro s _
  exact (inv_stringY κ A3 s).symm

/-- The third-moment ODE `A₃'=A₀A₃` differentiates `Y` to `-A₀Y`. -/
theorem hasDerivAt_stringY
    (κ : ℝ) (A0 A3 : ℝ → ℝ) {t : ℝ}
    (hA3 : HasDerivAt A3 (A0 t * A3 t) t)
    (hA3ne : A3 t ≠ 0) :
    HasDerivAt (stringY κ A3) (-A0 t * stringY κ A3 t) t := by
  have hquot := (hasDerivAt_const t κ).div hA3 hA3ne
  convert hquot using 1
  simp only [stringY]
  field_simp
  ring

/-- The two moment ODEs cancel their common `A₀A₂Y` term. -/
theorem hasDerivAt_stringA2Y
    (κ : ℝ) (A0 A2 A3 : ℝ → ℝ) {t : ℝ}
    (hA2 : HasDerivAt A2 (A0 t * A2 t - 1) t)
    (hA3 : HasDerivAt A3 (A0 t * A3 t) t)
    (hA3ne : A3 t ≠ 0) :
    HasDerivAt (stringA2Y κ A2 A3) (-stringY κ A3 t) t := by
  have hY := hasDerivAt_stringY κ A0 A3 hA3 hA3ne
  have hprod := hA2.mul hY
  convert hprod using 1
  ring

/-- Consequently the source coordinate has derivative `ξ'=Y`. -/
theorem hasDerivAt_stringXi
    (κ : ℝ) (A0 A2 A3 : ℝ → ℝ) {t : ℝ}
    (hA2 : HasDerivAt A2 (A0 t * A2 t - 1) t)
    (hA3 : HasDerivAt A3 (A0 t * A3 t) t)
    (hA3ne : A3 t ≠ 0) :
    HasDerivAt (stringXi κ A2 A3) (stringY κ A3 t) t := by
  simpa only [stringXi, neg_neg] using
    (hasDerivAt_stringA2Y κ A0 A2 A3 hA2 hA3 hA3ne).neg

/-- Pointwise derivative spelling of `Y'=-A₀Y`. -/
theorem deriv_stringY_eq
    (κ : ℝ) (A0 A3 : ℝ → ℝ) {t : ℝ}
    (hA3 : HasDerivAt A3 (A0 t * A3 t) t)
    (hA3ne : A3 t ≠ 0) :
    deriv (stringY κ A3) t = -A0 t * stringY κ A3 t :=
  (hasDerivAt_stringY κ A0 A3 hA3 hA3ne).deriv

/-- Pointwise derivative spelling of `(A₂Y)'=-Y`. -/
theorem deriv_stringA2Y_eq
    (κ : ℝ) (A0 A2 A3 : ℝ → ℝ) {t : ℝ}
    (hA2 : HasDerivAt A2 (A0 t * A2 t - 1) t)
    (hA3 : HasDerivAt A3 (A0 t * A3 t) t)
    (hA3ne : A3 t ≠ 0) :
    deriv (stringA2Y κ A2 A3) t = -stringY κ A3 t :=
  (hasDerivAt_stringA2Y κ A0 A2 A3 hA2 hA3 hA3ne).deriv

/-- Pointwise derivative spelling of `ξ'=Y`. -/
theorem deriv_stringXi_eq
    (κ : ℝ) (A0 A2 A3 : ℝ → ℝ) {t : ℝ}
    (hA2 : HasDerivAt A2 (A0 t * A2 t - 1) t)
    (hA3 : HasDerivAt A3 (A0 t * A3 t) t)
    (hA3ne : A3 t ≠ 0) :
    deriv (stringXi κ A2 A3) t = stringY κ A3 t :=
  (hasDerivAt_stringXi κ A0 A2 A3 hA2 hA3 hA3ne).deriv

/-- Positivity of the normalization and third moment gives positivity of `Y`. -/
theorem stringY_pos
    {κ : ℝ} {A3 : ℝ → ℝ} {t : ℝ}
    (hκ : 0 < κ) (hA3 : 0 < A3 t) :
    0 < stringY κ A3 t := by
  exact div_pos hκ hA3

/-- The quadratic two-sided bounds on `A₃` invert to inverse-square bounds on `Y`. -/
theorem stringY_two_sided
    {κ c C : ℝ} {A3 : ℝ → ℝ} {t : ℝ}
    (hκ : 0 < κ) (hc : 0 < c) (hC : 0 < C) (ht : 0 < t)
    (hlower : c * t ^ 2 ≤ A3 t) (hupper : A3 t ≤ C * t ^ 2) :
    κ / (C * t ^ 2) ≤ stringY κ A3 t ∧
      stringY κ A3 t ≤ κ / (c * t ^ 2) := by
  have hlowPos : 0 < c * t ^ 2 := mul_pos hc (sq_pos_of_pos ht)
  have huppPos : 0 < C * t ^ 2 := mul_pos hC (sq_pos_of_pos ht)
  have hA3Pos : 0 < A3 t := hlowPos.trans_le hlower
  constructor
  · exact (div_le_div_iff₀ huppPos hA3Pos).2
      (mul_le_mul_of_nonneg_left hupper hκ.le)
  · exact (div_le_div_iff₀ hA3Pos hlowPos).2
      (mul_le_mul_of_nonneg_left hlower hκ.le)

/-- The finite-interval mass primitive has derivative `Y⁻¹`. -/
theorem hasDerivAt_stringMassPrimitive
    {κ : ℝ} {A3 : ℝ → ℝ} {t : ℝ}
    (hint : IntervalIntegrable (fun s ↦ A3 s / κ) volume 0 t)
    (hmeas : StronglyMeasurableAtFilter (fun s ↦ A3 s / κ) (𝓝 t) volume)
    (hA3 : ContinuousAt A3 t) :
    HasDerivAt (stringMassPrimitive κ A3) ((stringY κ A3 t)⁻¹) t := by
  have hcont : ContinuousAt (fun s ↦ A3 s / κ) t := hA3.div_const κ
  have hderiv := intervalIntegral.integral_hasDerivAt_right
    hint hmeas hcont
  simpa only [stringMassPrimitive, inv_stringY] using hderiv

/-- The cubic bounds on the mass primitive follow by integrating the quadratic
bounds on `A₃`; endpoint values do not matter for Lebesgue integration. -/
theorem stringMassPrimitive_two_sided
    {κ c C t : ℝ} {A3 : ℝ → ℝ}
    (hκ : 0 < κ) (ht : 0 < t)
    (hA3int : IntervalIntegrable (fun s ↦ A3 s / κ) volume 0 t)
    (hbounds : ∀ s : ℝ, 0 < s → c * s ^ 2 ≤ A3 s ∧ A3 s ≤ C * s ^ 2) :
    (c / κ) * (t ^ 3 / 3) ≤ stringMassPrimitive κ A3 t ∧
      stringMassPrimitive κ A3 t ≤ (C / κ) * (t ^ 3 / 3) := by
  have hlowerInt : IntervalIntegrable (fun s : ℝ ↦ (c / κ) * s ^ 2) volume 0 t :=
    ((continuous_const.mul (continuous_id.pow 2)).intervalIntegrable 0 t)
  have hupperInt : IntervalIntegrable (fun s : ℝ ↦ (C / κ) * s ^ 2) volume 0 t :=
    ((continuous_const.mul (continuous_id.pow 2)).intervalIntegrable 0 t)
  constructor
  · calc
      (c / κ) * (t ^ 3 / 3) = ∫ s in (0 : ℝ)..t, (c / κ) * s ^ 2 := by
        rw [intervalIntegral.integral_const_mul, integral_pow]
        norm_num
      _ ≤ ∫ s in (0 : ℝ)..t, A3 s / κ := by
        apply intervalIntegral.integral_mono_on_of_le_Ioo ht.le hlowerInt hA3int
        intro s hs
        have hsBound := (hbounds s hs.1).1
        calc
          (c / κ) * s ^ 2 = (c * s ^ 2) / κ := by ring
          _ ≤ A3 s / κ := (div_le_div_iff_of_pos_right hκ).2 hsBound
      _ = stringMassPrimitive κ A3 t := rfl
  · calc
      stringMassPrimitive κ A3 t = ∫ s in (0 : ℝ)..t, A3 s / κ := rfl
      _ ≤ ∫ s in (0 : ℝ)..t, (C / κ) * s ^ 2 := by
        apply intervalIntegral.integral_mono_on_of_le_Ioo ht.le hA3int hupperInt
        intro s hs
        have hsBound := (hbounds s hs.1).2
        calc
          A3 s / κ ≤ (C * s ^ 2) / κ :=
            (div_le_div_iff_of_pos_right hκ).2 hsBound
          _ = (C / κ) * s ^ 2 := by ring
      _ = (C / κ) * (t ^ 3 / 3) := by
        rw [intervalIntegral.integral_const_mul, integral_pow]
        norm_num

/-- Integrability of `Y` on every tail follows from `(A₂Y)'=-Y`, positivity,
and the source endpoint condition `A₂Y → 0`. -/
theorem integrableOn_stringY_Ioi
    {κ : ℝ} {A0 A2 A3 : ℝ → ℝ} {t : ℝ}
    (ht : 0 < t)
    (hA2 : ∀ s : ℝ, 0 < s → HasDerivAt A2 (A0 s * A2 s - 1) s)
    (hA3 : ∀ s : ℝ, 0 < s → HasDerivAt A3 (A0 s * A3 s) s)
    (hA3pos : ∀ s : ℝ, 0 < s → 0 < A3 s)
    (hprodTop : Tendsto (stringA2Y κ A2 A3) atTop (𝓝 0))
    (hYnonneg : ∀ s : ℝ, 0 < s → 0 ≤ stringY κ A3 s) :
    IntegrableOn (stringY κ A3) (Ioi t) := by
  have hderiv : ∀ s ∈ Ioi t,
      HasDerivAt (stringA2Y κ A2 A3) (-stringY κ A3 s) s := by
    intro s hs
    exact hasDerivAt_stringA2Y κ A0 A2 A3
      (hA2 s (ht.trans hs)) (hA3 s (ht.trans hs))
      (ne_of_gt (hA3pos s (ht.trans hs)))
  have hcont : ContinuousWithinAt (stringA2Y κ A2 A3) (Ici t) t :=
    (hasDerivAt_stringA2Y κ A0 A2 A3
      (hA2 t ht) (hA3 t ht) (ne_of_gt (hA3pos t ht))).continuousAt.continuousWithinAt
  have hnegInt := integrableOn_Ioi_deriv_of_nonpos hcont hderiv
    (fun s hs ↦ neg_nonpos.mpr (hYnonneg s (ht.trans hs))) hprodTop
  change Integrable (-(stringY κ A3)) (volume.restrict (Ioi t)) at hnegInt
  exact integrable_neg_iff.mp hnegInt

/-- Fundamental theorem of calculus on `(t,∞)`: `A₂(t)Y(t)=∫_t^∞Y`. -/
theorem stringA2Y_eq_integral_Ioi
    {κ : ℝ} {A0 A2 A3 : ℝ → ℝ} {t : ℝ}
    (ht : 0 < t)
    (hA2 : ∀ s : ℝ, 0 < s → HasDerivAt A2 (A0 s * A2 s - 1) s)
    (hA3 : ∀ s : ℝ, 0 < s → HasDerivAt A3 (A0 s * A3 s) s)
    (hA3pos : ∀ s : ℝ, 0 < s → 0 < A3 s)
    (hprodTop : Tendsto (stringA2Y κ A2 A3) atTop (𝓝 0))
    (hYnonneg : ∀ s : ℝ, 0 < s → 0 ≤ stringY κ A3 s) :
    stringA2Y κ A2 A3 t = ∫ s in Ioi t, stringY κ A3 s := by
  have hderiv : ∀ s ∈ Ioi t,
      HasDerivAt (stringA2Y κ A2 A3) (-stringY κ A3 s) s := by
    intro s hs
    exact hasDerivAt_stringA2Y κ A0 A2 A3
      (hA2 s (ht.trans hs)) (hA3 s (ht.trans hs))
      (ne_of_gt (hA3pos s (ht.trans hs)))
  have hcont : ContinuousWithinAt (stringA2Y κ A2 A3) (Ici t) t :=
    (hasDerivAt_stringA2Y κ A0 A2 A3
      (hA2 t ht) (hA3 t ht) (ne_of_gt (hA3pos t ht))).continuousAt.continuousWithinAt
  have htail := integral_Ioi_of_hasDerivAt_of_nonpos hcont hderiv
    (fun s hs ↦ neg_nonpos.mpr (hYnonneg s (ht.trans hs))) hprodTop
  rw [integral_neg] at htail
  linarith

/-- The first coordinate identity `ξ(t)=-∫_t^∞Y`. -/
theorem stringXi_eq_neg_integral_Ioi
    {κ : ℝ} {A0 A2 A3 : ℝ → ℝ} {t : ℝ}
    (ht : 0 < t)
    (hA2 : ∀ s : ℝ, 0 < s → HasDerivAt A2 (A0 s * A2 s - 1) s)
    (hA3 : ∀ s : ℝ, 0 < s → HasDerivAt A3 (A0 s * A3 s) s)
    (hA3pos : ∀ s : ℝ, 0 < s → 0 < A3 s)
    (hprodTop : Tendsto (stringA2Y κ A2 A3) atTop (𝓝 0))
    (hYnonneg : ∀ s : ℝ, 0 < s → 0 ≤ stringY κ A3 s) :
    stringXi κ A2 A3 t = -∫ s in Ioi t, stringY κ A3 s := by
  rw [stringXi, stringA2Y_eq_integral_Ioi ht hA2 hA3 hA3pos hprodTop hYnonneg]

/-- The elementary inverse-square tail integral. -/
theorem integral_Ioi_inv_sq {t : ℝ} (ht : 0 < t) :
    ∫ s in Ioi t, (s ^ 2)⁻¹ = t⁻¹ := by
  calc
    (∫ s in Ioi t, (s ^ 2)⁻¹) = ∫ s in Ioi t, s ^ (-2 : ℝ) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro s hs
      change (s ^ 2)⁻¹ = s ^ (-2 : ℝ)
      rw [show (-2 : ℝ) = -(2 : ℝ) by norm_num, Real.rpow_neg (ht.trans hs).le,
        Real.rpow_two]
    _ = t⁻¹ := by
      rw [integral_Ioi_rpow_of_lt (a := (-2 : ℝ)) (by norm_num) ht]
      norm_num [Real.rpow_neg_one]

/-- The inverse-square tail is integrable away from zero. -/
theorem integrableOn_Ioi_inv_sq {t : ℝ} (ht : 0 < t) :
    IntegrableOn (fun s : ℝ ↦ (s ^ 2)⁻¹) (Ioi t) := by
  refine (integrableOn_Ioi_rpow_of_lt (a := (-2 : ℝ)) (by norm_num) ht).congr_fun ?_
    measurableSet_Ioi
  intro s hs
  change s ^ (-2 : ℝ) = (s ^ 2)⁻¹
  rw [show (-2 : ℝ) = -(2 : ℝ) by norm_num, Real.rpow_neg (ht.trans hs).le,
    Real.rpow_two]

/-- Integrating the inverse-square bounds gives the precise `-ξ(t) ≍ t⁻¹`
comparison used at the left endpoint. -/
theorem integral_stringY_Ioi_two_sided
    {κ c C : ℝ} {A3 : ℝ → ℝ} {t : ℝ}
    (hκ : 0 < κ) (hc : 0 < c) (hC : 0 < C) (ht : 0 < t)
    (hYint : IntegrableOn (stringY κ A3) (Ioi t))
    (hbounds : ∀ s : ℝ, 0 < s → c * s ^ 2 ≤ A3 s ∧ A3 s ≤ C * s ^ 2) :
    (κ / C) * t⁻¹ ≤ ∫ s in Ioi t, stringY κ A3 s ∧
      (∫ s in Ioi t, stringY κ A3 s) ≤ (κ / c) * t⁻¹ := by
  have hinv := integrableOn_Ioi_inv_sq ht
  have hlowerInt : IntegrableOn (fun s : ℝ ↦ (κ / C) * (s ^ 2)⁻¹) (Ioi t) :=
    hinv.const_mul (κ / C)
  have hupperInt : IntegrableOn (fun s : ℝ ↦ (κ / c) * (s ^ 2)⁻¹) (Ioi t) :=
    hinv.const_mul (κ / c)
  constructor
  · calc
      (κ / C) * t⁻¹ = ∫ s in Ioi t, (κ / C) * (s ^ 2)⁻¹ := by
        rw [integral_const_mul, integral_Ioi_inv_sq ht]
      _ ≤ ∫ s in Ioi t, stringY κ A3 s := by
        apply setIntegral_mono_on hlowerInt hYint measurableSet_Ioi
        intro s hs
        have hY := (stringY_two_sided hκ hc hC (ht.trans hs)
          (hbounds s (ht.trans hs)).1 (hbounds s (ht.trans hs)).2).1
        calc
          (κ / C) * (s ^ 2)⁻¹ = κ / (C * s ^ 2) := by
            field_simp [ne_of_gt hC, ne_of_gt (ht.trans hs)]
          _ ≤ stringY κ A3 s := hY
  · calc
      (∫ s in Ioi t, stringY κ A3 s) ≤
          ∫ s in Ioi t, (κ / c) * (s ^ 2)⁻¹ := by
        apply setIntegral_mono_on hYint hupperInt measurableSet_Ioi
        intro s hs
        have hY := (stringY_two_sided hκ hc hC (ht.trans hs)
          (hbounds s (ht.trans hs)).1 (hbounds s (ht.trans hs)).2).2
        calc
          stringY κ A3 s ≤ κ / (c * s ^ 2) := hY
          _ = (κ / c) * (s ^ 2)⁻¹ := by
            field_simp [ne_of_gt hc, ne_of_gt (ht.trans hs)]
      _ = (κ / c) * t⁻¹ := by
        rw [integral_const_mul, integral_Ioi_inv_sq ht]

/-- Source-shaped inverse-linear bounds for the actual coordinate. -/
theorem neg_stringXi_two_sided
    {κ c C : ℝ} {A0 A2 A3 : ℝ → ℝ} {t : ℝ}
    (hκ : 0 < κ) (hc : 0 < c) (hC : 0 < C) (ht : 0 < t)
    (hA2 : ∀ s : ℝ, 0 < s → HasDerivAt A2 (A0 s * A2 s - 1) s)
    (hA3 : ∀ s : ℝ, 0 < s → HasDerivAt A3 (A0 s * A3 s) s)
    (hprodTop : Tendsto (stringA2Y κ A2 A3) atTop (𝓝 0))
    (hbounds : ∀ s : ℝ, 0 < s → c * s ^ 2 ≤ A3 s ∧ A3 s ≤ C * s ^ 2) :
    (κ / C) * t⁻¹ ≤ -stringXi κ A2 A3 t ∧
      -stringXi κ A2 A3 t ≤ (κ / c) * t⁻¹ := by
  have hA3pos : ∀ s : ℝ, 0 < s → 0 < A3 s := by
    intro s hs
    exact (mul_pos hc (sq_pos_of_pos hs)).trans_le (hbounds s hs).1
  have hYnonneg : ∀ s : ℝ, 0 < s → 0 ≤ stringY κ A3 s := by
    intro s hs
    exact (stringY_pos hκ (hA3pos s hs)).le
  have hYint := integrableOn_stringY_Ioi ht hA2 hA3 hA3pos hprodTop hYnonneg
  have htail := integral_stringY_Ioi_two_sided hκ hc hC ht hYint hbounds
  have hxi := stringXi_eq_neg_integral_Ioi ht hA2 hA3 hA3pos hprodTop hYnonneg
  rw [hxi, neg_neg]
  exact htail

/-- The coordinate tends to the finite right endpoint zero. -/
theorem tendsto_stringXi_atTop
    {κ : ℝ} {A2 A3 : ℝ → ℝ}
    (hprodTop : Tendsto (stringA2Y κ A2 A3) atTop (𝓝 0)) :
    Tendsto (stringXi κ A2 A3) atTop (𝓝 0) := by
  simpa only [stringXi, neg_zero] using hprodTop.neg

/-- The inverse-linear lower bound forces the coordinate to `-∞` as time
approaches zero from the right. -/
theorem tendsto_stringXi_nhdsGT_zero_atBot
    {κ c C : ℝ} {A0 A2 A3 : ℝ → ℝ}
    (hκ : 0 < κ) (hc : 0 < c) (hC : 0 < C)
    (hA2 : ∀ s : ℝ, 0 < s → HasDerivAt A2 (A0 s * A2 s - 1) s)
    (hA3 : ∀ s : ℝ, 0 < s → HasDerivAt A3 (A0 s * A3 s) s)
    (hprodTop : Tendsto (stringA2Y κ A2 A3) atTop (𝓝 0))
    (hbounds : ∀ s : ℝ, 0 < s → c * s ^ 2 ≤ A3 s ∧ A3 s ≤ C * s ^ 2) :
    Tendsto (stringXi κ A2 A3) (𝓝[>] 0) atBot := by
  have hconst : 0 < κ / C := div_pos hκ hC
  have hbase : Tendsto (fun t : ℝ ↦ (κ / C) * t⁻¹) (𝓝[>] 0) atTop :=
    tendsto_const_nhds.pos_mul_atTop hconst tendsto_inv_nhdsGT_zero
  have hneg : Tendsto (fun t : ℝ ↦ -stringXi κ A2 A3 t) (𝓝[>] 0) atTop := by
    apply tendsto_atTop_mono' (𝓝[>] 0) _ hbase
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (neg_stringXi_two_sided hκ hc hC ht hA2 hA3 hprodTop hbounds).1
  simpa only [Function.comp_def, neg_neg] using tendsto_neg_atTop_atBot.comp hneg

/-- Positivity of `ξ'=Y` makes the coordinate strictly increasing. -/
theorem strictMonoOn_stringXi
    {κ : ℝ} {A0 A2 A3 : ℝ → ℝ}
    (hκ : 0 < κ)
    (hA2 : ∀ s : ℝ, 0 < s → HasDerivAt A2 (A0 s * A2 s - 1) s)
    (hA3 : ∀ s : ℝ, 0 < s → HasDerivAt A3 (A0 s * A3 s) s)
    (hA3pos : ∀ s : ℝ, 0 < s → 0 < A3 s) :
    StrictMonoOn (stringXi κ A2 A3) (Ioi 0) := by
  have hcont : ContinuousOn (stringXi κ A2 A3) (Ioi 0) := by
    intro t ht
    exact (hasDerivAt_stringXi κ A0 A2 A3 (hA2 t ht) (hA3 t ht)
      (ne_of_gt (hA3pos t ht))).continuousAt.continuousWithinAt
  apply strictMonoOn_of_deriv_pos (convex_Ioi (0 : ℝ)) hcont
  intro t ht
  have ht' : 0 < t := by simpa only [interior_Ioi, mem_Ioi] using ht
  rw [deriv_stringXi_eq κ A0 A2 A3 (hA2 t ht') (hA3 t ht')
    (ne_of_gt (hA3pos t ht'))]
  exact stringY_pos hκ (hA3pos t ht')

/-- A continuous strict increase with the two source endpoint limits is a
bijection `(0,∞) → (-∞,0)`. -/
theorem bijOn_Ioi_Iio_of_strictMonoOn_of_tendsto
    {f : ℝ → ℝ}
    (hmono : StrictMonoOn f (Ioi 0))
    (hcont : ContinuousOn f (Ioi 0))
    (hzero : Tendsto f atTop (𝓝 0))
    (hbot : Tendsto f (𝓝[>] 0) atBot) :
    BijOn f (Ioi 0) (Iio 0) := by
  have hmaps : MapsTo f (Ioi 0) (Iio 0) := by
    intro t ht
    change 0 < t at ht
    change f t < 0
    have hnext : t + 1 ∈ Ioi (0 : ℝ) := by
      change 0 < t + 1
      linarith
    have hle : f (t + 1) ≤ 0 := by
      apply ge_of_tendsto hzero
      filter_upwards [Ici_mem_atTop (t + 1)] with s hs
      change t + 1 ≤ s at hs
      have hspos : s ∈ Ioi (0 : ℝ) := by
        change 0 < s
        linarith
      exact hmono.monotoneOn hnext hspos hs
    exact (hmono ht hnext (by linarith)).trans_le hle
  refine ⟨hmaps, hmono.injOn, ?_⟩
  intro z hz
  have hleftEvent : ∀ᶠ t in 𝓝[>] (0 : ℝ), f t ≤ z - 1 :=
    tendsto_atBot.1 hbot (z - 1)
  rcases (hleftEvent.and self_mem_nhdsWithin).exists with ⟨a, hfa, ha⟩
  have haf : f a < z := by linarith
  have hrightEvent : ∀ᶠ t in atTop, z < f t :=
    hzero.eventually (Ioi_mem_nhds hz)
  rcases (hrightEvent.and (Ioi_mem_atTop a)).exists with ⟨b, hzb, hab⟩
  have hb : b ∈ Ioi (0 : ℝ) := ha.trans hab
  have hcontIcc : ContinuousOn f (Icc a b) :=
    hcont.mono fun x hx ↦ ha.trans_le hx.1
  rcases intermediate_value_Icc hab.le hcontIcc ⟨haf.le, hzb.le⟩ with ⟨x, hx, hfx⟩
  exact ⟨x, ha.trans_le hx.1, hfx⟩

/-- Source-shaped conclusion: the constructed coordinate is a strict increasing
bijection from positive time onto the negative half-line. -/
theorem stringXi_bijOn
    {κ c C : ℝ} {A0 A2 A3 : ℝ → ℝ}
    (hκ : 0 < κ) (hc : 0 < c) (hC : 0 < C)
    (hA2 : ∀ s : ℝ, 0 < s → HasDerivAt A2 (A0 s * A2 s - 1) s)
    (hA3 : ∀ s : ℝ, 0 < s → HasDerivAt A3 (A0 s * A3 s) s)
    (hprodTop : Tendsto (stringA2Y κ A2 A3) atTop (𝓝 0))
    (hbounds : ∀ s : ℝ, 0 < s → c * s ^ 2 ≤ A3 s ∧ A3 s ≤ C * s ^ 2) :
    BijOn (stringXi κ A2 A3) (Ioi 0) (Iio 0) := by
  have hA3pos : ∀ s : ℝ, 0 < s → 0 < A3 s := by
    intro s hs
    exact (mul_pos hc (sq_pos_of_pos hs)).trans_le (hbounds s hs).1
  have hmono := strictMonoOn_stringXi hκ hA2 hA3 hA3pos
  have hcont : ContinuousOn (stringXi κ A2 A3) (Ioi 0) := by
    intro t ht
    exact (hasDerivAt_stringXi κ A0 A2 A3 (hA2 t ht) (hA3 t ht)
      (ne_of_gt (hA3pos t ht))).continuousAt.continuousWithinAt
  exact bijOn_Ioi_Iio_of_strictMonoOn_of_tendsto hmono hcont
    (tendsto_stringXi_atTop hprodTop)
    (tendsto_stringXi_nhdsGT_zero_atBot hκ hc hC hA2 hA3 hprodTop hbounds)

/-- The order isomorphism induced by a strictly increasing half-line bijection. -/
noncomputable def coordinateOrderIso
    (f : ℝ → ℝ)
    (hmono : StrictMonoOn f (Ioi 0))
    (hbij : BijOn f (Ioi 0) (Iio 0)) :
    Ioi (0 : ℝ) ≃o Iio (0 : ℝ) := by
  let g : Ioi (0 : ℝ) → Iio (0 : ℝ) := fun t ↦ ⟨f t, hbij.1 t.property⟩
  have hgmono : StrictMono g := by
    intro s t hst
    exact hmono s.property t.property hst
  have hgsurj : Function.Surjective g := by
    intro x
    rcases hbij.2.2 x.property with ⟨t, ht, hft⟩
    refine ⟨⟨t, ht⟩, ?_⟩
    exact Subtype.ext hft
  exact StrictMono.orderIsoOfSurjective g hgmono hgsurj

@[simp] theorem coordinateOrderIso_apply
    (f : ℝ → ℝ)
    (hmono : StrictMonoOn f (Ioi 0))
    (hbij : BijOn f (Ioi 0) (Iio 0))
    (t : Ioi (0 : ℝ)) :
    (coordinateOrderIso f hmono hbij t : ℝ) = f t :=
  rfl

/-- The inverse time coordinate, extended by zero outside the negative half-line.
Only its restriction to `(-∞,0)` is used in the constructed string. -/
noncomputable def timeOfNegativeCoordinate
    (e : Ioi (0 : ℝ) ≃o Iio (0 : ℝ)) (x : ℝ) : ℝ :=
  if hx : x < 0 then (e.symm ⟨x, hx⟩ : Ioi (0 : ℝ)) else 0

@[simp] theorem timeOfNegativeCoordinate_of_neg
    (e : Ioi (0 : ℝ) ≃o Iio (0 : ℝ)) {x : ℝ} (hx : x < 0) :
    timeOfNegativeCoordinate e x = (e.symm ⟨x, hx⟩ : Ioi (0 : ℝ)) := by
  simp [timeOfNegativeCoordinate, hx]

theorem timeOfNegativeCoordinate_pos
    (e : Ioi (0 : ℝ) ≃o Iio (0 : ℝ)) {x : ℝ} (hx : x < 0) :
    0 < timeOfNegativeCoordinate e x := by
  rw [timeOfNegativeCoordinate_of_neg e hx]
  exact (e.symm ⟨x, hx⟩).property

/-- The extended inverse time map is continuous at every negative coordinate. -/
theorem continuousAt_timeOfNegativeCoordinate
    (e : Ioi (0 : ℝ) ≃o Iio (0 : ℝ)) {x : ℝ} (hx : x < 0) :
    ContinuousAt (timeOfNegativeCoordinate e) x := by
  have hrestrict : Continuous (Set.restrict (Iio 0) (timeOfNegativeCoordinate e)) := by
    have hcontinuous : Continuous (fun y : Iio (0 : ℝ) ↦ (e.symm y : Ioi (0 : ℝ)).1) :=
      continuous_subtype_val.comp e.symm.continuous
    convert hcontinuous using 1
    ext y
    exact timeOfNegativeCoordinate_of_neg e y.property
  have hwithin : ContinuousWithinAt (timeOfNegativeCoordinate e) (Iio 0) x :=
    (continuousOn_iff_continuous_restrict.2 hrestrict) x hx
  exact hwithin.continuousAt (Iio_mem_nhds hx)

/-- The inverse time map recovers a positive time under the induced order isomorphism. -/
theorem timeOfNegativeCoordinate_coordinateOrderIso
    (f : ℝ → ℝ)
    (hmono : StrictMonoOn f (Ioi 0))
    (hbij : BijOn f (Ioi 0) (Iio 0))
    {t : ℝ} (ht : 0 < t) :
    timeOfNegativeCoordinate (coordinateOrderIso f hmono hbij) (f t) = t := by
  have hft : f t < 0 := hbij.1 ht
  rw [timeOfNegativeCoordinate_of_neg _ hft]
  change ((coordinateOrderIso f hmono hbij).symm
    (coordinateOrderIso f hmono hbij ⟨t, ht⟩) : Ioi (0 : ℝ)) = t
  rw [OrderIso.symm_apply_apply]

/-- Conversely, applying the forward coordinate to the inverse time recovers
every negative coordinate. -/
theorem coordinateOrderIso_timeOfNegativeCoordinate
    (f : ℝ → ℝ)
    (hmono : StrictMonoOn f (Ioi 0))
    (hbij : BijOn f (Ioi 0) (Iio 0))
    {x : ℝ} (hx : x < 0) :
    f (timeOfNegativeCoordinate (coordinateOrderIso f hmono hbij) x) = x := by
  rw [timeOfNegativeCoordinate_of_neg _ hx]
  change ((coordinateOrderIso f hmono hbij)
    ((coordinateOrderIso f hmono hbij).symm ⟨x, hx⟩) : Iio (0 : ℝ)) = x
  rw [OrderIso.apply_symm_apply]

/-- The cumulative string as a function of its negative spatial coordinate. -/
def stringMassCoordinate
    (κ : ℝ) (A3 : ℝ → ℝ) (e : Ioi (0 : ℝ) ≃o Iio (0 : ℝ))
    (x : ℝ) : ℝ :=
  stringMassPrimitive κ A3 (timeOfNegativeCoordinate e x)

/-- The coordinate definition gives exactly the manuscript cumulative identity. -/
theorem stringMassCoordinate_comp_eq
    (κ : ℝ) (A3 f : ℝ → ℝ)
    (hmono : StrictMonoOn f (Ioi 0))
    (hbij : BijOn f (Ioi 0) (Iio 0))
    {t : ℝ} (ht : 0 < t) :
    stringMassCoordinate κ A3 (coordinateOrderIso f hmono hbij) (f t) =
      stringMassPrimitive κ A3 t := by
  rw [stringMassCoordinate,
    timeOfNegativeCoordinate_coordinateOrderIso f hmono hbij ht]

/-- The inverse-function theorem differentiates the inverse time coordinate. -/
theorem hasDerivAt_timeOfNegativeCoordinate
    (f f' : ℝ → ℝ)
    (hmono : StrictMonoOn f (Ioi 0))
    (hbij : BijOn f (Ioi 0) (Iio 0))
    {t : ℝ} (ht : 0 < t)
    (hf : HasDerivAt f (f' t) t)
    (hf' : f' t ≠ 0) :
    HasDerivAt (timeOfNegativeCoordinate (coordinateOrderIso f hmono hbij))
      (f' t)⁻¹ (f t) := by
  let e := coordinateOrderIso f hmono hbij
  have hft : f t < 0 := hbij.1 ht
  have htime : timeOfNegativeCoordinate e (f t) = t :=
    timeOfNegativeCoordinate_coordinateOrderIso f hmono hbij ht
  apply HasDerivAt.of_local_left_inverse
    (continuousAt_timeOfNegativeCoordinate e hft)
  · simpa only [htime] using hf
  · exact hf'
  · filter_upwards [Iio_mem_nhds hft] with x hx
    exact coordinateOrderIso_timeOfNegativeCoordinate f hmono hbij hx

/-- The chain rule proves the density formula
`m'(ξ(t)) = Y(t)⁻²`; differentiability is not built into the definition. -/
theorem hasDerivAt_stringMassCoordinate_at
    {κ : ℝ} {A3 f : ℝ → ℝ}
    (hmono : StrictMonoOn f (Ioi 0))
    (hbij : BijOn f (Ioi 0) (Iio 0))
    {t : ℝ} (ht : 0 < t)
    (hf : HasDerivAt f (stringY κ A3 t) t)
    (hYne : stringY κ A3 t ≠ 0)
    (hint : IntervalIntegrable (fun s ↦ A3 s / κ) volume 0 t)
    (hmeas : StronglyMeasurableAtFilter (fun s ↦ A3 s / κ) (𝓝 t) volume)
    (hA3cont : ContinuousAt A3 t) :
    HasDerivAt
      (stringMassCoordinate κ A3 (coordinateOrderIso f hmono hbij))
      ((stringY κ A3 t)⁻¹ ^ 2) (f t) := by
  have htime := hasDerivAt_timeOfNegativeCoordinate
    f (stringY κ A3) hmono hbij ht hf hYne
  have hmass := hasDerivAt_stringMassPrimitive hint hmeas hA3cont
  have htimeEq := timeOfNegativeCoordinate_coordinateOrderIso f hmono hbij ht
  have hmassAtInverse : HasDerivAt (stringMassPrimitive κ A3)
      ((stringY κ A3 t)⁻¹)
      (timeOfNegativeCoordinate (coordinateOrderIso f hmono hbij) (f t)) := by
    simpa only [htimeEq] using hmass
  have hcomp := hmassAtInverse.comp (f t) htime
  convert hcomp using 1
  ring

/-- The source coordinate order isomorphism, with its monotonicity and
bijection proofs kept as theorem data rather than postulated fields. -/
noncomputable def stringXiOrderIso
    (κ : ℝ) (A2 A3 : ℝ → ℝ)
    (hmono : StrictMonoOn (stringXi κ A2 A3) (Ioi 0))
    (hbij : BijOn (stringXi κ A2 A3) (Ioi 0) (Iio 0)) :
    Ioi (0 : ℝ) ≃o Iio (0 : ℝ) :=
  coordinateOrderIso (stringXi κ A2 A3) hmono hbij

/-- The real-valued cumulative mass function on negative coordinates. -/
def stringXiMassCoordinate
    (κ : ℝ) (A2 A3 : ℝ → ℝ)
    (hmono : StrictMonoOn (stringXi κ A2 A3) (Ioi 0))
    (hbij : BijOn (stringXi κ A2 A3) (Ioi 0) (Iio 0))
    (x : ℝ) : ℝ :=
  stringMassCoordinate κ A3 (stringXiOrderIso κ A2 A3 hmono hbij) x

/-- Source-specialized cumulative identity
`m(ξ(t)) = ∫₀ᵗY(s)⁻¹ ds`. -/
theorem stringXiMassCoordinate_comp_eq
    (κ : ℝ) (A2 A3 : ℝ → ℝ)
    (hmono : StrictMonoOn (stringXi κ A2 A3) (Ioi 0))
    (hbij : BijOn (stringXi κ A2 A3) (Ioi 0) (Iio 0))
    {t : ℝ} (ht : 0 < t) :
    stringXiMassCoordinate κ A2 A3 hmono hbij (stringXi κ A2 A3 t) =
      stringMassPrimitive κ A3 t := by
  simpa only [stringXiMassCoordinate, stringXiOrderIso] using
    (stringMassCoordinate_comp_eq κ A3 (stringXi κ A2 A3) hmono hbij ht)

/-- Source-specialized density identity `m'(ξ(t))=Y(t)⁻²`. -/
theorem hasDerivAt_stringXiMassCoordinate
    {κ : ℝ} {A0 A2 A3 : ℝ → ℝ}
    (hmono : StrictMonoOn (stringXi κ A2 A3) (Ioi 0))
    (hbij : BijOn (stringXi κ A2 A3) (Ioi 0) (Iio 0))
    {t : ℝ} (ht : 0 < t) (hκ : 0 < κ)
    (hA2 : HasDerivAt A2 (A0 t * A2 t - 1) t)
    (hA3 : HasDerivAt A3 (A0 t * A3 t) t)
    (hA3pos : 0 < A3 t)
    (hint : IntervalIntegrable (fun s ↦ A3 s / κ) volume 0 t)
    (hmeas : StronglyMeasurableAtFilter (fun s ↦ A3 s / κ) (𝓝 t) volume) :
    HasDerivAt (stringXiMassCoordinate κ A2 A3 hmono hbij)
      ((stringY κ A3 t)⁻¹ ^ 2) (stringXi κ A2 A3 t) := by
  have hxi := hasDerivAt_stringXi κ A0 A2 A3 hA2 hA3 (ne_of_gt hA3pos)
  have hYne := ne_of_gt (stringY_pos hκ hA3pos)
  have hA3cont := hA3.continuousAt
  simpa only [stringXiMassCoordinate, stringXiOrderIso] using
    (hasDerivAt_stringMassCoordinate_at hmono hbij ht hxi hYne hint hmeas hA3cont)

/-- The same inverse-linear estimate as `-ξ ≍ t⁻¹`, now stated for `A₂Y`. -/
theorem stringA2Y_two_sided
    {κ c C : ℝ} {A0 A2 A3 : ℝ → ℝ} {t : ℝ}
    (hκ : 0 < κ) (hc : 0 < c) (hC : 0 < C) (ht : 0 < t)
    (hA2 : ∀ s : ℝ, 0 < s → HasDerivAt A2 (A0 s * A2 s - 1) s)
    (hA3 : ∀ s : ℝ, 0 < s → HasDerivAt A3 (A0 s * A3 s) s)
    (hprodTop : Tendsto (stringA2Y κ A2 A3) atTop (𝓝 0))
    (hbounds : ∀ s : ℝ, 0 < s → c * s ^ 2 ≤ A3 s ∧ A3 s ≤ C * s ^ 2) :
    (κ / C) * t⁻¹ ≤ stringA2Y κ A2 A3 t ∧
      stringA2Y κ A2 A3 t ≤ (κ / c) * t⁻¹ := by
  simpa only [stringXi, neg_neg] using
    (neg_stringXi_two_sided hκ hc hC ht hA2 hA3 hprodTop hbounds)

/-- The cumulative mass is cubic along the source time coordinate. -/
theorem stringXiMassCoordinate_two_sided
    {κ c C t : ℝ} {A2 A3 : ℝ → ℝ}
    (hmono : StrictMonoOn (stringXi κ A2 A3) (Ioi 0))
    (hbij : BijOn (stringXi κ A2 A3) (Ioi 0) (Iio 0))
    (hκ : 0 < κ) (ht : 0 < t)
    (hA3int : IntervalIntegrable (fun s ↦ A3 s / κ) volume 0 t)
    (hbounds : ∀ s : ℝ, 0 < s → c * s ^ 2 ≤ A3 s ∧ A3 s ≤ C * s ^ 2) :
    (c / κ) * (t ^ 3 / 3) ≤
        stringXiMassCoordinate κ A2 A3 hmono hbij (stringXi κ A2 A3 t) ∧
      stringXiMassCoordinate κ A2 A3 hmono hbij (stringXi κ A2 A3 t) ≤
        (C / κ) * (t ^ 3 / 3) := by
  rw [stringXiMassCoordinate_comp_eq κ A2 A3 hmono hbij ht]
  exact stringMassPrimitive_two_sided hκ ht hA3int hbounds

/-- The string-density coefficient is quartic in time, equivalently of order
`|ξ|⁻⁴` once combined with `-ξ ≍ t⁻¹`. -/
theorem inv_stringY_sq_two_sided
    {κ c C : ℝ} {A3 : ℝ → ℝ} {t : ℝ}
    (hκ : 0 < κ) (hc : 0 < c) (ht : 0 < t)
    (hlower : c * t ^ 2 ≤ A3 t) (hupper : A3 t ≤ C * t ^ 2) :
    (c / κ) ^ 2 * t ^ 4 ≤ (stringY κ A3 t)⁻¹ ^ 2 ∧
      (stringY κ A3 t)⁻¹ ^ 2 ≤ (C / κ) ^ 2 * t ^ 4 := by
  have hlowerDiv : (c * t ^ 2) / κ ≤ A3 t / κ :=
    (div_le_div_iff_of_pos_right hκ).2 hlower
  have hupperDiv : A3 t / κ ≤ (C * t ^ 2) / κ :=
    (div_le_div_iff_of_pos_right hκ).2 hupper
  have hlowerNonneg : 0 ≤ (c * t ^ 2) / κ := by positivity
  have hA3DivNonneg : 0 ≤ A3 t / κ := hlowerNonneg.trans hlowerDiv
  have hupperDivNonneg : 0 ≤ (C * t ^ 2) / κ := hA3DivNonneg.trans hupperDiv
  constructor
  · calc
      (c / κ) ^ 2 * t ^ 4 = ((c * t ^ 2) / κ) ^ 2 := by ring
      _ ≤ (A3 t / κ) ^ 2 := (sq_le_sq₀ hlowerNonneg hA3DivNonneg).2 hlowerDiv
      _ = (stringY κ A3 t)⁻¹ ^ 2 := by rw [inv_stringY]
  · calc
      (stringY κ A3 t)⁻¹ ^ 2 = (A3 t / κ) ^ 2 := by rw [inv_stringY]
      _ ≤ ((C * t ^ 2) / κ) ^ 2 :=
        (sq_le_sq₀ hA3DivNonneg hupperDivNonneg).2 hupperDiv
      _ = (C / κ) ^ 2 * t ^ 4 := by ring

/-- Direct coordinate form of `m'(ξ) ≍ |ξ|⁻⁴`, evaluated along the
bijection `t ↦ ξ(t)`. -/
theorem stringDensityCoefficient_vs_coordinate
    {κ c C : ℝ} {A0 A2 A3 : ℝ → ℝ} {t : ℝ}
    (hκ : 0 < κ) (hc : 0 < c) (hC : 0 < C) (ht : 0 < t)
    (hA2 : ∀ s : ℝ, 0 < s → HasDerivAt A2 (A0 s * A2 s - 1) s)
    (hA3 : ∀ s : ℝ, 0 < s → HasDerivAt A3 (A0 s * A3 s) s)
    (hprodTop : Tendsto (stringA2Y κ A2 A3) atTop (𝓝 0))
    (hbounds : ∀ s : ℝ, 0 < s → c * s ^ 2 ≤ A3 s ∧ A3 s ≤ C * s ^ 2) :
    (c / κ) ^ 2 *
          ((κ / C) / (-stringXi κ A2 A3 t)) ^ 4 ≤
        (stringY κ A3 t)⁻¹ ^ 2 ∧
      (stringY κ A3 t)⁻¹ ^ 2 ≤
        (C / κ) ^ 2 *
          ((κ / c) / (-stringXi κ A2 A3 t)) ^ 4 := by
  have hxi := neg_stringXi_two_sided hκ hc hC ht hA2 hA3 hprodTop hbounds
  have hbasePos : 0 < (κ / C) * t⁻¹ :=
    mul_pos (div_pos hκ hC) (inv_pos.mpr ht)
  have hxiPos : 0 < -stringXi κ A2 A3 t := hbasePos.trans_le hxi.1
  have hleftDiv : (κ / C) / t ≤ -stringXi κ A2 A3 t := by
    simpa only [div_eq_mul_inv] using hxi.1
  have hrightDiv : -stringXi κ A2 A3 t ≤ (κ / c) / t := by
    simpa only [div_eq_mul_inv] using hxi.2
  have htimeLower : (κ / C) / (-stringXi κ A2 A3 t) ≤ t := by
    apply (div_le_iff₀ hxiPos).2
    have hcross := (div_le_iff₀ ht).1 hleftDiv
    simpa only [mul_comm] using hcross
  have htimeUpper : t ≤ (κ / c) / (-stringXi κ A2 A3 t) := by
    apply (le_div_iff₀ hxiPos).2
    have hcross := (le_div_iff₀ ht).1 hrightDiv
    simpa only [mul_comm] using hcross
  have htimeLowerNonneg : 0 ≤ (κ / C) / (-stringXi κ A2 A3 t) := by
    positivity
  have htPowLower := pow_le_pow_left₀ htimeLowerNonneg htimeLower 4
  have htPowUpper := pow_le_pow_left₀ ht.le htimeUpper 4
  have hdensity := inv_stringY_sq_two_sided hκ hc ht
    (hbounds t ht).1 (hbounds t ht).2
  constructor
  · exact (mul_le_mul_of_nonneg_left htPowLower (sq_nonneg _)).trans hdensity.1
  · exact hdensity.2.trans (mul_le_mul_of_nonneg_left htPowUpper (sq_nonneg _))

end

end DerridaRetaux
