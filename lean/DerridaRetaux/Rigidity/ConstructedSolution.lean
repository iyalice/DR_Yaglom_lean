import DerridaRetaux.Rigidity.StringCoordinates
import DerridaRetaux.Analysis.IntegratedRemainder
import Mathlib.Tactic

/-!
# The constructed decreasing solution in time coordinates

This file formalizes the algebraic and differential part of source equations
`eq:Phi`, `eq:fODE`, and `eq:fpentrance`.  It intentionally works first with
the time-coordinate representative `f_p(ξ(t))`; transporting the derivative
to the inverse string coordinate and proving its canonical Wronskian relation
remain separate obligations.
-/

set_option autoImplicit false

open Filter MeasureTheory Set Topology

namespace DerridaRetaux

noncomputable section

/-- The exponential factor in source equation `eq:Phi`. -/
def constructedPhi (Z : ℝ → ℝ) (t : ℝ) : ℝ :=
  Real.exp (-(1 / 2 : ℝ) * ∫ s in (0 : ℝ)..t, Z s)

/-- The time-coordinate value `f_p(ξ(t))` from `eq:Phi`. -/
def constructedEndpointAtTime
    (p : ℝ) (Y Z : ℝ → ℝ) (t : ℝ) : ℝ :=
  (2 / p ^ 2) * Y t * Z t * constructedPhi Z t

theorem constructedPhi_pos (Z : ℝ → ℝ) (t : ℝ) :
    0 < constructedPhi Z t :=
  Real.exp_pos _

theorem constructedPhi_le_one
    (Z : ℝ → ℝ) (t : ℝ)
    (hIntegral : 0 ≤ ∫ s in (0 : ℝ)..t, Z s) :
    constructedPhi Z t ≤ 1 := by
  rw [constructedPhi, ← Real.exp_zero]
  exact Real.exp_le_exp.mpr (mul_nonpos_of_nonpos_of_nonneg (by norm_num) hIntegral)

/-- Differentiating the defining interval integral gives
`Phi' = -(1/2) Z Phi`. -/
theorem hasDerivAt_constructedPhi
    (Z : ℝ → ℝ) (t : ℝ)
    (hInt : IntervalIntegrable Z volume 0 t)
    (hMeas : StronglyMeasurableAtFilter Z (𝓝 t) volume)
    (hCont : ContinuousAt Z t) :
    HasDerivAt (constructedPhi Z)
      (-(1 / 2 : ℝ) * Z t * constructedPhi Z t) t := by
  have hintegral := intervalIntegral.integral_hasDerivAt_right hInt hMeas hCont
  have hscaled := hintegral.const_mul (-(1 / 2 : ℝ))
  have hexp := (Real.hasDerivAt_exp
    (-(1 / 2 : ℝ) * ∫ s in (0 : ℝ)..t, Z s)).comp t hscaled
  convert hexp using 1
  · simp only [constructedPhi]
    ring

/-- The cancellation in `eq:ZODE` differentiates the constructed endpoint
solution to `-Y Phi`.  This is the first identity in `eq:fODE`. -/
theorem hasDerivAt_constructedEndpointAtTime
    (p : ℝ) (A0 Y Z : ℝ → ℝ) (t : ℝ)
    (hp : p ≠ 0)
    (hY : HasDerivAt Y (-A0 t * Y t) t)
    (hZ : HasDerivAt Z
      (A0 t * Z t + (1 / 2 : ℝ) * (Z t ^ 2 - p ^ 2)) t)
    (hInt : IntervalIntegrable Z volume 0 t)
    (hMeas : StronglyMeasurableAtFilter Z (𝓝 t) volume)
    (hCont : ContinuousAt Z t) :
    HasDerivAt (constructedEndpointAtTime p Y Z)
      (-Y t * constructedPhi Z t) t := by
  have hPhi := hasDerivAt_constructedPhi Z t hInt hMeas hCont
  have hproduct := (hY.mul hZ).mul hPhi
  have hscaled := hproduct.const_mul (2 / p ^ 2)
  convert hscaled using 1
  · funext s
    simp only [constructedEndpointAtTime, div_eq_mul_inv]
    ring
  · field_simp [hp]
    ring

theorem constructedEndpointAtTime_nonneg
    (p : ℝ) (Y Z : ℝ → ℝ) (t : ℝ)
    (hY : 0 ≤ Y t) (hZ : 0 ≤ Z t) :
    0 ≤ constructedEndpointAtTime p Y Z t := by
  unfold constructedEndpointAtTime
  exact mul_nonneg (mul_nonneg (mul_nonneg (by positivity) hY) hZ)
    (constructedPhi_pos Z t).le

/-- The source estimate `f_p(ξ(t)) ≤ Y(t)A₂(t)`. -/
theorem constructedEndpointAtTime_le_Y_mul_A2
    (p : ℝ) (A2 Y Z : ℝ → ℝ) (t : ℝ)
    (hp : 0 < p)
    (hA2 : 0 ≤ A2 t) (hY : 0 ≤ Y t)
    (hZupper : Z t ≤ (p ^ 2 / 2) * A2 t)
    (hIntegral : 0 ≤ ∫ s in (0 : ℝ)..t, Z s) :
    constructedEndpointAtTime p Y Z t ≤ Y t * A2 t := by
  have hPhiNonneg : 0 ≤ constructedPhi Z t := (constructedPhi_pos Z t).le
  have hPhiOne : constructedPhi Z t ≤ 1 :=
    constructedPhi_le_one Z t hIntegral
  have hcoeff : 0 ≤ 2 / p ^ 2 := by positivity
  calc
    constructedEndpointAtTime p Y Z t =
        (2 / p ^ 2) * Y t * Z t * constructedPhi Z t := rfl
    _ ≤ (2 / p ^ 2) * Y t * ((p ^ 2 / 2) * A2 t) *
        constructedPhi Z t := by
      gcongr
    _ ≤ (2 / p ^ 2) * Y t * ((p ^ 2 / 2) * A2 t) * 1 := by
      gcongr
    _ = Y t * A2 t := by
      field_simp [hp.ne']
      ring

/-- The preceding bound and `A₂Y → 0` give the right-endpoint limit. -/
theorem tendsto_constructedEndpointAtTime_atTop_zero
    (p : ℝ) (A2 Y Z : ℝ → ℝ)
    (hNonneg : ∀ t : ℝ, 0 ≤ constructedEndpointAtTime p Y Z t)
    (hUpper : ∀ t : ℝ,
      constructedEndpointAtTime p Y Z t ≤ Y t * A2 t)
    (hA2Y : Tendsto (fun t : ℝ ↦ Y t * A2 t) atTop (𝓝 0)) :
    Tendsto (constructedEndpointAtTime p Y Z) atTop (𝓝 0) := by
  exact squeeze_zero' (Eventually.of_forall hNonneg)
    (Eventually.of_forall hUpper) hA2Y

/-- The constructed endpoint solution transported from positive time to the
negative string coordinate.  Outside the negative half-line its value is an
irrelevant extension; every source-facing theorem below is restricted to
`x < 0`. -/
def constructedEndpointSolution
    (p : ℝ) (Y Z : ℝ → ℝ) (e : Ioi (0 : ℝ) ≃o Iio (0 : ℝ))
    (x : ℝ) : ℝ :=
  constructedEndpointAtTime p Y Z (timeOfNegativeCoordinate e x)

/-- The candidate spatial derivative `f_p'`, again transported through the
inverse string coordinate. -/
def constructedEndpointSlope
    (Z : ℝ → ℝ) (e : Ioi (0 : ℝ) ≃o Iio (0 : ℝ))
    (x : ℝ) : ℝ :=
  -constructedPhi Z (timeOfNegativeCoordinate e x)

/-- The inverse of any order isomorphism `(0,∞) ≃ (-∞,0)` tends to positive
infinity as the negative coordinate approaches the finite right endpoint. -/
theorem tendsto_timeOfNegativeCoordinate_orderIso_nhdsLT_zero_atTop
    (e : Ioi (0 : ℝ) ≃o Iio (0 : ℝ)) :
    Tendsto (timeOfNegativeCoordinate e) (𝓝[<] (0 : ℝ)) atTop := by
  rw [tendsto_atTop]
  intro b
  let a : Ioi (0 : ℝ) := ⟨max b 1, by
    show 0 < max b 1
    exact lt_max_of_lt_right zero_lt_one⟩
  have hea : (e a : ℝ) < 0 := (e a).property
  filter_upwards [mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hea),
    self_mem_nhdsWithin] with x hx hxneg
  have horder : a < e.symm ⟨x, hxneg⟩ := by
    have hsub : e a < (⟨x, hxneg⟩ : Iio (0 : ℝ)) := hx
    simpa using e.symm.strictMono hsub
  rw [timeOfNegativeCoordinate_of_neg e hxneg]
  exact le_trans (le_max_left b 1) horder.le

/-- The time-coordinate endpoint estimate transports to the literal spatial
right-endpoint condition `f_p(x) → 0` as `x ↑ 0`. -/
theorem tendsto_constructedEndpointSolution_nhdsLT_zero
    (p : ℝ) (Y Z : ℝ → ℝ) (e : Ioi (0 : ℝ) ≃o Iio (0 : ℝ))
    (hEndpoint : Tendsto (constructedEndpointAtTime p Y Z) atTop (𝓝 0)) :
    Tendsto (constructedEndpointSolution p Y Z e) (𝓝[<] (0 : ℝ)) (𝓝 0) := by
  exact hEndpoint.comp
    (tendsto_timeOfNegativeCoordinate_orderIso_nhdsLT_zero_atTop e)

/-- The inverse-coordinate chain rule gives the first spatial identity in
source equation `eq:fODE`: `f_p'(ξ(t)) = -Phi(t,p)`. -/
theorem hasDerivAt_constructedEndpointSolution_at
    (p : ℝ) (A0 Y Z f : ℝ → ℝ)
    (hmono : StrictMonoOn f (Ioi 0))
    (hbij : BijOn f (Ioi 0) (Iio 0))
    {t : ℝ} (ht : 0 < t) (hp : p ≠ 0)
    (hf : HasDerivAt f (Y t) t) (hYne : Y t ≠ 0)
    (hY : HasDerivAt Y (-A0 t * Y t) t)
    (hZ : HasDerivAt Z
      (A0 t * Z t + (1 / 2 : ℝ) * (Z t ^ 2 - p ^ 2)) t)
    (hInt : IntervalIntegrable Z volume 0 t)
    (hMeas : StronglyMeasurableAtFilter Z (𝓝 t) volume)
    (hCont : ContinuousAt Z t) :
    HasDerivAt
      (constructedEndpointSolution p Y Z (coordinateOrderIso f hmono hbij))
      (constructedEndpointSlope Z (coordinateOrderIso f hmono hbij) (f t))
      (f t) := by
  have htime := hasDerivAt_timeOfNegativeCoordinate
    f Y hmono hbij ht hf hYne
  have hendpoint := hasDerivAt_constructedEndpointAtTime
    p A0 Y Z t hp hY hZ hInt hMeas hCont
  have htimeEq := timeOfNegativeCoordinate_coordinateOrderIso f hmono hbij ht
  have hendpointAtInverse : HasDerivAt (constructedEndpointAtTime p Y Z)
      (-Y t * constructedPhi Z t)
      (timeOfNegativeCoordinate (coordinateOrderIso f hmono hbij) (f t)) := by
    simpa only [htimeEq] using hendpoint
  have hcomp := hendpointAtInverse.comp (f t) htime
  convert hcomp using 1 <;>
    simp only [constructedEndpointSolution, constructedEndpointSlope, htimeEq]
  field_simp [hYne]
  ring

/-- Differentiating the transported slope gives the second spatial identity
in `eq:fODE`, evaluated at every coordinate `f(t)`. -/
theorem hasDerivAt_constructedEndpointSlope_at
    (p : ℝ) (Y Z f : ℝ → ℝ)
    (hmono : StrictMonoOn f (Ioi 0))
    (hbij : BijOn f (Ioi 0) (Iio 0))
    {t : ℝ} (ht : 0 < t) (hp : p ≠ 0)
    (hf : HasDerivAt f (Y t) t) (hYne : Y t ≠ 0)
    (hInt : IntervalIntegrable Z volume 0 t)
    (hMeas : StronglyMeasurableAtFilter Z (𝓝 t) volume)
    (hCont : ContinuousAt Z t) :
    HasDerivAt
      (constructedEndpointSlope Z (coordinateOrderIso f hmono hbij))
      ((p ^ 2 / 4) * (Y t)⁻¹ ^ 2 *
        constructedEndpointSolution p Y Z
          (coordinateOrderIso f hmono hbij) (f t))
      (f t) := by
  have htime := hasDerivAt_timeOfNegativeCoordinate
    f Y hmono hbij ht hf hYne
  have hslopeTime := (hasDerivAt_constructedPhi Z t hInt hMeas hCont).neg
  have htimeEq := timeOfNegativeCoordinate_coordinateOrderIso f hmono hbij ht
  have hslopeAtInverse : HasDerivAt (fun s ↦ -constructedPhi Z s)
      (-(-(1 / 2 : ℝ) * Z t * constructedPhi Z t))
      (timeOfNegativeCoordinate (coordinateOrderIso f hmono hbij) (f t)) := by
    simpa only [htimeEq] using hslopeTime
  have hcomp := hslopeAtInverse.comp (f t) htime
  convert hcomp using 1 <;>
    simp only [constructedEndpointSolution, constructedEndpointSlope, htimeEq,
      constructedEndpointAtTime]
  field_simp [hp, hYne]
  ring

/-- Exact algebra behind the entrance expansion in `eq:fpentrance`. -/
theorem constructedEndpointAtTime_add_coordinate_eq
    (p κ A2 A3 Y Z R xi Phi : ℝ)
    (hp : p ≠ 0)
    (hZ : Z = (p ^ 2 / 2) * A2 - (p ^ 3 / 6) * A3 + R)
    (hYA3 : Y * A3 = κ)
    (hxi : xi = -A2 * Y) :
    (2 / p ^ 2) * Y * Z * Phi + xi =
      Y * A2 * (Phi - 1) - (κ * p / 3) * Phi +
        (2 / p ^ 2) * Y * Phi * R := by
  rw [hZ, hxi, ← hYA3]
  field_simp [hp]
  ring

/-- The exact expansion plus the three source small terms yields the entrance
The constant `-κp/3`. -/
theorem tendsto_constructedEndpoint_add_coordinate_at_zero
    (p κ : ℝ) (F xi first Phi remainder : ℝ → ℝ)
    (hexpansion : ∀ t : ℝ, 0 < t →
      F t + xi t = first t - (κ * p / 3) * Phi t + remainder t)
    (hfirst : Tendsto first (𝓝[>] (0 : ℝ)) (𝓝 0))
    (hPhi : Tendsto Phi (𝓝[>] (0 : ℝ)) (𝓝 1))
    (hremainder : Tendsto remainder (𝓝[>] (0 : ℝ)) (𝓝 0)) :
    Tendsto (fun t : ℝ ↦ F t + xi t)
      (𝓝[>] (0 : ℝ)) (𝓝 (-κ * p / 3)) := by
  have hmiddle : Tendsto (fun t : ℝ ↦ -(κ * p / 3) * Phi t)
      (𝓝[>] (0 : ℝ)) (𝓝 (-(κ * p / 3) * 1)) :=
    tendsto_const_nhds.mul hPhi
  have hsum := (hfirst.add hmiddle).add hremainder
  have hevent :
      (fun t : ℝ ↦ first t + -(κ * p / 3) * Phi t + remainder t) =ᶠ[𝓝[>] (0 : ℝ)]
        (fun t : ℝ ↦ F t + xi t) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    rw [hexpansion t ht]
    ring
  have htarget := hsum.congr' hevent
  convert htarget using 1
  ring

end

end DerridaRetaux
