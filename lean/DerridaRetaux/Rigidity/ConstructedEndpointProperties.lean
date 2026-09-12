import DerridaRetaux.Rigidity.ConstructedSolution
import Mathlib.Analysis.Calculus.Deriv.MeanValue

set_option autoImplicit false

open Filter MeasureTheory Set Topology

namespace DerridaRetaux

noncomputable section

/-!
# Qualitative properties of the constructed endpoint solution

This file upgrades the pointwise derivative formulas from `ConstructedSolution` to
the positivity and strict monotonicity needed by the Wronskian argument.
-/

/-- Positivity of the time-coordinate endpoint solution. -/
theorem constructedEndpointAtTime_pos
    {p t : ℝ} {Y Z : ℝ → ℝ} (hp : p ≠ 0)
    (hY : 0 < Y t) (hZ : 0 < Z t) :
    0 < constructedEndpointAtTime p Y Z t := by
  unfold constructedEndpointAtTime
  exact mul_pos (mul_pos (mul_pos (div_pos (by norm_num) (sq_pos_of_ne_zero hp)) hY) hZ)
    (constructedPhi_pos Z t)

/-- Positivity transported through the inverse string coordinate. -/
theorem constructedEndpointSolution_pos_of_neg
    {p : ℝ} {Y Z f : ℝ → ℝ}
    (hmono : StrictMonoOn f (Ioi 0))
    (hbij : BijOn f (Ioi 0) (Iio 0))
    (hp : p ≠ 0)
    (hY : ∀ t : ℝ, 0 < t → 0 < Y t)
    (hZ : ∀ t : ℝ, 0 < t → 0 < Z t)
    {x : ℝ} (hx : x < 0) :
    0 < constructedEndpointSolution p Y Z
      (coordinateOrderIso f hmono hbij) x := by
  let t := timeOfNegativeCoordinate (coordinateOrderIso f hmono hbij) x
  have ht : 0 < t := timeOfNegativeCoordinate_pos _ hx
  exact constructedEndpointAtTime_pos hp (hY t ht) (hZ t ht)

/-- The constructed endpoint solution is strictly decreasing on the negative
string half-line once the source differential identities hold at every positive
time. -/
theorem strictAntiOn_constructedEndpointSolution
    {p : ℝ} {A0 Y Z f : ℝ → ℝ}
    (hmono : StrictMonoOn f (Ioi 0))
    (hbij : BijOn f (Ioi 0) (Iio 0))
    (hp : p ≠ 0)
    (hf : ∀ t : ℝ, 0 < t → HasDerivAt f (Y t) t)
    (hYne : ∀ t : ℝ, 0 < t → Y t ≠ 0)
    (hY : ∀ t : ℝ, 0 < t → HasDerivAt Y (-A0 t * Y t) t)
    (hZ : ∀ t : ℝ, 0 < t → HasDerivAt Z
      (A0 t * Z t + (1 / 2 : ℝ) * (Z t ^ 2 - p ^ 2)) t)
    (hInt : ∀ t : ℝ, 0 < t → IntervalIntegrable Z volume 0 t)
    (hMeas : ∀ t : ℝ, 0 < t → StronglyMeasurableAtFilter Z (𝓝 t) volume)
    (hCont : ∀ t : ℝ, 0 < t → ContinuousAt Z t) :
    StrictAntiOn
      (constructedEndpointSolution p Y Z (coordinateOrderIso f hmono hbij))
      (Iio 0) := by
  let e := coordinateOrderIso f hmono hbij
  have hderiv : ∀ x ∈ Iio (0 : ℝ),
      HasDerivAt (constructedEndpointSolution p Y Z e)
        (constructedEndpointSlope Z e x) x := by
    intro x hx
    have hxneg : x < 0 := hx
    let t := timeOfNegativeCoordinate e x
    have ht : 0 < t := timeOfNegativeCoordinate_pos e hxneg
    have hpoint : f t = x := by
      exact coordinateOrderIso_timeOfNegativeCoordinate f hmono hbij hxneg
    have hresult := hasDerivAt_constructedEndpointSolution_at
      p A0 Y Z f hmono hbij ht hp (hf t ht) (hYne t ht)
        (hY t ht) (hZ t ht) (hInt t ht) (hMeas t ht) (hCont t ht)
    simpa only [e, hpoint] using hresult
  apply strictAntiOn_of_deriv_neg (convex_Iio 0)
  · exact continuousOn_of_forall_continuousAt fun x hx ↦
      (hderiv x hx).continuousAt
  · intro x hx
    have hxneg : x < 0 := by simpa using hx
    rw [(hderiv x hxneg).deriv]
    simp only [constructedEndpointSlope]
    exact neg_neg_of_pos (constructedPhi_pos Z (timeOfNegativeCoordinate e x))

end

end DerridaRetaux
