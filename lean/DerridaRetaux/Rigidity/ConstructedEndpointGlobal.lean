import DerridaRetaux.Rigidity.ConstructedEntranceExpansion

set_option autoImplicit false

open Filter MeasureTheory Set Topology

namespace DerridaRetaux

noncomputable section

/-- The first spatial derivative identity for the constructed endpoint
solution, now stated at every negative coordinate. -/
theorem hasDerivAt_constructedEndpointSolution_of_neg
    {κ c C p x : ℝ} {A0 A2 A3 Z : ℝ → ℝ}
    (hκ : 0 < κ) (hc : 0 < c) (hC : 0 < C) (hp : p ≠ 0)
    (hA2 : ∀ s : ℝ, 0 < s → HasDerivAt A2 (A0 s * A2 s - 1) s)
    (hA3 : ∀ s : ℝ, 0 < s → HasDerivAt A3 (A0 s * A3 s) s)
    (hprodTop : Tendsto (stringA2Y κ A2 A3) atTop (𝓝 0))
    (hbounds : ∀ s : ℝ, 0 < s → c * s ^ 2 ≤ A3 s ∧ A3 s ≤ C * s ^ 2)
    (hZ : ∀ s : ℝ, 0 < s → HasDerivAt Z
      (A0 s * Z s + (1 / 2 : ℝ) * (Z s ^ 2 - p ^ 2)) s)
    (hInt : ∀ s : ℝ, 0 < s → IntervalIntegrable Z volume 0 s)
    (hMeas : ∀ s : ℝ, 0 < s → StronglyMeasurableAtFilter Z (𝓝 s) volume)
    (hCont : ∀ s : ℝ, 0 < s → ContinuousAt Z s)
    (hx : x < 0) :
    HasDerivAt
      (constructedEndpointSolution p (stringY κ A3) Z
        (stringXiOrderIso κ A2 A3
          (strictMonoOn_stringXi hκ hA2 hA3 (fun s hs ↦
            ((mul_pos hc (sq_pos_of_pos hs)).trans_le (hbounds s hs).1)))
          (stringXi_bijOn hκ hc hC hA2 hA3 hprodTop hbounds)))
      (constructedEndpointSlope Z
        (stringXiOrderIso κ A2 A3
          (strictMonoOn_stringXi hκ hA2 hA3 (fun s hs ↦
            ((mul_pos hc (sq_pos_of_pos hs)).trans_le (hbounds s hs).1)))
          (stringXi_bijOn hκ hc hC hA2 hA3 hprodTop hbounds)) x) x := by
  let hA3pos : ∀ s : ℝ, 0 < s → 0 < A3 s := fun s hs ↦
    (mul_pos hc (sq_pos_of_pos hs)).trans_le (hbounds s hs).1
  let hmono := strictMonoOn_stringXi hκ hA2 hA3 hA3pos
  let hbij := stringXi_bijOn hκ hc hC hA2 hA3 hprodTop hbounds
  let e := stringXiOrderIso κ A2 A3 hmono hbij
  let t := timeOfNegativeCoordinate e x
  have ht : 0 < t := timeOfNegativeCoordinate_pos e hx
  have hxt : stringXi κ A2 A3 t = x :=
    coordinateOrderIso_timeOfNegativeCoordinate
      (stringXi κ A2 A3) hmono hbij hx
  have hA3t : A3 t ≠ 0 := (hA3pos t ht).ne'
  have hxit := hasDerivAt_stringXi κ A0 A2 A3
    (hA2 t ht) (hA3 t ht) hA3t
  have hY := hasDerivAt_stringY κ A0 A3 (hA3 t ht) hA3t
  have hresult := hasDerivAt_constructedEndpointSolution_at
    p A0 (stringY κ A3) Z (stringXi κ A2 A3)
      hmono hbij ht hp hxit (stringY_pos hκ (hA3pos t ht)).ne'
      hY (hZ t ht) (hInt t ht) (hMeas t ht) (hCont t ht)
  simpa only [e, t, hxt] using hresult

/-- The second spatial derivative identity, likewise valid at every negative
coordinate. -/
theorem hasDerivAt_constructedEndpointSlope_of_neg
    {κ c C p x : ℝ} {A0 A2 A3 Z : ℝ → ℝ}
    (hκ : 0 < κ) (hc : 0 < c) (hC : 0 < C) (hp : p ≠ 0)
    (hA2 : ∀ s : ℝ, 0 < s → HasDerivAt A2 (A0 s * A2 s - 1) s)
    (hA3 : ∀ s : ℝ, 0 < s → HasDerivAt A3 (A0 s * A3 s) s)
    (hprodTop : Tendsto (stringA2Y κ A2 A3) atTop (𝓝 0))
    (hbounds : ∀ s : ℝ, 0 < s → c * s ^ 2 ≤ A3 s ∧ A3 s ≤ C * s ^ 2)
    (hInt : ∀ s : ℝ, 0 < s → IntervalIntegrable Z volume 0 s)
    (hMeas : ∀ s : ℝ, 0 < s → StronglyMeasurableAtFilter Z (𝓝 s) volume)
    (hCont : ∀ s : ℝ, 0 < s → ContinuousAt Z s)
    (hx : x < 0) :
    let hA3pos : ∀ s : ℝ, 0 < s → 0 < A3 s := fun s hs ↦
      (mul_pos hc (sq_pos_of_pos hs)).trans_le (hbounds s hs).1
    let hmono := strictMonoOn_stringXi hκ hA2 hA3 hA3pos
    let hbij := stringXi_bijOn hκ hc hC hA2 hA3 hprodTop hbounds
    let e := stringXiOrderIso κ A2 A3 hmono hbij
    HasDerivAt (constructedEndpointSlope Z e)
      ((p ^ 2 / 4) *
        (stringY κ A3 (timeOfNegativeCoordinate e x))⁻¹ ^ 2 *
          constructedEndpointSolution p (stringY κ A3) Z e x) x := by
  dsimp only
  let hA3pos : ∀ s : ℝ, 0 < s → 0 < A3 s := fun s hs ↦
    (mul_pos hc (sq_pos_of_pos hs)).trans_le (hbounds s hs).1
  let hmono := strictMonoOn_stringXi hκ hA2 hA3 hA3pos
  let hbij := stringXi_bijOn hκ hc hC hA2 hA3 hprodTop hbounds
  let e := stringXiOrderIso κ A2 A3 hmono hbij
  let t := timeOfNegativeCoordinate e x
  have ht : 0 < t := timeOfNegativeCoordinate_pos e hx
  have hxt : stringXi κ A2 A3 t = x :=
    coordinateOrderIso_timeOfNegativeCoordinate
      (stringXi κ A2 A3) hmono hbij hx
  have hA3t : A3 t ≠ 0 := (hA3pos t ht).ne'
  have hxit := hasDerivAt_stringXi κ A0 A2 A3
    (hA2 t ht) (hA3 t ht) hA3t
  have hresult := hasDerivAt_constructedEndpointSlope_at
    p (stringY κ A3) Z (stringXi κ A2 A3)
      hmono hbij ht hp hxit (stringY_pos hκ (hA3pos t ht)).ne'
      (hInt t ht) (hMeas t ht) (hCont t ht)
  simpa only [e, t, hxt] using hresult

end

end DerridaRetaux
