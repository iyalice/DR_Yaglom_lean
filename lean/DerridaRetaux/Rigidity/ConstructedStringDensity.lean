import DerridaRetaux.Rigidity.EndpointRepresentation
import DerridaRetaux.Rigidity.ConstructedEndpointAsymptotics

set_option autoImplicit false

open Filter Set Topology MeasureTheory

namespace DerridaRetaux

noncomputable section

def constructedStringLebesgueDensity
    (κ : ℝ) (A2 A3 : ℝ → ℝ)
    (hmono : StrictMonoOn (stringXi κ A2 A3) (Ioi 0))
    (hbij : BijOn (stringXi κ A2 A3) (Ioi 0) (Iio 0))
    (x : ℝ) : ℝ :=
  (stringY κ A3
    (timeOfNegativeCoordinate
      (stringXiOrderIso κ A2 A3 hmono hbij) x))⁻¹ ^ 2

theorem tendsto_stringMassPrimitive_nhdsGT_zero
    {κ c C : ℝ} {A0 A3 : ℝ → ℝ}
    (hκ : 0 < κ) (hc : 0 < c) (hC : 0 < C)
    (hA3 : ∀ s : ℝ, 0 < s → HasDerivAt A3 (A0 s * A3 s) s)
    (hA3pos : ∀ s : ℝ, 0 < s → 0 < A3 s)
    (hbounds : ∀ s : ℝ, 0 < s → c * s ^ 2 ≤ A3 s ∧ A3 s ≤ C * s ^ 2) :
    Tendsto (stringMassPrimitive κ A3) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hcube : Tendsto (fun t : ℝ ↦ (C / κ) * (t ^ 3 / 3)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hconst : Tendsto (fun _ : ℝ ↦ C / κ) (𝓝[>] (0 : ℝ)) (𝓝 (C / κ)) := tendsto_const_nhds
    have hid : Tendsto (fun t : ℝ ↦ t) (𝓝[>] (0 : ℝ)) (𝓝 0) := tendsto_id.mono_left inf_le_left
    have hcubic := (hid.pow 3).div_const (3 : ℝ)
    convert hconst.mul hcubic using 1 <;> ring
  apply squeeze_zero' _ _ hcube
  · filter_upwards [self_mem_nhdsWithin] with t ht
    have hint := intervalIntegrable_A3_div hκ hC ht hA3 hA3pos (fun s hs ↦ (hbounds s hs).2)
    rw [stringMassPrimitive, intervalIntegral.integral_of_le ht.le]
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    exact (div_pos (hA3pos s hs.1) hκ).le
  · filter_upwards [self_mem_nhdsWithin] with t ht
    have hint := intervalIntegrable_A3_div hκ hC ht hA3 hA3pos (fun s hs ↦ (hbounds s hs).2)
    exact (stringMassPrimitive_two_sided hκ ht hint hbounds).2

theorem tendsto_stringXiMassCoordinate_atBot_zero
    {κ c C : ℝ} {A0 A2 A3 : ℝ → ℝ}
    (hκ : 0 < κ) (hc : 0 < c) (hC : 0 < C)
    (hA2 : ∀ s : ℝ, 0 < s → HasDerivAt A2 (A0 s * A2 s - 1) s)
    (hA3 : ∀ s : ℝ, 0 < s → HasDerivAt A3 (A0 s * A3 s) s)
    (hprodTop : Tendsto (stringA2Y κ A2 A3) atTop (𝓝 0))
    (hbounds : ∀ s : ℝ, 0 < s → c * s ^ 2 ≤ A3 s ∧ A3 s ≤ C * s ^ 2)
    (hmono : StrictMonoOn (stringXi κ A2 A3) (Ioi 0))
    (hbij : BijOn (stringXi κ A2 A3) (Ioi 0) (Iio 0)) :
    Tendsto (stringXiMassCoordinate κ A2 A3 hmono hbij) atBot (𝓝 0) := by
  have hA3pos : ∀ s : ℝ, 0 < s → 0 < A3 s := fun s hs ↦
    (mul_pos hc (sq_pos_of_pos hs)).trans_le (hbounds s hs).1
  have hmass := tendsto_stringMassPrimitive_nhdsGT_zero hκ hc hC hA3
    hA3pos hbounds
  have hcomp := hmass.comp
    (tendsto_timeOfNegativeCoordinate_atBot_nhdsGT_zero
      (stringXiOrderIso κ A2 A3 hmono hbij))
  apply hcomp.congr'
  filter_upwards [eventually_lt_atBot (0 : ℝ)] with x hx
  let t := timeOfNegativeCoordinate
    (stringXiOrderIso κ A2 A3 hmono hbij) x
  have ht : 0 < t := timeOfNegativeCoordinate_pos _ hx
  have hxt : stringXi κ A2 A3 t = x :=
    coordinateOrderIso_timeOfNegativeCoordinate
      (stringXi κ A2 A3) hmono hbij hx
  calc
    stringMassPrimitive κ A3 (timeOfNegativeCoordinate (stringXiOrderIso κ A2 A3 hmono hbij) x) = stringMassPrimitive κ A3 t := rfl
    _ = stringXiMassCoordinate κ A2 A3 hmono hbij (stringXi κ A2 A3 t) :=
        (stringXiMassCoordinate_comp_eq κ A2 A3 hmono hbij ht).symm
    _ = stringXiMassCoordinate κ A2 A3 hmono hbij x := by rw [hxt]
theorem hasDerivAt_stringXiMassCoordinate_of_neg
    {κ C : ℝ} {A0 A2 A3 : ℝ → ℝ}
    (hκ : 0 < κ) (hC : 0 < C)
    (hA2 : ∀ s : ℝ, 0 < s → HasDerivAt A2 (A0 s * A2 s - 1) s)
    (hA3 : ∀ s : ℝ, 0 < s → HasDerivAt A3 (A0 s * A3 s) s)
    (hA3pos : ∀ s : ℝ, 0 < s → 0 < A3 s)
    (hupper : ∀ s : ℝ, 0 < s → A3 s ≤ C * s ^ 2)
    (hmono : StrictMonoOn (stringXi κ A2 A3) (Ioi 0))
    (hbij : BijOn (stringXi κ A2 A3) (Ioi 0) (Iio 0))
    {x : ℝ} (hx : x < 0) :
    HasDerivAt (stringXiMassCoordinate κ A2 A3 hmono hbij)
      (constructedStringLebesgueDensity κ A2 A3 hmono hbij x) x := by
  let e := stringXiOrderIso κ A2 A3 hmono hbij
  let t := timeOfNegativeCoordinate e x
  have ht : 0 < t := timeOfNegativeCoordinate_pos e hx
  have hxt : stringXi κ A2 A3 t = x :=
    coordinateOrderIso_timeOfNegativeCoordinate
      (stringXi κ A2 A3) hmono hbij hx
  have hint := intervalIntegrable_A3_div hκ hC ht hA3 hA3pos hupper
  have hderiv := hasDerivAt_stringXiMassCoordinate hmono hbij ht hκ
    (hA2 t ht) (hA3 t ht) (hA3pos t ht) hint
    (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioi
      (continuousOn_of_forall_continuousAt fun s hs ↦
        (hA3 s hs).continuousAt.div_const κ) t ht)
  simpa only [constructedStringLebesgueDensity, e, t, hxt] using hderiv

theorem integral_constructedStringLebesgueDensity_Iic
    {κ c C x : ℝ} {A0 A2 A3 : ℝ → ℝ}
    (hκ : 0 < κ) (hc : 0 < c) (hC : 0 < C)
    (hA2 : ∀ s : ℝ, 0 < s → HasDerivAt A2 (A0 s * A2 s - 1) s)
    (hA3 : ∀ s : ℝ, 0 < s → HasDerivAt A3 (A0 s * A3 s) s)
    (hprodTop : Tendsto (stringA2Y κ A2 A3) atTop (𝓝 0))
    (hbounds : ∀ s : ℝ, 0 < s → c * s ^ 2 ≤ A3 s ∧ A3 s ≤ C * s ^ 2)
    (hmono : StrictMonoOn (stringXi κ A2 A3) (Ioi 0))
    (hbij : BijOn (stringXi κ A2 A3) (Ioi 0) (Iio 0))
    (hx : x < 0) :
    IntegrableOn (constructedStringLebesgueDensity κ A2 A3 hmono hbij) (Iic x) ∧
      ∫ y in Iic x, constructedStringLebesgueDensity κ A2 A3 hmono hbij y =
        stringXiMassCoordinate κ A2 A3 hmono hbij x := by
  have hA3pos : ∀ s : ℝ, 0 < s → 0 < A3 s := fun s hs ↦
    (mul_pos hc (sq_pos_of_pos hs)).trans_le (hbounds s hs).1
  have hderiv : ∀ y ∈ Iic x,
      HasDerivAt (stringXiMassCoordinate κ A2 A3 hmono hbij)
        (constructedStringLebesgueDensity κ A2 A3 hmono hbij y) y := by
    intro y hy
    exact hasDerivAt_stringXiMassCoordinate_of_neg hκ hC hA2 hA3 hA3pos
      (fun s hs ↦ (hbounds s hs).2) hmono hbij (hy.trans_lt hx)
  have hnonneg : ∀ y ∈ Iio x,
      0 ≤ constructedStringLebesgueDensity κ A2 A3 hmono hbij y :=
    fun y hy ↦ sq_nonneg _
  have hlim := tendsto_stringXiMassCoordinate_atBot_zero hκ hc hC hA2 hA3
    hprodTop hbounds hmono hbij
  have hint := integrableOn_Iic_deriv_of_nonneg' hderiv hnonneg hlim
  refine ⟨hint, ?_⟩
  simpa using integral_Iic_of_hasDerivAt_of_tendsto' hderiv hint hlim

end

end DerridaRetaux
