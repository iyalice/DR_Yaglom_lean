import DerridaRetaux.Rigidity.ConstructedStringDensity

set_option autoImplicit false

open Filter Set Topology MeasureTheory

namespace DerridaRetaux

noncomputable section

theorem measurable_constructedStringLebesgueDensity
    {κ : ℝ} {A0 A2 A3 : ℝ → ℝ}
    (hκ : 0 < κ)
    (hA3 : ∀ s : ℝ, 0 < s → HasDerivAt A3 (A0 s * A3 s) s)
    (hA3pos : ∀ s : ℝ, 0 < s → 0 < A3 s)
    (hmono : StrictMonoOn (stringXi κ A2 A3) (Ioi 0))
    (hbij : BijOn (stringXi κ A2 A3) (Ioi 0) (Iio 0)) :
    Measurable (constructedStringLebesgueDensity κ A2 A3 hmono hbij) := by
  let e := stringXiOrderIso κ A2 A3 hmono hbij
  have hin : ContinuousOn
      (constructedStringLebesgueDensity κ A2 A3 hmono hbij) (Iio 0) := by
    intro x hx
    have ht : 0 < timeOfNegativeCoordinate e x :=
      timeOfNegativeCoordinate_pos e hx
    have htcont : ContinuousAt (timeOfNegativeCoordinate e) x :=
      continuousAt_timeOfNegativeCoordinate e hx
    have hYcont : ContinuousAt (stringY κ A3) (timeOfNegativeCoordinate e x) :=
      continuousAt_const.div (hA3 _ ht).continuousAt (ne_of_gt (hA3pos _ ht))
    unfold constructedStringLebesgueDensity
    exact ((hYcont.comp' htcont).inv₀
      (ne_of_gt (stringY_pos hκ (hA3pos _ ht)))).pow 2 |>.continuousWithinAt
  let c0 : ℝ := (stringY κ A3 0)⁻¹ ^ 2
  have hout : ContinuousOn (fun _ : ℝ ↦ c0) (Iio (0 : ℝ))ᶜ :=
    continuous_const.continuousOn
  have hpiece := hin.measurable_piecewise hout measurableSet_Iio
  convert hpiece using 1
  funext x
  by_cases hx : x < 0
  · simp [Set.piecewise, hx]
  · simp [Set.piecewise, constructedStringLebesgueDensity, timeOfNegativeCoordinate, hx, c0]

/-- On every negative left half-line, the pushed-forward string mass agrees
with its ordinary Lebesgue density in string coordinates. -/
theorem constructedStringMass_restrict_Iic_eq_withDensity
    {κ c C xi : ℝ} {A0 A2 A3 : ℝ → ℝ}
    (hκ : 0 < κ) (hc : 0 < c) (hC : 0 < C)
    (hA2 : ∀ s : ℝ, 0 < s → HasDerivAt A2 (A0 s * A2 s - 1) s)
    (hA3 : ∀ s : ℝ, 0 < s → HasDerivAt A3 (A0 s * A3 s) s)
    (hprodTop : Tendsto (stringA2Y κ A2 A3) atTop (𝓝 0))
    (hbounds : ∀ s : ℝ, 0 < s → c * s ^ 2 ≤ A3 s ∧ A3 s ≤ C * s ^ 2)
    (hmono : StrictMonoOn (stringXi κ A2 A3) (Ioi 0))
    (hbij : BijOn (stringXi κ A2 A3) (Ioi 0) (Iio 0))
    (hxi : xi < 0) :
    (constructedStringMass κ A2 A3).restrict (Iic xi) =
      (volume.withDensity fun x ↦ ENNReal.ofReal
        (constructedStringLebesgueDensity κ A2 A3 hmono hbij x)).restrict
          (Iic xi) := by
  let rho := constructedStringLebesgueDensity κ A2 A3 hmono hbij
  let μ := (constructedStringMass κ A2 A3).restrict (Iic xi)
  let ν := (volume.withDensity fun x ↦ ENNReal.ofReal (rho x)).restrict (Iic xi)
  have hrhoMeas : Measurable rho :=
    measurable_constructedStringLebesgueDensity hκ hA3 (fun s hs ↦ (mul_pos hc (sq_pos_of_pos hs)).trans_le (hbounds s hs).1) hmono hbij
  have hIic (y : ℝ) (hy : y < 0) :
      constructedStringMass κ A2 A3 (Iic y) =
        (volume.withDensity fun x ↦ ENNReal.ofReal (rho x)) (Iic y) := by
    obtain ⟨hint, hintegral⟩ := integral_constructedStringLebesgueDensity_Iic
      hκ hc hC hA2 hA3 hprodTop hbounds hmono hbij hy
    have hnonneg : 0 ≤ᵐ[volume.restrict (Iic y)] rho := by
      filter_upwards with z
      exact sq_nonneg _
    rw [withDensity_apply _ measurableSet_Iic]
    rw [← ofReal_integral_eq_lintegral_ofReal hint hnonneg]
    rw [hintegral]
    exact constructed_stringCumulative_of_neg hκ hC hA2 hA3
      (fun s hs ↦ (mul_pos hc (sq_pos_of_pos hs)).trans_le (hbounds s hs).1)
      (fun s hs ↦ (hbounds s hs).2) hmono hbij hy
  have hμfinite : μ Set.univ < ⊤ := by
    dsimp only [μ]
    rw [Measure.restrict_apply_univ]
    change stringCumulative (constructedEntranceString κ A2 A3) xi < ⊤
    rw [constructed_stringCumulative_of_neg hκ hC hA2 hA3
      (fun s hs ↦ (mul_pos hc (sq_pos_of_pos hs)).trans_le (hbounds s hs).1)
      (fun s hs ↦ (hbounds s hs).2) hmono hbij hxi]
    exact ENNReal.ofReal_lt_top
  letI : IsFiniteMeasure μ := ⟨hμfinite⟩
  apply Measure.ext_of_Iic μ ν
  intro y
  have hmin : min y xi < 0 := (min_le_right y xi).trans_lt hxi
  simp only [μ, ν, Measure.restrict_apply measurableSet_Iic, Iic_inter_Iic]
  exact hIic (min y xi) hmin

end

end DerridaRetaux
