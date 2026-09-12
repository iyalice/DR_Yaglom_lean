import DerridaRetaux.ExternalSignatures

set_option autoImplicit false

open Filter

namespace DerridaRetaux

/-!
# Endpoint de-translation

These elementary lemmas isolate the endpoint argument that must remain internal after
the Kotani input returns equality only up to translation.
-/

/-- Boundary divergence makes the cumulative mass infinite at and to the right of
the declared endpoint. -/
theorem stringCumulative_eq_top_of_endpoint_le
    {M : EntranceString} {l x : ℝ} (hright : HasRightEnd M l) (hx : l ≤ x) :
    stringCumulative M x = ⊤ := by
  apply ENNReal.eq_top_of_forall_nnreal_le
  intro r
  have hlarge :
      ∀ᶠ y : ℝ in nhdsWithin M.endpoint (Set.Iio M.endpoint),
        (r : ENNReal) ≤ stringCumulative M y :=
    hright.2.eventually (Ici_mem_nhds (ENNReal.coe_lt_top : (r : ENNReal) < ⊤))
  have hinside :
      ∀ᶠ y : ℝ in nhdsWithin M.endpoint (Set.Iio M.endpoint),
        y ∈ Set.Iio M.endpoint :=
    self_mem_nhdsWithin
  obtain ⟨y, hyr, hyend⟩ := (hlarge.and hinside).exists
  have hyx : y ≤ x := by
    rw [hright.1] at hyend
    exact (le_of_lt hyend).trans hx
  exact hyr.trans (MeasureTheory.measure_mono (Set.Iic_subset_Iic.2 hyx))

/-- Below the common endpoint, entrance-type local finiteness rules out infinite
cumulative mass. -/
theorem stringCumulative_lt_top_of_lt_endpoint
    {M : EntranceString} {x : ℝ} (hentrance : IsEntranceType M)
    (hx : x < M.endpoint) :
    stringCumulative M x < ⊤ :=
  isEntranceType_locallyFiniteBelow hentrance hx

/-- Equality of cumulative strings after a shift has zero shift when both strings
have the same divergent finite right endpoint.  This matches the conclusion returned
by `KotaniCharacteristicFact`, without strengthening that published input to equality
of bundled measures. -/
theorem cumulative_translate_eq_with_common_rightEnd_imp_zero
    {M₁ M₂ : EntranceString} {c : ℝ}
    (hentrance₁ : IsEntranceType M₁) (hentrance₂ : IsEntranceType M₂)
    (hright₁ : HasRightEnd M₁ 0) (hright₂ : HasRightEnd M₂ 0)
    (htranslate : ∀ x : ℝ,
      stringCumulative M₁ (x + c) = stringCumulative M₂ x) :
    c = 0 := by
  rcases lt_trichotomy c 0 with hcneg | hczero | hcpos
  · have hxpos : 0 ≤ -c / 2 := by linarith
    have hxleft : -c / 2 + c < M₁.endpoint := by rw [hright₁.1]; linarith
    have hfinite := stringCumulative_lt_top_of_lt_endpoint hentrance₁ hxleft
    have htop := stringCumulative_eq_top_of_endpoint_le hright₂ hxpos
    have heq := htranslate (-c / 2)
    rw [htop] at heq
    exfalso
    exact (ne_of_lt hfinite) heq
  · exact hczero
  · have hxneg : -c / 2 < M₂.endpoint := by rw [hright₂.1]; linarith
    have hxright : 0 ≤ -c / 2 + c := by linarith
    have htop := stringCumulative_eq_top_of_endpoint_le hright₁ hxright
    have hfinite := stringCumulative_lt_top_of_lt_endpoint hentrance₂ hxneg
    have heq := htranslate (-c / 2)
    rw [htop] at heq
    exfalso
    exact (ne_of_lt hfinite) heq.symm

/-- The translation conclusion of the frozen Kotani specialization therefore reduces
to literal equality of cumulative strings. -/
theorem kotaniCharacteristicFact_imp_cumulative_eq
    (M₁ M₂ : EntranceString) (h₁ h₂ : ℝ → ℝ)
    (hentrance₁ : IsEntranceType M₁) (hentrance₂ : IsEntranceType M₂)
    (hsecond₁ : HasSecondEntranceMoment M₁)
    (hsecond₂ : HasSecondEntranceMoment M₂)
    (hright₁ : HasRightEnd M₁ 0) (hright₂ : HasRightEnd M₂ 0)
    (hcharacteristic₁ : ∀ lambda : ℝ, lambda < 0 →
      HasSingularCharacteristic M₁ lambda (h₁ lambda))
    (hcharacteristic₂ : ∀ lambda : ℝ, lambda < 0 →
      HasSingularCharacteristic M₂ lambda (h₂ lambda))
    (hequal : ∀ lambda : ℝ, lambda < 0 → h₁ lambda = h₂ lambda)
    (hfact : KotaniCharacteristicFact M₁ M₂ h₁ h₂ hentrance₁ hentrance₂
      hsecond₁ hsecond₂ hright₁ hright₂ hcharacteristic₁ hcharacteristic₂ hequal) :
    ∀ x : ℝ, stringCumulative M₁ x = stringCumulative M₂ x := by
  rcases hfact with ⟨c, htranslate⟩
  have hc := cumulative_translate_eq_with_common_rightEnd_imp_zero
    hentrance₁ hentrance₂ hright₁ hright₂ htranslate
  subst c
  simpa using htranslate

theorem translate_eq_with_common_rightEnd_imp_zero
    {M₁ M₂ : EntranceString} {c : ℝ}
    (h₁ : HasRightEnd M₁ 0) (h₂ : HasRightEnd M₂ 0)
    (htranslate : M₁.translate c = M₂) : c = 0 := by
  have hendpoint := congrArg EntranceString.endpoint htranslate
  rw [EntranceString.translate_endpoint, h₁.1, h₂.1] at hendpoint
  linarith

theorem translate_eq_with_common_rightEnd_imp_original_eq
    {M₁ M₂ : EntranceString} {c : ℝ}
    (h₁ : HasRightEnd M₁ 0) (h₂ : HasRightEnd M₂ 0)
    (htranslate : M₁.translate c = M₂) : M₁ = M₂ := by
  have hc := translate_eq_with_common_rightEnd_imp_zero h₁ h₂ htranslate
  subst c
  simpa [EntranceString.translate] using htranslate

end DerridaRetaux
