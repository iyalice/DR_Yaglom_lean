import DerridaRetaux.Rigidity.ConstructedStringMeasureDensity
import Mathlib.MeasureTheory.Function.L1Space.Integrable

set_option autoImplicit false

open Filter Set Topology MeasureTheory

namespace DerridaRetaux

noncomputable section

theorem integrableOn_constructedStringMass_of_density
    {κ c C xi : ℝ} {A0 A2 A3 g : ℝ → ℝ}
    (hκ : 0 < κ) (hc : 0 < c) (hC : 0 < C)
    (hA2 : ∀ s : ℝ, 0 < s → HasDerivAt A2 (A0 s * A2 s - 1) s)
    (hA3 : ∀ s : ℝ, 0 < s → HasDerivAt A3 (A0 s * A3 s) s)
    (hprodTop : Tendsto (stringA2Y κ A2 A3) atTop (𝓝 0))
    (hbounds : ∀ s : ℝ, 0 < s → c * s ^ 2 ≤ A3 s ∧ A3 s ≤ C * s ^ 2)
    (hmono : StrictMonoOn (stringXi κ A2 A3) (Ioi 0))
    (hbij : BijOn (stringXi κ A2 A3) (Ioi 0) (Iio 0))
    (hxi : xi < 0)
    (hg : IntegrableOn (fun x ↦ g x *
      constructedStringLebesgueDensity κ A2 A3 hmono hbij x) (Iic xi)) :
    IntegrableOn g (Iic xi) (constructedStringMass κ A2 A3) := by
  let rho := constructedStringLebesgueDensity κ A2 A3 hmono hbij
  have hA3pos : ∀ s : ℝ, 0 < s → 0 < A3 s := fun s hs ↦
    (mul_pos hc (sq_pos_of_pos hs)).trans_le (hbounds s hs).1
  have hrhoMeas : Measurable rho :=
    measurable_constructedStringLebesgueDensity hκ hA3 hA3pos hmono hbij
  rw [IntegrableOn,
    constructedStringMass_restrict_Iic_eq_withDensity hκ hc hC hA2 hA3
      hprodTop hbounds hmono hbij hxi,
    restrict_withDensity measurableSet_Iic]
  apply (integrable_withDensity_iff_integrable_smul₀'
    hrhoMeas.ennreal_ofReal.aemeasurable.restrict
    (Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)).2
  apply hg.congr
  filter_upwards [ae_restrict_mem measurableSet_Iic] with x hx
  have hrho : 0 ≤ rho x := sq_nonneg _
  simp only [ENNReal.toReal_ofReal hrho, smul_eq_mul]
  ring

theorem integral_constructedStringMass_eq_density
    {κ c C xi : ℝ} {A0 A2 A3 g : ℝ → ℝ}
    (hκ : 0 < κ) (hc : 0 < c) (hC : 0 < C)
    (hA2 : ∀ s : ℝ, 0 < s → HasDerivAt A2 (A0 s * A2 s - 1) s)
    (hA3 : ∀ s : ℝ, 0 < s → HasDerivAt A3 (A0 s * A3 s) s)
    (hprodTop : Tendsto (stringA2Y κ A2 A3) atTop (𝓝 0))
    (hbounds : ∀ s : ℝ, 0 < s → c * s ^ 2 ≤ A3 s ∧ A3 s ≤ C * s ^ 2)
    (hmono : StrictMonoOn (stringXi κ A2 A3) (Ioi 0))
    (hbij : BijOn (stringXi κ A2 A3) (Ioi 0) (Iio 0))
    (hxi : xi < 0) :
    ∫ x in Iic xi, g x ∂constructedStringMass κ A2 A3 =
      ∫ x in Iic xi, g x *
        constructedStringLebesgueDensity κ A2 A3 hmono hbij x := by
  let rho := constructedStringLebesgueDensity κ A2 A3 hmono hbij
  have hA3pos : ∀ s : ℝ, 0 < s → 0 < A3 s := fun s hs ↦
    (mul_pos hc (sq_pos_of_pos hs)).trans_le (hbounds s hs).1
  have hrhoMeas : Measurable rho :=
    measurable_constructedStringLebesgueDensity hκ hA3 hA3pos hmono hbij
  change (∫ x, g x ∂(constructedStringMass κ A2 A3).restrict (Iic xi)) = _
  rw [constructedStringMass_restrict_Iic_eq_withDensity hκ hc hC hA2 hA3
    hprodTop hbounds hmono hbij hxi]
  change (∫ x in Iic xi, g x ∂volume.withDensity
    (fun x ↦ ENNReal.ofReal (rho x))) = _
  rw [setIntegral_withDensity_eq_setIntegral_toReal_smul
    hrhoMeas.ennreal_ofReal
    (Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top) g measurableSet_Iic]
  apply integral_congr_ae
  filter_upwards with x
  have hrho : 0 ≤ rho x := sq_nonneg _
  simp only [ENNReal.toReal_ofReal hrho, smul_eq_mul]
  ring

end

end DerridaRetaux
