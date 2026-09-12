import DerridaRetaux.Analysis.ExpRemainder
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# The integrated third-order remainder

This file carries the pointwise estimates from `ExpRemainder` through the cutoff
argument used in `lem:remainder`.  The measure is restricted to the nonnegative
half-line, matching the spatial domain of the continuum density.  No fourth moment
is assumed: on the bounded part one power of `x` is traded for the cutoff, and on
the complement only the third-moment tail is used.
-/

set_option autoImplicit false

namespace DerridaRetaux

noncomputable section

open MeasureTheory Set

/-- The `r`th moment of a measure on the nonnegative half-line. -/
def positiveHalfLineMoment (r : ℕ) (μ : Measure ℝ) : ℝ :=
  ∫ x in Ici (0 : ℝ), x ^ r ∂μ

/-- The third-moment tail beyond a positive spatial cutoff. -/
def positiveHalfLineThirdMomentTail (μ : Measure ℝ) (δ : ℝ) : ℝ :=
  ∫ x in Ioi δ, x ^ 3 ∂μ

/-- The integral of the source remainder on the nonnegative half-line. -/
def integratedExpThirdRemainder (μ : Measure ℝ) (p : ℝ) : ℝ :=
  ∫ x in Ici (0 : ℝ), expThirdRemainder p x ∂μ

/-- The integral denoted by `Z(t,p)` in the source, with the time-dependent measure
left abstract. -/
def integratedLaplaceSecondGap (μ : Measure ℝ) (p : ℝ) : ℝ :=
  ∫ x in Ici (0 : ℝ), Real.exp (-(p * x)) - 1 + p * x ∂μ

/-- The integrated remainder is nonnegative, just as its pointwise integrand is. -/
theorem integratedExpThirdRemainder_nonneg (μ : Measure ℝ) {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ integratedExpThirdRemainder μ p := by
  unfold integratedExpThirdRemainder
  apply integral_nonneg_of_ae
  filter_upwards [self_mem_ae_restrict measurableSet_Ici] with x hx
  exact expThirdRemainder_nonneg hp hx

/-- A finite third moment makes the nonnegative exponential remainder integrable. -/
theorem integrableOn_expThirdRemainder_of_thirdMoment
    (μ : Measure ℝ) {p : ℝ} (hp : 0 ≤ p)
    (hthird : IntegrableOn (fun x : ℝ ↦ x ^ 3) (Ici 0) μ) :
    IntegrableOn (expThirdRemainder p) (Ici 0) μ := by
  have hdom : IntegrableOn (fun x : ℝ ↦ (p ^ 3 / 6) * x ^ 3) (Ici 0) μ :=
    hthird.const_mul (p ^ 3 / 6)
  refine hdom.mono' (continuous_expThirdRemainder p).aestronglyMeasurable ?_
  filter_upwards [self_mem_ae_restrict measurableSet_Ici] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (expThirdRemainder_nonneg hp hx)]
  exact expThirdRemainder_le_largeTail hp hx

/-- Exact integral Taylor decomposition.  The two explicit moment integrability
hypotheses are upstream properties of the limiting density, not remainder assumptions. -/
theorem integratedLaplaceSecondGap_eq
    (μ : Measure ℝ) {p : ℝ} (hp : 0 ≤ p)
    (hsecond : IntegrableOn (fun x : ℝ ↦ x ^ 2) (Ici 0) μ)
    (hthird : IntegrableOn (fun x : ℝ ↦ x ^ 3) (Ici 0) μ) :
    integratedLaplaceSecondGap μ p =
      (p ^ 2 / 2) * positiveHalfLineMoment 2 μ -
        (p ^ 3 / 6) * positiveHalfLineMoment 3 μ +
          integratedExpThirdRemainder μ p := by
  have hquadratic :
      IntegrableOn (fun x : ℝ ↦ (p ^ 2 / 2) * x ^ 2) (Ici 0) μ :=
    hsecond.const_mul (p ^ 2 / 2)
  have hcubic : IntegrableOn (fun x : ℝ ↦ (p ^ 3 / 6) * x ^ 3) (Ici 0) μ :=
    hthird.const_mul (p ^ 3 / 6)
  have hremainder := integrableOn_expThirdRemainder_of_thirdMoment μ hp hthird
  calc
    integratedLaplaceSecondGap μ p =
        ∫ x in Ici (0 : ℝ),
          (p ^ 2 / 2) * x ^ 2 - (p ^ 3 / 6) * x ^ 3 +
            expThirdRemainder p x ∂μ := by
      apply setIntegral_congr_fun measurableSet_Ici
      intro x _
      change Real.exp (-(p * x)) - 1 + p * x =
        (p ^ 2 / 2) * x ^ 2 - (p ^ 3 / 6) * x ^ 3 + expThirdRemainder p x
      rw [expThirdRemainder_eq]
      ring
    _ = (p ^ 2 / 2) * positiveHalfLineMoment 2 μ -
          (p ^ 3 / 6) * positiveHalfLineMoment 3 μ +
            integratedExpThirdRemainder μ p := by
      calc
        (∫ x in Ici (0 : ℝ),
            (p ^ 2 / 2) * x ^ 2 - (p ^ 3 / 6) * x ^ 3 +
              expThirdRemainder p x ∂μ) =
            (∫ x in Ici (0 : ℝ),
              (p ^ 2 / 2) * x ^ 2 - (p ^ 3 / 6) * x ^ 3 ∂μ) +
                ∫ x in Ici (0 : ℝ), expThirdRemainder p x ∂μ := by
          simpa only [Pi.add_apply, Pi.sub_apply] using
            integral_add (hquadratic.sub hcubic) hremainder
        _ = ((∫ x in Ici (0 : ℝ), (p ^ 2 / 2) * x ^ 2 ∂μ) -
              ∫ x in Ici (0 : ℝ), (p ^ 3 / 6) * x ^ 3 ∂μ) +
                ∫ x in Ici (0 : ℝ), expThirdRemainder p x ∂μ := by
          rw [integral_sub hquadratic hcubic]
        _ = (p ^ 2 / 2) * positiveHalfLineMoment 2 μ -
              (p ^ 3 / 6) * positiveHalfLineMoment 3 μ +
                integratedExpThirdRemainder μ p := by
          rw [integral_const_mul, integral_const_mul]
          rfl

/-- The integrated cutoff estimate from the proof of `lem:remainder`:

`∫ R_p dμ ≤ (p^4 δ / 24) A₃ + (p^3 / 6) Tail₃(δ)`.

It uses the fourth-order pointwise bound only on `[0, δ]`; globally it needs merely
integrability of the third moment. -/
theorem integratedExpThirdRemainder_le_cutoff
    (μ : Measure ℝ) {p δ : ℝ} (hp : 0 ≤ p) (hδ : 0 ≤ δ)
    (hthird : IntegrableOn (fun x : ℝ ↦ x ^ 3) (Ici 0) μ) :
    integratedExpThirdRemainder μ p ≤
      (p ^ 4 * δ / 24) * positiveHalfLineMoment 3 μ +
        (p ^ 3 / 6) * positiveHalfLineThirdMomentTail μ δ := by
  have htailSubset : Ioi δ ⊆ Ici (0 : ℝ) := by
    intro x hx
    exact hδ.trans hx.le
  have hremainder := integrableOn_expThirdRemainder_of_thirdMoment μ hp hthird
  have hremaSmall : IntegrableOn (expThirdRemainder p) (Icc 0 δ) μ :=
    hremainder.mono_set fun _ hx ↦ hx.1
  have hremaTail : IntegrableOn (expThirdRemainder p) (Ioi δ) μ :=
    hremainder.mono_set htailSubset
  have hthirdSmall : IntegrableOn (fun x : ℝ ↦ x ^ 3) (Icc 0 δ) μ :=
    hthird.mono_set fun _ hx ↦ hx.1
  have hthirdTail : IntegrableOn (fun x : ℝ ↦ x ^ 3) (Ioi δ) μ :=
    hthird.mono_set htailSubset
  have hsmallDom :
      IntegrableOn (fun x : ℝ ↦ (p ^ 4 * δ / 24) * x ^ 3) (Icc 0 δ) μ :=
    hthirdSmall.const_mul (p ^ 4 * δ / 24)
  have htailDom :
      IntegrableOn (fun x : ℝ ↦ (p ^ 3 / 6) * x ^ 3) (Ioi δ) μ :=
    hthirdTail.const_mul (p ^ 3 / 6)
  have hsmall :
      (∫ x in Icc (0 : ℝ) δ, expThirdRemainder p x ∂μ) ≤
        (p ^ 4 * δ / 24) * ∫ x in Icc (0 : ℝ) δ, x ^ 3 ∂μ := by
    calc
      (∫ x in Icc (0 : ℝ) δ, expThirdRemainder p x ∂μ) ≤
          ∫ x in Icc (0 : ℝ) δ, (p ^ 4 * δ / 24) * x ^ 3 ∂μ := by
        exact setIntegral_mono_on hremaSmall hsmallDom measurableSet_Icc fun x hx ↦
          expThirdRemainder_le_smallCutoff hp hx.1 hx.2
      _ = (p ^ 4 * δ / 24) * ∫ x in Icc (0 : ℝ) δ, x ^ 3 ∂μ := by
        rw [integral_const_mul]
  have htail :
      (∫ x in Ioi δ, expThirdRemainder p x ∂μ) ≤
        (p ^ 3 / 6) * ∫ x in Ioi δ, x ^ 3 ∂μ := by
    calc
      (∫ x in Ioi δ, expThirdRemainder p x ∂μ) ≤
          ∫ x in Ioi δ, (p ^ 3 / 6) * x ^ 3 ∂μ := by
        exact setIntegral_mono_on hremaTail htailDom measurableSet_Ioi fun x hx ↦
          expThirdRemainder_le_largeTail hp (htailSubset hx)
      _ = (p ^ 3 / 6) * ∫ x in Ioi δ, x ^ 3 ∂μ := by
        rw [integral_const_mul]
  have hthirdNonneg :
      0 ≤ᵐ[μ.restrict (Ici (0 : ℝ))] fun x : ℝ ↦ x ^ 3 := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ici] with x hx
    exact pow_nonneg hx 3
  have hsmallMoment :
      (∫ x in Icc (0 : ℝ) δ, x ^ 3 ∂μ) ≤ ∫ x in Ici (0 : ℝ), x ^ 3 ∂μ := by
    exact setIntegral_mono_set hthird hthirdNonneg
      (Filter.Eventually.of_forall fun _ hx ↦ hx.1)
  have hcoeffSmall : 0 ≤ p ^ 4 * δ / 24 := by positivity
  have hsmallFull :
      (∫ x in Icc (0 : ℝ) δ, expThirdRemainder p x ∂μ) ≤
        (p ^ 4 * δ / 24) * ∫ x in Ici (0 : ℝ), x ^ 3 ∂μ :=
    hsmall.trans (mul_le_mul_of_nonneg_left hsmallMoment hcoeffSmall)
  have hdisjoint : Disjoint (Icc (0 : ℝ) δ) (Ioi δ) :=
    (Iic_disjoint_Ioi le_rfl).mono (fun _ hx ↦ hx.2) le_rfl
  calc
    integratedExpThirdRemainder μ p =
        (∫ x in Icc (0 : ℝ) δ, expThirdRemainder p x ∂μ) +
          ∫ x in Ioi δ, expThirdRemainder p x ∂μ := by
      rw [integratedExpThirdRemainder, ← setIntegral_union hdisjoint measurableSet_Ioi
        hremaSmall hremaTail, Icc_union_Ioi_eq_Ici hδ]
    _ ≤ (p ^ 4 * δ / 24) * ∫ x in Ici (0 : ℝ), x ^ 3 ∂μ +
          (p ^ 3 / 6) * ∫ x in Ioi δ, x ^ 3 ∂μ :=
      add_le_add hsmallFull htail
    _ = (p ^ 4 * δ / 24) * positiveHalfLineMoment 3 μ +
          (p ^ 3 / 6) * positiveHalfLineThirdMomentTail μ δ := by
      rfl

/-- Source-shaped normalization of the cutoff estimate at `δ = √t`.  The premises
are precisely the upstream lower bound `c t² ≤ A₃(t)` and the quantitative tail
bound `Tail₃(t,δ) ≤ C t³ / δ`; the conclusion is the advertised `O_p(√t)` bound. -/
theorem normalizedIntegratedExpThirdRemainder_le_sqrt
    (μ : Measure ℝ) {p t c C : ℝ} (hp : 0 ≤ p) (ht : 0 < t)
    (hc : 0 < c) (hC : 0 ≤ C)
    (hthird : IntegrableOn (fun x : ℝ ↦ x ^ 3) (Ici 0) μ)
    (hA3Lower : c * t ^ 2 ≤ positiveHalfLineMoment 3 μ)
    (htail : positiveHalfLineThirdMomentTail μ (Real.sqrt t) ≤
      C * t ^ 3 / Real.sqrt t) :
    integratedExpThirdRemainder μ p / positiveHalfLineMoment 3 μ ≤
      (p ^ 4 / 24 + p ^ 3 * C / (6 * c)) * Real.sqrt t := by
  have hsqrtPos : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
  have hsqrtSq : (Real.sqrt t) ^ 2 = t := Real.sq_sqrt ht.le
  have hA3Pos : 0 < positiveHalfLineMoment 3 μ := by
    have hctPos : 0 < c * t ^ 2 := mul_pos hc (sq_pos_of_pos ht)
    exact hctPos.trans_le hA3Lower
  have htDivSqrt : t / Real.sqrt t = Real.sqrt t := by
    apply (div_eq_iff (ne_of_gt hsqrtPos)).2
    nlinarith
  have htCubeDivSqrt : t ^ 3 / Real.sqrt t = Real.sqrt t * t ^ 2 := by
    calc
      t ^ 3 / Real.sqrt t = t ^ 2 * (t / Real.sqrt t) := by ring
      _ = t ^ 2 * Real.sqrt t := by rw [htDivSqrt]
      _ = Real.sqrt t * t ^ 2 := by ring
  have htail' : positiveHalfLineThirdMomentTail μ (Real.sqrt t) ≤
      C * (Real.sqrt t * t ^ 2) := by
    calc
      positiveHalfLineThirdMomentTail μ (Real.sqrt t) ≤
          C * t ^ 3 / Real.sqrt t := htail
      _ = C * (t ^ 3 / Real.sqrt t) := by ring
      _ = C * (Real.sqrt t * t ^ 2) := by rw [htCubeDivSqrt]
  have hscaleNonneg : 0 ≤ C / c * Real.sqrt t := by positivity
  have hscaledLower := mul_le_mul_of_nonneg_left hA3Lower hscaleNonneg
  have hscaleIdentity :
      (C / c * Real.sqrt t) * (c * t ^ 2) = C * (Real.sqrt t * t ^ 2) := by
    field_simp
    all_goals ring
  rw [hscaleIdentity] at hscaledLower
  have htailByA3 : positiveHalfLineThirdMomentTail μ (Real.sqrt t) ≤
      (C / c * Real.sqrt t) * positiveHalfLineMoment 3 μ :=
    htail'.trans hscaledLower
  have htailCoeffNonneg : 0 ≤ p ^ 3 / 6 := by positivity
  have htailScaled := mul_le_mul_of_nonneg_left htailByA3 htailCoeffNonneg
  apply (div_le_iff₀ hA3Pos).2
  calc
    integratedExpThirdRemainder μ p ≤
        (p ^ 4 * Real.sqrt t / 24) * positiveHalfLineMoment 3 μ +
          (p ^ 3 / 6) * positiveHalfLineThirdMomentTail μ (Real.sqrt t) :=
      integratedExpThirdRemainder_le_cutoff μ hp (Real.sqrt_nonneg t) hthird
    _ ≤ (p ^ 4 * Real.sqrt t / 24) * positiveHalfLineMoment 3 μ +
          (p ^ 3 / 6) *
            ((C / c * Real.sqrt t) * positiveHalfLineMoment 3 μ) :=
      add_le_add_left htailScaled _
    _ = (p ^ 4 / 24 + p ^ 3 * C / (6 * c)) * Real.sqrt t *
          positiveHalfLineMoment 3 μ := by
      field_simp
      all_goals ring

/-- Absolute-value form of `normalizedIntegratedExpThirdRemainder_le_sqrt`.  Since
the Taylor remainder and `A₃` are positive, this is the literal quantitative
`O_p(√t)` estimate asserted in the source. -/
theorem abs_normalizedIntegratedExpThirdRemainder_le_sqrt
    (μ : Measure ℝ) {p t c C : ℝ} (hp : 0 ≤ p) (ht : 0 < t)
    (hc : 0 < c) (hC : 0 ≤ C)
    (hthird : IntegrableOn (fun x : ℝ ↦ x ^ 3) (Ici 0) μ)
    (hA3Lower : c * t ^ 2 ≤ positiveHalfLineMoment 3 μ)
    (htail : positiveHalfLineThirdMomentTail μ (Real.sqrt t) ≤
      C * t ^ 3 / Real.sqrt t) :
    |integratedExpThirdRemainder μ p / positiveHalfLineMoment 3 μ| ≤
      (p ^ 4 / 24 + p ^ 3 * C / (6 * c)) * Real.sqrt t := by
  have hA3Pos : 0 < positiveHalfLineMoment 3 μ := by
    have hctPos : 0 < c * t ^ 2 := mul_pos hc (sq_pos_of_pos ht)
    exact hctPos.trans_le hA3Lower
  rw [abs_of_nonneg (div_nonneg (integratedExpThirdRemainder_nonneg μ hp) hA3Pos.le)]
  exact normalizedIntegratedExpThirdRemainder_le_sqrt μ hp ht hc hC hthird hA3Lower htail

end

end DerridaRetaux
