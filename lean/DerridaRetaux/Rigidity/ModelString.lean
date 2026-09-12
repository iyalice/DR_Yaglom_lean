import DerridaRetaux.Rigidity.EntranceStringBase
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Tactic

set_option autoImplicit false

open Filter MeasureTheory Set Topology
open scoped ENNReal

namespace DerridaRetaux

noncomputable section

/-!
# The explicit model string

This file constructs the Stieltjes measure in source equation `eq:modelstring`.
For `d > 0`, its density on the negative half-line is `d² / (-ξ)⁴`, so its
cumulative mass is `d² / (3(-ξ)³)` for `ξ < 0` and diverges at the endpoint
zero.  Endpoint divergence is stated directly with the correct one-sided
filters; no frozen right-boundary predicate is used.
-/

/-- Lebesgue density of the model string, extended by zero off `(-∞, 0)`. -/
def modelStringDensity (d x : ℝ) : ℝ :=
  if x < 0 then d ^ 2 / (-x) ^ 4 else 0

/-- Real-valued cumulative formula, used only at negative coordinates. -/
def modelStringCumulativeReal (d x : ℝ) : ℝ :=
  d ^ 2 / (3 * (-x) ^ 3)

/-- The explicit Stieltjes measure with density `d² / (-ξ)⁴`. -/
def modelStringMass (d : ℝ) : Measure ℝ :=
  volume.withDensity fun x ↦ ENNReal.ofReal (modelStringDensity d x)

/-- The explicit model string, with finite right endpoint zero. -/
def modelEntranceString (d : ℝ) : EntranceString where
  mass := modelStringMass d
  endpoint := 0

@[simp] theorem modelEntranceString_endpoint (d : ℝ) :
    (modelEntranceString d).endpoint = 0 :=
  rfl

theorem measurable_modelStringDensity (d : ℝ) :
    Measurable (modelStringDensity d) := by
  unfold modelStringDensity
  apply Measurable.ite measurableSet_Iio <;> fun_prop

theorem modelStringDensity_nonneg (d x : ℝ) :
    0 ≤ modelStringDensity d x := by
  by_cases hx : x < 0
  · simp only [modelStringDensity, hx, if_true]
    positivity
  · simp [modelStringDensity, hx]

theorem modelStringDensity_of_neg (d : ℝ) {x : ℝ} (hx : x < 0) :
    modelStringDensity d x = d ^ 2 / (-x) ^ 4 := by
  simp [modelStringDensity, hx]

theorem integrableOn_modelStringDensity_Iic (d : ℝ) {b : ℝ} (hb : b < 0) :
    IntegrableOn (modelStringDensity d) (Iic b) volume := by
  have hpow : IntegrableOn (fun y : ℝ ↦ y ^ (-4 : ℝ)) (Ioi (-b)) volume :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) (neg_pos.mpr hb)
  have hscaled : IntegrableOn (fun y : ℝ ↦ d ^ 2 * y ^ (-4 : ℝ))
      (Ioi (-b)) volume := by
    simpa only [smul_eq_mul] using hpow.const_mul (d ^ 2)
  have hscaled' : IntegrableOn (fun y : ℝ ↦ d ^ 2 / y ^ 4)
      (Ioi (-b)) volume := by
    refine hscaled.congr_fun ?_ measurableSet_Ioi
    intro y hy
    have hypos : 0 ≤ y := (lt_of_lt_of_le (neg_pos.mpr hb) hy.le).le
    change d ^ 2 * y ^ (-4 : ℝ) = d ^ 2 / y ^ 4
    rw [show (-4 : ℝ) = -(4 : ℝ) by norm_num, Real.rpow_neg hypos]
    have hnat : y ^ (4 : ℝ) = y ^ (4 : ℕ) := Real.rpow_natCast y 4
    rw [hnat]
    simp only [div_eq_mul_inv]
  have hneg : IntegrableOn (fun x : ℝ ↦ d ^ 2 / (-x) ^ 4)
      (Iic b) volume := by
    rw [← Measure.map_neg_eq_self (volume : Measure ℝ)]
    let emb : MeasurableEmbedding (fun x : ℝ ↦ -x) :=
      (Homeomorph.neg ℝ).measurableEmbedding
    apply (emb.integrableOn_map_iff).2
    simpa only [Function.comp_def, neg_neg, neg_preimage, neg_Iic,
      integrableOn_Ici_iff_integrableOn_Ioi] using hscaled'
  refine hneg.congr_fun ?_ measurableSet_Iic
  intro x hx
  have hxneg : x < 0 := lt_of_le_of_lt hx hb
  simp [modelStringDensity, hxneg]

theorem hasDerivAt_modelStringCumulativeReal
    (d : ℝ) {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (modelStringCumulativeReal d)
      (d ^ 2 / (-x) ^ 4) x := by
  have hneg : HasDerivAt (fun y : ℝ ↦ -y) (-1) x :=
    (hasDerivAt_id x).neg
  have hden : HasDerivAt (fun y : ℝ ↦ 3 * (-y) ^ 3)
      (3 * (3 * (-x) ^ 2 * (-1))) x :=
    by
      convert (hasDerivAt_const x 3).mul (hneg.pow 3) using 1
      ring
  have hdenne : 3 * (-x) ^ 3 ≠ 0 := by
    exact mul_ne_zero (by norm_num) (pow_ne_zero 3 (neg_ne_zero.mpr hx))
  have hquot := (hasDerivAt_const x (d ^ 2)).div hden hdenne
  convert hquot using 1
  field_simp [hx]
  ring

theorem tendsto_modelStringCumulativeReal_atBot (d : ℝ) :
    Tendsto (modelStringCumulativeReal d) atBot (𝓝 0) := by
  have hneg : Tendsto (fun x : ℝ ↦ -x) atBot atTop :=
    tendsto_neg_atBot_atTop
  have hpow : Tendsto (fun x : ℝ ↦ (-x) ^ 3) atBot atTop :=
    (tendsto_pow_atTop (by norm_num)).comp hneg
  have hinv : Tendsto (fun x : ℝ ↦ ((-x) ^ 3)⁻¹) atBot (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hpow
  have hmul : Tendsto (fun x : ℝ ↦ (d ^ 2 / 3) * ((-x) ^ 3)⁻¹)
      atBot (𝓝 ((d ^ 2 / 3) * 0)) :=
    tendsto_const_nhds.mul hinv
  have heq : modelStringCumulativeReal d =
      fun x : ℝ ↦ (d ^ 2 / 3) * ((-x) ^ 3)⁻¹ := by
    funext x
    simp only [modelStringCumulativeReal, div_eq_mul_inv, mul_inv_rev]
    ring
  rw [heq]
  simpa using hmul

theorem integral_modelStringDensity_Iic
    (d : ℝ) {b : ℝ} (hb : b < 0) :
    ∫ x in Iic b, modelStringDensity d x = modelStringCumulativeReal d b := by
  have hderiv : ∀ x ∈ Iic b,
      HasDerivAt (modelStringCumulativeReal d) (modelStringDensity d x) x := by
    intro x hx
    have hxneg : x < 0 := lt_of_le_of_lt hx hb
    rw [modelStringDensity_of_neg d hxneg]
    exact hasDerivAt_modelStringCumulativeReal d (ne_of_lt hxneg)
  have h := integral_Iic_of_hasDerivAt_of_tendsto' hderiv
    (integrableOn_modelStringDensity_Iic d hb)
    (tendsto_modelStringCumulativeReal_atBot d)
  simpa using h

theorem model_stringCumulative_of_neg
    (d : ℝ) {b : ℝ} (hb : b < 0) :
    stringCumulative (modelEntranceString d) b =
      ENNReal.ofReal (modelStringCumulativeReal d b) := by
  have hint := integrableOn_modelStringDensity_Iic d hb
  have hnonneg : 0 ≤ᵐ[volume.restrict (Iic b)] modelStringDensity d :=
    Filter.Eventually.of_forall fun x ↦ modelStringDensity_nonneg d x
  rw [stringCumulative, modelEntranceString, modelStringMass,
    withDensity_apply _ measurableSet_Iic]
  calc
    (∫⁻ x in Iic b, ENNReal.ofReal (modelStringDensity d x) ∂volume) =
        ENNReal.ofReal (∫ x in Iic b, modelStringDensity d x ∂volume) :=
      (ofReal_integral_eq_lintegral_ofReal hint hnonneg).symm
    _ = ENNReal.ofReal (modelStringCumulativeReal d b) := by
      rw [integral_modelStringDensity_Iic d hb]

theorem modelStringCumulativeReal_pos
    {d x : ℝ} (hd : d ≠ 0) (hx : x < 0) :
    0 < modelStringCumulativeReal d x := by
  unfold modelStringCumulativeReal
  exact div_pos (sq_pos_of_ne_zero hd)
    (mul_pos (by norm_num) (pow_pos (neg_pos.mpr hx) 3))

theorem tendsto_modelStringCumulativeReal_nhdsLT_zero_atTop
    {d : ℝ} (hd : d ≠ 0) :
    Tendsto (modelStringCumulativeReal d) (𝓝[<] (0 : ℝ)) atTop := by
  have hneg : Tendsto (fun x : ℝ ↦ -x) (𝓝[<] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    simpa using (tendsto_neg_nhdsLT (a := (0 : ℝ)))
  have hinv : Tendsto (fun x : ℝ ↦ (-x)⁻¹) (𝓝[<] (0 : ℝ)) atTop :=
    tendsto_inv_nhdsGT_zero.comp hneg
  have hpow : Tendsto (fun x : ℝ ↦ ((-x)⁻¹) ^ 3)
      (𝓝[<] (0 : ℝ)) atTop :=
    (tendsto_pow_atTop (by norm_num)).comp hinv
  have hcoef : 0 < d ^ 2 / 3 :=
    div_pos (sq_pos_of_ne_zero hd) (by norm_num)
  have hmul := tendsto_const_nhds.pos_mul_atTop hcoef hpow
  convert hmul using 1
  ext x
  simp only [modelStringCumulativeReal]
  field_simp

theorem tendsto_model_stringCumulative_nhdsLT_zero_top
    {d : ℝ} (hd : d ≠ 0) :
    Tendsto (stringCumulative (modelEntranceString d))
      (𝓝[<] (0 : ℝ)) (𝓝 ⊤) := by
  have hlim := ENNReal.tendsto_ofReal_atTop.comp
    (tendsto_modelStringCumulativeReal_nhdsLT_zero_atTop hd)
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact (model_stringCumulative_of_neg d hx).symm

/-- Integrability of every inverse power needed for the first two entrance moments. -/
theorem integrableOn_modelStringInvPow_Iic
    (d : ℝ) {b : ℝ} (hb : b < 0) {n : ℕ} (hn : 1 < n) :
    IntegrableOn (fun x : ℝ ↦ d ^ 2 / (-x) ^ n) (Iic b) volume := by
  have hexp : -(n : ℝ) < -1 := by
    have hcast : (1 : ℝ) < n := by exact_mod_cast hn
    linarith
  have hpow : IntegrableOn (fun y : ℝ ↦ y ^ (-(n : ℝ))) (Ioi (-b)) volume :=
    integrableOn_Ioi_rpow_of_lt hexp (neg_pos.mpr hb)
  have hscaled : IntegrableOn (fun y : ℝ ↦ d ^ 2 * y ^ (-(n : ℝ)))
      (Ioi (-b)) volume := by
    simpa only [smul_eq_mul] using hpow.const_mul (d ^ 2)
  have hscaled' : IntegrableOn (fun y : ℝ ↦ d ^ 2 / y ^ n)
      (Ioi (-b)) volume := by
    refine hscaled.congr_fun ?_ measurableSet_Ioi
    intro y hy
    have hypos : 0 ≤ y := (lt_of_lt_of_le (neg_pos.mpr hb) hy.le).le
    change d ^ 2 * y ^ (-(n : ℝ)) = d ^ 2 / y ^ n
    rw [Real.rpow_neg hypos]
    have hnat : y ^ (n : ℝ) = y ^ n := Real.rpow_natCast y n
    rw [hnat]
    simp only [div_eq_mul_inv]
  rw [← Measure.map_neg_eq_self (volume : Measure ℝ)]
  let emb : MeasurableEmbedding (fun x : ℝ ↦ -x) :=
    (Homeomorph.neg ℝ).measurableEmbedding
  apply (emb.integrableOn_map_iff).2
  simpa only [Function.comp_def, neg_neg, neg_preimage, neg_Iic,
    integrableOn_Ici_iff_integrableOn_Ioi] using hscaled'

theorem integrableOn_modelStringMass_iff
    (d : ℝ) (g : ℝ → ℝ) (s : Set ℝ) (hs : MeasurableSet s) :
    IntegrableOn g s (modelStringMass d) ↔
      IntegrableOn (fun x ↦ g x * modelStringDensity d x) s volume := by
  rw [IntegrableOn, modelStringMass, restrict_withDensity hs]
  have hmeas : Measurable (fun x ↦ ENNReal.ofReal (modelStringDensity d x)) :=
    (measurable_modelStringDensity d).ennreal_ofReal
  have hfinite : ∀ᵐ x ∂volume.restrict s,
      ENNReal.ofReal (modelStringDensity d x) < ⊤ :=
    Filter.Eventually.of_forall fun x ↦ ENNReal.ofReal_lt_top
  rw [integrable_withDensity_iff hmeas hfinite]
  apply integrable_congr
  filter_upwards with x
  rw [ENNReal.toReal_ofReal (modelStringDensity_nonneg d x)]

theorem modelEntranceString_hasFirstEntranceMomentAt
    (d : ℝ) {b : ℝ} (hb : b < 0) :
    HasFirstEntranceMomentAt (modelEntranceString d) b := by
  rw [HasFirstEntranceMomentAt, modelEntranceString,
    integrableOn_modelStringMass_iff d (fun x : ℝ ↦ |x|) (Iic b) measurableSet_Iic]
  have hint := integrableOn_modelStringInvPow_Iic d hb (n := 3) (by norm_num)
  refine hint.congr_fun ?_ measurableSet_Iic
  intro x hx
  have hxneg : x < 0 := lt_of_le_of_lt hx hb
  change d ^ 2 / (-x) ^ 3 = |x| * modelStringDensity d x
  rw [modelStringDensity_of_neg d hxneg, abs_of_neg hxneg]
  field_simp [ne_of_gt (neg_pos.mpr hxneg)]
  ring

theorem modelEntranceString_hasSecondEntranceMomentAt
    (d : ℝ) {b : ℝ} (hb : b < 0) :
    HasSecondEntranceMomentAt (modelEntranceString d) b := by
  rw [HasSecondEntranceMomentAt, modelEntranceString,
    integrableOn_modelStringMass_iff d (fun x : ℝ ↦ x ^ 2) (Iic b) measurableSet_Iic]
  have hint := integrableOn_modelStringInvPow_Iic d hb (n := 2) (by norm_num)
  refine hint.congr_fun ?_ measurableSet_Iic
  intro x hx
  have hxneg : x < 0 := lt_of_le_of_lt hx hb
  change d ^ 2 / (-x) ^ 2 = x ^ 2 * modelStringDensity d x
  rw [modelStringDensity_of_neg d hxneg]
  field_simp [ne_of_lt hxneg, ne_of_gt (neg_pos.mpr hxneg)]
  ring

theorem modelStringMass_Ioi_zero (d : ℝ) :
    modelStringMass d (Ioi 0) = 0 := by
  rw [modelStringMass, withDensity_apply _ measurableSet_Ioi]
  calc
    (∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal (modelStringDensity d x) ∂volume) =
        ∫⁻ _x in Ioi (0 : ℝ), (0 : ENNReal) ∂volume := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hxnonneg : 0 ≤ x := le_of_lt hx
      simp [modelStringDensity, not_lt_of_ge hxnonneg]
    _ = 0 := by simp

theorem model_stringCumulative_zero_eq_top
    {d : ℝ} (hd : d ≠ 0) :
    stringCumulative (modelEntranceString d) 0 = ⊤ := by
  apply top_unique
  apply le_of_tendsto (tendsto_model_stringCumulative_nhdsLT_zero_top hd)
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact measure_mono (Iic_subset_Iic.mpr hx.le)

theorem model_stringCumulative_of_nonneg
    {d x : ℝ} (hd : d ≠ 0) (hx : 0 ≤ x) :
    stringCumulative (modelEntranceString d) x = ⊤ := by
  apply top_unique
  rw [← model_stringCumulative_zero_eq_top hd]
  exact measure_mono (Iic_subset_Iic.mpr hx)

theorem modelStringMass_ne_zero
    {d : ℝ} (hd : d ≠ 0) :
    modelStringMass d ≠ 0 := by
  intro hzero
  have hpos : 0 < stringCumulative (modelEntranceString d) (-1) := by
    rw [model_stringCumulative_of_neg d (by norm_num)]
    exact ENNReal.ofReal_pos.mpr
      (modelStringCumulativeReal_pos hd (by norm_num))
  rw [stringCumulative, modelEntranceString, hzero] at hpos
  simp at hpos

theorem modelEntranceString_isEntranceType
    {d : ℝ} (hd : d ≠ 0) :
    IsEntranceType (modelEntranceString d) := by
  refine ⟨modelStringMass_ne_zero hd, ?_, ?_, ?_⟩
  · intro b hb
    change stringCumulative (modelEntranceString d) b < ⊤
    rw [model_stringCumulative_of_neg d (by simpa using hb)]
    exact ENNReal.ofReal_lt_top
  · simpa [modelEntranceString] using modelStringMass_Ioi_zero d
  · refine ⟨-1, by norm_num, ?_, modelEntranceString_hasFirstEntranceMomentAt d
      (by norm_num)⟩
    change 0 < stringCumulative (modelEntranceString d) (-1)
    rw [model_stringCumulative_of_neg d (by norm_num)]
    exact ENNReal.ofReal_pos.mpr
      (modelStringCumulativeReal_pos hd (by norm_num))

theorem modelEntranceString_hasSecondEntranceMoment (d : ℝ) :
    HasSecondEntranceMoment (modelEntranceString d) := by
  intro b hb
  exact modelEntranceString_hasSecondEntranceMomentAt d (by simpa using hb)

/-- Endpoint zero and divergence of cumulative mass from the left. -/
theorem modelEntranceString_correctRightEnd
    {d : ℝ} (hd : d ≠ 0) :
    (modelEntranceString d).endpoint = 0 ∧
      Tendsto (stringCumulative (modelEntranceString d))
        (nhdsWithin (modelEntranceString d).endpoint
          (Iio (modelEntranceString d).endpoint)) (𝓝 ⊤) := by
  simpa using tendsto_model_stringCumulative_nhdsLT_zero_top hd

/-- The model string has the manuscript's divergent right endpoint. -/
theorem modelEntranceString_hasRightEnd_zero {d : ℝ} (hd : d ≠ 0) :
    HasRightEnd (modelEntranceString d) 0 := by
  simpa [HasRightEnd, NoRightBoundaryAmbiguity] using
    modelEntranceString_correctRightEnd hd

/-- The decreasing endpoint solution displayed after `eq:modelstring`. -/
def modelStringEndpointSolution (d p x : ℝ) : ℝ :=
  (-x) * Real.exp (d * p / (2 * x))

/-- Its explicit first derivative. -/
def modelStringEndpointSolutionDeriv (d p x : ℝ) : ℝ :=
  Real.exp (d * p / (2 * x)) * (d * p / (2 * x) - 1)

/-- Its explicit second derivative. -/
def modelStringEndpointSolutionSecond (d p x : ℝ) : ℝ :=
  -(d * p / 2) ^ 2 / x ^ 3 * Real.exp (d * p / (2 * x))

theorem hasDerivAt_modelStringExponent
    (d p : ℝ) {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun y : ℝ ↦ d * p / (2 * y))
      (-d * p / (2 * x ^ 2)) x := by
  have hden : HasDerivAt (fun y : ℝ ↦ 2 * y) 2 x := by
    convert (hasDerivAt_const x 2).mul (hasDerivAt_id x) using 1
    ring
  have hdenne : 2 * x ≠ 0 := mul_ne_zero (by norm_num) hx
  have hquot := (hasDerivAt_const x (d * p)).div hden hdenne
  convert hquot using 1
  field_simp [hx]
  ring

theorem hasDerivAt_modelStringEndpointSolution
    (d p : ℝ) {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (modelStringEndpointSolution d p)
      (modelStringEndpointSolutionDeriv d p x) x := by
  have hinner := hasDerivAt_modelStringExponent d p hx
  have hexp := (Real.hasDerivAt_exp (d * p / (2 * x))).comp x hinner
  have hprod := (hasDerivAt_id x).neg.mul hexp
  convert hprod using 1
  simp only [modelStringEndpointSolution, modelStringEndpointSolutionDeriv]
  field_simp [hx]
  ring

theorem hasDerivAt_modelStringEndpointSolutionDeriv
    (d p : ℝ) {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (modelStringEndpointSolutionDeriv d p)
      (modelStringEndpointSolutionSecond d p x) x := by
  have hinner := hasDerivAt_modelStringExponent d p hx
  have hexp := (Real.hasDerivAt_exp (d * p / (2 * x))).comp x hinner
  have hsub := hinner.sub_const 1
  have hprod := hexp.mul hsub
  convert hprod using 1
  simp only [modelStringEndpointSolutionDeriv, modelStringEndpointSolutionSecond]
  field_simp [hx]
  ring

/-- The displayed solution satisfies `f'' = (p²/4) m_*' f` on `(-∞,0)`. -/
theorem modelStringEndpointSolution_ode
    (d p : ℝ) {x : ℝ} (hx : x < 0) :
    modelStringEndpointSolutionSecond d p x =
      (p ^ 2 / 4) * modelStringDensity d x *
        modelStringEndpointSolution d p x := by
  rw [modelStringDensity_of_neg d hx]
  simp only [modelStringEndpointSolutionSecond, modelStringEndpointSolution]
  field_simp [ne_of_lt hx, ne_of_gt (neg_pos.mpr hx)]
  ring

theorem modelStringEndpointSolution_secondODE
    (d p : ℝ) {x : ℝ} (hx : x < 0) :
    HasDerivAt (modelStringEndpointSolutionDeriv d p)
      ((p ^ 2 / 4) * modelStringDensity d x *
        modelStringEndpointSolution d p x) x := by
  rw [← modelStringEndpointSolution_ode d p hx]
  exact hasDerivAt_modelStringEndpointSolutionDeriv d p (ne_of_lt hx)

theorem tendsto_modelStringExponent_atBot (d p : ℝ) :
    Tendsto (fun x : ℝ ↦ d * p / (2 * x)) atBot (𝓝 0) := by
  have hinv : Tendsto (fun x : ℝ ↦ x⁻¹) atBot (𝓝 0) :=
    tendsto_inv_atBot_zero
  have hmul : Tendsto (fun x : ℝ ↦ (d * p / 2) * x⁻¹)
      atBot (𝓝 ((d * p / 2) * 0)) :=
    tendsto_const_nhds.mul hinv
  convert hmul using 1 <;> ring_nf

/-- The source normalization `f_*'(-∞) = -1`. -/
theorem tendsto_modelStringEndpointSolutionDeriv_atBot
    (d p : ℝ) :
    Tendsto (modelStringEndpointSolutionDeriv d p) atBot (𝓝 (-1)) := by
  have hinner := tendsto_modelStringExponent_atBot d p
  have hexp := Real.tendsto_exp_nhds_zero_nhds_one.comp hinner
  have hsub : Tendsto (fun x : ℝ ↦ d * p / (2 * x) - 1)
      atBot (𝓝 (0 - 1)) :=
    hinner.sub_const 1
  simpa [modelStringEndpointSolutionDeriv] using hexp.mul hsub

/-- The displayed endpoint solution vanishes as the endpoint is approached from below. -/
theorem tendsto_modelStringEndpointSolution_nhdsLT_zero
    {d p : ℝ} (hd : 0 < d) (hp : 0 < p) :
    Tendsto (modelStringEndpointSolution d p)
      (𝓝[<] (0 : ℝ)) (𝓝 0) := by
  have ha : 0 < d * p / 2 := div_pos (mul_pos hd hp) (by norm_num)
  have hinv : Tendsto (fun x : ℝ ↦ x⁻¹) (𝓝[<] (0 : ℝ)) atBot :=
    tendsto_inv_zero_atBot
  have hinnerRaw : Tendsto (fun x : ℝ ↦ (d * p / 2) * x⁻¹)
      (𝓝[<] (0 : ℝ)) atBot :=
    tendsto_const_nhds.pos_mul_atBot ha hinv
  have hinner : Tendsto (fun x : ℝ ↦ d * p / (2 * x))
      (𝓝[<] (0 : ℝ)) atBot := by
    convert hinnerRaw using 1
    all_goals ring_nf
  have hexp : Tendsto (fun x : ℝ ↦ Real.exp (d * p / (2 * x)))
      (𝓝[<] (0 : ℝ)) (𝓝 0) :=
    Real.tendsto_exp_atBot.comp hinner
  have hneg : Tendsto (fun x : ℝ ↦ -x)
      (𝓝[<] (0 : ℝ)) (𝓝 0) :=
    by
      have hfull : ContinuousAt (fun x : ℝ ↦ -x) 0 := continuousAt_id.neg
      simpa using hfull.tendsto.mono_left
        (show (𝓝[<] (0 : ℝ)) ≤ 𝓝 (0 : ℝ) from inf_le_left)
  change Tendsto (fun x : ℝ ↦ (-x) * Real.exp (d * p / (2 * x)))
    (𝓝[<] (0 : ℝ)) (𝓝 0)
  simpa only [zero_mul] using hneg.mul hexp

/-- The source entrance expansion `lim (f_*(ξ) + ξ) = -dp/2`. -/
theorem tendsto_modelStringEndpointSolution_add_id_atBot
    {d p : ℝ} (hd : 0 < d) (hp : 0 < p) :
    Tendsto (fun x : ℝ ↦ modelStringEndpointSolution d p x + x)
      atBot (𝓝 (-d * p / 2)) := by
  have hinner := tendsto_modelStringExponent_atBot d p
  have hinnerNe : Tendsto (fun x : ℝ ↦ d * p / (2 * x))
      atBot (𝓝[≠] (0 : ℝ)) := by
    refine tendsto_inf.2 ⟨hinner, ?_⟩
    rw [tendsto_principal]
    filter_upwards [eventually_lt_atBot (0 : ℝ)] with x hx
    exact div_ne_zero (mul_ne_zero hd.ne' hp.ne')
      (mul_ne_zero (by norm_num) hx.ne)
  have hslope := (Real.hasDerivAt_exp 0).tendsto_slope_zero.comp hinnerNe
  have hslope' : Tendsto
      (fun x : ℝ ↦ (d * p / (2 * x))⁻¹ *
        (Real.exp (d * p / (2 * x)) - 1))
      atBot (𝓝 1) := by
    simpa only [Function.comp_def, zero_add, Real.exp_zero, smul_eq_mul] using hslope
  have hscaled : Tendsto
      (fun x : ℝ ↦ (-d * p / 2) *
        ((d * p / (2 * x))⁻¹ *
          (Real.exp (d * p / (2 * x)) - 1)))
      atBot (𝓝 ((-d * p / 2) * 1)) :=
    tendsto_const_nhds.mul hslope'
  have hscaled' : Tendsto
      (fun x : ℝ ↦ (-d * p / 2) *
        ((d * p / (2 * x))⁻¹ *
          (Real.exp (d * p / (2 * x)) - 1)))
      atBot (𝓝 (-d * p / 2)) := by
    simpa using hscaled
  apply hscaled'.congr'
  filter_upwards [eventually_lt_atBot (0 : ℝ)] with x hx
  simp only [modelStringEndpointSolution]
  field_simp [hd.ne', hp.ne', hx.ne]
  ring

end

end DerridaRetaux
