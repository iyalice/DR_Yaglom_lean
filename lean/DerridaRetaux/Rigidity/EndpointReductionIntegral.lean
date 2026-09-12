import DerridaRetaux.Analysis.ImproperFTCNonneg
import DerridaRetaux.Rigidity.StringCoordinates
import Mathlib.Tactic

set_option autoImplicit false

open Filter Set Topology MeasureTheory

namespace DerridaRetaux

noncomputable section

/-- The improper reduction-of-order integral attached to a positive endpoint
solution on the negative half-line. -/
def endpointReductionIntegral (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ v in Iic x, ((f v) ^ 2)⁻¹

/-- The corresponding entrance-normalized candidate. -/
def entranceSolutionFromEndpoint (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  f x * endpointReductionIntegral f x

theorem integrableOn_inv_sq_Iic {a : ℝ} (ha : a < 0) :
    IntegrableOn (fun x : ℝ ↦ (x ^ 2)⁻¹) (Iic a) := by
  rw [← Measure.map_neg_eq_self (volume : Measure ℝ)]
  let emb : MeasurableEmbedding (fun x : ℝ ↦ -x) :=
    (Homeomorph.neg ℝ).measurableEmbedding
  apply (emb.integrableOn_map_iff).2
  simpa only [Function.comp_def, neg_sq, neg_preimage, neg_Iic,
    integrableOn_Ici_iff_integrableOn_Ioi] using
      (integrableOn_Ioi_inv_sq (t := -a) (neg_pos.mpr ha))

theorem tendsto_endpoint_div_neg_id_atBot
    {f : ℝ → ℝ} {h : ℝ}
    (hlimit : Tendsto (fun x : ℝ ↦ f x + x) atBot (𝓝 h)) :
    Tendsto (fun x : ℝ ↦ f x / (-x)) atBot (𝓝 1) := by
  have hneg : Tendsto (fun x : ℝ ↦ -x) atBot atTop :=
    tendsto_neg_atBot_atTop
  have hinv : Tendsto (fun x : ℝ ↦ (-x)⁻¹) atBot (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hneg
  have hprod := hlimit.mul hinv
  have hsum := hprod.add (tendsto_const_nhds :
    Tendsto (fun _ : ℝ ↦ (1 : ℝ)) atBot (𝓝 1))
  have heq : (fun x => (f x + x) * (-x)⁻¹ + 1) =ᶠ[atBot] (fun x => f x / (-x)) := by
    filter_upwards [eventually_lt_atBot (0 : ℝ)] with x hx
    field_simp [hx.ne]
  simpa only [mul_zero, zero_add] using hsum.congr' heq

/-- Linear entrance asymptotics imply integrability of `f⁻²` on every left
half-line. -/
theorem integrableOn_inv_sq_endpoint
    {f : ℝ → ℝ} {h x : ℝ}
    (hx : x < 0)
    (hfcont : ContinuousOn f (Iio (0 : ℝ)))
    (hfpos : ∀ y : ℝ, y < 0 → 0 < f y)
    (hlimit : Tendsto (fun y : ℝ ↦ f y + y) atBot (𝓝 h)) :
    IntegrableOn (fun y : ℝ ↦ ((f y) ^ 2)⁻¹) (Iic x) := by
  have hratio := tendsto_endpoint_div_neg_id_atBot hlimit
  have hevent : ∀ᶠ y : ℝ in atBot, (1 / 2 : ℝ) < f y / (-y) :=
    (tendsto_order.1 hratio).1 (1 / 2) (by norm_num)
  obtain ⟨B, hB⟩ := eventually_atBot.mp hevent
  let a : ℝ := min B x
  have hax : a ≤ x := min_le_right _ _
  have ha0 : a < 0 := hax.trans_lt hx
  have htailDom : IntegrableOn (fun y : ℝ ↦ 4 * (y ^ 2)⁻¹) (Iic a) :=
    (integrableOn_inv_sq_Iic ha0).const_mul 4
  have hfTail : ContinuousOn (fun y : ℝ ↦ ((f y) ^ 2)⁻¹) (Iic a) := by
    have hfI : ContinuousOn f (Iic a) := hfcont.mono fun y hy ↦ hy.trans_lt ha0
    exact (hfI.pow 2).inv₀ fun y hy ↦ pow_ne_zero 2 (hfpos y (hy.trans_lt ha0)).ne'
  have htail : IntegrableOn (fun y : ℝ ↦ ((f y) ^ 2)⁻¹) (Iic a) := by
    apply htailDom.mono' (hfTail.aestronglyMeasurable measurableSet_Iic)
    filter_upwards [self_mem_ae_restrict measurableSet_Iic] with y hy
    have hyB : y ≤ B := hy.trans (min_le_left B x)
    have hyratio := hB y hyB
    have hy0 : y < 0 := hy.trans_lt ha0
    have hhalf : 0 < (-y) / 2 := half_pos (neg_pos.mpr hy0)
    have hlinear : (-y) / 2 < f y := by
      apply (lt_div_iff₀ (neg_pos.mpr hy0)).mp at hyratio
      nlinarith
    have hfsq : ((-y) / 2) ^ 2 ≤ f y ^ 2 :=
      (sq_le_sq₀ hhalf.le (hfpos y hy0).le).2 hlinear.le
    have hinv : (f y ^ 2)⁻¹ ≤ (((-y) / 2) ^ 2)⁻¹ :=
      (inv_le_inv₀ (sq_pos_of_pos (hfpos y hy0))
        (sq_pos_of_pos hhalf)).2 hfsq
    rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (sq_nonneg _))]
    calc
      (f y ^ 2)⁻¹ ≤ (((-y) / 2) ^ 2)⁻¹ := hinv
      _ = 4 * (y ^ 2)⁻¹ := by field_simp [hy0.ne]; ring
  have hfMid : ContinuousOn (fun y : ℝ ↦ ((f y) ^ 2)⁻¹) (Icc a x) := by
    have hfI : ContinuousOn f (Icc a x) := hfcont.mono fun y hy ↦ hy.2.trans_lt hx
    exact (hfI.pow 2).inv₀ fun y hy ↦ pow_ne_zero 2 (hfpos y (hy.2.trans_lt hx)).ne'
  have hmid : IntegrableOn (fun y : ℝ ↦ ((f y) ^ 2)⁻¹) (Ioc a x) :=
    (hfMid.integrableOn_compact isCompact_Icc).mono_set Ioc_subset_Icc_self
  rw [← Iic_union_Ioc_eq_Iic hax]
  exact htail.union hmid

end

end DerridaRetaux
