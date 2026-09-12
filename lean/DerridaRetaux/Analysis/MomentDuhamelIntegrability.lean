import DerridaRetaux.Analysis.MildMomentIdentity
import Mathlib.Tactic

set_option autoImplicit false

open Filter Set Topology MeasureTheory

namespace DerridaRetaux

noncomputable section

/-- A polynomially weighted shifted kernel, with the normalization used in
the quadratic Duhamel term. -/
def weightedShiftedKernel
    (v : ℝ → ℝ → ℝ) (r : ℕ) (t h : ℝ) (z : ℝ × ℝ) : ℝ :=
  z.1 ^ r * ((1 / 2 : ℝ) * v z.2 (z.1 + t + h - z.2))

/-- Slice integrability and integrability of the shifted moments imply
space-time integrability of a nonnegative Duhamel kernel. -/
theorem integrable_weightedShiftedKernel
    (v : ℝ → ℝ → ℝ) (r : ℕ) (t h : ℝ) (hh : 0 ≤ h)
    (hvcont : ContinuousOn (Function.uncurry v)
      (Ici t ×ˢ Ici (0 : ℝ)))
    (hvnonneg : ∀ s x : ℝ, t ≤ s → 0 ≤ x → 0 ≤ v s x)
    (hslice : ∀ s : ℝ, s ∈ Ioc t (t + h) →
      IntegrableOn
        (fun x : ℝ ↦ x ^ r * v s (x + (t + h - s))) (Ici 0))
    (hshift : IntegrableOn
      (fun s : ℝ ↦ (1 / 2 : ℝ) *
        shiftedHalfLineMoment (v s) r (t + h - s))
      (Ioc t (t + h))) :
    Integrable (weightedShiftedKernel v r t h)
      ((volume.restrict (Ici (0 : ℝ))).prod
        (volume.restrict (Ioc t (t + h)))) := by
  let S : Set (ℝ × ℝ) := Ici (0 : ℝ) ×ˢ Ioc t (t + h)
  let q : ℝ × ℝ → ℝ × ℝ := fun z ↦ (z.2, z.1 + t + h - z.2)
  have hq : Continuous q := by dsimp only [q]; fun_prop
  have hqmap : MapsTo q S (Ici t ×ˢ Ici (0 : ℝ)) := by
    intro z hz
    change (0 : ℝ) ≤ z.1 ∧ t < z.2 ∧ z.2 ≤ t + h at hz
    exact ⟨hz.2.1.le,
      show (0 : ℝ) ≤ z.1 + t + h - z.2 by linarith [hz.1, hz.2.2]⟩
  have hkernel : ContinuousOn
      (fun z : ℝ × ℝ ↦ v z.2 (z.1 + t + h - z.2)) S := by
    change ContinuousOn ((Function.uncurry v) ∘ q) S
    exact hvcont.comp hq.continuousOn hqmap
  have hcont : ContinuousOn (weightedShiftedKernel v r t h) S := by
    unfold weightedShiftedKernel
    exact (continuousOn_fst.pow r).mul (continuousOn_const.mul hkernel)
  have hmeas : AEStronglyMeasurable (weightedShiftedKernel v r t h)
      ((volume.restrict (Ici (0 : ℝ))).prod
        (volume.restrict (Ioc t (t + h)))) := by
    rw [Measure.prod_restrict]
    exact hcont.aestronglyMeasurable
      (measurableSet_Ici.prod measurableSet_Ioc)
  rw [integrable_prod_iff' hmeas]
  constructor
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with s hs
    have hscaled := (hslice s hs).const_mul (1 / 2 : ℝ)
    refine hscaled.congr ?_
    filter_upwards [self_mem_ae_restrict measurableSet_Ici] with x hx
    unfold weightedShiftedKernel
    ring
  · apply hshift.congr
    filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with s hs
    have ha : 0 ≤ t + h - s := by linarith [hs.2]
    symm
    change (∫ x in Ici (0 : ℝ),
      ‖weightedShiftedKernel v r t h (x, s)‖) = _
    have hpoint : ∀ x ∈ Ici (0 : ℝ),
        ‖weightedShiftedKernel v r t h (x, s)‖ =
          (1 / 2 : ℝ) * (x ^ r * v s (x + (t + h - s))) := by
      intro x hx
      have hx0 : 0 ≤ x := hx
      have hz0 : 0 ≤ x + (t + h - s) := by linarith
      unfold weightedShiftedKernel
      rw [Real.norm_eq_abs, abs_of_nonneg]
      · ring
      · exact mul_nonneg (pow_nonneg hx0 r)
          (mul_nonneg (by norm_num)
            (hvnonneg s (x + t + h - s) hs.1.le (by linarith [hz0])))
    rw [setIntegral_congr_fun measurableSet_Ici hpoint,
      integral_const_mul]
    rfl

end

end DerridaRetaux
