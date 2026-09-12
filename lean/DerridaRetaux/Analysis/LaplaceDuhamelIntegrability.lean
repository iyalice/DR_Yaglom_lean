import DerridaRetaux.Analysis.MomentDuhamelIntegrability
import Mathlib.Tactic

set_option autoImplicit false

open Filter Set Topology MeasureTheory

namespace DerridaRetaux

noncomputable section

/-- The exponentially weighted space-time kernel obtained by testing the
quadratic Duhamel term against a half-line Laplace function. -/
def laplaceDuhamelIntegrand
    (v : ℝ → ℝ → ℝ) (p t h : ℝ) (z : ℝ × ℝ) : ℝ :=
  Real.exp (-(p * z.1)) *
    ((1 / 2 : ℝ) * v z.2 (z.1 + t + h - z.2))

/-- For a nonnegative Laplace parameter, the Laplace-weighted kernel is
dominated by the unweighted mass kernel. -/
theorem integrable_laplaceDuhamelIntegrand_of_mass
    (v : ℝ → ℝ → ℝ) (p t h : ℝ) (hp : 0 ≤ p)
    (hvcont : ContinuousOn (Function.uncurry v)
      (Ici t ×ˢ Ici (0 : ℝ)))
    (hvnonneg : ∀ s x : ℝ, t ≤ s → 0 ≤ x → 0 ≤ v s x)
    (hmass : Integrable (weightedShiftedKernel v 0 t h)
      ((volume.restrict (Ici (0 : ℝ))).prod
        (volume.restrict (Ioc t (t + h))))) :
    Integrable (laplaceDuhamelIntegrand v p t h)
      ((volume.restrict (Ici (0 : ℝ))).prod
        (volume.restrict (Ioc t (t + h)))) := by
  let S : Set (ℝ × ℝ) := Ici (0 : ℝ) ×ˢ Ioc t (t + h)
  let q : ℝ × ℝ → ℝ × ℝ := fun z ↦ (z.2, z.1 + t + h - z.2)
  have hq : Continuous q := by dsimp only [q]; fun_prop
  have hqmap : MapsTo q S (Ici t ×ˢ Ici (0 : ℝ)) := by
    intro z hz
    change (0 : ℝ) ≤ z.1 ∧ t < z.2 ∧ z.2 ≤ t + h at hz
    change t ≤ z.2 ∧ (0 : ℝ) ≤ z.1 + t + h - z.2
    exact ⟨hz.2.1.le, by linarith [hz.1, hz.2.2]⟩
  have hkernel : ContinuousOn
      (fun z : ℝ × ℝ ↦ v z.2 (z.1 + t + h - z.2)) S := by
    change ContinuousOn ((Function.uncurry v) ∘ q) S
    exact hvcont.comp hq.continuousOn hqmap
  have hcont : ContinuousOn (laplaceDuhamelIntegrand v p t h) S := by
    unfold laplaceDuhamelIntegrand
    exact ((Real.continuous_exp.comp
      (continuous_const.mul continuous_fst).neg).continuousOn).mul
        (continuousOn_const.mul hkernel)
  have hmeas : AEStronglyMeasurable (laplaceDuhamelIntegrand v p t h)
      ((volume.restrict (Ici (0 : ℝ))).prod
        (volume.restrict (Ioc t (t + h)))) := by
    rw [Measure.prod_restrict]
    exact hcont.aestronglyMeasurable
      (measurableSet_Ici.prod measurableSet_Ioc)
  apply hmass.mono' hmeas
  rw [Measure.prod_restrict]
  filter_upwards [self_mem_ae_restrict
    (measurableSet_Ici.prod measurableSet_Ioc)] with z hz
  change (0 : ℝ) ≤ z.1 ∧ t < z.2 ∧ z.2 ≤ t + h at hz
  have hy : 0 ≤ z.1 + t + h - z.2 := by linarith [hz.1, hz.2.2]
  have hv0 := hvnonneg z.2 (z.1 + t + h - z.2) hz.2.1.le hy
  have hexp0 := (Real.exp_pos (-(p * z.1))).le
  have hexp1 : Real.exp (-(p * z.1)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hp hz.1))
  unfold laplaceDuhamelIntegrand weightedShiftedKernel
  simp only [pow_zero, one_mul]
  rw [Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg hexp0 (mul_nonneg (by norm_num) hv0)),]
  nlinarith [mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) hv0]

end

end DerridaRetaux
