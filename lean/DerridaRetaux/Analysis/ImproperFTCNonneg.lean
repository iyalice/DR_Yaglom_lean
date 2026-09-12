import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

set_option autoImplicit false

open Filter MeasureTheory Set Topology

namespace DerridaRetaux

noncomputable section

/-- A left-half-line counterpart of mathlib's
`integrableOn_Ioi_deriv_of_nonpos'`, obtained by reflection. -/
theorem integrableOn_Iic_deriv_of_nonneg'
    {g g' : ℝ → ℝ} {a l : ℝ}
    (hderiv : ∀ x ∈ Iic a, HasDerivAt g (g' x) x)
    (hg' : ∀ x ∈ Iio a, 0 ≤ g' x)
    (hg : Tendsto g atBot (𝓝 l)) :
    IntegrableOn g' (Iic a) := by
  let G : ℝ → ℝ := fun x ↦ g (-x)
  let G' : ℝ → ℝ := fun x ↦ -g' (-x)
  have hGderiv : ∀ x ∈ Ici (-a), HasDerivAt G (G' x) x := by
    intro x hx
    have hxa : -x ∈ Iic a := by
      have hx' : -a ≤ x := hx
      change -x ≤ a
      linarith
    convert HasDerivAt.scomp x (hderiv (-x) hxa) (hasDerivAt_neg' x) using 1 <;>
      simp [G, G']
  have hG' : ∀ x ∈ Ioi (-a), G' x ≤ 0 := by
    intro x hx
    dsimp only [G']
    apply neg_nonpos.mpr
    apply hg' (-x)
    have hx' : -a < x := hx
    change -x < a
    linarith
  have hG : Tendsto G atTop (𝓝 l) :=
    hg.comp tendsto_neg_atTop_atBot
  have hInt : IntegrableOn G' (Ioi (-a)) :=
    integrableOn_Ioi_deriv_of_nonpos' hGderiv hG' hG
  have hcomp : IntegrableOn (fun x : ℝ ↦ g' (-x)) (Ioi (-a)) := by
    refine Integrable.congr hInt.neg ?_
    filter_upwards with x
    simp [G']
  rw [← Measure.map_neg_eq_self (volume : Measure ℝ)]
  let emb : MeasurableEmbedding (fun x : ℝ ↦ -x) :=
    (Homeomorph.neg ℝ).measurableEmbedding
  apply (emb.integrableOn_map_iff).2
  simpa only [Function.comp_def, neg_preimage, neg_Iic,
    integrableOn_Ici_iff_integrableOn_Ioi] using hcomp

end

end DerridaRetaux
