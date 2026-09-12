import DerridaRetaux.Analysis.ContinuumMomentContinuity
import Mathlib.Tactic

set_option autoImplicit false

open Filter Set Topology MeasureTheory

namespace DerridaRetaux

noncomputable section

/-- Uniformly small polynomial tails upgrade compact-space continuity to
continuity of the full half-line moment. -/
theorem continuousOn_continuumMoment_of_uniformTails
    (u : ℝ → ℝ → ℝ) (r : ℕ) (eta T : ℝ)
    (hu : ∀ R : ℝ, 0 ≤ R →
      ContinuousOn (Function.uncurry u)
        (Icc eta T ×ˢ Icc (0 : ℝ) R))
    (hnonneg : ∀ t x : ℝ, t ∈ Icc eta T → 0 ≤ x → 0 ≤ u t x)
    (hint : ∀ t : ℝ, t ∈ Icc eta T →
      IntegrableOn (fun x : ℝ ↦ x ^ r * u t x) (Ici 0))
    (htail : ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ R : ℕ in atTop, ∀ t : ℝ, t ∈ Icc eta T →
        (∫ x in Ioi (R : ℝ), x ^ r * u t x) < epsilon) :
    ContinuousOn (fun t : ℝ ↦ continuumMoment (u t) r) (Icc eta T) := by
  let F : ℕ → ℝ → ℝ := fun R t ↦
    ∫ x in Icc (0 : ℝ) (R : ℝ), x ^ r * u t x
  have hFcont : ∀ R : ℕ, ContinuousOn (F R) (Icc eta T) := by
    intro R
    exact continuousOn_compactMomentIntegral u r eta T (R : ℝ)
      (Nat.cast_nonneg R) (hu (R : ℝ) (Nat.cast_nonneg R))
  have hconv : TendstoUniformlyOn F
      (fun t : ℝ ↦ continuumMoment (u t) r) atTop (Icc eta T) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro epsilon hepsilon
    filter_upwards [htail epsilon hepsilon] with R htailR
    intro t ht
    let integrand : ℝ → ℝ := fun x ↦ x ^ r * u t x
    have hintFull := hint t ht
    have hintHead : IntegrableOn integrand (Icc (0 : ℝ) (R : ℝ)) :=
      hintFull.mono_set (Icc_subset_Ici_self)
    have hintTail : IntegrableOn integrand (Ioi (R : ℝ)) :=
      hintFull.mono_set (fun x hx ↦ show (0 : ℝ) ≤ x from (Nat.cast_nonneg R).trans hx.le)
    have hdisjoint : Disjoint (Icc (0 : ℝ) (R : ℝ)) (Ioi (R : ℝ)) := by
      rw [Set.disjoint_left]
      intro x hx hxtail
      exact (not_lt_of_ge hx.2) hxtail
    have hsplit : continuumMoment (u t) r =
        F R t + ∫ x in Ioi (R : ℝ), integrand x := by
      have hunion := setIntegral_union hdisjoint measurableSet_Ioi
        hintHead hintTail
      rw [Icc_union_Ioi_eq_Ici (Nat.cast_nonneg R)] at hunion
      simpa only [continuumMoment, F, integrand] using hunion
    have htailNonneg : 0 ≤ ∫ x in Ioi (R : ℝ), integrand x := by
      apply integral_nonneg_of_ae
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
      have hx0 : (0 : ℝ) ≤ x := (Nat.cast_nonneg R).trans hx.le
      exact mul_nonneg (pow_nonneg hx0 r) (hnonneg t x ht hx0)
    rw [Real.dist_eq, hsplit]
    simp only [add_sub_cancel_left, abs_of_nonneg htailNonneg]
    exact htailR t ht
  exact hconv.continuousOn (Eventually.of_forall hFcont)

end

end DerridaRetaux
