import DerridaRetaux.Analysis.ContinuumMomentContinuity
import DerridaRetaux.Analysis.HalfLineLaplaceIntegrability
import Mathlib.Tactic

set_option autoImplicit false

open Filter Set Topology MeasureTheory
set_option maxHeartbeats 800000

namespace DerridaRetaux

noncomputable section

theorem continuousOn_compactLaplaceIntegral
    (u : ℝ → ℝ → ℝ) (p eta T R : ℝ) (hR : 0 ≤ R)
    (hu : ContinuousOn (Function.uncurry u)
      (Icc eta T ×ˢ Icc (0 : ℝ) R)) :
    ContinuousOn
      (fun t : ℝ ↦ ∫ x in Icc (0 : ℝ) R,
        Real.exp (-(p * x)) * u t x) (Icc eta T) := by
  let clamp : ℝ → ℝ := nonnegativeIntervalClamp R
  have hclamp : Continuous clamp := continuous_nonnegativeIntervalClamp R
  let f : ↥(Icc eta T) → ℝ → ℝ := fun t x ↦
    Real.exp (-(p * clamp x)) * u t (clamp x)
  have hmap : Continuous (fun q : ↥(Icc eta T) × ℝ ↦
      (((q.1 : ↥(Icc eta T)) : ℝ), clamp q.2)) :=
    (continuous_subtype_val.comp continuous_fst).prodMk
      (hclamp.comp continuous_snd)
  have hmaps : ∀ q : ↥(Icc eta T) × ℝ,
      (((q.1 : ↥(Icc eta T)) : ℝ), clamp q.2) ∈
        Icc eta T ×ˢ Icc (0 : ℝ) R := by
    intro q
    exact ⟨q.1.property, nonnegativeIntervalClamp_mem hR⟩
  have hu' : Continuous
      (fun q : ↥(Icc eta T) × ℝ ↦ u q.1 (clamp q.2)) :=
    hu.comp_continuous hmap hmaps
  have hf : Continuous (Function.uncurry f) := by
    dsimp only [f, Function.uncurry_apply_pair]
    have heArg : Continuous (fun q : ↥(Icc eta T) × ℝ ↦ -(p * clamp q.2)) :=
      (continuous_const.mul (hclamp.comp continuous_snd)).neg
    have he : Continuous (fun q : ↥(Icc eta T) × ℝ ↦ Real.exp (-(p * clamp q.2))) :=
      Real.continuous_exp.comp heArg
    exact he.mul (by assumption)
  have hint := continuous_parametric_integral_of_continuous
    (μ := volume) hf (s := Icc (0 : ℝ) R) isCompact_Icc
  rw [continuousOn_iff_continuous_restrict]
  apply hint.congr
  intro t
  apply setIntegral_congr_fun measurableSet_Icc
  intro x hx
  simp only [f, clamp, Function.uncurry_apply_pair]
  rw [nonnegativeIntervalClamp_eq_self hx]

/-- Uniform mass tails upgrade compact continuity to continuity of the full
Laplace transform. -/
theorem continuousOn_continuumLaplace_of_uniformMassTails
    (u : ℝ → ℝ → ℝ) (p eta T : ℝ) (hp : 0 ≤ p)
    (hu : ∀ R : ℝ, 0 ≤ R → ContinuousOn (Function.uncurry u)
      (Icc eta T ×ˢ Icc (0 : ℝ) R))
    (hnonneg : ∀ t x : ℝ, t ∈ Icc eta T → 0 ≤ x → 0 ≤ u t x)
    (hint : ∀ t : ℝ, t ∈ Icc eta T → IntegrableOn (u t) (Ici 0))
    (hLap : ∀ t : ℝ, t ∈ Icc eta T → IntegrableOn
      (fun x : ℝ ↦ Real.exp (-(p * x)) * u t x) (Ici 0))
    (htail : ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ R : ℕ in atTop, ∀ t : ℝ, t ∈ Icc eta T →
        (∫ x in Ioi (R : ℝ), u t x) < epsilon) :
    ContinuousOn (fun t : ℝ ↦ continuumLaplace (u t) p) (Icc eta T) := by
  let F : ℕ → ℝ → ℝ := fun R t ↦
    ∫ x in Icc (0 : ℝ) (R : ℝ), Real.exp (-(p * x)) * u t x
  have hF : ∀ R : ℕ, ContinuousOn (F R) (Icc eta T) := by
    intro R
    exact continuousOn_compactLaplaceIntegral u p eta T R (Nat.cast_nonneg R)
      (hu R (Nat.cast_nonneg R))
  have hconv : TendstoUniformlyOn F (fun t ↦ continuumLaplace (u t) p)
      atTop (Icc eta T) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro epsilon hepsilon
    filter_upwards [htail epsilon hepsilon] with R htailR
    intro t ht
    let integrand : ℝ → ℝ := fun x ↦ Real.exp (-(p * x)) * u t x
    have hintLap : IntegrableOn integrand (Ici (0 : ℝ)) := by
      simpa only [integrand] using hLap t ht
    have hhead : IntegrableOn integrand (Icc (0 : ℝ) (R : ℝ)) :=
      hintLap.mono_set (fun x hx ↦ hx.1)
    have htailInt : IntegrableOn integrand (Ioi (R : ℝ)) := hintLap.mono_set
      (fun x hx ↦ show (0 : ℝ) ≤ x from (Nat.cast_nonneg R).trans hx.le)
    have hdisj : Disjoint (Icc (0 : ℝ) (R : ℝ)) (Ioi (R : ℝ)) := by
      rw [Set.disjoint_left]
      intro x hx hxo
      exact (not_lt_of_ge hx.2) hxo
    have hsplit : continuumLaplace (u t) p = F R t +
        ∫ x in Ioi (R : ℝ), integrand x := by
      have hs := setIntegral_union hdisj measurableSet_Ioi hhead htailInt
      rw [Icc_union_Ioi_eq_Ici (Nat.cast_nonneg R)] at hs
      simpa only [continuumLaplace, F, integrand] using hs
    have htail0 : 0 ≤ ∫ x in Ioi (R : ℝ), integrand x := by
      apply integral_nonneg_of_ae
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
      exact mul_nonneg (Real.exp_pos _).le
        (hnonneg t x ht ((Nat.cast_nonneg R).trans hx.le))
    have htailLe : (∫ x in Ioi (R : ℝ), integrand x) ≤
        ∫ x in Ioi (R : ℝ), u t x := by
      apply setIntegral_mono_on htailInt
        ((hint t ht).mono_set
          (fun x hx ↦ show (0 : ℝ) ≤ x from (Nat.cast_nonneg R).trans hx.le))
        measurableSet_Ioi
      intro x hx
      have hx0 : 0 ≤ x := (Nat.cast_nonneg R).trans hx.le
      dsimp only [integrand]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right
        (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hp hx0)))
        (hnonneg t x ht hx0)
    rw [Real.dist_eq, hsplit]
    simp only [add_sub_cancel_left, abs_of_nonneg htail0]
    exact lt_of_le_of_lt htailLe (htailR t ht)
  exact hconv.continuousOn (Eventually.of_forall hF)

end

end DerridaRetaux
