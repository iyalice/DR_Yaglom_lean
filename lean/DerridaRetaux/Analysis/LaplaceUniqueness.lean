import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.FiniteMeasureExt
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.Topology.ContinuousMap.Weierstrass
import Mathlib.Tactic

set_option autoImplicit false

open Filter MeasureTheory Polynomial Set
open scoped ENNReal NNReal Topology

namespace DerridaRetaux

noncomputable section

attribute [local instance] Measure.Subtype.measureSpace

/-!
# Uniqueness for the half-line Laplace transform

The main argument sends `x ∈ [0, ∞)` to `exp (-x) ∈ [0, 1]`.  Positive
integer Laplace parameters become the moments of the pushed measure.  The
missing zeroth moment follows by dominated convergence as the parameter tends
to zero.  Weierstrass approximation then determines the pushed measure, and
measurable-embedding injectivity recovers the original half-line measure.
-/

/-- The compactifying coordinate `x ↦ exp (-x)` on the nonnegative half-line. -/
def laplaceCompactMap (x : Set.Ici (0 : ℝ)) : Set.Icc (0 : ℝ) 1 :=
  ⟨Real.exp (-x.1), Real.exp_pos (-x.1) |>.le, Real.exp_le_one_iff.mpr (neg_nonpos.mpr x.2)⟩

lemma continuous_laplaceCompactMap : Continuous laplaceCompactMap := by
  apply Continuous.subtype_mk
  exact Real.continuous_exp.comp (continuous_neg.comp continuous_subtype_val)

lemma injective_laplaceCompactMap : Function.Injective laplaceCompactMap := by
  intro x y hxy
  apply Subtype.ext
  have hval := congrArg Subtype.val hxy
  exact neg_injective (Real.exp_injective hval)

lemma measurableEmbedding_laplaceCompactMap :
    MeasurableEmbedding laplaceCompactMap :=
  by
    letI : PolishSpace (Set.Ici (0 : ℝ)) := isClosed_Ici.polishSpace
    exact continuous_laplaceCompactMap.measurableEmbedding injective_laplaceCompactMap

/-- Integration against a finite measure, as a continuous functional on a compact space. -/
def continuousIntegralCLM {K : Type*} [MeasurableSpace K] [TopologicalSpace K]
    [BorelSpace K] [CompactSpace K] (μ : Measure K) [IsFiniteMeasure μ] :
    C(K, ℝ) →L[ℝ] ℝ :=
  L1.integralCLM.comp (ContinuousMap.toLp 1 μ ℝ)

@[simp]
lemma continuousIntegralCLM_apply {K : Type*} [MeasurableSpace K] [TopologicalSpace K]
    [BorelSpace K] [CompactSpace K] (μ : Measure K) [IsFiniteMeasure μ]
    (f : C(K, ℝ)) : continuousIntegralCLM μ f = ∫ x, f x ∂μ := by
  rw [continuousIntegralCLM, ContinuousLinearMap.comp_apply, ← L1.integral_eq]
  rw [L1.integral_eq_integral]
  exact integral_congr_ae (ContinuousMap.coeFn_toLp (p := 1) (𝕜 := ℝ) μ f)

/-- Half-line Laplace kernels converge to one as their positive parameters decrease to zero. -/
lemma tendsto_halfLineLaplace_integral_zero (μ : Measure (Set.Ici (0 : ℝ)))
    [IsFiniteMeasure μ] :
    Tendsto
      (fun n : ℕ ↦ ∫ x, Real.exp
        (-((((n + 1 : ℕ) : ℝ)⁻¹) * (x.1 : ℝ))) ∂μ)
      atTop (𝓝 (∫ _x, (1 : ℝ) ∂μ)) := by
  apply tendsto_integral_of_dominated_convergence (fun _x ↦ (1 : ℝ))
  · intro n
    exact (Real.continuous_exp.comp
      ((continuous_const.mul continuous_subtype_val).neg)).aestronglyMeasurable
  · exact integrable_const 1
  · intro n
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_one_iff.mpr
    exact neg_nonpos.mpr (mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) x.2)
  · filter_upwards with x
    have hcast :
        Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
    have hinv :
        Tendsto (fun n : ℕ ↦ (((n + 1 : ℕ) : ℝ)⁻¹)) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp hcast
    have hzero :
        Tendsto (fun n : ℕ ↦ -((((n + 1 : ℕ) : ℝ)⁻¹) * x.1)) atTop (𝓝 0) := by
      convert (hinv.mul_const x.1).neg using 1
      simp
    exact Real.tendsto_exp_nhds_zero_nhds_one.comp hzero

/-- On `[0, 1]`, equality of all power moments determines a finite measure. -/
theorem measure_eq_of_compact_moments
    {μ ν : Measure (Set.Icc (0 : ℝ) 1)} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hmom : ∀ n : ℕ, (∫ x, (x.1 : ℝ) ^ n ∂μ) = ∫ x, (x.1 : ℝ) ^ n ∂ν) :
    μ = ν := by
  let Lμ : C(Set.Icc (0 : ℝ) 1, ℝ) →L[ℝ] ℝ := continuousIntegralCLM μ
  let Lν : C(Set.Icc (0 : ℝ) 1, ℝ) →L[ℝ] ℝ := continuousIntegralCLM ν
  have hpolynomial : ∀ P : ℝ[X],
      Lμ ((Polynomial.toContinuousMapOnAlgHom (Set.Icc (0 : ℝ) 1)) P) =
        Lν ((Polynomial.toContinuousMapOnAlgHom (Set.Icc (0 : ℝ) 1)) P) := by
    intro P
    induction P using Polynomial.induction_on' with
    | add P Q hP hQ =>
        have hadd :
            (Polynomial.toContinuousMapOnAlgHom (Set.Icc (0 : ℝ) 1)) (P + Q) =
              (Polynomial.toContinuousMapOnAlgHom (Set.Icc (0 : ℝ) 1)) P +
                (Polynomial.toContinuousMapOnAlgHom (Set.Icc (0 : ℝ) 1)) Q :=
          map_add _ P Q
        rw [hadd, Lμ.map_add, Lν.map_add, hP, hQ]
    | monomial n a =>
        let Xc : C(Set.Icc (0 : ℝ) 1, ℝ) :=
          (Polynomial.toContinuousMapOnAlgHom (Set.Icc (0 : ℝ) 1)) Polynomial.X
        have hmono :
            (Polynomial.toContinuousMapOnAlgHom (Set.Icc (0 : ℝ) 1))
                (Polynomial.monomial n a) = a • Xc ^ n := by
          ext x
          simp [Xc, Polynomial.toContinuousMapOnAlgHom_apply,
            Polynomial.toContinuousMapOn_apply]
        rw [hmono, Lμ.map_smul, Lν.map_smul]
        congr 1
        rw [continuousIntegralCLM_apply, continuousIntegralCLM_apply]
        simpa [Xc, Polynomial.toContinuousMapOnAlgHom_apply,
          Polynomial.toContinuousMapOn_apply] using hmom n
  have heqOn : Set.EqOn Lμ Lν
      (polynomialFunctions (Set.Icc (0 : ℝ) 1) : Set C(Set.Icc (0 : ℝ) 1, ℝ)) := by
    intro f hf
    rw [polynomialFunctions_coe] at hf
    obtain ⟨P, rfl⟩ := hf
    exact hpolynomial P
  have hdense : Dense
      (polynomialFunctions (Set.Icc (0 : ℝ) 1) : Set C(Set.Icc (0 : ℝ) 1, ℝ)) := by
    rw [dense_iff_closure_eq, ← Subalgebra.topologicalClosure_coe,
      polynomialFunctions_closure_eq_top]
    rfl
  have hfunctional : Lμ = Lν := by
    apply DFunLike.coe_injective
    exact Continuous.ext_on hdense Lμ.continuous Lν.continuous heqOn
  apply MeasureTheory.ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  have happly : Lμ f.toContinuousMap = Lν f.toContinuousMap := by
    rw [hfunctional]
  simpa [Lμ, Lν] using happly

/-- Positive-parameter Laplace values determine a finite measure on `[0, ∞)`. -/
theorem finiteMeasure_eq_of_halfLine_laplace_eq
    {μ ν : Measure (Set.Ici (0 : ℝ))} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hLaplace : ∀ p : ℝ, 0 < p →
      (∫ x, Real.exp (-p * (x.1 : ℝ)) ∂μ) =
        ∫ x, Real.exp (-p * (x.1 : ℝ)) ∂ν) :
    μ = ν := by
  have hmass : (∫ _x, (1 : ℝ) ∂μ) = ∫ _x, (1 : ℝ) ∂ν := by
    have hμlim := tendsto_halfLineLaplace_integral_zero μ
    have hνlim :
        Tendsto
          (fun n : ℕ ↦ ∫ x, Real.exp
            (-((((n + 1 : ℕ) : ℝ)⁻¹) * (x.1 : ℝ))) ∂μ)
          atTop (𝓝 (∫ _x, (1 : ℝ) ∂ν)) := by
      refine (tendsto_halfLineLaplace_integral_zero ν).congr' ?_
      exact Eventually.of_forall fun n ↦
        by
          simpa only [neg_mul] using
            (hLaplace ((((n + 1 : ℕ) : ℝ)⁻¹))
              (inv_pos.mpr (Nat.cast_pos.mpr (Nat.succ_pos n)))).symm
    exact tendsto_nhds_unique hμlim hνlim
  let μc : Measure (Set.Icc (0 : ℝ) 1) := Measure.map laplaceCompactMap μ
  let νc : Measure (Set.Icc (0 : ℝ) 1) := Measure.map laplaceCompactMap ν
  letI : IsFiniteMeasure μc := μ.isFiniteMeasure_map laplaceCompactMap
  letI : IsFiniteMeasure νc := ν.isFiniteMeasure_map laplaceCompactMap
  have hmom : ∀ n : ℕ, (∫ y, (y.1 : ℝ) ^ n ∂μc) =
      ∫ y, (y.1 : ℝ) ^ n ∂νc := by
    intro n
    cases n with
    | zero =>
        simp only [pow_zero]
        change (∫ _y, (1 : ℝ) ∂Measure.map laplaceCompactMap μ) =
          ∫ _y, (1 : ℝ) ∂Measure.map laplaceCompactMap ν
        rw [measurableEmbedding_laplaceCompactMap.integral_map,
          measurableEmbedding_laplaceCompactMap.integral_map]
        exact hmass
    | succ n =>
        change (∫ y, (y.1 : ℝ) ^ (n + 1) ∂Measure.map laplaceCompactMap μ) =
          ∫ y, (y.1 : ℝ) ^ (n + 1) ∂Measure.map laplaceCompactMap ν
        rw [measurableEmbedding_laplaceCompactMap.integral_map,
          measurableEmbedding_laplaceCompactMap.integral_map]
        convert hLaplace ((n + 1 : ℕ) : ℝ) (Nat.cast_pos.mpr (Nat.succ_pos n)) using 1 <;>
          apply integral_congr_ae <;>
          filter_upwards with x <;>
          change Real.exp (-x.1) ^ (n + 1) = _ <;>
          rw [← Real.exp_nat_mul] <;>
          congr 1 <;>
          ring
  have hmap : μc = νc := measure_eq_of_compact_moments hmom
  have hcomap := congrArg (Measure.comap laplaceCompactMap) hmap
  simpa only [μc, νc, measurableEmbedding_laplaceCompactMap.comap_map] using hcomap

/-- Nonnegative integrable densities with equal positive-parameter Laplace values
are equal almost everywhere. -/
theorem ae_eq_of_halfLine_laplace_eq
    {ρ : Measure (Set.Ici (0 : ℝ))} [SigmaFinite ρ]
    {u v : Set.Ici (0 : ℝ) → ℝ}
    (hu : ∀ x, 0 ≤ u x) (hv : ∀ x, 0 ≤ v x)
    (huint : Integrable u ρ) (hvint : Integrable v ρ)
    (hLaplace : ∀ p : ℝ, 0 < p →
      (∫ x, Real.exp (-p * x.1) * u x ∂ρ) =
        ∫ x, Real.exp (-p * x.1) * v x ∂ρ) :
    u =ᵐ[ρ] v := by
  let μ : Measure (Set.Ici (0 : ℝ)) :=
    ρ.withDensity (fun x ↦ ENNReal.ofReal (u x))
  let ν : Measure (Set.Ici (0 : ℝ)) :=
    ρ.withDensity (fun x ↦ ENNReal.ofReal (v x))
  have huAe : 0 ≤ᵐ[ρ] u := Eventually.of_forall hu
  have hvAe : 0 ≤ᵐ[ρ] v := Eventually.of_forall hv
  letI : IsFiniteMeasure μ := isFiniteMeasure_withDensity
    ((hasFiniteIntegral_iff_ofReal huAe).1 huint.2).ne
  letI : IsFiniteMeasure ν := isFiniteMeasure_withDensity
    ((hasFiniteIntegral_iff_ofReal hvAe).1 hvint.2).ne
  have hmeasure : μ = ν := by
    apply finiteMeasure_eq_of_halfLine_laplace_eq
    intro p hp
    change (∫ x, Real.exp (-p * x.1) ∂ρ.withDensity
      (fun x ↦ ENNReal.ofReal (u x))) =
      ∫ x, Real.exp (-p * x.1) ∂ρ.withDensity
        (fun x ↦ ENNReal.ofReal (v x))
    rw [integral_withDensity_eq_integral_toReal_smul₀
      huint.1.aemeasurable.ennreal_ofReal
      (Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top),
      integral_withDensity_eq_integral_toReal_smul₀
      hvint.1.aemeasurable.ennreal_ofReal
      (Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
    simpa only [ENNReal.toReal_ofReal (hu _), ENNReal.toReal_ofReal (hv _), smul_eq_mul,
      mul_comm] using hLaplace p hp
  have hOfReal : (fun x ↦ ENNReal.ofReal (u x)) =ᵐ[ρ]
      fun x ↦ ENNReal.ofReal (v x) :=
    (withDensity_eq_iff_of_sigmaFinite
      huint.1.aemeasurable.ennreal_ofReal hvint.1.aemeasurable.ennreal_ofReal).mp hmeasure
  exact hOfReal.mono fun x hx ↦
    (ENNReal.ofReal_eq_ofReal_iff (hu x) (hv x)).mp hx

/-- Continuous nonnegative densities on the half-line are pointwise determined by
positive-parameter Laplace values. -/
theorem continuous_density_eq_of_halfLine_laplace_eq
    {ρ : Measure (Set.Ici (0 : ℝ))} [SigmaFinite ρ] [ρ.IsOpenPosMeasure]
    {u v : Set.Ici (0 : ℝ) → ℝ}
    (hucont : Continuous u) (hvcont : Continuous v)
    (hu : ∀ x, 0 ≤ u x) (hv : ∀ x, 0 ≤ v x)
    (huint : Integrable u ρ) (hvint : Integrable v ρ)
    (hLaplace : ∀ p : ℝ, 0 < p →
      (∫ x, Real.exp (-p * x.1) * u x ∂ρ) =
        ∫ x, Real.exp (-p * x.1) * v x ∂ρ) :
    u = v := by
  apply ρ.eq_of_ae_eq _ hucont hvcont
  exact ae_eq_of_halfLine_laplace_eq hu hv huint hvint hLaplace

/-- The candidate density obtained by inverting `4 / (t * (t * p + 2))`. -/
def yaglomDensity (t x : ℝ) : ℝ :=
  4 / t ^ 2 * Real.exp (-2 * x / t)

lemma continuous_yaglomDensity (t : ℝ) : Continuous (yaglomDensity t) := by
  unfold yaglomDensity
  fun_prop

lemma yaglomDensity_nonneg (t : ℝ) (x : ℝ) : 0 ≤ yaglomDensity t x := by
  exact mul_nonneg (div_nonneg (by norm_num) (sq_nonneg t)) (Real.exp_pos _).le

lemma integrableOn_yaglomDensity {t : ℝ} (ht : 0 < t) :
    IntegrableOn (yaglomDensity t) (Set.Ici (0 : ℝ)) := by
  change Integrable (yaglomDensity t) (volume.restrict (Set.Ici (0 : ℝ)))
  have ha : -2 / t < 0 := div_neg_of_neg_of_pos (by norm_num) ht
  have hexp : Integrable
      (fun x : ℝ ↦ Real.exp ((-2 / t) * x))
      (volume.restrict (Set.Ici (0 : ℝ))) :=
    integrableOn_Ici_iff_integrableOn_Ioi.mpr (integrableOn_exp_mul_Ioi ha 0)
  convert hexp.const_mul (4 / t ^ 2) using 1
  ext x
  unfold yaglomDensity
  congr 2
  ring

/-- Direct Laplace transform of the candidate density. -/
theorem integral_laplace_yaglomDensity {t p : ℝ} (ht : 0 < t) (hp : 0 < p) :
    (∫ x : ℝ in Set.Ici 0, Real.exp (-p * x) * yaglomDensity t x) =
      4 / (t * (t * p + 2)) := by
  let a : ℝ := -p - 2 / t
  have ha : a < 0 := by
    dsimp [a]
    have htwo : 0 < 2 / t := div_pos (by norm_num) ht
    linarith
  calc
    (∫ x : ℝ in Set.Ici 0, Real.exp (-p * x) * yaglomDensity t x) =
        (4 / t ^ 2) * ∫ x : ℝ in Set.Ici 0, Real.exp (a * x) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with x
      unfold yaglomDensity
      calc
        Real.exp (-p * x) * (4 / t ^ 2 * Real.exp (-2 * x / t)) =
            (4 / t ^ 2) * (Real.exp (-p * x) * Real.exp (-2 * x / t)) := by ring
        _ = (4 / t ^ 2) * Real.exp ((-p * x) + (-2 * x / t)) := by
          rw [Real.exp_add]
        _ = (4 / t ^ 2) * Real.exp (a * x) := by
          congr 2
          dsimp [a]
          ring
    _ = (4 / t ^ 2) * (-1 / a) := by
      rw [integral_Ici_eq_integral_Ioi, integral_exp_mul_Ioi ha 0]
      simp
    _ = 4 / (t * (t * p + 2)) := by
      have ht0 : t ≠ 0 := ne_of_gt ht
      have hden : t * p + 2 ≠ 0 := ne_of_gt (add_pos (mul_pos ht hp) (by norm_num))
      have ha_eq : a = -(t * p + 2) / t := by
        dsimp [a]
        field_simp [ht0]
        ring
      have hrecip : -1 / a = t / (t * p + 2) := by
        rw [ha_eq, div_div_eq_mul_div, div_neg]
        ring
      rw [hrecip]
      field_simp [ht0, hden]
      ring

/-- U59: inversion of the limiting Laplace transform, including the endpoint `x = 0`. -/
theorem yaglomDensity_eq_of_laplace
    {t : ℝ} (ht : 0 < t) {u : ℝ → ℝ}
    (hucont : ContinuousOn u (Set.Ici (0 : ℝ)))
    (hu : ∀ x ∈ Set.Ici (0 : ℝ), 0 ≤ u x)
    (huint : IntegrableOn u (Set.Ici (0 : ℝ)))
    (hLaplace : ∀ p : ℝ, 0 < p →
      (∫ x : ℝ in Set.Ici 0, Real.exp (-p * x) * u x) =
        4 / (t * (t * p + 2))) :
    ∀ x ∈ Set.Ici (0 : ℝ),
      u x = 4 / t ^ 2 * Real.exp (-2 * x / t) := by
  let us : Set.Ici (0 : ℝ) → ℝ := fun x ↦ u x.1
  let vs : Set.Ici (0 : ℝ) → ℝ := fun x ↦ yaglomDensity t x.1
  have huconts : Continuous us := by
    exact hucont.restrict
  have hvconts : Continuous vs := by
    exact (continuous_yaglomDensity t).comp continuous_subtype_val
  have hus : ∀ x, 0 ≤ us x := fun x ↦ hu x.1 x.2
  have hvs : ∀ x, 0 ≤ vs x := fun x ↦ yaglomDensity_nonneg t x.1
  have huints : Integrable us (volume : Measure (Set.Ici (0 : ℝ))) := by
    rw [Measure.Subtype.volume_def]
    exact (integrableOn_iff_comap_subtypeVal measurableSet_Ici).mp huint
  have hvints : Integrable vs (volume : Measure (Set.Ici (0 : ℝ))) := by
    rw [Measure.Subtype.volume_def]
    exact (integrableOn_iff_comap_subtypeVal measurableSet_Ici).mp
      (integrableOn_yaglomDensity ht)
  have hLaplaceSub : ∀ p : ℝ, 0 < p →
      (∫ x, Real.exp (-p * x.1) * us x) =
        ∫ x, Real.exp (-p * x.1) * vs x := by
    intro p hp
    change (∫ x : Set.Ici (0 : ℝ), Real.exp (-p * x.1) * u x.1) =
      ∫ x : Set.Ici (0 : ℝ), Real.exp (-p * x.1) * yaglomDensity t x.1
    rw [integral_subtype measurableSet_Ici
      (fun x : ℝ ↦ Real.exp (-p * x) * u x),
      integral_subtype measurableSet_Ici
        (fun x : ℝ ↦ Real.exp (-p * x) * yaglomDensity t x)]
    exact (hLaplace p hp).trans (integral_laplace_yaglomDensity ht hp).symm
  letI : SigmaFinite (volume : Measure (Set.Ici (0 : ℝ))) := by
    apply SigmaFinite.of_map (volume : Measure (Set.Ici (0 : ℝ)))
      measurable_subtype_coe.aemeasurable
    rw [MeasurableSet.map_coe_volume measurableSet_Ici]
    infer_instance
  have haeSub : us =ᵐ[(volume : Measure (Set.Ici (0 : ℝ)))] vs :=
    ae_eq_of_halfLine_laplace_eq hus hvs huints hvints hLaplaceSub
  have haeReal : u =ᵐ[volume.restrict (Set.Ici (0 : ℝ))] yaglomDensity t := by
    change ∀ᵐ x ∂volume.restrict (Set.Ici (0 : ℝ)), u x = yaglomDensity t x
    apply (ae_restrict_iff_subtype measurableSet_Ici).mpr
    simpa only [Measure.Subtype.volume_def, us, vs] using haeSub
  have heq : Set.EqOn u (yaglomDensity t) (Set.Ici (0 : ℝ)) :=
    Measure.eqOn_of_ae_eq haeReal hucont (continuous_yaglomDensity t).continuousOn (by
      simp [interior_Ici, closure_Ioi])
  intro x hx
  exact heq hx

end

end DerridaRetaux
