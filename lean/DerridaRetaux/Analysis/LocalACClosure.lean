import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.UniformSpace.UniformConvergence
import Mathlib.Tactic

/-!
# Closure of local integral derivatives

This file isolates the analytic closure step U47.  On a compact time interval,
an absolutely continuous observable is represented by an integrable derivative
and the fundamental integral identity on every subinterval.  Uniform convergence
of the observables and local `L¹` convergence of their derivatives preserve this
representation.  No equation from the Derrida--Retaux model is assumed here.
-/

set_option autoImplicit false

open Filter MeasureTheory Set Topology
open scoped ENNReal

namespace DerridaRetaux

noncomputable section

/-- Integral-identity form of absolute continuity with a specified derivative
on a set.  In applications `K` is a compact interval. -/
def HasIntegralDerivativeOn (F g : ℝ → ℝ) (K : Set ℝ) : Prop :=
  Integrable g (volume.restrict K) ∧
    ∀ x : ℝ, x ∈ K → ∀ y : ℝ, y ∈ K → x ≤ y →
      F y - F x = ∫ s in Ioc x y, g s ∂(volume.restrict K)

/-- Local `L¹` convergence on a fixed set, with all integrability data made
explicit.  The `lintegral` is the literal `L¹` distance. -/
def TendstoInL1On
    (gSeq : ℕ → ℝ → ℝ) (g : ℝ → ℝ) (K : Set ℝ) : Prop :=
  Integrable g (volume.restrict K) ∧
    (∀ n : ℕ, Integrable (gSeq n) (volume.restrict K)) ∧
    Tendsto
      (fun n : ℕ ↦
        ∫⁻ s, ‖gSeq n s - g s‖ₑ ∂(volume.restrict K))
      atTop (𝓝 0)

/-- Fixed-compact closure lemma requested in U47.  Uniform convergence of the
observables and `L¹` convergence of their derivatives preserve the full
subinterval integral identity, hence local absolute continuity and the a.e.
derivative represented by `g`. -/
theorem hasIntegralDerivativeOn_of_tendstoUniformly_of_tendstoInL1On
    (FSeq : ℕ → ℝ → ℝ) (F : ℝ → ℝ)
    (gSeq : ℕ → ℝ → ℝ) (g : ℝ → ℝ) (K : Set ℝ)
    (hFSeq : ∀ n : ℕ, HasIntegralDerivativeOn (FSeq n) (gSeq n) K)
    (hFuniform : TendstoUniformly
      (fun n (x : K) ↦ FSeq n x) (fun x : K ↦ F x) atTop)
    (hgL1 : TendstoInL1On gSeq g K) :
    HasIntegralDerivativeOn F g K := by
  refine ⟨hgL1.1, ?_⟩
  intro x hx y hy hxy
  let xK : K := ⟨x, hx⟩
  let yK : K := ⟨y, hy⟩
  have hxlim : Tendsto (fun n : ℕ ↦ FSeq n x) atTop (𝓝 (F x)) := by
    simpa only [xK] using hFuniform.tendsto_at xK
  have hylim : Tendsto (fun n : ℕ ↦ FSeq n y) atTop (𝓝 (F y)) := by
    simpa only [yK] using hFuniform.tendsto_at yK
  have hleft :
      Tendsto (fun n : ℕ ↦ FSeq n y - FSeq n x)
        atTop (𝓝 (F y - F x)) := hylim.sub hxlim
  have hright :
      Tendsto
        (fun n : ℕ ↦
          ∫ s in Ioc x y, gSeq n s ∂(volume.restrict K))
        atTop
        (𝓝 (∫ s in Ioc x y, g s ∂(volume.restrict K))) := by
    exact tendsto_setIntegral_of_L1 g hgL1.1
      (Eventually.of_forall fun n ↦ hgL1.2.1 n) hgL1.2.2 (Ioc x y)
  have hright' :
      Tendsto (fun n : ℕ ↦ FSeq n y - FSeq n x)
        atTop
        (𝓝 (∫ s in Ioc x y, g s ∂(volume.restrict K))) := by
    apply hright.congr'
    exact Eventually.of_forall fun n ↦
      ((hFSeq n).2 x hx y hy hxy).symm
  exact tendsto_nhds_unique hleft hright'

/-- Local form on every compact positive-time interval. -/
theorem hasIntegralDerivativeOn_Icc_of_local_uniform_and_L1
    (FSeq : ℕ → ℝ → ℝ) (F : ℝ → ℝ)
    (gSeq : ℕ → ℝ → ℝ) (g : ℝ → ℝ)
    (hFSeq : ∀ eta T : ℝ, 0 < eta → eta ≤ T → ∀ n : ℕ,
      HasIntegralDerivativeOn (FSeq n) (gSeq n) (Icc eta T))
    (hFuniform : ∀ eta T : ℝ, 0 < eta → eta ≤ T →
      TendstoUniformly
        (fun n (x : Icc eta T) ↦ FSeq n x)
        (fun x : Icc eta T ↦ F x) atTop)
    (hgL1 : ∀ eta T : ℝ, 0 < eta → eta ≤ T →
      TendstoInL1On gSeq g (Icc eta T)) :
    ∀ eta T : ℝ, 0 < eta → eta ≤ T →
      HasIntegralDerivativeOn F g (Icc eta T) := by
  intro eta T heta hetaT
  exact hasIntegralDerivativeOn_of_tendstoUniformly_of_tendstoInL1On
    FSeq F gSeq g (Icc eta T)
    (hFSeq eta T heta hetaT) (hFuniform eta T heta hetaT)
    (hgL1 eta T heta hetaT)

/-- If the limiting derivative is continuous, the integral representation
upgrades the a.e. derivative to a pointwise derivative at every interior time.
This is the generic final step used by U48. -/
theorem HasIntegralDerivativeOn.hasDerivAt_of_continuousOn_Icc
    (F g : ℝ → ℝ) (eta T t : ℝ)
    (hF : HasIntegralDerivativeOn F g (Icc eta T))
    (hg : ContinuousOn g (Icc eta T))
    (ht : t ∈ Ioo eta T) :
    HasDerivAt F (g t) t := by
  have htK : t ∈ Icc eta T := ⟨ht.1.le, ht.2.le⟩
  have hKnhds : Icc eta T ∈ 𝓝 t :=
    mem_of_superset (Ioo_mem_nhds ht.1 ht.2) Ioo_subset_Icc_self
  have hgt : ContinuousAt g t := (hg t htK).continuousAt hKnhds
  have hgsm : StronglyMeasurableAtFilter g (𝓝 t) volume := by
    apply ContinuousAt.stronglyMeasurableAtFilter (μ := volume) isOpen_Ioo
    · intro z hz
      apply (hg z ⟨hz.1.le, hz.2.le⟩).continuousAt
      exact mem_of_superset (Ioo_mem_nhds hz.1 hz.2) Ioo_subset_Icc_self
    · exact ht
  have hprimitive :
      HasDerivAt (fun z : ℝ ↦ F t + ∫ s in t..z, g s) (g t) t := by
    have hint : IntervalIntegrable g volume t t := by simp
    exact (intervalIntegral.integral_hasDerivAt_right
      hint hgsm hgt).const_add (F t)
  apply hprimitive.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds ht.1 ht.2] with z hz
  have hzK : z ∈ Icc eta T := ⟨hz.1.le, hz.2.le⟩
  by_cases htz : t ≤ z
  · have hsubset : Ioc t z ⊆ Icc eta T := by
      intro s hs
      exact ⟨ht.1.le.trans hs.1.le, hs.2.trans hz.2.le⟩
    have hrestrict :
        (∫ s in Ioc t z, g s ∂(volume.restrict (Icc eta T))) =
          ∫ s in t..z, g s := by
      rw [Measure.restrict_restrict_of_subset hsubset,
        intervalIntegral.integral_of_le htz]
    rw [← hrestrict, ← (hF.2 t htK z hzK htz)]
    ring
  · have hzt : z ≤ t := le_of_not_ge htz
    have hsubset : Ioc z t ⊆ Icc eta T := by
      intro s hs
      exact ⟨hz.1.le.trans hs.1.le, hs.2.trans ht.2.le⟩
    have hrestrict :
        (∫ s in Ioc z t, g s ∂(volume.restrict (Icc eta T))) =
          ∫ s in z..t, g s := by
      rw [Measure.restrict_restrict_of_subset hsubset,
        intervalIntegral.integral_of_le hzt]
    rw [intervalIntegral.integral_symm, ← hrestrict,
      ← (hF.2 z hzK t htK hzt)]
    ring

/-- Continuous integral derivatives are continuously differentiable on the
open interior of the compact interval. -/
theorem HasIntegralDerivativeOn.contDiffOn_Ioo_of_continuousOn_Icc
    (F g : ℝ → ℝ) (eta T : ℝ)
    (hF : HasIntegralDerivativeOn F g (Icc eta T))
    (hg : ContinuousOn g (Icc eta T)) :
    ContDiffOn ℝ 1 F (Ioo eta T) := by
  apply (contDiffOn_succ_iff_deriv_of_isOpen
    (𝕜 := ℝ) (n := 0) isOpen_Ioo).2
  refine ⟨fun t ht ↦
    (hF.hasDerivAt_of_continuousOn_Icc F g eta T t hg ht).differentiableAt.differentiableWithinAt,
    by simp, ?_⟩
  rw [contDiffOn_zero]
  have hderiv : EqOn (deriv F) g (Ioo eta T) := by
    intro t ht
    exact (hF.hasDerivAt_of_continuousOn_Icc F g eta T t hg ht).deriv
  exact (hg.mono Ioo_subset_Icc_self).congr hderiv

end

end DerridaRetaux
