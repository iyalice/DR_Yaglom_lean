import DerridaRetaux.Analysis.ProfileCompactnessSubsequence
import DerridaRetaux.Main.ContinuumProfile

set_option autoImplicit false

open Filter Set Topology

namespace DerridaRetaux.FixedArity

noncomputable section

/-- A globally continuous extension of the Yaglom density from the half-strip `t ≥ eta`. -/
def positiveTimeYaglomExtension (eta : ℝ) (p : ℝ × ℝ) : ℝ :=
  yaglomDensity (max p.1 eta) p.2

theorem continuous_positiveTimeYaglomExtension {eta : ℝ} (heta : 0 < eta) :
    Continuous (positiveTimeYaglomExtension eta) := by
  unfold positiveTimeYaglomExtension yaglomDensity
  have hmax : Continuous (fun p : ℝ × ℝ ↦ max p.1 eta) :=
    continuous_fst.max continuous_const
  have hne : ∀ p : ℝ × ℝ, max p.1 eta ≠ 0 := by
    intro p
    exact ne_of_gt (heta.trans_le (le_max_right p.1 eta))
  have hleft : Continuous (fun p : ℝ × ℝ ↦ 4 / max p.1 eta ^ 2) :=
    continuous_const.div₀ (hmax.pow 2) (fun p ↦ pow_ne_zero 2 (hne p))
  have harg : Continuous (fun p : ℝ × ℝ ↦ -2 * p.2 / max p.1 eta) :=
    (continuous_const.mul continuous_snd).div₀ hmax hne
  exact hleft.mul (Real.continuous_exp.comp harg)

/-- The explicit candidate, packaged in the sup-norm space on one exhaustion rectangle. -/
def yaglomRectangleLimit (k : ℕ) :
    BoundedContinuousFunction (gridExhaustionRectangle k) ℝ :=
  compactRestriction (isCompact_gridExhaustionRectangle k)
    (positiveTimeYaglomExtension (((k + 1 : ℕ) : ℝ)⁻¹))
    (continuous_positiveTimeYaglomExtension (by positivity))

@[simp]
theorem yaglomRectangleLimit_apply (k : ℕ)
    (p : gridExhaustionRectangle k) :
    yaglomRectangleLimit k p = yaglomDensity p.1.1 p.1.2 := by
  rw [yaglomRectangleLimit, compactRestriction_apply]
  unfold positiveTimeYaglomExtension
  rw [max_eq_left p.property.1.1]

/-- On every exhaustion rectangle, the full sequence of interpolated rescaled tilted densities
converges uniformly to the explicit Yaglom density. -/
theorem orbitInterpolants_tendstoUniformlyOn_exhaustion
    (m : ℕ) (data : ProfileInitialData m) :
    ∀ k, TendstoUniformly
      (fun N (p : gridExhaustionRectangle k) ↦
        gridBilinearInterp N (orbitScaledGrid m data.law N)
          (p : ℝ × ℝ).1 (p : ℝ × ℝ).2)
      (fun p ↦ yaglomDensity (p : ℝ × ℝ).1 (p : ℝ × ℝ).2) atTop := by
  obtain ⟨C, hC, hSup, _hGradient, hSpatial, hTemporal⟩ :=
    smoothing m data.law data.arity data.critical data.third data.notBinaryFixedPoint
  intro k
  let K : Set (ℝ × ℝ) := gridExhaustionRectangle k
  let F : ℕ → (ℝ × ℝ) → ℝ := fun N p ↦
    gridBilinearInterp N (orbitScaledGrid m data.law N) p.1 p.2
  let FB : ℕ → BoundedContinuousFunction K ℝ := fun N ↦
    compactRestriction (isCompact_gridExhaustionRectangle k) (F N)
      (continuous_gridBilinearInterp N (orbitScaledGrid m data.law N))
  let y : BoundedContinuousFunction K ℝ := yaglomRectangleLimit k
  have hBCF : Tendsto FB atTop (𝓝 y) := by
    apply tendsto_of_subseq_tendsto
    intro ns hns
    obtain ⟨g, phi, _hphi, hphiTop, hlim⟩ :=
      orbitScaledGrid_compactness_after m data.law hC.le hSup hSpatial hTemporal ns hns
    let psi : ℕ → ℕ := ns ∘ phi
    have hpsi : Tendsto psi atTop atTop := hns.comp hphiTop
    have hlimPsi : ∀ l, TendstoUniformly
        (fun n (p : gridExhaustionRectangle l) ↦
          gridBilinearInterp (psi n) (orbitScaledGrid m data.law (psi n))
            (p : ℝ × ℝ).1 (p : ℝ × ℝ).2)
        (fun p ↦ g l p) atTop := by
      simpa only [psi, Function.comp_apply] using hlim
    have hprofile := subsequentialDensity_eq_yaglom
      m data psi g hpsi hlimPsi (κ := 1) (by norm_num)
    have hcompat : ∀ {a b : ℕ}, ∀ hab : a ≤ b,
        ∀ p : gridExhaustionRectangle a,
          g a p = g b ⟨(p : ℝ × ℝ),
            gridExhaustionRectangle_mono hab p.property⟩ := by
      intro a b hab p
      exact exhaustionLimits_compatible F psi g hlimPsi hab p
    have hgy : g k = y := by
      ext p
      change g k p = yaglomRectangleLimit k p
      rw [← gluedExhaustionLimit_eq_local g hcompat k p.1.1 p.1.2 p.property,
        yaglomRectangleLimit_apply]
      exact hprofile p.1.1 p.1.2
        (lt_of_lt_of_le (by positivity) p.property.1.1) p.property.2.1
    refine ⟨phi, ?_⟩
    have hlimBCF : Tendsto
        (fun n ↦ compactRestriction (isCompact_gridExhaustionRectangle k)
          (F (psi n))
          (continuous_gridBilinearInterp (psi n) (orbitScaledGrid m data.law (psi n))))
        atTop (𝓝 (g k)) := by
      apply BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mpr
      simpa only [F, compactRestriction_apply] using hlimPsi k
    simpa only [FB, F, psi, Function.comp_apply, hgy] using hlimBCF
  have huniform := BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp hBCF
  change TendstoUniformly (fun N (p : K) ↦ F N p) (fun p ↦ yaglomDensity p.1.1 p.1.2) atTop
  change TendstoUniformly (fun N (p : K) ↦ F N p) (fun p ↦ y p) atTop at huniform
  have hy : (fun p : K ↦ y p) = (fun p ↦ yaglomDensity p.1.1 p.1.2) := by
    funext p
    exact yaglomRectangleLimit_apply k p
  rwa [hy] at huniform

end

end DerridaRetaux.FixedArity
