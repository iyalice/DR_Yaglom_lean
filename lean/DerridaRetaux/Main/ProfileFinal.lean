import DerridaRetaux.Main.ProfileConvergence
import DerridaRetaux.Analysis.ProfileConsequences
import DerridaRetaux.Analysis.DensityMassFromCompact

set_option autoImplicit false

open Filter Set Topology

namespace DerridaRetaux.FixedArity

noncomputable section

/-- The source theorem `thm:profile` / equation `eq:mainprofile`, in explicit compact-uniform
error form. -/
theorem profileDensity
    (m : ℕ) (data : ProfileInitialData m) :
    ∀ R : ℝ, 0 ≤ R → ∃ error : ℕ → ℝ,
      Tendsto error atTop (𝓝 0) ∧
        ∀ n : ℕ, 0 < n → ∀ x : ℝ, 0 ≤ x → x ≤ R →
          |(n : ℝ) ^ 2 * rho m (orbit m data.law n) (gridIndex n x) -
            4 * Real.exp (-2 * x)| ≤ error n := by
  obtain ⟨C, hC, _hSup, hGradient, _hSpatial, _hTemporal⟩ :=
    smoothing m data.law data.arity data.critical data.third data.notBinaryFixedPoint
  intro R hR
  obtain ⟨k, hk⟩ := exists_mem_gridExhaustionRectangle (t := (1 : ℝ)) (x := R)
    (by norm_num) hR
  let K : Set (ℝ × ℝ) := gridExhaustionRectangle k
  let F : ℕ → (ℝ × ℝ) → ℝ := fun N p ↦
    gridBilinearInterp N (orbitScaledGrid m data.law N) p.1 p.2
  let v : ℕ → BoundedContinuousFunction K ℝ := fun N ↦
    compactRestriction (isCompact_gridExhaustionRectangle k) (F N)
      (continuous_gridBilinearInterp N (orbitScaledGrid m data.law N))
  let y : BoundedContinuousFunction K ℝ := yaglomRectangleLimit k
  have huniform := orbitInterpolants_tendstoUniformlyOn_exhaustion m data k
  have hv : Tendsto v atTop (𝓝 y) := by
    apply BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mpr
    change TendstoUniformly (fun N (p : K) ↦ F N p) (fun p ↦ y p) atTop
    have hy : (fun p : K ↦ y p) =
        (fun p ↦ yaglomDensity p.1.1 p.1.2) := by
      funext p
      exact yaglomRectangleLimit_apply k p
    rw [hy]
    exact huniform
  let interpolationError : ℕ → ℝ := fun n ↦ ‖v n - y‖
  have hinterpolationError : Tendsto interpolationError atTop (𝓝 0) := by
    have hsub : Tendsto (fun n ↦ v n - y) atTop (𝓝 0) := by
      simpa only [sub_self] using hv.sub
        (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ y) atTop (𝓝 y))
    simpa only [interpolationError, norm_zero] using hsub.norm
  let error : ℕ → ℝ := fun n ↦
    orbitScaledGridStepError C n + interpolationError n
  have herror : Tendsto error atTop (𝓝 0) := by
    simpa only [error, zero_add] using
      (orbitScaledGridStepError_tendsto_zero C).add hinterpolationError
  refine ⟨error, herror, ?_⟩
  intro n hn x hx hxR
  have hp : (1, x) ∈ gridExhaustionRectangle k :=
    ⟨hk.1, hx, hxR.trans hk.2.2⟩
  let p : K := ⟨(1, x), hp⟩
  have hnorm : |F n p - yaglomDensity 1 x| ≤ interpolationError n := by
    have hpoint := (v n - y).norm_coe_le_norm p
    change |F n p - y p| ≤ interpolationError n at hpoint
    rw [yaglomRectangleLimit_apply] at hpoint
    simpa only [p] using hpoint
  have hGradientCast : ∀ r : ℕ,
      WeightedSupThreeLE (profileScale r)
        (discreteDerivative (positiveTiltedDensity m (orbit m data.law r)))
        (C * Real.log ((r : ℝ) + 2) / profileScale r ^ 3) := by
    intro r
    simpa only [Nat.cast_add, Nat.cast_ofNat] using hGradient r
  have hread := abs_gridBilinearInterp_time_one_sub_floor_le_of_bound
    n (orbitScaledGrid m data.law n) x (orbitScaledGridStepError C n) hn
      (orbitScaledGrid_adjacent_le_of_gradient m data.law C hGradientCast n hn)
  change |orbitScaledGrid m data.law n n (gridIndex n x) -
    4 * Real.exp (-2 * x)| ≤ error n
  have htarget : yaglomDensity 1 x = 4 * Real.exp (-2 * x) := by
    unfold yaglomDensity
    ring_nf
  rw [← htarget]
  calc
    |orbitScaledGrid m data.law n n (gridIndex n x) - yaglomDensity 1 x| ≤
        |orbitScaledGrid m data.law n n (gridIndex n x) - F n p| +
          |F n p - yaglomDensity 1 x| := abs_sub_le _ _ _
    _ ≤ orbitScaledGridStepError C n + interpolationError n :=
      add_le_add (by simpa only [F, p, abs_sub_comm] using hread) hnorm
    _ = error n := rfl

end

end DerridaRetaux.FixedArity
