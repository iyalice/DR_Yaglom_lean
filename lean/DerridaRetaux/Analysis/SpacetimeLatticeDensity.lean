import DerridaRetaux.Analysis.GluedExhaustionLimit
import DerridaRetaux.Analysis.LatticeRiemannLimit
import Mathlib.Tactic

set_option autoImplicit false

open Filter Set Topology

namespace DerridaRetaux

noncomputable section

/-- Quantitative local-uniform convergence at every lattice node in a compact
positive-time spacetime box. -/
def LocallyUniformSpacetimeLatticeDensity
    (rho : ℕ → ℕ → Seq) (scale : ℕ → ℕ) (u : ℝ → ℝ → ℝ) : Prop :=
  ∀ eta T : ℝ, ∀ R : ℕ, 0 < eta → eta ≤ T →
    ∃ error : ℕ → ℝ, Tendsto error atTop (nhds 0) ∧
      ∀ n : ℕ, 0 < scale n → ∀ s : ℕ,
        eta * (scale n : ℝ) ≤ s →
        (s : ℝ) ≤ T * (scale n : ℝ) →
        ∀ j : ℕ, j ≤ R * scale n →
          |(scale n : ℝ) ^ 2 * rho n s j -
            u ((s : ℝ) / (scale n : ℝ))
              ((j : ℝ) / (scale n : ℝ))| ≤ error n

/-- Uniform convergence of the two-dimensional interpolants gives the exact
spacetime lattice property, since bilinear interpolation agrees with the
array at every mesh node. -/
theorem locallyUniformSpacetimeLatticeDensity_of_gluedExhaustion
    (rho : ℕ → ℕ → Seq) (a : ℕ → ℕ → ℕ → ℝ) (phi : ℕ → ℕ)
    (g : ∀ k, BoundedContinuousFunction (gridExhaustionRectangle k) ℝ)
    (hnode : ∀ n s j : ℕ,
      a (phi n) s j = (phi n : ℝ) ^ 2 * rho n s j)
    (hlim : ∀ k, TendstoUniformly
      (fun n (p : gridExhaustionRectangle k) ↦
        gridBilinearInterp (phi n) (a (phi n))
          (p : ℝ × ℝ).1 (p : ℝ × ℝ).2)
      (fun p ↦ g k p) atTop) :
    LocallyUniformSpacetimeLatticeDensity rho phi
      (gluedExhaustionLimit g) := by
  intro eta T R heta hetaT
  let B : ℝ := max T (R : ℝ)
  have hB0 : 0 ≤ B := by
    exact le_trans (Nat.cast_nonneg R) (le_max_right T (R : ℝ))
  obtain ⟨k, hk⟩ := exists_mem_gridExhaustionRectangle heta hB0
  let v : ℕ → BoundedContinuousFunction (gridExhaustionRectangle k) ℝ :=
    fun n ↦ compactRestriction (isCompact_gridExhaustionRectangle k)
      (fun p : ℝ × ℝ ↦
        gridBilinearInterp (phi n) (a (phi n)) p.1 p.2)
      (continuous_gridBilinearInterp (phi n) (a (phi n)))
  let error : ℕ → ℝ := fun n ↦ ‖v n - g k‖
  have hv : Tendsto v atTop (nhds (g k)) := by
    apply BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mpr
    simpa only [v, compactRestriction_apply] using hlim k
  have herror : Tendsto error atTop (nhds 0) := by
    have hsub : Tendsto (fun n ↦ v n - g k) atTop (nhds 0) := by
      simpa only [sub_self] using hv.sub
        (tendsto_const_nhds :
          Tendsto (fun _ : ℕ ↦ g k) atTop (nhds (g k)))
    simpa only [error, norm_zero] using hsub.norm
  refine ⟨error, herror, ?_⟩
  intro n hn s hsLower hsUpper j hj
  have hNreal : (0 : ℝ) < (phi n : ℝ) := by exact_mod_cast hn
  let st : ℝ := (s : ℝ) / (phi n : ℝ)
  let x : ℝ := (j : ℝ) / (phi n : ℝ)
  have hstLower : eta ≤ st := by
    dsimp only [st]
    exact (le_div_iff₀ hNreal).2 (by simpa only [mul_comm] using hsLower)
  have hstUpper : st ≤ T := by
    dsimp only [st]
    exact (div_le_iff₀ hNreal).2 (by simpa only [mul_comm] using hsUpper)
  have hx0 : 0 ≤ x := div_nonneg (Nat.cast_nonneg j) hNreal.le
  have hxR : x ≤ (R : ℝ) := by
    dsimp only [x]
    rw [div_le_iff₀ hNreal]
    exact_mod_cast hj
  have hp : (st, x) ∈ gridExhaustionRectangle k := by
    refine ⟨⟨hk.1.1.trans hstLower, hstUpper.trans ?_⟩,
      hx0, hxR.trans ?_⟩
    · exact (le_max_left T (R : ℝ)).trans hk.2.2
    · exact (le_max_right T (R : ℝ)).trans hk.2.2
  let p : gridExhaustionRectangle k := ⟨(st, x), hp⟩
  have hgrid : gridBilinearInterp (phi n) (a (phi n)) st x =
      (phi n : ℝ) ^ 2 * rho n s j := by
    rw [show st = (s : ℝ) / (phi n : ℝ) by rfl,
      show x = (j : ℝ) / (phi n : ℝ) by rfl,
      gridBilinearInterp_at_node (phi n) s j (a (phi n)) hn,
      hnode]
  have hcompat : ∀ {r l : ℕ}, ∀ hrl : r ≤ l,
      ∀ q : gridExhaustionRectangle r,
        g r q = g l ⟨(q : ℝ × ℝ),
          gridExhaustionRectangle_mono hrl q.property⟩ := by
    intro r l hrl q
    exact exhaustionLimits_compatible
      (fun N z ↦ gridBilinearInterp N (a N) z.1 z.2)
      phi g hlim hrl q
  have hglue : gluedExhaustionLimit g st x = g k p :=
    gluedExhaustionLimit_eq_local g hcompat k st x hp
  have hpoint : |v n p - g k p| ≤ error n := by
    simpa only [error, Real.norm_eq_abs] using
      (v n - g k).norm_coe_le_norm p
  calc
    |(phi n : ℝ) ^ 2 * rho n s j -
        gluedExhaustionLimit g ((s : ℝ) / (phi n : ℝ))
          ((j : ℝ) / (phi n : ℝ))| =
      |v n p - g k p| := by
        rw [compactRestriction_apply]
        dsimp only [p]
        rw [hgrid, hglue]
    _ ≤ error n := hpoint

/-- Source specialization to the literal scaled DR orbit array. -/
theorem locallyUniformSpacetimeLatticeDensity_orbit_of_gluedExhaustion
    (m : ℕ) (p₀ : ProbabilityMass) (phi : ℕ → ℕ)
    (g : ∀ k, BoundedContinuousFunction (gridExhaustionRectangle k) ℝ)
    (hlim : ∀ k, TendstoUniformly
      (fun n (p : gridExhaustionRectangle k) ↦
        gridBilinearInterp (phi n) (orbitScaledGrid m p₀ (phi n))
          (p : ℝ × ℝ).1 (p : ℝ × ℝ).2)
      (fun p ↦ g k p) atTop) :
    LocallyUniformSpacetimeLatticeDensity
      (fun _n s ↦ positiveTiltedDensity m (orbit m p₀ s))
      phi (gluedExhaustionLimit g) := by
  apply locallyUniformSpacetimeLatticeDensity_of_gluedExhaustion
    (a := orbitScaledGrid m p₀) (g := g)
  · intro n s j
    rfl
  · exact hlim

end

end DerridaRetaux
