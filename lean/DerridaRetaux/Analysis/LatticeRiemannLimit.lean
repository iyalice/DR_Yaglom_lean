import DerridaRetaux.Analysis.LatticeWeakConvergence
import DerridaRetaux.Analysis.GridReadout
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

set_option autoImplicit false

open Filter Topology MeasureTheory Set
open scoped BigOperators BoundedContinuousFunction ENNReal Interval

namespace DerridaRetaux

noncomputable section

/-!
# Local-uniform lattice limits

The purpose of this file is to discharge the genuinely analytic part of the
U40 measure bridge.  A uniform error for the quadratic-scale coefficients on
each fixed macroscopic window is first integrated over that window.  An
independent left-Riemann-sum lemma then identifies the resulting limit.  No
measure convergence (or compact-sum convergence) is used as a premise.
-/

/-- The left Riemann sum on `[0,R]` with mesh `1 / N`.  The value at the
right endpoint is omitted, as usual; this is convenient for `Finset.range`.
The definition at `N = 0` is harmless for limits at infinity. -/
def latticeLeftRiemannSum (f : ℝ → ℝ) (R N : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (R * N),
    (N : ℝ)⁻¹ * f ((j : ℝ) / (N : ℝ))

/-- Continuity on the fixed compact interval is enough for the usual left
Riemann sums.  This statement is deliberately independent of the lattice
measures used later in the file. -/
theorem latticeLeftRiemannSum_tendsto_intervalIntegral
    (f : ℝ → ℝ) (R : ℕ)
    (hf : ContinuousOn f (Icc (0 : ℝ) (R : ℝ))) :
    Tendsto (latticeLeftRiemannSum f R) atTop
      (nhds (∫ x in (0 : ℝ)..(R : ℝ), f x)) := by
  by_cases hR : R = 0
  · subst R
    have hzero : latticeLeftRiemannSum f 0 = fun _ : ℕ ↦ (0 : ℝ) := by
      funext N
      simp [latticeLeftRiemannSum]
    rw [hzero]
    simp
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  let η : ℝ := ε / ((R : ℝ) + 1)
  have hη : 0 < η := by
    dsimp only [η]
    exact div_pos hε (by positivity)
  have hfuniform : UniformContinuousOn f (Icc (0 : ℝ) (R : ℝ)) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hf
  obtain ⟨δ, hδ, hmod⟩ :=
    Metric.uniformContinuousOn_iff.mp hfuniform η hη
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt δ⁻¹
  refine ⟨max N₀ 1, fun N hN ↦ ?_⟩
  have hN₀N : N₀ ≤ N := (le_max_left N₀ 1).trans hN
  have hNpos : 0 < N := (le_max_right N₀ 1).trans hN
  have hNreal : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNpos
  have hNne : (N : ℝ) ≠ 0 := hNreal.ne'
  have hinvlt : (N : ℝ)⁻¹ < δ := by
    apply (inv_lt_comm₀ hNreal hδ).2
    exact hN₀.trans_le (by exact_mod_cast hN₀N)
  let a : ℕ → ℝ := fun j ↦ (j : ℝ) / (N : ℝ)
  have ha_mono : ∀ j : ℕ, a j ≤ a (j + 1) := by
    intro j
    dsimp only [a]
    apply div_le_div_of_nonneg_right _ hNreal.le
    exact_mod_cast Nat.le_succ j
  have ha_nonneg : ∀ j : ℕ, 0 ≤ a j := by
    intro j
    exact div_nonneg (Nat.cast_nonneg j) hNreal.le
  have ha_le_R : ∀ {j : ℕ}, j ≤ R * N → a j ≤ (R : ℝ) := by
    intro j hj
    dsimp only [a]
    rw [div_le_iff₀ hNreal]
    exact_mod_cast hj
  have hcellSubset : ∀ j < R * N,
      Icc (a j) (a (j + 1)) ⊆ Icc (0 : ℝ) (R : ℝ) := by
    intro j hj x hx
    exact ⟨(ha_nonneg j).trans hx.1,
      hx.2.trans (ha_le_R (Nat.succ_le_iff.mpr hj))⟩
  have hpartition :
      ∑ j ∈ Finset.range (R * N),
          ∫ x in a j..a (j + 1), f x =
        ∫ x in (0 : ℝ)..(R : ℝ), f x := by
    have hsum := intervalIntegral.sum_integral_adjacent_intervals
      (f := f) (a := a) (n := R * N) (μ := volume)
      (fun j hj ↦
        (hf.mono (hcellSubset j hj)).intervalIntegrable_of_Icc (ha_mono j))
    simpa [a, Nat.cast_mul, hNne] using hsum
  have hcell : ∀ j < R * N,
      |(N : ℝ)⁻¹ * f (a j) - ∫ x in a j..a (j + 1), f x| ≤
        η * (N : ℝ)⁻¹ := by
    intro j hj
    have hstep : a (j + 1) - a j = (N : ℝ)⁻¹ := by
      dsimp only [a]
      push_cast
      field_simp only [hNne]
      ring
    have hconst :
        (N : ℝ)⁻¹ * f (a j) =
          ∫ _x in a j..a (j + 1), f (a j) := by
      rw [intervalIntegral.integral_const]
      simp only [smul_eq_mul, hstep]
    have hconstInt : IntervalIntegrable (fun _x : ℝ ↦ f (a j)) volume
        (a j) (a (j + 1)) := continuous_const.intervalIntegrable _ _
    have hfInt : IntervalIntegrable f volume (a j) (a (j + 1)) :=
      (hf.mono (hcellSubset j hj)).intervalIntegrable_of_Icc (ha_mono j)
    rw [hconst, ← intervalIntegral.integral_sub hconstInt hfInt]
    calc
      |∫ x in a j..a (j + 1), f (a j) - f x| =
          ‖∫ x in a j..a (j + 1), f (a j) - f x‖ := by
            rw [Real.norm_eq_abs]
      _ ≤ η * |a (j + 1) - a j| := by
        apply intervalIntegral.norm_integral_le_of_norm_le_const
        intro x hx
        rw [Set.uIoc_of_le (ha_mono j)] at hx
        have hd : dist (a j) x < δ := by
          rw [Real.dist_eq, abs_sub_comm,
            abs_of_nonneg (sub_nonneg.mpr hx.1.le)]
          calc
            x - a j ≤ a (j + 1) - a j := sub_le_sub_right hx.2 _
            _ = (N : ℝ)⁻¹ := hstep
            _ < δ := hinvlt
        simpa only [Real.norm_eq_abs, Real.dist_eq] using
          (le_of_lt (hmod (a j)
            (hcellSubset j hj ⟨le_rfl, ha_mono j⟩) x
            (hcellSubset j hj ⟨hx.1.le, hx.2⟩) hd))
      _ = η * (N : ℝ)⁻¹ := by
        congr 1
        rw [hstep, abs_of_pos (inv_pos.mpr hNreal)]
  rw [latticeLeftRiemannSum, ← hpartition, Real.dist_eq,
    ← Finset.sum_sub_distrib]
  calc
    |∑ j ∈ Finset.range (R * N),
        ((N : ℝ)⁻¹ * f ((j : ℝ) / (N : ℝ)) -
          ∫ x in a j..a (j + 1), f x)| ≤
        ∑ j ∈ Finset.range (R * N),
          |(N : ℝ)⁻¹ * f ((j : ℝ) / (N : ℝ)) -
            ∫ x in a j..a (j + 1), f x| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ Finset.range (R * N), η * (N : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro j hj
      simpa only [a] using hcell j (Finset.mem_range.mp hj)
    _ = (R : ℝ) * η := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      push_cast
      field_simp only [hNne]
      ring
    _ < ε := by
      dsimp only [η]
      have hdenpos : (0 : ℝ) < (R : ℝ) + 1 := by positivity
      have hfrac : (R : ℝ) / ((R : ℝ) + 1) < 1 :=
        (div_lt_one hdenpos).2 (by linarith)
      calc
        (R : ℝ) * (ε / ((R : ℝ) + 1)) =
            ε * ((R : ℝ) / ((R : ℝ) + 1)) := by ring
        _ < ε * 1 := mul_lt_mul_of_pos_left hfrac hε
        _ = ε := mul_one _

/-- A sequential, quantitative formulation of local-uniform convergence of
the scaled lattice density.  For each fixed window `[0,R]`, one error modulus
controls all grid nodes in that window and tends to zero.  The condition is
only imposed when the selected scale is positive, so a cofinal scale may
still have finitely many initial zero values. -/
def LocallyUniformLatticeDensity
    (rho : ℕ → Seq) (scale : ℕ → ℕ) (u : ℝ → ℝ) : Prop :=
  ∀ R : ℕ, ∃ error : ℕ → ℝ,
    Tendsto error atTop (nhds 0) ∧
      ∀ k : ℕ, 0 < scale k → ∀ j : ℕ, j ≤ R * scale k →
        |((scale k : ℕ) : ℝ) ^ 2 * rho k j -
          u ((j : ℝ) / ((scale k : ℕ) : ℝ))| ≤ error k

/-- A compactly supported real function has a strict natural upper cutoff.
Only the positive half-line is relevant for the lattice measures. -/
theorem exists_nat_upper_cutoff_of_hasCompactSupport
    (g : ℝ → ℝ) (hg : HasCompactSupport g) :
    ∃ R : ℕ, ∀ x : ℝ, (R : ℝ) ≤ x → g x = 0 := by
  obtain ⟨r, hr⟩ := hg.isCompact.isBounded.subset_ball (0 : ℝ)
  obtain ⟨R, hR⟩ := exists_nat_gt r
  refine ⟨R, fun x hx ↦ image_eq_zero_of_nmem_tsupport ?_⟩
  intro hxmem
  have hxball := hr hxmem
  rw [Metric.mem_ball] at hxball
  have hxnonneg : 0 ≤ x := (Nat.cast_nonneg R).trans hx
  have hdist : dist x (0 : ℝ) = x := by
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hxnonneg]
  rw [hdist] at hxball
  linarith

/-- If a function vanishes to the left of zero and from a natural cutoff
onwards, its full Lebesgue integral is the corresponding interval integral. -/
theorem integral_eq_intervalIntegral_of_zero_outside_nat
    (f : ℝ → ℝ) (R : ℕ)
    (hneg : ∀ x : ℝ, x < 0 → f x = 0)
    (hupper : ∀ x : ℝ, (R : ℝ) ≤ x → f x = 0) :
    (∫ x, f x ∂volume) = ∫ x in (0 : ℝ)..(R : ℝ), f x := by
  have hindicator : (Icc (0 : ℝ) (R : ℝ)).indicator f = f := by
    funext x
    by_cases hx : x ∈ Icc (0 : ℝ) (R : ℝ)
    · exact Set.indicator_of_mem hx f
    · rw [Set.indicator_of_not_mem hx]
      have hout : x < 0 ∨ (R : ℝ) < x := by
        simp only [Set.mem_Icc, not_and_or, not_le] at hx
        exact hx
      rcases hout with hxneg | hxupper
      · exact (hneg x hxneg).symm
      · exact (hupper x hxupper.le).symm
  calc
    (∫ x, f x ∂volume) =
        ∫ x, (Icc (0 : ℝ) (R : ℝ)).indicator f x ∂volume := by
          rw [hindicator]
    _ = ∫ x in Icc (0 : ℝ) (R : ℝ), f x ∂volume := by
      rw [integral_indicator measurableSet_Icc]
    _ = ∫ x in Ioc (0 : ℝ) (R : ℝ), f x ∂volume :=
      integral_Icc_eq_integral_Ioc
    _ = ∫ x in (0 : ℝ)..(R : ℝ), f x := by
      rw [intervalIntegral.integral_of_le (Nat.cast_nonneg R)]

/-- A convergent comparison sequence and a vanishing absolute error have the
same limit.  Kept local to this file's Riemann bridge to avoid importing any
profile-specific module. -/
private theorem tendsto_of_abs_sub_le_vanishing
    {a b error : ℕ → ℝ} {c : ℝ}
    (hb : Tendsto b atTop (nhds c))
    (herror : Tendsto error atTop (nhds 0))
    (hclose : ∀ᶠ k : ℕ in atTop, |a k - b k| ≤ error k) :
    Tendsto a atTop (nhds c) := by
  apply hb.congr_dist
  apply squeeze_zero' (Eventually.of_forall fun _ ↦ dist_nonneg) _ herror
  filter_upwards [hclose] with k hk
  simpa only [Real.dist_eq, abs_sub_comm] using hk

/-- The analytic heart of U40.  Local-uniform convergence of the quadratic
coefficient density implies convergence of every compactly supported lattice
test sum.  This theorem does not assume summability, positivity, tightness, or
measure convergence; compact support makes each relevant sum finite. -/
theorem compact_lattice_sums_tendsto_of_locallyUniform
    (rho : ℕ → Seq) (scale : ℕ → ℕ) (u : ℝ → ℝ)
    (hscale : Tendsto scale atTop atTop)
    (hucont : ContinuousOn u (Ici (0 : ℝ)))
    (huneg : ∀ x : ℝ, x < 0 → u x = 0)
    (hlocal : LocallyUniformLatticeDensity rho scale u)
    (g : ℝ →ᵇ ℝ) (hg : HasCompactSupport g) :
    Tendsto
      (fun k : ℕ ↦ ∑' j : ℕ,
        (((scale k : ℕ) : ℝ) * rho k j) *
          g ((j : ℝ) / ((scale k : ℕ) : ℝ)))
      atTop (nhds (∫ x, u x * g x ∂volume)) := by
  obtain ⟨R, hcut⟩ :=
    exists_nat_upper_cutoff_of_hasCompactSupport (g : ℝ → ℝ) hg
  obtain ⟨error, herror, hlocalR⟩ := hlocal R
  let f : ℝ → ℝ := fun x ↦ u x * g x
  have hfcont : ContinuousOn f (Icc (0 : ℝ) (R : ℝ)) := by
    exact (hucont.mono fun _ hx ↦ hx.1).mul g.continuous.continuousOn
  have hriemann : Tendsto
      (fun k : ℕ ↦ latticeLeftRiemannSum f R (scale k))
      atTop (nhds (∫ x in (0 : ℝ)..(R : ℝ), f x)) :=
    (latticeLeftRiemannSum_tendsto_intervalIntegral f R hfcont).comp hscale
  have hintegral :
      (∫ x, u x * g x ∂volume) =
        ∫ x in (0 : ℝ)..(R : ℝ), f x := by
    apply integral_eq_intervalIntegral_of_zero_outside_nat f R
    · intro x hx
      simp only [f, huneg x hx, zero_mul]
    · intro x hx
      simp only [f, hcut x hx, mul_zero]
  rw [hintegral]
  have hscaledError : Tendsto
      (fun k : ℕ ↦ (R : ℝ) * |error k| * ‖g‖)
      atTop (nhds 0) := by
    simpa only [abs_zero, mul_zero, zero_mul] using
      ((tendsto_const_nhds.mul herror.abs).mul tendsto_const_nhds :
        Tendsto (fun k : ℕ ↦ (R : ℝ) * |error k| * ‖g‖)
          atTop (nhds ((R : ℝ) * |(0 : ℝ)| * ‖g‖)))
  apply tendsto_of_abs_sub_le_vanishing hriemann hscaledError
  have hscalePos : ∀ᶠ k : ℕ in atTop, 0 < scale k := by
    have hge : ∀ᶠ k : ℕ in atTop, 1 ≤ scale k :=
      hscale (eventually_ge_atTop (1 : ℕ))
    exact hge.mono fun _ hk ↦ by omega
  filter_upwards [hscalePos] with k hkpos
  let N : ℕ := scale k
  have hNreal : (0 : ℝ) < (N : ℝ) := by
    dsimp only [N]
    exact_mod_cast hkpos
  have hNne : (N : ℝ) ≠ 0 := hNreal.ne'
  have hatom :
      (∑' j : ℕ, ((N : ℝ) * rho k j) *
          g ((j : ℝ) / (N : ℝ))) =
        ∑ j ∈ Finset.range (R * N), ((N : ℝ) * rho k j) *
          g ((j : ℝ) / (N : ℝ)) := by
    apply tsum_eq_sum
    intro j hj
    rw [Finset.mem_range, not_lt] at hj
    have hx : (R : ℝ) ≤ (j : ℝ) / (N : ℝ) := by
      rw [le_div_iff₀ hNreal]
      exact_mod_cast hj
    rw [hcut _ hx, mul_zero]
  rw [show scale k = N from rfl, hatom, latticeLeftRiemannSum,
    ← Finset.sum_sub_distrib]
  calc
    |∑ j ∈ Finset.range (R * N),
        (((N : ℝ) * rho k j) * g ((j : ℝ) / (N : ℝ)) -
          (N : ℝ)⁻¹ * f ((j : ℝ) / (N : ℝ)))| ≤
        ∑ j ∈ Finset.range (R * N),
          |((N : ℝ) * rho k j) * g ((j : ℝ) / (N : ℝ)) -
            (N : ℝ)⁻¹ * f ((j : ℝ) / (N : ℝ))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ Finset.range (R * N),
        (N : ℝ)⁻¹ * |error k| * ‖g‖ := by
      apply Finset.sum_le_sum
      intro j hj
      have hjle : j ≤ R * scale k := by
        exact (Nat.le_of_lt (by simpa only [N] using Finset.mem_range.mp hj))
      have hjerr := hlocalR k hkpos j hjle
      let x : ℝ := (j : ℝ) / (N : ℝ)
      have halgebra :
          ((N : ℝ) * rho k j) * g x - (N : ℝ)⁻¹ * f x =
            (N : ℝ)⁻¹ *
              ((N : ℝ) ^ 2 * rho k j - u x) * g x := by
        dsimp only [f, x]
        field_simp only [hNne]
        ring
      rw [halgebra, abs_mul, abs_mul, abs_of_pos (inv_pos.mpr hNreal)]
      rw [mul_assoc, mul_assoc]
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hNreal.le)
      apply mul_le_mul
      · have hjerr' :
            |(N : ℝ) ^ 2 * rho k j - u x| ≤ error k := by
            simpa only [N, x] using hjerr
        exact hjerr'.trans (le_abs_self (error k))
      · exact g.norm_coe_le_norm x
      · exact abs_nonneg _
      · exact abs_nonneg _
    _ = (R : ℝ) * |error k| * ‖g‖ := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      push_cast
      field_simp only [hNne]
      ring

/-! ## Gluing the exhaustion limits at time one -/

/-- The time-one segment `[0,k+1]` lies in the `k`-th exhaustion rectangle. -/
theorem timeOne_mem_gridExhaustionRectangle
    (k : ℕ) (x : ℝ) (hx₀ : 0 ≤ x) (hxk : x ≤ ((k + 1 : ℕ) : ℝ)) :
    (1, x) ∈ gridExhaustionRectangle k := by
  change ((1 : ℝ) ∈
      Icc (((k + 1 : ℕ) : ℝ))⁻¹ (((k + 1 : ℕ) : ℝ))) ∧
    x ∈ Icc 0 (((k + 1 : ℕ) : ℝ))
  have hdenom : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
  constructor
  · constructor
    · exact (inv_le_one₀ (by positivity)).2 hdenom
    · exact hdenom
  · exact ⟨hx₀, hxk⟩

/-- Glue a compatible family of exhaustion limits into its time-one slice.
The choice of exhaustion index is immaterial by compatibility; negative
arguments are set to zero because the lattice measures live on `ℝ≥0`. -/
def gluedExhaustionTimeOneSlice
    (g : ∀ k, BoundedContinuousFunction (gridExhaustionRectangle k) ℝ)
    (x : ℝ) : ℝ :=
  if hx : 0 ≤ x then
    let hex : ∃ k : ℕ, (1, x) ∈ gridExhaustionRectangle k :=
      exists_mem_gridExhaustionRectangle (by norm_num) hx
    g (Classical.choose hex) ⟨(1, x), Classical.choose_spec hex⟩
  else 0

/-- Compatibility makes the glued value agree with every local exhaustion
representative containing the point. -/
theorem gluedExhaustionTimeOneSlice_eq_local
    (g : ∀ k, BoundedContinuousFunction (gridExhaustionRectangle k) ℝ)
    (hcompat : ∀ {k l : ℕ}, ∀ hkl : k ≤ l,
      ∀ p : gridExhaustionRectangle k,
        g k p = g l ⟨(p : ℝ × ℝ),
          gridExhaustionRectangle_mono hkl p.property⟩)
    (k : ℕ) (x : ℝ) (hx : (1, x) ∈ gridExhaustionRectangle k) :
    gluedExhaustionTimeOneSlice g x = g k ⟨(1, x), hx⟩ := by
  have hx₀ : 0 ≤ x := hx.2.1
  let hex : ∃ l : ℕ, (1, x) ∈ gridExhaustionRectangle l :=
    exists_mem_gridExhaustionRectangle (by norm_num) hx₀
  let l : ℕ := Classical.choose hex
  let p : gridExhaustionRectangle l :=
    ⟨(1, x), Classical.choose_spec hex⟩
  rw [gluedExhaustionTimeOneSlice, dif_pos hx₀]
  change g l p = g k ⟨(1, x), hx⟩
  let q : ℕ := max l k
  calc
    g l p = g q ⟨(p : ℝ × ℝ),
        gridExhaustionRectangle_mono (le_max_left l k) p.property⟩ :=
      hcompat (le_max_left l k) p
    _ = g q ⟨((⟨(1, x), hx⟩ : gridExhaustionRectangle k) : ℝ × ℝ),
        gridExhaustionRectangle_mono (le_max_right l k) hx⟩ := by
      congr 2
    _ = g k ⟨(1, x), hx⟩ :=
      (hcompat (le_max_right l k) ⟨(1, x), hx⟩).symm

/-- On each compact positive interval, the glued slice is represented by one
fixed exhaustion coordinate and is therefore continuous. -/
theorem continuousOn_gluedExhaustionTimeOneSlice_Icc
    (g : ∀ k, BoundedContinuousFunction (gridExhaustionRectangle k) ℝ)
    (hcompat : ∀ {k l : ℕ}, ∀ hkl : k ≤ l,
      ∀ p : gridExhaustionRectangle k,
        g k p = g l ⟨(p : ℝ × ℝ),
          gridExhaustionRectangle_mono hkl p.property⟩)
    (R : ℕ) :
    ContinuousOn (gluedExhaustionTimeOneSlice g)
      (Icc (0 : ℝ) (R : ℝ)) := by
  rw [continuousOn_iff_continuous_restrict]
  let p : Icc (0 : ℝ) (R : ℝ) → gridExhaustionRectangle R :=
    fun x ↦ ⟨(1, (x : ℝ)), timeOne_mem_gridExhaustionRectangle R x
      x.property.1 (x.property.2.trans (by norm_num))⟩
  have hp : Continuous p := by
    have hpbase : Continuous
        (fun x : Icc (0 : ℝ) (R : ℝ) ↦ ((1, (x : ℝ)) : ℝ × ℝ)) := by
      fun_prop
    exact hpbase.subtype_mk _
  have heq :
      (fun x : Icc (0 : ℝ) (R : ℝ) ↦
        gluedExhaustionTimeOneSlice g (x : ℝ)) =
      fun x ↦ g R (p x) := by
    funext x
    exact gluedExhaustionTimeOneSlice_eq_local g hcompat R x
      (timeOne_mem_gridExhaustionRectangle R x x.property.1
        (x.property.2.trans (by norm_num)))
  change Continuous
    (fun x : Icc (0 : ℝ) (R : ℝ) ↦ gluedExhaustionTimeOneSlice g (x : ℝ))
  rw [heq]
  exact (g R).continuous.comp hp

/-- The glued time-one slice is continuous on the entire nonnegative
half-line.  No compatibility beyond the one already forced by common uniform
limits is needed. -/
theorem continuousOn_gluedExhaustionTimeOneSlice_Ici
    (g : ∀ k, BoundedContinuousFunction (gridExhaustionRectangle k) ℝ)
    (hcompat : ∀ {k l : ℕ}, ∀ hkl : k ≤ l,
      ∀ p : gridExhaustionRectangle k,
        g k p = g l ⟨(p : ℝ × ℝ),
          gridExhaustionRectangle_mono hkl p.property⟩) :
    ContinuousOn (gluedExhaustionTimeOneSlice g) (Ici (0 : ℝ)) := by
  intro x hx
  obtain ⟨R, hR⟩ := exists_nat_gt x
  have hxIcc : x ∈ Icc (0 : ℝ) (R : ℝ) := ⟨hx, hR.le⟩
  have hlocal := continuousOn_gluedExhaustionTimeOneSlice_Icc g hcompat R x hxIcc
  apply hlocal.mono_of_mem_nhdsWithin
  apply mem_nhdsWithin_iff_exists_mem_nhds_inter.mpr
  refine ⟨Iio (R : ℝ), Iio_mem_nhds hR, ?_⟩
  rintro y ⟨hyR, hy₀⟩
  exact ⟨hy₀, hyR.le⟩

/-- Uniform convergence of the bilinear interpolants on every exhaustion
rectangle yields the local-uniform lattice-density hypothesis for the actual
terminal grid nodes.  Exact interpolation at mesh nodes is the only bridge;
no floor-readout estimate and no convergence of lattice measures is assumed. -/
theorem locallyUniformLatticeDensity_of_exhaustionLimits
    (rho : ℕ → Seq) (a : ℕ → ℕ → ℕ → ℝ)
    (phi : ℕ → ℕ)
    (g : ∀ k, BoundedContinuousFunction (gridExhaustionRectangle k) ℝ)
    (hterminal : ∀ N j : ℕ,
      a N N j = (N : ℝ) ^ 2 * rho N j)
    (hlim : ∀ k, TendstoUniformly
      (fun n (p : gridExhaustionRectangle k) ↦
        gridBilinearInterp (phi n) (a (phi n))
          (p : ℝ × ℝ).1 (p : ℝ × ℝ).2)
      (fun p ↦ g k p) atTop) :
    LocallyUniformLatticeDensity
      (fun n ↦ rho (phi n)) phi (gluedExhaustionTimeOneSlice g) := by
  let F : ℕ → (ℝ × ℝ) → ℝ := fun N p ↦
    gridBilinearInterp N (a N) p.1 p.2
  have hcompat : ∀ {k l : ℕ}, ∀ hkl : k ≤ l,
      ∀ p : gridExhaustionRectangle k,
        g k p = g l ⟨(p : ℝ × ℝ),
          gridExhaustionRectangle_mono hkl p.property⟩ := by
    intro k l hkl p
    exact exhaustionLimits_compatible F phi g hlim hkl p
  intro R
  let v : ℕ → BoundedContinuousFunction (gridExhaustionRectangle R) ℝ :=
    fun n ↦ compactRestriction (isCompact_gridExhaustionRectangle R)
      (fun p : ℝ × ℝ ↦
        gridBilinearInterp (phi n) (a (phi n)) p.1 p.2)
      (continuous_gridBilinearInterp (phi n) (a (phi n)))
  let error : ℕ → ℝ := fun n ↦ ‖v n - g R‖
  have hv : Tendsto v atTop (nhds (g R)) := by
    apply BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mpr
    simpa only [v, compactRestriction_apply] using hlim R
  have herror : Tendsto error atTop (nhds 0) := by
    have hsub : Tendsto (fun n ↦ v n - g R) atTop (nhds 0) := by
      simpa only [sub_self] using hv.sub
        (tendsto_const_nhds :
          Tendsto (fun _ : ℕ ↦ g R) atTop (nhds (g R)))
    simpa only [error, norm_zero] using hsub.norm
  refine ⟨error, herror, ?_⟩
  intro n hn j hj
  let N : ℕ := phi n
  have hNreal : (0 : ℝ) < (N : ℝ) := by
    dsimp only [N]
    exact_mod_cast hn
  have hNne : (N : ℝ) ≠ 0 := hNreal.ne'
  let x : ℝ := (j : ℝ) / (N : ℝ)
  have hx₀ : 0 ≤ x := div_nonneg (Nat.cast_nonneg j) hNreal.le
  have hxR : x ≤ (R : ℝ) := by
    dsimp only [x]
    rw [div_le_iff₀ hNreal]
    exact_mod_cast hj
  have hxR' : x ≤ ((R + 1 : ℕ) : ℝ) :=
    hxR.trans (by norm_num)
  have hp : (1, x) ∈ gridExhaustionRectangle R :=
    timeOne_mem_gridExhaustionRectangle R x hx₀ hxR'
  let p : gridExhaustionRectangle R := ⟨(1, x), hp⟩
  have hnode :
      gridBilinearInterp N (a N) 1 x = a N N j := by
    have hraw := gridBilinearInterp_at_node N N j (a N) hn
    have htime : (N : ℝ) / (N : ℝ) = 1 := div_self hNne
    simpa only [htime, N, x] using hraw
  have hglue : gluedExhaustionTimeOneSlice g x = g R p := by
    exact gluedExhaustionTimeOneSlice_eq_local g hcompat R x hp
  have hpoint : |v n p - g R p| ≤ error n := by
    simpa only [error, Real.norm_eq_abs] using
      (v n - g R).norm_coe_le_norm p
  have hleft :
      ((phi n : ℕ) : ℝ) ^ 2 * rho (phi n) j = v n p := by
    rw [compactRestriction_apply]
    dsimp only [p]
    change (N : ℝ) ^ 2 * rho N j =
      gridBilinearInterp N (a N) 1 x
    rw [hnode, hterminal]
  calc
    |((phi n : ℕ) : ℝ) ^ 2 * rho (phi n) j -
        gluedExhaustionTimeOneSlice g ((j : ℝ) / ((phi n : ℕ) : ℝ))| =
      |v n p - g R p| := by
        rw [hleft]
        simpa only [N, x] using congrArg (fun z ↦ |v n p - z|) hglue
    _ ≤ error n := hpoint

/-- Source-facing specialization of the preceding exact-node bridge to the
`GridReadout.orbitScaledGrid` array. -/
theorem locallyUniformLatticeDensity_of_orbitScaledGrid_exhaustionLimits
    (m : ℕ) (p₀ : ProbabilityMass) (phi : ℕ → ℕ)
    (g : ∀ k, BoundedContinuousFunction (gridExhaustionRectangle k) ℝ)
    (hlim : ∀ k, TendstoUniformly
      (fun n (p : gridExhaustionRectangle k) ↦
        gridBilinearInterp (phi n) (orbitScaledGrid m p₀ (phi n))
          (p : ℝ × ℝ).1 (p : ℝ × ℝ).2)
      (fun p ↦ g k p) atTop) :
    LocallyUniformLatticeDensity
      (fun n ↦ positiveTiltedDensity m (orbit m p₀ (phi n))) phi
      (gluedExhaustionTimeOneSlice g) := by
  apply locallyUniformLatticeDensity_of_exhaustionLimits
    (fun N ↦ positiveTiltedDensity m (orbit m p₀ N))
    (orbitScaledGrid m p₀) phi g
  · intro N j
    rfl
  · exact hlim

/-- Nonnegative interpolation arrays have a nonnegative glued exhaustion
limit.  This removes another property that otherwise would have to be assumed
separately when constructing the limiting density measure. -/
theorem gluedExhaustionTimeOneSlice_nonneg_of_exhaustionLimits
    (a : ℕ → ℕ → ℕ → ℝ) (phi : ℕ → ℕ)
    (g : ∀ k, BoundedContinuousFunction (gridExhaustionRectangle k) ℝ)
    (ha : ∀ N n j : ℕ, 0 ≤ a N n j)
    (hlim : ∀ k, TendstoUniformly
      (fun n (p : gridExhaustionRectangle k) ↦
        gridBilinearInterp (phi n) (a (phi n))
          (p : ℝ × ℝ).1 (p : ℝ × ℝ).2)
      (fun p ↦ g k p) atTop) :
    ∀ x : ℝ, 0 ≤ gluedExhaustionTimeOneSlice g x := by
  let F : ℕ → (ℝ × ℝ) → ℝ := fun N p ↦
    gridBilinearInterp N (a N) p.1 p.2
  have hcompat : ∀ {k l : ℕ}, ∀ hkl : k ≤ l,
      ∀ p : gridExhaustionRectangle k,
        g k p = g l ⟨(p : ℝ × ℝ),
          gridExhaustionRectangle_mono hkl p.property⟩ := by
    intro k l hkl p
    exact exhaustionLimits_compatible F phi g hlim hkl p
  intro x
  by_cases hx : 0 ≤ x
  · obtain ⟨k, hk⟩ := exists_mem_gridExhaustionRectangle
      (t := (1 : ℝ)) (x := x) (by norm_num) hx
    let p : gridExhaustionRectangle k := ⟨(1, x), hk⟩
    rw [gluedExhaustionTimeOneSlice_eq_local g hcompat k x hk]
    have hpoint := (hlim k).tendsto_at p
    apply isClosed_Ici.mem_of_tendsto hpoint
    exact Eventually.of_forall fun n ↦
      gridBilinearInterp_nonneg (phi n) (a (phi n)) (ha (phi n)) 1 x
  · simp [gluedExhaustionTimeOneSlice, hx]

/-- Full U40 Riemann bridge along an arbitrary cofinal scale.  Local-uniform
grid-density convergence supplies the compact test integrals, while convergence
of the literal total masses supplies tightness at infinity.  The conclusion is
weak convergence of the actual `scaledLatticeMeasuresAlong`, not of a
truncated surrogate. -/
theorem scaledLatticeMeasuresAlong_tendsto_finiteDensityMeasure_of_locallyUniform
    (rho : ℕ → Seq) (scale : ℕ → ℕ) (u : ℝ → ℝ)
    (hrho : ∀ k j, 0 ≤ rho k j)
    (hsum : ∀ k, Summable (rho k))
    (hscale : Tendsto scale atTop atTop)
    (hucont : ContinuousOn u (Ici (0 : ℝ)))
    (hu : ∀ x, 0 ≤ u x)
    (huneg : ∀ x : ℝ, x < 0 → u x = 0)
    (hint : Integrable u volume)
    (hlocal : LocallyUniformLatticeDensity rho scale u)
    (hmass : Tendsto
      (fun k : ℕ ↦ ((scale k : ℕ) : ℝ) * ∑' j : ℕ, rho k j)
      atTop (nhds (∫ x, u x ∂volume))) :
    Tendsto (scaledLatticeMeasuresAlong rho scale hrho hsum)
      atTop (nhds (finiteDensityMeasure u hu hint)) := by
  apply scaledLatticeMeasuresAlong_tendsto_finiteDensityMeasure
    rho scale u hrho hsum hu hint
  · intro g hg
    exact compact_lattice_sums_tendsto_of_locallyUniform
      rho scale u hscale hucont huneg hlocal g hg
  · exact hmass

/-- Grid-compactness form of the full U40 bridge.  A compatible exhaustion
limit is glued automatically, exact terminal-node interpolation gives local
uniform density convergence, and total-mass convergence upgrades the compact
test convergence to weak convergence of the actual atomic measures. -/
theorem scaledLatticeMeasuresAlong_tendsto_of_exhaustionLimits
    (rho : ℕ → Seq) (a : ℕ → ℕ → ℕ → ℝ)
    (phi : ℕ → ℕ)
    (g : ∀ k, BoundedContinuousFunction (gridExhaustionRectangle k) ℝ)
    (hrho : ∀ N j, 0 ≤ rho N j)
    (hsum : ∀ N, Summable (rho N))
    (hphi : Tendsto phi atTop atTop)
    (ha : ∀ N n j : ℕ, 0 ≤ a N n j)
    (hterminal : ∀ N j : ℕ,
      a N N j = (N : ℝ) ^ 2 * rho N j)
    (hlim : ∀ k, TendstoUniformly
      (fun n (p : gridExhaustionRectangle k) ↦
        gridBilinearInterp (phi n) (a (phi n))
          (p : ℝ × ℝ).1 (p : ℝ × ℝ).2)
      (fun p ↦ g k p) atTop)
    (hint : Integrable (gluedExhaustionTimeOneSlice g) volume)
    (hmass : Tendsto
      (fun n : ℕ ↦ ((phi n : ℕ) : ℝ) * ∑' j : ℕ, rho (phi n) j)
      atTop (nhds (∫ x, gluedExhaustionTimeOneSlice g x ∂volume))) :
    Tendsto
      (scaledLatticeMeasuresAlong (fun n ↦ rho (phi n)) phi
        (fun n j ↦ hrho (phi n) j) (fun n ↦ hsum (phi n)))
      atTop
      (nhds (finiteDensityMeasure (gluedExhaustionTimeOneSlice g)
        (gluedExhaustionTimeOneSlice_nonneg_of_exhaustionLimits
          a phi g ha hlim) hint)) := by
  let F : ℕ → (ℝ × ℝ) → ℝ := fun N p ↦
    gridBilinearInterp N (a N) p.1 p.2
  have hcompat : ∀ {k l : ℕ}, ∀ hkl : k ≤ l,
      ∀ p : gridExhaustionRectangle k,
        g k p = g l ⟨(p : ℝ × ℝ),
          gridExhaustionRectangle_mono hkl p.property⟩ := by
    intro k l hkl p
    exact exhaustionLimits_compatible F phi g hlim hkl p
  apply scaledLatticeMeasuresAlong_tendsto_finiteDensityMeasure_of_locallyUniform
    (fun n ↦ rho (phi n)) phi (gluedExhaustionTimeOneSlice g)
    (fun n j ↦ hrho (phi n) j) (fun n ↦ hsum (phi n)) hphi
    (continuousOn_gluedExhaustionTimeOneSlice_Ici g hcompat)
    (gluedExhaustionTimeOneSlice_nonneg_of_exhaustionLimits a phi g ha hlim)
    (fun x hx ↦ by simp [gluedExhaustionTimeOneSlice, not_le.mpr hx])
    hint
    (locallyUniformLatticeDensity_of_exhaustionLimits
      rho a phi g hterminal hlim)
    hmass

end

end DerridaRetaux
