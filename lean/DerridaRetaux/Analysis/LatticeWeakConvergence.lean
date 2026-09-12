import DerridaRetaux.Analysis.LatticeMeasure
import Mathlib.Topology.ContinuousMap.BoundedCompactlySupported
import Mathlib.Tactic

set_option autoImplicit false

open Filter Topology MeasureTheory Set
open scoped BoundedContinuousFunction ENNReal

namespace DerridaRetaux

noncomputable section

/-!
# Weak convergence of the scaled lattice measures

This file isolates the passage from compactly supported test functions to the
weak topology on finite measures.  The bridge uses convergence of total mass;
equivalently, that hypothesis supplies the missing tightness at infinity.
-/

/-- A continuous cutoff equal to one on `[-R,R]` and zero outside
`[-(R+1),R+1]`. -/
def compactMassCutoff (R : ℕ) (x : ℝ) : ℝ :=
  max 0 (min 1 ((R : ℝ) + 1 - |x|))

theorem continuous_compactMassCutoff (R : ℕ) :
    Continuous (compactMassCutoff R) := by
  unfold compactMassCutoff
  fun_prop

theorem compactMassCutoff_nonneg (R : ℕ) (x : ℝ) :
    0 ≤ compactMassCutoff R x := by
  exact le_max_left _ _

theorem compactMassCutoff_le_one (R : ℕ) (x : ℝ) :
    compactMassCutoff R x ≤ 1 := by
  unfold compactMassCutoff
  exact max_le zero_le_one (min_le_left _ _)

theorem compactMassCutoff_eq_one_of_abs_le
    (R : ℕ) (x : ℝ) (hx : |x| ≤ (R : ℝ)) :
    compactMassCutoff R x = 1 := by
  unfold compactMassCutoff
  rw [min_eq_left, max_eq_right]
  · exact zero_le_one
  · linarith

theorem compactMassCutoff_eq_zero_of_radius_le_abs
    (R : ℕ) (x : ℝ) (hx : (R : ℝ) + 1 ≤ |x|) :
    compactMassCutoff R x = 0 := by
  unfold compactMassCutoff
  rw [min_eq_right, max_eq_left]
  · linarith
  · linarith

theorem compactMassCutoff_hasCompactSupport (R : ℕ) :
    HasCompactSupport (compactMassCutoff R) := by
  apply HasCompactSupport.intro (isCompact_Icc : IsCompact
    (Icc (-((R : ℝ) + 1)) ((R : ℝ) + 1)))
  intro x hx
  have hout : x < -((R : ℝ) + 1) ∨ (R : ℝ) + 1 < x := by
    simpa only [mem_Icc, not_and_or, not_le] using hx
  apply compactMassCutoff_eq_zero_of_radius_le_abs
  rcases hout with hxleft | hxright
  · exact le_trans (le_of_lt (by linarith : (R : ℝ) + 1 < -x)) (neg_le_abs x)
  · exact le_trans (le_of_lt hxright) (le_abs_self x)

/-- The cutoff as a bounded continuous function. -/
def compactMassCutoffBCF (R : ℕ) : ℝ →ᵇ ℝ :=
  ofCompactSupport (compactMassCutoff R) (continuous_compactMassCutoff R)
    (compactMassCutoff_hasCompactSupport R)

@[simp]
theorem compactMassCutoffBCF_apply (R : ℕ) (x : ℝ) :
    compactMassCutoffBCF R x = compactMassCutoff R x := rfl

theorem compactMassCutoff_tendsto_one (x : ℝ) :
    Tendsto (fun R : ℕ ↦ compactMassCutoff R x) atTop (nhds 1) := by
  obtain ⟨N, hN⟩ := exists_nat_gt |x|
  apply tendsto_atTop_of_eventually_const (i₀ := N)
  intro R hR
  apply compactMassCutoff_eq_one_of_abs_le
  exact le_trans (le_of_lt hN) (by exact_mod_cast hR)

/-- For a finite measure, the mass left outside the compact cutoff vanishes. -/
theorem integral_one_sub_compactMassCutoff_tendsto_zero
    (mu : FiniteMeasure ℝ) :
    Tendsto
      (fun R : ℕ ↦ ∫ x, 1 - compactMassCutoff R x ∂(mu : Measure ℝ))
      atTop (nhds 0) := by
  simpa only [integral_zero] using
    (tendsto_integral_of_dominated_convergence
      (F := fun R : ℕ ↦ fun x : ℝ ↦ 1 - compactMassCutoff R x)
      (f := fun _ : ℝ ↦ 0) (μ := (mu : Measure ℝ)) (fun _ : ℝ ↦ 1)
      (fun R ↦
        (continuous_const.sub (continuous_compactMassCutoff R)).aestronglyMeasurable)
      (integrable_const 1)
      (fun R ↦ Eventually.of_forall fun x ↦ by
        rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr
          (compactMassCutoff_le_one R x))]
        exact sub_le_self 1 (compactMassCutoff_nonneg R x))
      (Eventually.of_forall fun x ↦ by
        simpa only [sub_self] using
          ((tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (nhds 1)).sub
            (compactMassCutoff_tendsto_one x))))

theorem integral_one_sub_compactMassCutoff_nonneg
    (mu : FiniteMeasure ℝ) (R : ℕ) :
    0 ≤ ∫ x, 1 - compactMassCutoff R x ∂(mu : Measure ℝ) := by
  apply integral_nonneg
  intro x
  exact sub_nonneg.mpr (compactMassCutoff_le_one R x)

theorem integral_one_sub_compactMassCutoff_eq
    (mu : FiniteMeasure ℝ) (R : ℕ) :
    (∫ x, 1 - compactMassCutoff R x ∂(mu : Measure ℝ)) =
      (mu : Measure ℝ).real Set.univ -
        ∫ x, compactMassCutoff R x ∂(mu : Measure ℝ) := by
  have hcutoffIntegrable : Integrable (compactMassCutoff R) (mu : Measure ℝ) := by
    simpa only [compactMassCutoffBCF_apply] using
      ((compactMassCutoffBCF R).integrable (mu : Measure ℝ))
  rw [integral_sub (integrable_const 1) hcutoffIntegrable]
  simp only [integral_const, smul_eq_mul, mul_one]

/-- The error made by multiplying a bounded continuous test by the compact
cutoff is bounded by its norm times the discarded mass. -/
theorem abs_integral_sub_cutoff_le
    (mu : FiniteMeasure ℝ) (f : ℝ →ᵇ ℝ) (R : ℕ) :
    |(∫ x, f x ∂(mu : Measure ℝ)) -
        ∫ x, f x * compactMassCutoff R x ∂(mu : Measure ℝ)| ≤
      ‖f‖ * ∫ x, 1 - compactMassCutoff R x ∂(mu : Measure ℝ) := by
  let c : ℝ →ᵇ ℝ := compactMassCutoffBCF R
  have hf : Integrable f (mu : Measure ℝ) := f.integrable _
  have hfc : Integrable (f * c) (mu : Measure ℝ) := (f * c).integrable _
  change |(∫ x, f x ∂(mu : Measure ℝ)) -
      ∫ x, (f * c) x ∂(mu : Measure ℝ)| ≤ _
  rw [← integral_sub hf hfc]
  have hdom : Integrable
      (fun x : ℝ ↦ ‖f‖ * (1 - compactMassCutoff R x))
      (mu : Measure ℝ) := by
    apply Integrable.const_mul
    exact ((1 : ℝ →ᵇ ℝ) - c).integrable _
  have hbound :=
    norm_integral_le_of_norm_le hdom (Eventually.of_forall fun x ↦ by
      have hcut : 0 ≤ 1 - compactMassCutoff R x :=
        sub_nonneg.mpr (compactMassCutoff_le_one R x)
      calc
        ‖f x - f x * compactMassCutoff R x‖ =
            ‖f x‖ * |1 - compactMassCutoff R x| := by
              rw [show f x - f x * compactMassCutoff R x =
                f x * (1 - compactMassCutoff R x) by ring,
                norm_mul]
              simp only [Real.norm_eq_abs]
        _ = ‖f x‖ * (1 - compactMassCutoff R x) := by
              rw [abs_of_nonneg hcut]
        _ ≤ ‖f‖ * (1 - compactMassCutoff R x) :=
          mul_le_mul_of_nonneg_right (f.norm_coe_le_norm x) hcut)
  rw [integral_const_mul] at hbound
  simpa only [Real.norm_eq_abs, Pi.sub_apply, Pi.mul_apply, c,
    compactMassCutoffBCF_apply] using hbound

/-- Vague convergence plus convergence of total masses implies weak
convergence for finite measures on the real line. -/
theorem finiteMeasure_tendsto_of_compact_integrals_and_mass
    (mus : ℕ → FiniteMeasure ℝ) (mu : FiniteMeasure ℝ)
    (hcompact : ∀ g : ℝ →ᵇ ℝ, HasCompactSupport g →
      Tendsto (fun n : ℕ ↦ ∫ x, g x ∂(mus n : Measure ℝ)) atTop
        (nhds (∫ x, g x ∂(mu : Measure ℝ))))
    (hmass : Tendsto (fun n : ℕ ↦ (mus n : Measure ℝ).real Set.univ)
      atTop (nhds ((mu : Measure ℝ).real Set.univ))) :
    Tendsto mus atTop (nhds mu) := by
  apply FiniteMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro f
  apply Metric.tendsto_atTop.mpr
  intro eps heps
  let K : ℝ := ‖f‖ + 1
  have hK : 0 < K := by dsimp only [K]; positivity
  let delta : ℝ := eps / (4 * K)
  have hdelta : 0 < delta := by dsimp only [delta]; positivity
  obtain ⟨R, hR⟩ := Metric.tendsto_atTop.mp
    (integral_one_sub_compactMassCutoff_tendsto_zero mu) delta hdelta
  have htargetNear := hR R le_rfl
  have htargetNonneg := integral_one_sub_compactMassCutoff_nonneg mu R
  have htargetSmall :
      (∫ x, 1 - compactMassCutoff R x ∂(mu : Measure ℝ)) < delta := by
    simpa only [Real.dist_eq, sub_zero, abs_of_nonneg htargetNonneg] using htargetNear
  let c : ℝ →ᵇ ℝ := compactMassCutoffBCF R
  let g : ℝ →ᵇ ℝ := f * c
  have hgcompact : HasCompactSupport g := by
    exact (compactMassCutoff_hasCompactSupport R).mul_left
  have hlocal := hcompact g hgcompact
  have hcutoff := hcompact c (compactMassCutoff_hasCompactSupport R)
  have hresidual : Tendsto
      (fun n : ℕ ↦ ∫ x, 1 - compactMassCutoff R x ∂(mus n : Measure ℝ))
      atTop
      (nhds (∫ x, 1 - compactMassCutoff R x ∂(mu : Measure ℝ))) := by
    rw [integral_one_sub_compactMassCutoff_eq mu R]
    have hsub := hmass.sub hcutoff
    simpa only [integral_one_sub_compactMassCutoff_eq, c,
      compactMassCutoffBCF_apply] using hsub
  obtain ⟨Nres, hNres⟩ := Metric.tendsto_atTop.mp hresidual delta hdelta
  obtain ⟨Nlocal, hNlocal⟩ := Metric.tendsto_atTop.mp hlocal (eps / 4) (by positivity)
  refine ⟨max Nres Nlocal, ?_⟩
  intro n hn
  have hnres : Nres ≤ n := le_trans (le_max_left _ _) hn
  have hnlocal : Nlocal ≤ n := le_trans (le_max_right _ _) hn
  have hresNear := hNres n hnres
  have hlocalNear := hNlocal n hnlocal
  have hresNonneg := integral_one_sub_compactMassCutoff_nonneg (mus n) R
  have hresSmall :
      (∫ x, 1 - compactMassCutoff R x ∂(mus n : Measure ℝ)) < 2 * delta := by
    rw [Real.dist_eq] at hresNear
    have := (abs_lt.mp hresNear).2
    linarith
  rw [Real.dist_eq] at hlocalNear ⊢
  have hsourceError := abs_integral_sub_cutoff_le (mus n) f R
  have htargetError := abs_integral_sub_cutoff_le mu f R
  change |(∫ x, f x ∂(mus n : Measure ℝ)) -
      ∫ x, g x ∂(mus n : Measure ℝ)| ≤ _ at hsourceError
  change |(∫ x, f x ∂(mu : Measure ℝ)) -
      ∫ x, g x ∂(mu : Measure ℝ)| ≤ _ at htargetError
  calc
    |(∫ x, f x ∂(mus n : Measure ℝ)) - ∫ x, f x ∂(mu : Measure ℝ)| =
        |((∫ x, f x ∂(mus n : Measure ℝ)) -
            ∫ x, g x ∂(mus n : Measure ℝ)) +
          ((∫ x, g x ∂(mus n : Measure ℝ)) -
            ∫ x, g x ∂(mu : Measure ℝ)) +
          ((∫ x, g x ∂(mu : Measure ℝ)) -
            ∫ x, f x ∂(mu : Measure ℝ))| := by
              congr 1
              ring
    _ ≤ |(∫ x, f x ∂(mus n : Measure ℝ)) -
            ∫ x, g x ∂(mus n : Measure ℝ)| +
          |(∫ x, g x ∂(mus n : Measure ℝ)) -
            ∫ x, g x ∂(mu : Measure ℝ)| +
          |(∫ x, g x ∂(mu : Measure ℝ)) -
            ∫ x, f x ∂(mu : Measure ℝ)| := by
              exact (abs_add_three _ _ _)
    _ ≤ ‖f‖ * (∫ x, 1 - compactMassCutoff R x ∂(mus n : Measure ℝ)) +
          |(∫ x, g x ∂(mus n : Measure ℝ)) -
            ∫ x, g x ∂(mu : Measure ℝ)| +
          ‖f‖ * (∫ x, 1 - compactMassCutoff R x ∂(mu : Measure ℝ)) := by
      gcongr
      simpa only [abs_sub_comm] using htargetError
    _ < eps := by
      have hfK : ‖f‖ < K := by dsimp only [K]; linarith
      have hlocalSmall :
          |(∫ x, g x ∂(mus n : Measure ℝ)) -
            ∫ x, g x ∂(mu : Measure ℝ)| < eps / 4 := by
        simpa only [Real.dist_eq] using hlocalNear
      have hsourceProduct :
          ‖f‖ * (∫ x, 1 - compactMassCutoff R x ∂(mus n : Measure ℝ)) <
            K * (2 * delta) := by
        calc
          ‖f‖ * (∫ x, 1 - compactMassCutoff R x ∂(mus n : Measure ℝ)) ≤
              ‖f‖ * (2 * delta) :=
            mul_le_mul_of_nonneg_left hresSmall.le (norm_nonneg f)
          _ < K * (2 * delta) :=
            mul_lt_mul_of_pos_right hfK (by positivity)
      have htargetProduct :
          ‖f‖ * (∫ x, 1 - compactMassCutoff R x ∂(mu : Measure ℝ)) <
            K * delta := by
        calc
          ‖f‖ * (∫ x, 1 - compactMassCutoff R x ∂(mu : Measure ℝ)) ≤
              ‖f‖ * delta :=
            mul_le_mul_of_nonneg_left htargetSmall.le (norm_nonneg f)
          _ < K * delta := mul_lt_mul_of_pos_right hfK hdelta
      have hKne : K ≠ 0 := ne_of_gt hK
      have hsourceCap : K * (2 * delta) = eps / 2 := by
        dsimp only [delta]
        field_simp [hKne]
        ring
      have htargetCap : K * delta = eps / 4 := by
        dsimp only [delta]
        field_simp [hKne]
        ring
      rw [hsourceCap] at hsourceProduct
      rw [htargetCap] at htargetProduct
      linarith

/-- Every bounded continuous test integrates against a scaled lattice measure
as the literal weighted atom sum. -/
theorem integral_scaledLatticeMeasure_eq_tsum_bcf
    (rho : Seq) (N : ℕ) (hrho : ∀ j, 0 ≤ rho j) (hsum : Summable rho)
    (f : ℝ →ᵇ ℝ) :
    (∫ x, f x ∂(scaledLatticeMeasure rho N hrho hsum : Measure ℝ)) =
      ∑' j : ℕ, ((N : ℝ) * rho j) * f ((j : ℝ) / (N : ℝ)) := by
  have hf : Integrable f (scaledLatticeMeasureRaw rho N) := by
    change Integrable f (scaledLatticeMeasure rho N hrho hsum : Measure ℝ)
    exact f.integrable _
  change (∫ x, f x ∂scaledLatticeMeasureRaw rho N) = _
  rw [scaledLatticeMeasureRaw, integral_sum_measure hf]
  simp only [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal,
    Nat.cast_nonneg, mul_nonneg, hrho, smul_eq_mul]

/-- The real total mass of the lattice measure is the scaled coefficient
sum. -/
theorem scaledLatticeMeasure_real_univ
    (rho : Seq) (N : ℕ) (hrho : ∀ j, 0 ≤ rho j) (hsum : Summable rho) :
    (scaledLatticeMeasure rho N hrho hsum : Measure ℝ).real Set.univ =
      (N : ℝ) * ∑' j : ℕ, rho j := by
  rw [measureReal_def]
  change (scaledLatticeMeasureRaw rho N Set.univ).toReal = _
  rw [scaledLatticeMeasureRaw_univ rho N hrho hsum]
  rw [ENNReal.toReal_ofReal]
  exact mul_nonneg (Nat.cast_nonneg N) (tsum_nonneg fun j ↦ hrho j)

/-- Coefficient-level U40 bridge.  Compactly supported Riemann sums and the
literal scaled total mass determine the weak limit of the actual lattice
measures. -/
theorem scaledLatticeMeasures_tendsto_of_compact_sums_and_mass
    (rho : ℕ → Seq) (mu : FiniteMeasure ℝ)
    (hrho : ∀ N j, 0 ≤ rho N j)
    (hsum : ∀ N, Summable (rho N))
    (hcompact : ∀ g : ℝ →ᵇ ℝ, HasCompactSupport g →
      Tendsto
        (fun N : ℕ ↦ ∑' j : ℕ,
          (((N + 1 : ℕ) : ℝ) * rho (N + 1) j) *
            g ((j : ℝ) / ((N + 1 : ℕ) : ℝ)))
        atTop (nhds (∫ x, g x ∂(mu : Measure ℝ))))
    (hmass : Tendsto
      (fun N : ℕ ↦ ((N + 1 : ℕ) : ℝ) * ∑' j : ℕ, rho (N + 1) j)
      atTop (nhds ((mu : Measure ℝ).real Set.univ))) :
    Tendsto (scaledLatticeMeasures rho hrho hsum) atTop (nhds mu) := by
  apply finiteMeasure_tendsto_of_compact_integrals_and_mass
  · intro g hg
    simpa only [scaledLatticeMeasures,
      integral_scaledLatticeMeasure_eq_tsum_bcf] using hcompact g hg
  · simpa only [scaledLatticeMeasures, scaledLatticeMeasure_real_univ] using hmass

/-- Cofinal-scale version of the coefficient-level U40 bridge.  The theorem
index, the coefficient-generation index, and the lattice scale are kept
separate; no particular choice such as `N + 1` is built into this statement. -/
theorem scaledLatticeMeasuresAlong_tendsto_of_compact_sums_and_mass
    (rho : ℕ → Seq) (scale : ℕ → ℕ) (mu : FiniteMeasure ℝ)
    (hrho : ∀ k j, 0 ≤ rho k j)
    (hsum : ∀ k, Summable (rho k))
    (hcompact : ∀ g : ℝ →ᵇ ℝ, HasCompactSupport g →
      Tendsto
        (fun k : ℕ ↦ ∑' j : ℕ,
          (((scale k : ℕ) : ℝ) * rho k j) *
            g ((j : ℝ) / ((scale k : ℕ) : ℝ)))
        atTop (nhds (∫ x, g x ∂(mu : Measure ℝ))))
    (hmass : Tendsto
      (fun k : ℕ ↦ ((scale k : ℕ) : ℝ) * ∑' j : ℕ, rho k j)
      atTop (nhds ((mu : Measure ℝ).real Set.univ))) :
    Tendsto (scaledLatticeMeasuresAlong rho scale hrho hsum)
      atTop (nhds mu) := by
  apply finiteMeasure_tendsto_of_compact_integrals_and_mass
  · intro g hg
    simpa only [scaledLatticeMeasuresAlong,
      integral_scaledLatticeMeasure_eq_tsum_bcf] using hcompact g hg
  · simpa only [scaledLatticeMeasuresAlong,
      scaledLatticeMeasure_real_univ] using hmass

/-- The finite measure whose Lebesgue density is a nonnegative integrable
function. -/
def finiteDensityMeasure
    (u : ℝ → ℝ) (hu : ∀ x, 0 ≤ u x) (hint : Integrable u volume) :
    FiniteMeasure ℝ :=
  ⟨volume.withDensity (fun x ↦ ENNReal.ofReal (u x)),
    isFiniteMeasure_withDensity
      ((hasFiniteIntegral_iff_ofReal (Eventually.of_forall hu)).1 hint.2).ne⟩

theorem integral_finiteDensityMeasure_eq
    (u : ℝ → ℝ) (hu : ∀ x, 0 ≤ u x) (hint : Integrable u volume)
    (g : ℝ →ᵇ ℝ) :
    (∫ x, g x ∂(finiteDensityMeasure u hu hint : Measure ℝ)) =
      ∫ x, u x * g x ∂volume := by
  change (∫ x, g x ∂volume.withDensity (fun x ↦ ENNReal.ofReal (u x))) = _
  rw [integral_withDensity_eq_integral_toReal_smul₀
    hint.1.aemeasurable.ennreal_ofReal
    (Eventually.of_forall fun x ↦ ENNReal.ofReal_lt_top) g]
  apply integral_congr_ae
  exact Eventually.of_forall fun x ↦ by
    change (ENNReal.ofReal (u x)).toReal * g x = u x * g x
    rw [ENNReal.toReal_ofReal (hu x)]

theorem finiteDensityMeasure_real_univ
    (u : ℝ → ℝ) (hu : ∀ x, 0 ≤ u x) (hint : Integrable u volume) :
    (finiteDensityMeasure u hu hint : Measure ℝ).real Set.univ = ∫ x, u x ∂volume := by
  have h := integral_finiteDensityMeasure_eq u hu hint (1 : ℝ →ᵇ ℝ)
  simpa [integral_const, smul_eq_mul] using h

/-- Density-valued version of U40: literal compact lattice Riemann sums and
the scaled zeroth moment imply weak convergence to `u(x) dx`. -/
theorem scaledLatticeMeasures_tendsto_finiteDensityMeasure
    (rho : ℕ → Seq) (u : ℝ → ℝ)
    (hrho : ∀ N j, 0 ≤ rho N j)
    (hsum : ∀ N, Summable (rho N))
    (hu : ∀ x, 0 ≤ u x) (hint : Integrable u volume)
    (hcompact : ∀ g : ℝ →ᵇ ℝ, HasCompactSupport g →
      Tendsto
        (fun N : ℕ ↦ ∑' j : ℕ,
          (((N + 1 : ℕ) : ℝ) * rho (N + 1) j) *
            g ((j : ℝ) / ((N + 1 : ℕ) : ℝ)))
        atTop (nhds (∫ x, u x * g x ∂volume)))
    (hmass : Tendsto
      (fun N : ℕ ↦ ((N + 1 : ℕ) : ℝ) * ∑' j : ℕ, rho (N + 1) j)
      atTop (nhds (∫ x, u x ∂volume))) :
    Tendsto (scaledLatticeMeasures rho hrho hsum) atTop
      (nhds (finiteDensityMeasure u hu hint)) := by
  apply scaledLatticeMeasures_tendsto_of_compact_sums_and_mass
  · intro g hg
    rw [integral_finiteDensityMeasure_eq]
    exact hcompact g hg
  · rw [finiteDensityMeasure_real_univ]
    exact hmass

/-- Density-valued U40 bridge along an arbitrary selected lattice scale. -/
theorem scaledLatticeMeasuresAlong_tendsto_finiteDensityMeasure
    (rho : ℕ → Seq) (scale : ℕ → ℕ) (u : ℝ → ℝ)
    (hrho : ∀ k j, 0 ≤ rho k j)
    (hsum : ∀ k, Summable (rho k))
    (hu : ∀ x, 0 ≤ u x) (hint : Integrable u volume)
    (hcompact : ∀ g : ℝ →ᵇ ℝ, HasCompactSupport g →
      Tendsto
        (fun k : ℕ ↦ ∑' j : ℕ,
          (((scale k : ℕ) : ℝ) * rho k j) *
            g ((j : ℝ) / ((scale k : ℕ) : ℝ)))
        atTop (nhds (∫ x, u x * g x ∂volume)))
    (hmass : Tendsto
      (fun k : ℕ ↦ ((scale k : ℕ) : ℝ) * ∑' j : ℕ, rho k j)
      atTop (nhds (∫ x, u x ∂volume))) :
    Tendsto (scaledLatticeMeasuresAlong rho scale hrho hsum) atTop
      (nhds (finiteDensityMeasure u hu hint)) := by
  apply scaledLatticeMeasuresAlong_tendsto_of_compact_sums_and_mass
  · intro g hg
    rw [integral_finiteDensityMeasure_eq]
    exact hcompact g hg
  · rw [finiteDensityMeasure_real_univ]
    exact hmass

end

end DerridaRetaux
