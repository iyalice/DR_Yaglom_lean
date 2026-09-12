import DerridaRetaux.Analysis.LimitTail
import Mathlib.Tactic

set_option autoImplicit false

open Filter Topology MeasureTheory Set
open scoped BigOperators ENNReal

namespace DerridaRetaux

noncomputable section

/-!
# The source lattice profile as a finite measure

This file packages the scaled atoms `N * rho(j)` at `j / N` into the concrete
finite measure used in the weak-limit and Portmanteau steps.  The hypotheses are
kept at coefficient level, so no extra probability-law abstraction is hidden.
-/

/-- The raw scaled lattice measure with mass `N * rho(j)` at `j / N`. -/
def scaledLatticeMeasureRaw (rho : Seq) (N : ℕ) : Measure ℝ :=
  Measure.sum fun j : ℕ ↦
    ENNReal.ofReal ((N : ℝ) * rho j) • Measure.dirac ((j : ℝ) / (N : ℝ))

theorem scaledLatticeMeasureRaw_univ
    (rho : Seq) (N : ℕ) (hrho : ∀ j, 0 ≤ rho j) (hsum : Summable rho) :
    scaledLatticeMeasureRaw rho N Set.univ =
      ENNReal.ofReal ((N : ℝ) * ∑' j : ℕ, rho j) := by
  rw [scaledLatticeMeasureRaw, Measure.sum_apply _ MeasurableSet.univ]
  simp only [Measure.smul_apply, Measure.dirac_apply_of_mem, Set.mem_univ,
    smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_tsum_of_nonneg
    (fun j ↦ mul_nonneg (Nat.cast_nonneg N) (hrho j))
    (hsum.mul_left (N : ℝ))]
  congr 1
  exact hsum.tsum_mul_left (N : ℝ)

/-- The concrete finite measure associated with a nonnegative summable profile. -/
def scaledLatticeMeasure
    (rho : Seq) (N : ℕ) (hrho : ∀ j, 0 ≤ rho j) (hsum : Summable rho) :
    FiniteMeasure ℝ :=
  ⟨scaledLatticeMeasureRaw rho N, ⟨by
    rw [scaledLatticeMeasureRaw_univ rho N hrho hsum]
    exact ENNReal.ofReal_lt_top⟩⟩

theorem integrable_scaledLatticeMeasureRaw_of_summable
    (rho : Seq) (N : ℕ) (f : ℝ → ℝ)
    (hrho : ∀ j, 0 ≤ rho j)
    (hf : ∀ x, 0 ≤ f x) (hfmeas : StronglyMeasurable f)
    (hsum : Summable fun j : ℕ ↦
      ((N : ℝ) * rho j) * f ((j : ℝ) / (N : ℝ))) :
    Integrable f (scaledLatticeMeasureRaw rho N) := by
  refine ⟨hfmeas.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall hf)]
  rw [scaledLatticeMeasureRaw, lintegral_sum_measure]
  simp only [lintegral_smul_measure, lintegral_dirac, smul_eq_mul]
  simp_rw [← ENNReal.ofReal_mul (mul_nonneg (Nat.cast_nonneg N) (hrho _))]
  rw [← ENNReal.ofReal_tsum_of_nonneg
    (fun j ↦ mul_nonneg (mul_nonneg (Nat.cast_nonneg N) (hrho j)) (hf _)) hsum]
  exact ENNReal.ofReal_lt_top

theorem integral_scaledLatticeMeasureRaw_eq_tsum
    (rho : Seq) (N : ℕ) (f : ℝ → ℝ)
    (hrho : ∀ j, 0 ≤ rho j)
    (hf : ∀ x, 0 ≤ f x) (hfmeas : StronglyMeasurable f)
    (hsum : Summable fun j : ℕ ↦
      ((N : ℝ) * rho j) * f ((j : ℝ) / (N : ℝ))) :
    ∫ x, f x ∂(scaledLatticeMeasureRaw rho N) =
      ∑' j : ℕ, ((N : ℝ) * rho j) * f ((j : ℝ) / (N : ℝ)) := by
  rw [scaledLatticeMeasureRaw, integral_sum_measure
    (integrable_scaledLatticeMeasureRaw_of_summable rho N f hrho hf hfmeas hsum)]
  simp only [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal,
    Nat.cast_nonneg, mul_nonneg, hrho, smul_eq_mul]

theorem scaledLattice_cubicTail_term_eq
    (rho : Seq) (N j : ℕ) (delta : ℝ) (hN : 1 ≤ N) :
    ((N : ℝ) * rho j) *
        cubicTailIntegrand delta ((j : ℝ) / (N : ℝ)) =
      ((N : ℝ) / (N : ℝ) ^ 3) *
        ((j : ℝ) ^ 3 * rho j *
          strictTailIndicator (delta * (N : ℝ)) (j : ℝ)) := by
  have hNR : 0 < (N : ℝ) := by exact_mod_cast hN
  have hj0 : 0 ≤ (j : ℝ) / (N : ℝ) := div_nonneg (Nat.cast_nonneg j) hNR.le
  by_cases hj : delta * (N : ℝ) < (j : ℝ)
  · have hjdiv : delta < (j : ℝ) / (N : ℝ) := (lt_div_iff₀ hNR).2 hj
    rw [cubicTailIntegrand, if_pos hjdiv, max_eq_left hj0,
      strictTailIndicator, if_pos hj]
    field_simp
    ring
  · have hjdiv : ¬ delta < (j : ℝ) / (N : ℝ) := by
      intro h
      exact hj ((lt_div_iff₀ hNR).1 h)
    rw [cubicTailIntegrand, if_neg hjdiv, strictTailIndicator, if_neg hj]
    ring

theorem scaledLattice_cubicTail_term_eq_all
    (rho : Seq) (N j : ℕ) (delta : ℝ) :
    ((N : ℝ) * rho j) *
        cubicTailIntegrand delta ((j : ℝ) / (N : ℝ)) =
      ((N : ℝ) / (N : ℝ) ^ 3) *
        ((j : ℝ) ^ 3 * rho j *
          strictTailIndicator (delta * (N : ℝ)) (j : ℝ)) := by
  by_cases hN : N = 0
  · subst N
    norm_num
  · exact scaledLattice_cubicTail_term_eq rho N j delta
      (Nat.one_le_iff_ne_zero.mpr hN)

theorem summable_scaledLattice_cubicTail
    (rho : Seq) (N : ℕ) (delta : ℝ) (hN : 1 ≤ N)
    (hrho : ∀ j, 0 ≤ rho j)
    (hthird : Summable fun j : ℕ ↦ (j : ℝ) ^ 3 * rho j) :
    Summable fun j : ℕ ↦
      ((N : ℝ) * rho j) * cubicTailIntegrand delta ((j : ℝ) / (N : ℝ)) := by
  have htail := momentTail_summable_of_moment rho 3 (delta * (N : ℝ)) hrho hthird
  have hscaled := htail.mul_left ((N : ℝ) / (N : ℝ) ^ 3)
  refine hscaled.congr fun j ↦ ?_
  exact (scaledLattice_cubicTail_term_eq rho N j delta hN).symm

theorem summable_scaledLattice_cubicTail_all
    (rho : Seq) (N : ℕ) (delta : ℝ)
    (hrho : ∀ j, 0 ≤ rho j)
    (hthird : Summable fun j : ℕ ↦ (j : ℝ) ^ 3 * rho j) :
    Summable fun j : ℕ ↦
      ((N : ℝ) * rho j) * cubicTailIntegrand delta ((j : ℝ) / (N : ℝ)) := by
  by_cases hN : N = 0
  · subst N
    simpa only [Nat.cast_zero, zero_mul] using
      (summable_zero : Summable (fun _ : ℕ ↦ (0 : ℝ)))
  · exact summable_scaledLattice_cubicTail rho N delta
      (Nat.one_le_iff_ne_zero.mpr hN) hrho hthird

theorem integrable_cubicTail_scaledLatticeMeasure
    (rho : Seq) (N : ℕ) (delta : ℝ) (hN : 1 ≤ N)
    (hrho : ∀ j, 0 ≤ rho j) (hzero : Summable rho)
    (hthird : Summable fun j : ℕ ↦ (j : ℝ) ^ 3 * rho j) :
    Integrable (cubicTailIntegrand delta)
      (scaledLatticeMeasure rho N hrho hzero : Measure ℝ) := by
  change Integrable (cubicTailIntegrand delta) (scaledLatticeMeasureRaw rho N)
  apply integrable_scaledLatticeMeasureRaw_of_summable rho N
  · exact hrho
  · exact cubicTailIntegrand_nonneg delta
  · exact (cubicTailIntegrand_lowerSemicontinuous delta).measurable.stronglyMeasurable
  · exact summable_scaledLattice_cubicTail rho N delta hN hrho hthird

theorem integrable_cubicTail_scaledLatticeMeasure_all
    (rho : Seq) (N : ℕ) (delta : ℝ)
    (hrho : ∀ j, 0 ≤ rho j) (hzero : Summable rho)
    (hthird : Summable fun j : ℕ ↦ (j : ℝ) ^ 3 * rho j) :
    Integrable (cubicTailIntegrand delta)
      (scaledLatticeMeasure rho N hrho hzero : Measure ℝ) := by
  change Integrable (cubicTailIntegrand delta) (scaledLatticeMeasureRaw rho N)
  apply integrable_scaledLatticeMeasureRaw_of_summable rho N
  · exact hrho
  · exact cubicTailIntegrand_nonneg delta
  · exact (cubicTailIntegrand_lowerSemicontinuous delta).measurable.stronglyMeasurable
  · exact summable_scaledLattice_cubicTail_all rho N delta hrho hthird

/-- Exact identification of the source's normalized discrete cubic tail with
the cubic tail integral of its concrete scaled lattice measure. -/
theorem integral_cubicTail_scaledLatticeMeasure_eq
    (rho : Seq) (N : ℕ) (delta : ℝ) (hN : 1 ≤ N)
    (hrho : ∀ j, 0 ≤ rho j) (hzero : Summable rho)
    (hthird : Summable fun j : ℕ ↦ (j : ℝ) ^ 3 * rho j) :
    (∫ x, cubicTailIntegrand delta x
        ∂(scaledLatticeMeasure rho N hrho hzero : Measure ℝ)) =
      scaledDiscreteMomentTail rho 3 N delta := by
  change (∫ x, cubicTailIntegrand delta x ∂(scaledLatticeMeasureRaw rho N)) = _
  rw [integral_scaledLatticeMeasureRaw_eq_tsum rho N
    (cubicTailIntegrand delta) hrho
    (cubicTailIntegrand_nonneg delta)
    ((cubicTailIntegrand_lowerSemicontinuous delta).measurable.stronglyMeasurable)
    (summable_scaledLattice_cubicTail rho N delta hN hrho hthird)]
  have htail := momentTail_summable_of_moment
    rho 3 (delta * (N : ℝ)) hrho hthird
  rw [scaledDiscreteMomentTail]
  calc
    (∑' j : ℕ, (N : ℝ) * rho j *
        cubicTailIntegrand delta ((j : ℝ) / (N : ℝ))) =
        ∑' j : ℕ, ((N : ℝ) / (N : ℝ) ^ 3) *
          ((j : ℝ) ^ 3 * rho j *
            strictTailIndicator (delta * (N : ℝ)) (j : ℝ)) := by
      apply tsum_congr
      intro j
      exact scaledLattice_cubicTail_term_eq rho N j delta hN
    _ = ((N : ℝ) / (N : ℝ) ^ 3) *
        ∑' j : ℕ, (j : ℝ) ^ 3 * rho j *
          strictTailIndicator (delta * (N : ℝ)) (j : ℝ) :=
      htail.tsum_mul_left ((N : ℝ) / (N : ℝ) ^ 3)

theorem integral_cubicTail_scaledLatticeMeasure_eq_all
    (rho : Seq) (N : ℕ) (delta : ℝ)
    (hrho : ∀ j, 0 ≤ rho j) (hzero : Summable rho)
    (hthird : Summable fun j : ℕ ↦ (j : ℝ) ^ 3 * rho j) :
    (∫ x, cubicTailIntegrand delta x
        ∂(scaledLatticeMeasure rho N hrho hzero : Measure ℝ)) =
      scaledDiscreteMomentTail rho 3 N delta := by
  by_cases hN : N = 0
  · subst N
    change (∫ x, cubicTailIntegrand delta x
      ∂(scaledLatticeMeasureRaw rho 0)) = scaledDiscreteMomentTail rho 3 0 delta
    have hraw : scaledLatticeMeasureRaw rho 0 = 0 := by
      simp [scaledLatticeMeasureRaw]
    rw [hraw]
    simp [scaledDiscreteMomentTail]
  · exact integral_cubicTail_scaledLatticeMeasure_eq rho N delta
      (Nat.one_le_iff_ne_zero.mpr hN) hrho hzero hthird

/-- A proof-carrying sequence of scaled lattice measures, indexed from the
positive scales `N+1` so division by the lattice scale is always legitimate. -/
def scaledLatticeMeasures
    (rho : ℕ → Seq) (hrho : ∀ N j, 0 ≤ rho N j)
    (hzero : ∀ N, Summable (rho N)) : ℕ → FiniteMeasure ℝ :=
  fun N ↦ scaledLatticeMeasure (rho (N + 1)) (N + 1) (hrho (N + 1)) (hzero (N + 1))

/-- Scaled lattice measures along an arbitrary selected lattice scale. -/
def scaledLatticeMeasuresAlong
    (rho : ℕ → Seq) (scale : ℕ → ℕ)
    (hrho : ∀ k j, 0 ≤ rho k j)
    (hzero : ∀ k, Summable (rho k)) : ℕ → FiniteMeasure ℝ :=
  fun k ↦ scaledLatticeMeasure (rho k) (scale k) (hrho k) (hzero k)

/-- Source-shaped Portmanteau wrapper.  A concrete weak limit of the scaled
lattice measures and a uniform discrete cubic-tail estimate imply the same
tail estimate for the limiting measure. -/
theorem limit_cubicTail_le_of_scaledLatticeMeasures_tendsto
    (rho : ℕ → Seq) (mu : FiniteMeasure ℝ)
    (hrho : ∀ N j, 0 ≤ rho N j)
    (hzero : ∀ N, Summable (rho N))
    (hthird : ∀ N, Summable fun j : ℕ ↦ (j : ℝ) ^ 3 * rho N j)
    (hweak : Tendsto (scaledLatticeMeasures rho hrho hzero) atTop (nhds mu))
    (delta B : ℝ)
    (hmuIntegrable : Integrable (cubicTailIntegrand delta) (mu : Measure ℝ))
    (hbound : ∀ N : ℕ,
      scaledDiscreteMomentTail (rho (N + 1)) 3 (N + 1) delta ≤ B) :
    (∫ x, cubicTailIntegrand delta x ∂(mu : Measure ℝ)) ≤ B := by
  apply integral_cubicTail_le_of_finiteMeasure_tendsto
    (scaledLatticeMeasures rho hrho hzero) mu hweak delta B
  · intro N
    exact integrable_cubicTail_scaledLatticeMeasure
      (rho (N + 1)) (N + 1) delta (Nat.succ_le_succ (Nat.zero_le N))
      (hrho (N + 1)) (hzero (N + 1)) (hthird (N + 1))
  · exact hmuIntegrable
  · intro N
    change (∫ x, cubicTailIntegrand delta x
      ∂(scaledLatticeMeasure (rho (N + 1)) (N + 1)
        (hrho (N + 1)) (hzero (N + 1)) : Measure ℝ)) ≤ B
    rw [integral_cubicTail_scaledLatticeMeasure_eq
      (rho (N + 1)) (N + 1) delta (Nat.succ_le_succ (Nat.zero_le N))
      (hrho (N + 1)) (hzero (N + 1)) (hthird (N + 1))]
    exact hbound N

/-- Cofinal-subsequence version of the concrete Portmanteau wrapper.  The
scale map is not hard-coded to the theorem index. -/
theorem limit_cubicTail_le_of_scaledLatticeMeasuresAlong_tendsto
    (rho : ℕ → Seq) (scale : ℕ → ℕ) (mu : FiniteMeasure ℝ)
    (hrho : ∀ k j, 0 ≤ rho k j)
    (hzero : ∀ k, Summable (rho k))
    (hthird : ∀ k, Summable fun j : ℕ ↦ (j : ℝ) ^ 3 * rho k j)
    (hweak : Tendsto (scaledLatticeMeasuresAlong rho scale hrho hzero)
      atTop (nhds mu))
    (delta B : ℝ)
    (hmuIntegrable : Integrable (cubicTailIntegrand delta) (mu : Measure ℝ))
    (hbound : ∀ k : ℕ,
      scaledDiscreteMomentTail (rho k) 3 (scale k) delta ≤ B) :
    (∫ x, cubicTailIntegrand delta x ∂(mu : Measure ℝ)) ≤ B := by
  apply integral_cubicTail_le_of_finiteMeasure_tendsto
    (scaledLatticeMeasuresAlong rho scale hrho hzero) mu hweak delta B
  · intro k
    exact integrable_cubicTail_scaledLatticeMeasure_all
      (rho k) (scale k) delta (hrho k) (hzero k) (hthird k)
  · exact hmuIntegrable
  · intro k
    change (∫ x, cubicTailIntegrand delta x
      ∂(scaledLatticeMeasure (rho k) (scale k)
        (hrho k) (hzero k) : Measure ℝ)) ≤ B
    rw [integral_cubicTail_scaledLatticeMeasure_eq_all
      (rho k) (scale k) delta (hrho k) (hzero k) (hthird k)]
    exact hbound k

/-- Asymptotic version of the cofinal-scale wrapper: only an eventual
prelimit tail bound is required. -/
theorem limit_cubicTail_le_of_scaledLatticeMeasuresAlong_tendsto_eventually
    (rho : ℕ → Seq) (scale : ℕ → ℕ) (mu : FiniteMeasure ℝ)
    (hrho : ∀ k j, 0 ≤ rho k j)
    (hzero : ∀ k, Summable (rho k))
    (hthird : ∀ k, Summable fun j : ℕ ↦ (j : ℝ) ^ 3 * rho k j)
    (hweak : Tendsto (scaledLatticeMeasuresAlong rho scale hrho hzero)
      atTop (nhds mu))
    (delta B : ℝ)
    (hmuIntegrable : Integrable (cubicTailIntegrand delta) (mu : Measure ℝ))
    (hbound : ∀ᶠ k : ℕ in atTop,
      scaledDiscreteMomentTail (rho k) 3 (scale k) delta ≤ B) :
    (∫ x, cubicTailIntegrand delta x ∂(mu : Measure ℝ)) ≤ B := by
  apply integral_cubicTail_le_of_finiteMeasure_tendsto_eventually
    (scaledLatticeMeasuresAlong rho scale hrho hzero) mu hweak delta B
  · intro k
    exact integrable_cubicTail_scaledLatticeMeasure_all
      (rho k) (scale k) delta (hrho k) (hzero k) (hthird k)
  · exact hmuIntegrable
  · filter_upwards [hbound] with k hk
    change (∫ x, cubicTailIntegrand delta x
      ∂(scaledLatticeMeasure (rho k) (scale k)
        (hrho k) (hzero k) : Measure ℝ)) ≤ B
    rw [integral_cubicTail_scaledLatticeMeasure_eq_all
      (rho k) (scale k) delta (hrho k) (hzero k) (hthird k)]
    exact hk

end

end DerridaRetaux
