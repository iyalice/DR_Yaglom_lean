import DerridaRetaux.Sharpness.ProductContradiction
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.PSeries
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Tactic

set_option autoImplicit false

open Filter Topology Asymptotics
open scoped BigOperators

namespace DerridaRetaux

/-!
# Logarithmic Cesaro passage for the sharpness product

This file formalizes the logarithmic calculation displayed in source unit `U62`.
It is entirely internal: the only hypotheses are the scaled one-step limit and
the lower bound `G n >= 1`.
-/

noncomputable section

/-- Harmonic normalization of a sequence, with weights `1 / (j + 1)`. -/
def harmonicWeightedMean (v : ℕ → ℝ) (n : ℕ) : ℝ :=
  (∑ j ∈ Finset.range n, v j / ((j + 1 : ℕ) : ℝ)) / (harmonic n : ℝ)

theorem harmonic_cast_eq_sum_inv_nat_succ (n : ℕ) :
    (harmonic n : ℝ) =
      ∑ j ∈ Finset.range n, (((j + 1 : ℕ) : ℝ))⁻¹ := by
  simp only [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]

theorem harmonic_cast_tendsto_atTop :
    Tendsto (fun n : ℕ ↦ (harmonic n : ℝ)) atTop atTop := by
  have harg : Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hlog : Tendsto (fun n : ℕ ↦ Real.log ((n + 1 : ℕ) : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp harg
  exact tendsto_atTop_mono' atTop
    (Eventually.of_forall fun n ↦ log_add_one_le_harmonic n) hlog

/-- Harmonic numbers and `log (n + 1)` have ratio one. -/
theorem harmonic_div_log_add_one_tendsto_one :
    Tendsto
      (fun n : ℕ ↦ (harmonic n : ℝ) / Real.log ((n + 1 : ℕ) : ℝ))
      atTop (nhds 1) := by
  have harg : Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hlog : Tendsto (fun n : ℕ ↦ Real.log ((n + 1 : ℕ) : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp harg
  have hquot := Real.tendsto_harmonic_sub_log_add_one.div_atTop hlog
  have hsum := hquot.add_const 1
  have hsum' : Tendsto
      (fun n : ℕ ↦
        ((harmonic n : ℝ) - Real.log ((n + 1 : ℕ) : ℝ)) /
            Real.log ((n + 1 : ℕ) : ℝ) + 1)
      atTop (nhds 1) := by
    simpa only [zero_add, Nat.cast_add, Nat.cast_one] using hsum
  apply hsum'.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hlogpos : 0 < Real.log ((n + 1 : ℕ) : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (show 1 < n + 1 by omega)
  field_simp only [hlogpos.ne']
  ring

/-- Logarithmic weighted Cesaro: convergence is preserved by harmonic weights. -/
theorem harmonicWeightedMean_tendsto
    (v : ℕ → ℝ) (a : ℝ) (hv : Tendsto v atTop (nhds a)) :
    Tendsto (harmonicWeightedMean v) atTop (nhds a) := by
  let w : ℕ → ℝ := fun j ↦ (((j + 1 : ℕ) : ℝ))⁻¹
  have hw : ∀ j : ℕ, 0 ≤ w j := fun j ↦ by
    dsimp only [w]
    positivity
  have hwTop : Tendsto
      (fun n : ℕ ↦ ∑ j ∈ Finset.range n, w j) atTop atTop := by
    simpa only [w, ← harmonic_cast_eq_sum_inv_nat_succ] using
      harmonic_cast_tendsto_atTop
  have herror : Tendsto (fun j : ℕ ↦ v j - a) atTop (nhds 0) := by
    simpa only [sub_self] using hv.sub_const a
  have herrorLittleO :
      (fun j : ℕ ↦ v j - a) =o[atTop] (fun _j : ℕ ↦ (1 : ℝ)) :=
    (isLittleO_one_iff ℝ).2 herror
  have htermLittleO :
      (fun j : ℕ ↦ (v j - a) * w j) =o[atTop] w := by
    simpa only [one_mul] using
      herrorLittleO.mul_isBigO (isBigO_refl w atTop)
  have hsumLittleO := htermLittleO.sum_range hw hwTop
  have hquot : Tendsto
      (fun n : ℕ ↦
        (∑ j ∈ Finset.range n, (v j - a) * w j) / (harmonic n : ℝ))
      atTop (nhds 0) := by
    simpa only [w, ← harmonic_cast_eq_sum_inv_nat_succ] using
      hsumLittleO.tendsto_div_nhds_zero
  have hcomparison := hquot.add_const a
  have hcomparison' : Tendsto
      (fun n : ℕ ↦
        (∑ j ∈ Finset.range n, (v j - a) * w j) / (harmonic n : ℝ) + a)
      atTop (nhds a) := by
    simpa only [zero_add] using hcomparison
  apply hcomparison'.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hlogpos : 0 < Real.log ((n + 1 : ℕ) : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (show 1 < n + 1 by omega)
  have hHpos : 0 < (harmonic n : ℝ) :=
    lt_of_lt_of_le hlogpos (log_add_one_le_harmonic n)
  have hsumIdentity :
      (∑ j ∈ Finset.range n, v j / ((j + 1 : ℕ) : ℝ)) =
        (∑ j ∈ Finset.range n, (v j - a) * w j) +
          a * (harmonic n : ℝ) := by
    rw [harmonic_cast_eq_sum_inv_nat_succ, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    dsimp only [w]
    rw [div_eq_mul_inv]
    ring
  rw [harmonicWeightedMean, hsumIdentity]
  field_simp only [hHpos.ne']

/-- A finite limit of `n * u_n` forces square summability of `u`. -/
theorem summable_sq_of_nat_mul_tendsto
    (u : ℕ → ℝ) (a : ℝ)
    (hlimit : Tendsto (fun n : ℕ ↦ (n : ℝ) * u n) atTop (nhds a)) :
    Summable (fun n : ℕ ↦ (u n) ^ 2) := by
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hlimit 1 zero_lt_one
  let C : ℝ := |a| + 1
  have hC : 0 ≤ C := by
    dsimp only [C]
    positivity
  have hbound : ∀ n : ℕ, max N 1 ≤ n → |(n : ℝ) * u n| ≤ C := by
    intro n hn
    have hdist := hN n (le_trans (le_max_left N 1) hn)
    rw [Real.dist_eq] at hdist
    dsimp only [C]
    calc
      |(n : ℝ) * u n| = |((n : ℝ) * u n - a) + a| := by ring_nf
      _ ≤ |(n : ℝ) * u n - a| + |a| :=
        abs_add ((n : ℝ) * u n - a) a
      _ ≤ |a| + 1 := by linarith
  have hseries : Summable (fun n : ℕ ↦ C ^ 2 * (1 / (n : ℝ) ^ 2)) :=
    (Real.summable_one_div_nat_pow.mpr (by norm_num)).mul_left (C ^ 2)
  apply hseries.of_norm_bounded_eventually_nat
  filter_upwards [eventually_ge_atTop (max N 1)] with n hn
  have hnOne : 1 ≤ n := le_trans (le_max_right N 1) hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnOne
  have hu : |u n| ≤ C / (n : ℝ) := by
    rw [le_div_iff₀ hnpos]
    calc
      |u n| * (n : ℝ) = |(n : ℝ) * u n| := by
        rw [abs_mul, abs_of_pos hnpos]
        ring
      _ ≤ C := hbound n hn
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (u n))]
  calc
    u n ^ 2 = |u n| ^ 2 := by rw [sq_abs]
    _ ≤ (C / (n : ℝ)) ^ 2 := by gcongr
    _ = C ^ 2 * (1 / (n : ℝ) ^ 2) := by
      field_simp only [hnpos.ne']
      ring

/-- Source specialization: `n * (G_n - 1)` having a finite limit implies the
square summability stated in `U62`. -/
theorem summable_partition_excess_sq
    (G : ℕ → ℝ) (a : ℝ)
    (hlimit : Tendsto (fun n : ℕ ↦ (n : ℝ) * (G n - 1)) atTop (nhds a)) :
    Summable (fun n : ℕ ↦ (G n - 1) ^ 2) :=
  summable_sq_of_nat_mul_tendsto (fun n ↦ G n - 1) a hlimit

/-- The nonnegative logarithmic Taylor remainder is bounded by the square. -/
theorem sub_log_one_add_nonneg_and_le_sq (x : ℝ) (hx : 0 ≤ x) :
    0 ≤ x - Real.log (1 + x) ∧ x - Real.log (1 + x) ≤ x ^ 2 := by
  have hpos : 0 < 1 + x := by linarith
  have hupper : Real.log (1 + x) ≤ x := by
    simpa only [add_sub_cancel_left] using Real.log_le_sub_one_of_pos hpos
  have hlower := Real.le_log_one_add_of_nonneg hx
  have hden : 0 < x + 2 := by linarith
  have heq : x - 2 * x / (x + 2) = x ^ 2 / (x + 2) := by
    field_simp only [hden.ne']
    ring
  have hfrac : x ^ 2 / (x + 2) ≤ x ^ 2 := by
    rw [div_le_iff₀ hden]
    nlinarith [sq_nonneg x, mul_nonneg (sq_nonneg x) hx]
  constructor
  · linarith
  · calc
      x - Real.log (1 + x) ≤ x - 2 * x / (x + 2) := by linarith
      _ = x ^ 2 / (x + 2) := heq
      _ ≤ x ^ 2 := hfrac

/-- The difference `(G_n - 1) - log G_n` is summable under the hypotheses of
the logarithmic product calculation. -/
theorem summable_partition_log_remainder
    (G : ℕ → ℝ) (a : ℝ) (hG : ∀ n : ℕ, 1 ≤ G n)
    (hlimit : Tendsto (fun n : ℕ ↦ (n : ℝ) * (G n - 1)) atTop (nhds a)) :
    Summable (fun n : ℕ ↦ (G n - 1) - Real.log (G n)) := by
  have hsquare := summable_partition_excess_sq G a hlimit
  apply Summable.of_nonneg_of_le (f := fun n : ℕ ↦ (G n - 1) ^ 2)
  · intro n
    have hx : 0 ≤ G n - 1 := sub_nonneg.mpr (hG n)
    have h := (sub_log_one_add_nonneg_and_le_sq (G n - 1) hx).1
    simpa only [show 1 + (G n - 1) = G n by ring] using h
  · intro n
    have hx : 0 ≤ G n - 1 := sub_nonneg.mpr (hG n)
    have h := (sub_log_one_add_nonneg_and_le_sq (G n - 1) hx).2
    simpa only [show 1 + (G n - 1) = G n by ring] using h
  · exact hsquare

/-- Summability makes the accumulated logarithmic Taylor remainder negligible
on the logarithmic scale. -/
theorem partition_log_remainder_sum_div_log_tendsto_zero
    (G : ℕ → ℝ) (a : ℝ) (hG : ∀ n : ℕ, 1 ≤ G n)
    (hlimit : Tendsto (fun n : ℕ ↦ (n : ℝ) * (G n - 1)) atTop (nhds a)) :
    Tendsto
      (fun n : ℕ ↦
        (∑ j ∈ Finset.range n, ((G j - 1) - Real.log (G j))) /
          Real.log (n : ℝ))
      atTop (nhds 0) := by
  have hsum := summable_partition_log_remainder G a hG hlimit
  have hpartial : Tendsto
      (fun n : ℕ ↦ ∑ j ∈ Finset.range n, ((G j - 1) - Real.log (G j)))
      atTop (nhds (∑' j : ℕ, ((G j - 1) - Real.log (G j)))) :=
    hsum.hasSum.tendsto_sum_nat
  have hlog : Tendsto (fun n : ℕ ↦ Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  exact hpartial.div_atTop hlog

/-- The shifted excess sum has harmonic mean `a`. -/
theorem shifted_partition_excess_sum_div_harmonic_tendsto
    (G : ℕ → ℝ) (a : ℝ)
    (hlimit : Tendsto (fun n : ℕ ↦ (n : ℝ) * (G n - 1)) atTop (nhds a)) :
    Tendsto
      (fun n : ℕ ↦
        (∑ j ∈ Finset.range n, (G (j + 1) - 1)) / (harmonic n : ℝ))
      atTop (nhds a) := by
  let v : ℕ → ℝ := fun j ↦ ((j + 1 : ℕ) : ℝ) * (G (j + 1) - 1)
  have hv : Tendsto v atTop (nhds a) := by
    dsimp only [v]
    exact hlimit.comp (tendsto_add_atTop_nat 1)
  have hmean := harmonicWeightedMean_tendsto v a hv
  apply hmean.congr'
  filter_upwards with n
  rw [harmonicWeightedMean]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  dsimp only [v]
  have hjpos : (0 : ℝ) < ((j + 1 : ℕ) : ℝ) := by positivity
  field_simp only [hjpos.ne']
  ring

/-- Replacing harmonic normalization by `log (n + 1)` preserves the shifted
excess-sum limit. -/
theorem shifted_partition_excess_sum_div_log_add_one_tendsto
    (G : ℕ → ℝ) (a : ℝ)
    (hlimit : Tendsto (fun n : ℕ ↦ (n : ℝ) * (G n - 1)) atTop (nhds a)) :
    Tendsto
      (fun n : ℕ ↦
        (∑ j ∈ Finset.range n, (G (j + 1) - 1)) /
          Real.log ((n + 1 : ℕ) : ℝ))
      atTop (nhds a) := by
  have hmean := shifted_partition_excess_sum_div_harmonic_tendsto G a hlimit
  have hproduct := hmean.mul harmonic_div_log_add_one_tendsto_one
  have hproduct' : Tendsto
      (fun n : ℕ ↦
        ((∑ j ∈ Finset.range n, (G (j + 1) - 1)) / (harmonic n : ℝ)) *
          ((harmonic n : ℝ) / Real.log ((n + 1 : ℕ) : ℝ)))
      atTop (nhds a) := by
    simpa only [mul_one] using hproduct
  apply hproduct'.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hlogpos : 0 < Real.log ((n + 1 : ℕ) : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (show 1 < n + 1 by omega)
  have hHpos : 0 < (harmonic n : ℝ) :=
    lt_of_lt_of_le hlogpos (log_add_one_le_harmonic n)
  field_simp only [hHpos.ne', hlogpos.ne']
  ring

/-- The scaled one-step limit implies the harmonic-Cesaro asymptotic for the
unshifted excess sum. -/
theorem partition_excess_sum_div_log_tendsto
    (G : ℕ → ℝ) (a : ℝ)
    (hlimit : Tendsto (fun n : ℕ ↦ (n : ℝ) * (G n - 1)) atTop (nhds a)) :
    Tendsto
      (fun n : ℕ ↦
        (∑ j ∈ Finset.range n, (G j - 1)) / Real.log (n : ℝ))
      atTop (nhds a) := by
  have harg : Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hlog : Tendsto (fun n : ℕ ↦ Real.log ((n + 1 : ℕ) : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp harg
  have hzero : Tendsto
      (fun n : ℕ ↦ (G 0 - 1) / Real.log ((n + 1 : ℕ) : ℝ))
      atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hlog
  have hshift := shifted_partition_excess_sum_div_log_add_one_tendsto G a hlimit
  have hadd := hzero.add hshift
  have hadd' : Tendsto
      (fun n : ℕ ↦
        (G 0 - 1) / Real.log ((n + 1 : ℕ) : ℝ) +
          (∑ j ∈ Finset.range n, (G (j + 1) - 1)) /
            Real.log ((n + 1 : ℕ) : ℝ))
      atTop (nhds a) := by
    simpa only [zero_add] using hadd
  apply (tendsto_add_atTop_iff_nat 1).mp
  apply hadd'.congr'
  filter_upwards with n
  rw [Finset.sum_range_succ']
  push_cast
  ring

/-- Full logarithmic Cesaro conclusion from `U62`. -/
theorem partition_log_sum_div_log_tendsto
    (G : ℕ → ℝ) (a : ℝ) (hG : ∀ n : ℕ, 1 ≤ G n)
    (hlimit : Tendsto (fun n : ℕ ↦ (n : ℝ) * (G n - 1)) atTop (nhds a)) :
    Tendsto
      (fun n : ℕ ↦
        (∑ j ∈ Finset.range n, Real.log (G j)) / Real.log (n : ℝ))
      atTop (nhds a) := by
  have hexcess := partition_excess_sum_div_log_tendsto G a hlimit
  have hremainder :=
    partition_log_remainder_sum_div_log_tendsto_zero G a hG hlimit
  have hdifference := hexcess.sub hremainder
  have hdifference' : Tendsto
      (fun n : ℕ ↦
        (∑ j ∈ Finset.range n, (G j - 1)) / Real.log (n : ℝ) -
          (∑ j ∈ Finset.range n, ((G j - 1) - Real.log (G j))) /
            Real.log (n : ℝ))
      atTop (nhds a) := by
    simpa only [sub_zero] using hdifference
  apply hdifference'.congr'
  filter_upwards with n
  have hsumIdentity :
      (∑ j ∈ Finset.range n, (G j - 1)) -
          (∑ j ∈ Finset.range n, ((G j - 1) - Real.log (G j))) =
        ∑ j ∈ Finset.range n, Real.log (G j) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [← hsumIdentity]
  ring

/-- A quotient limit is equivalently an `o(log n)` remainder. -/
theorem sub_mul_log_isLittleO_of_div_tendsto
    (f : ℕ → ℝ) (a : ℝ)
    (hlimit : Tendsto
      (fun n : ℕ ↦ f n / Real.log (n : ℝ)) atTop (nhds a)) :
    (fun n : ℕ ↦ f n - a * Real.log (n : ℝ)) =o[atTop]
      (fun n : ℕ ↦ Real.log (n : ℝ)) := by
  have hzero : ∀ᶠ n : ℕ in atTop,
      Real.log (n : ℝ) = 0 → f n - a * Real.log (n : ℝ) = 0 := by
    filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn
    intro hzero
    have hlogpos : 0 < Real.log (n : ℝ) := by
      apply Real.log_pos
      exact_mod_cast (show 1 < n by omega)
    exact (hlogpos.ne' hzero).elim
  apply (isLittleO_iff_tendsto' hzero).2
  have hsub := hlimit.sub_const a
  have hsub' : Tendsto
      (fun n : ℕ ↦ f n / Real.log (n : ℝ) - a)
      atTop (nhds 0) := by
    simpa only [sub_self] using hsub
  apply hsub'.congr'
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn
  have hlogpos : 0 < Real.log (n : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (show 1 < n by omega)
  field_simp only [hlogpos.ne']
  ring

/-- Equivalent source form: the logarithmic prefix sum is
`a * log n + o(log n)`. -/
theorem partition_log_sum_sub_mul_log_isLittleO
    (G : ℕ → ℝ) (a : ℝ) (hG : ∀ n : ℕ, 1 ≤ G n)
    (hlimit : Tendsto (fun n : ℕ ↦ (n : ℝ) * (G n - 1)) atTop (nhds a)) :
    (fun n : ℕ ↦
      (∑ j ∈ Finset.range n, Real.log (G j)) - a * Real.log (n : ℝ))
      =o[atTop] (fun n : ℕ ↦ Real.log (n : ℝ)) :=
  sub_mul_log_isLittleO_of_div_tendsto
    (fun n ↦ ∑ j ∈ Finset.range n, Real.log (G j)) a
      (partition_log_sum_div_log_tendsto G a hG hlimit)

/-- At the Derrida--Retaux constant, multiplying the log sum by `m - 1`
produces exponent two. -/
theorem critical_partition_log_sum_div_log_tendsto_two
    (m : ℕ) (G : ℕ → ℝ) (hm : 2 ≤ m) (hG : ∀ n : ℕ, 1 ≤ G n)
    (hlimit : Tendsto
      (fun n : ℕ ↦ (n : ℝ) * (G n - 1))
      atTop (nhds (2 / ((m : ℝ) - 1)))) :
    Tendsto
      (fun n : ℕ ↦
        ((m : ℝ) - 1) *
          (∑ j ∈ Finset.range n, Real.log (G j)) / Real.log (n : ℝ))
      atTop (nhds 2) := by
  have hfactor : (m : ℝ) - 1 ≠ 0 := by
    have hmReal : (1 : ℝ) < (m : ℝ) := by exact_mod_cast (show 1 < m by omega)
    linarith
  have hsum :=
    partition_log_sum_div_log_tendsto G (2 / ((m : ℝ) - 1)) hG hlimit
  have hscaled := (tendsto_const_nhds.mul hsum : Tendsto
    (fun n : ℕ ↦
      ((m : ℝ) - 1) *
        ((∑ j ∈ Finset.range n, Real.log (G j)) / Real.log (n : ℝ)))
    atTop (nhds (((m : ℝ) - 1) * (2 / ((m : ℝ) - 1)))))
  convert hscaled using 1
  · funext n
    ring
  · congr 1
    field_simp only [hfactor]
    ring

/-- The same exponent-two conclusion, expressed as the logarithm of the
`poweredPrefixProduct` used in the sharpness contradiction. -/
theorem log_poweredPrefixProduct_div_log_tendsto_two
    (m : ℕ) (G : ℕ → ℝ) (hm : 2 ≤ m) (hG : ∀ n : ℕ, 1 ≤ G n)
    (hlimit : Tendsto
      (fun n : ℕ ↦ (n : ℝ) * (G n - 1))
      atTop (nhds (2 / ((m : ℝ) - 1)))) :
    Tendsto
      (fun n : ℕ ↦
        Real.log (poweredPrefixProduct G (m - 1) n) / Real.log (n : ℝ))
      atTop (nhds 2) := by
  have hsum := critical_partition_log_sum_div_log_tendsto_two
    m G hm hG hlimit
  apply hsum.congr'
  filter_upwards with n
  rw [log_poweredPrefixProduct G (m - 1) n hG, Nat.cast_sub (by omega : 1 ≤ m)]
  ring

/-- Literal `U62` remainder form for the powered product:
`log P_n = 2 log n + o(log n)`. -/
theorem log_poweredPrefixProduct_sub_two_log_isLittleO
    (m : ℕ) (G : ℕ → ℝ) (hm : 2 ≤ m) (hG : ∀ n : ℕ, 1 ≤ G n)
    (hlimit : Tendsto
      (fun n : ℕ ↦ (n : ℝ) * (G n - 1))
      atTop (nhds (2 / ((m : ℝ) - 1)))) :
    (fun n : ℕ ↦
      Real.log (poweredPrefixProduct G (m - 1) n) - 2 * Real.log (n : ℝ))
      =o[atTop] (fun n : ℕ ↦ Real.log (n : ℝ)) :=
  sub_mul_log_isLittleO_of_div_tendsto
    (fun n ↦ Real.log (poweredPrefixProduct G (m - 1) n)) 2
      (log_poweredPrefixProduct_div_log_tendsto_two m G hm hG hlimit)

/-- The source's displayed log-sum identity, before rewriting it as a product. -/
theorem critical_partition_log_sum_sub_two_log_isLittleO
    (m : ℕ) (G : ℕ → ℝ) (hm : 2 ≤ m) (hG : ∀ n : ℕ, 1 ≤ G n)
    (hlimit : Tendsto
      (fun n : ℕ ↦ (n : ℝ) * (G n - 1))
      atTop (nhds (2 / ((m : ℝ) - 1)))) :
    (fun n : ℕ ↦
      ((m : ℝ) - 1) * (∑ j ∈ Finset.range n, Real.log (G j)) -
        2 * Real.log (n : ℝ))
      =o[atTop] (fun n : ℕ ↦ Real.log (n : ℝ)) :=
  sub_mul_log_isLittleO_of_div_tendsto
    (fun n ↦ ((m : ℝ) - 1) * ∑ j ∈ Finset.range n, Real.log (G j)) 2
      (critical_partition_log_sum_div_log_tendsto_two m G hm hG hlimit)

/-- Orbit specialization of the exponent-two result, in the source's
`criticalProduct` notation. -/
theorem orbit_criticalProduct_log_div_log_tendsto_two
    (m : ℕ) (p0 : ProbabilityMass) (hm : 2 ≤ m) (hcrit : Critical m p0)
    (hlimit : Tendsto
      (fun n : ℕ ↦
        (n : ℝ) * (tiltedPartition m (orbit m p0 n) - 1))
      atTop (nhds (2 / ((m : ℝ) - 1)))) :
    Tendsto
      (fun n : ℕ ↦
        Real.log (criticalProduct m p0 n) / Real.log (n : ℝ))
      atTop (nhds 2) := by
  have hG : ∀ n : ℕ, 1 ≤ tiltedPartition m (orbit m p0 n) := by
    intro n
    exact tiltedPartition_one_le_of_critical m (orbit m p0 n) (by omega)
      (orbit_critical m p0 (by omega) hcrit n)
  simpa only [poweredPrefixProduct_tiltedPartition_eq_criticalProduct] using
    log_poweredPrefixProduct_div_log_tendsto_two
      m (fun n ↦ tiltedPartition m (orbit m p0 n)) hm hG hlimit

/-- Literal orbit form of `U62`:
`log criticalProduct_n = 2 log n + o(log n)`. -/
theorem orbit_criticalProduct_sub_two_log_isLittleO
    (m : ℕ) (p0 : ProbabilityMass) (hm : 2 ≤ m) (hcrit : Critical m p0)
    (hlimit : Tendsto
      (fun n : ℕ ↦
        (n : ℝ) * (tiltedPartition m (orbit m p0 n) - 1))
      atTop (nhds (2 / ((m : ℝ) - 1)))) :
    (fun n : ℕ ↦
      Real.log (criticalProduct m p0 n) - 2 * Real.log (n : ℝ))
      =o[atTop] (fun n : ℕ ↦ Real.log (n : ℝ)) :=
  sub_mul_log_isLittleO_of_div_tendsto
    (fun n ↦ Real.log (criticalProduct m p0 n)) 2
      (orbit_criticalProduct_log_div_log_tendsto_two m p0 hm hcrit hlimit)

end

end DerridaRetaux
