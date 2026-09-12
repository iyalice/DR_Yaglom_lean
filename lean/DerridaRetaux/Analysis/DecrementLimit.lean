import DerridaRetaux.Model.Readout
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic

set_option autoImplicit false

open Filter Topology
open scoped BigOperators

namespace DerridaRetaux

noncomputable section

/-!
# The excess-decrement limit

This file isolates the finite polynomial limit calculation after the exact
identity excess_orbit_decrement.  The source uses a second-order survival
limit and a first-order excess limit; these scales are kept explicit.
-/

/-- The first divided difference of the survival power polynomial at zero. -/
def survivalPowerCoeff (m : ℕ) (x : ℝ) : ℝ :=
  ∑ j ∈ Finset.range m, (1 - x) ^ j

/-- The second divided difference of the excess power polynomial at zero. -/
def excessPowerCoeff (m : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range m, ∑ j ∈ Finset.range k, (1 + x) ^ j

/-- Exact first-order factorization of the survival polynomial. -/
theorem one_sub_one_sub_pow_eq_mul_survivalPowerCoeff
    (m : ℕ) (x : ℝ) :
    1 - (1 - x) ^ m = x * survivalPowerCoeff m x := by
  have h := geom_sum_mul_add (-x) m
  dsimp only [survivalPowerCoeff]
  ring_nf at h ⊢
  nlinarith

/-- Exact second-order factorization of the excess polynomial remainder. -/
theorem one_add_pow_sub_linear_eq_sq_mul_excessPowerCoeff
    (m : ℕ) (x : ℝ) :
    (1 + x) ^ m - 1 - (m : ℝ) * x = x ^ 2 * excessPowerCoeff m x := by
  induction m with
  | zero =>
      simp [excessPowerCoeff]
  | succ m ih =>
      have hgeom := geom_sum_mul_add x m
      rw [excessPowerCoeff, Finset.sum_range_succ]
      push_cast
      change
        (1 + x) ^ (m + 1) - 1 - ((m : ℝ) + 1) * x =
          x ^ 2 *
            (excessPowerCoeff m x + ∑ j ∈ Finset.range m, (1 + x) ^ j)
      have hgeom' :
          (1 + x) ^ m - 1 = x * ∑ j ∈ Finset.range m, (1 + x) ^ j := by
        ring_nf at hgeom ⊢
        linarith
      rw [pow_succ]
      calc
        (1 + x) ^ m * (1 + x) - 1 - ((m : ℝ) + 1) * x =
            ((1 + x) ^ m - 1 - (m : ℝ) * x) +
              x * ((1 + x) ^ m - 1) := by ring
        _ = x ^ 2 * excessPowerCoeff m x +
              x * ((1 + x) ^ m - 1) := by rw [ih]
        _ = x ^ 2 * excessPowerCoeff m x +
              x * (x * ∑ j ∈ Finset.range m, (1 + x) ^ j) := by rw [hgeom']
        _ = x ^ 2 *
            (excessPowerCoeff m x + ∑ j ∈ Finset.range m, (1 + x) ^ j) := by
          ring

/-- The survival coefficient takes the expected derivative value at zero. -/
@[simp]
theorem survivalPowerCoeff_zero (m : ℕ) :
    survivalPowerCoeff m 0 = m := by
  simp [survivalPowerCoeff]

/-- The excess coefficient takes the quadratic binomial coefficient at zero. -/
@[simp]
theorem excessPowerCoeff_zero (m : ℕ) :
    excessPowerCoeff m 0 = (m.choose 2 : ℝ) := by
  simp only [excessPowerCoeff, add_zero, one_pow, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul, mul_one]
  rw [← Nat.cast_sum, Finset.sum_range_id, Nat.choose_two_right]

/-- The first divided-difference coefficient is continuous along arbitrary filters. -/
theorem survivalPowerCoeff_tendsto
    {α : Type*} {l : Filter α} (m : ℕ) (u : α → ℝ)
    (hu : Tendsto u l (nhds 0)) :
    Tendsto (fun a ↦ survivalPowerCoeff m (u a)) l (nhds (m : ℝ)) := by
  have honeSub : Tendsto (fun a ↦ 1 - u a) l (nhds (1 : ℝ)) := by
    simpa using tendsto_const_nhds.sub hu
  have hsum :
      Tendsto
        (fun a ↦ ∑ j ∈ Finset.range m, (1 - u a) ^ j) l
        (nhds (∑ j ∈ Finset.range m, (1 : ℝ) ^ j)) := by
    apply tendsto_finset_sum
    intro j hj
    exact honeSub.pow j
  simpa [survivalPowerCoeff] using hsum

/-- The second divided-difference coefficient is continuous along arbitrary filters. -/
theorem excessPowerCoeff_tendsto
    {α : Type*} {l : Filter α} (m : ℕ) (u : α → ℝ)
    (hu : Tendsto u l (nhds 0)) :
    Tendsto (fun a ↦ excessPowerCoeff m (u a)) l (nhds (m.choose 2 : ℝ)) := by
  have honeAdd : Tendsto (fun a ↦ 1 + u a) l (nhds (1 : ℝ)) := by
    simpa using tendsto_const_nhds.add hu
  have hsum :
      Tendsto
        (fun a ↦ ∑ k ∈ Finset.range m, ∑ j ∈ Finset.range k, (1 + u a) ^ j) l
        (nhds (∑ k ∈ Finset.range m, ∑ j ∈ Finset.range k, (1 : ℝ) ^ j)) := by
    apply tendsto_finset_sum
    intro k hk
    apply tendsto_finset_sum
    intro j hj
    exact honeAdd.pow j
  rw [← excessPowerCoeff_zero m]
  simpa [excessPowerCoeff] using hsum

/-- A finite limit for n times u_n forces u_n to zero. -/
theorem tendsto_zero_of_natCast_mul_tendsto
    (u : ℕ → ℝ) (c : ℝ)
    (hscaled : Tendsto (fun n : ℕ ↦ (n : ℝ) * u n) atTop (nhds c)) :
    Tendsto u atTop (nhds 0) := by
  have hinv : Tendsto (fun n : ℕ ↦ ((n : ℝ))⁻¹) atTop (nhds 0) := by
    simpa only [one_div] using tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)
  have hproduct :
      Tendsto (fun n : ℕ ↦ ((n : ℝ) * u n) * ((n : ℝ))⁻¹) atTop (nhds 0) := by
    simpa only [mul_zero] using hscaled.mul hinv
  apply Tendsto.congr' _ hproduct
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (by omega : 0 < n))
  field_simp [hn0]

/-- A finite limit for n squared times u_n likewise forces u_n to zero. -/
theorem tendsto_zero_of_natSquare_mul_tendsto
    (u : ℕ → ℝ) (c : ℝ)
    (hscaled : Tendsto (fun n : ℕ ↦ (n : ℝ) ^ 2 * u n) atTop (nhds c)) :
    Tendsto u atTop (nhds 0) := by
  have hinv : Tendsto (fun n : ℕ ↦ ((n : ℝ))⁻¹) atTop (nhds 0) := by
    simpa only [one_div] using tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)
  have hproduct :
      Tendsto
        (fun n : ℕ ↦ ((n : ℝ) ^ 2 * u n) * ((n : ℝ))⁻¹ ^ 2)
        atTop (nhds 0) := by
    simpa only [pow_two, zero_mul, mul_zero] using hscaled.mul (hinv.pow 2)
  apply Tendsto.congr' _ hproduct
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (by omega : 0 < n))
  field_simp [hn0]

/-- First-order survival polynomial limit on the source second-order scale. -/
theorem natSquare_mul_survivalPower_tendsto
    (m : ℕ) (u : ℕ → ℝ) (P : ℝ)
    (hscaled : Tendsto (fun n : ℕ ↦ (n : ℝ) ^ 2 * u n) atTop (nhds P)) :
    Tendsto
      (fun n : ℕ ↦ (n : ℝ) ^ 2 * (1 - (1 - u n) ^ m))
      atTop (nhds ((m : ℝ) * P)) := by
  have hu := tendsto_zero_of_natSquare_mul_tendsto u P hscaled
  have hcoeff := survivalPowerCoeff_tendsto m u hu
  have hproduct := hscaled.mul hcoeff
  convert hproduct using 1
  · funext n
    rw [one_sub_one_sub_pow_eq_mul_survivalPowerCoeff]
    ring
  · ring_nf

/-- Quadratic excess polynomial limit on the source second-order scale. -/
theorem natSquare_mul_excessPowerRemainder_tendsto
    (m : ℕ) (u : ℕ → ℝ) (E : ℝ)
    (hscaled : Tendsto (fun n : ℕ ↦ (n : ℝ) * u n) atTop (nhds E)) :
    Tendsto
      (fun n : ℕ ↦ (n : ℝ) ^ 2 *
        ((1 + u n) ^ m - 1 - (m : ℝ) * u n))
      atTop (nhds ((m.choose 2 : ℝ) * E ^ 2)) := by
  have hu := tendsto_zero_of_natCast_mul_tendsto u E hscaled
  have hcoeff := excessPowerCoeff_tendsto m u hu
  have hproduct := (hscaled.pow 2).mul hcoeff
  convert hproduct using 1
  · funext n
    rw [one_add_pow_sub_linear_eq_sq_mul_excessPowerCoeff]
    ring
  · ring_nf

/-- First-order scaling of the survival polynomial. -/
theorem natCast_mul_survivalPower_tendsto
    (m : ℕ) (u : ℕ → ℝ) (S : ℝ)
    (hscaled : Tendsto (fun n : ℕ ↦ (n : ℝ) * u n) atTop (nhds S)) :
    Tendsto
      (fun n : ℕ ↦ (n : ℝ) * (1 - (1 - u n) ^ m))
      atTop (nhds ((m : ℝ) * S)) := by
  have hu := tendsto_zero_of_natCast_mul_tendsto u S hscaled
  have hcoeff := survivalPowerCoeff_tendsto m u hu
  have hproduct := hscaled.mul hcoeff
  convert hproduct using 1
  · funext n
    rw [one_sub_one_sub_pow_eq_mul_survivalPowerCoeff]
    ring
  · ring_nf

/-- On the first-order scale, the quadratic excess remainder vanishes. -/
theorem natCast_mul_excessPowerRemainder_tendsto_zero
    (m : ℕ) (u : ℕ → ℝ) (E : ℝ)
    (hscaled : Tendsto (fun n : ℕ ↦ (n : ℝ) * u n) atTop (nhds E)) :
    Tendsto
      (fun n : ℕ ↦ (n : ℝ) *
        ((1 + u n) ^ m - 1 - (m : ℝ) * u n))
      atTop (nhds 0) := by
  have hu := tendsto_zero_of_natCast_mul_tendsto u E hscaled
  have hcoeff := excessPowerCoeff_tendsto m u hu
  have hproduct := (hscaled.mul hu).mul hcoeff
  convert hproduct using 1
  · funext n
    rw [one_add_pow_sub_linear_eq_sq_mul_excessPowerCoeff]
    ring
  · ring_nf

/-- A sequence with a finite limit for n times its value has vanishing
first-order forward difference. -/
theorem natCast_mul_forwardDifference_tendsto_zero
    (u : ℕ → ℝ) (E : ℝ)
    (hscaled : Tendsto (fun n : ℕ ↦ (n : ℝ) * u n) atTop (nhds E)) :
    Tendsto (fun n : ℕ ↦ (n : ℝ) * (u n - u (n + 1))) atTop (nhds 0) := by
  have hshift :
      Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ) * u (n + 1)) atTop (nhds E) := by
    simpa only using (Filter.tendsto_add_atTop_iff_nat 1).mpr hscaled
  have hratio :
      Tendsto (fun n : ℕ ↦ (n : ℝ) / ((n : ℝ) + 1)) atTop (nhds 1) :=
    tendsto_natCast_div_add_atTop (1 : ℝ)
  have hdifference := hscaled.sub (hratio.mul hshift)
  convert hdifference using 1
  · apply funext
    intro n
    have hsucc : (((n + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
    field_simp [hsucc]
    ring
  · ring_nf

/-- If survival were of first order with a positive constant, the exact
decrement identity would contradict the first-order excess asymptotic. -/
theorem firstOrder_survival_incompatible_with_exact_decrement
    (m : ℕ) (hm : 2 ≤ m) (survivalSeq excessSeq : ℕ → ℝ) (S E : ℝ)
    (hS : 0 < S)
    (hsurvival :
      Tendsto (fun n : ℕ ↦ (n : ℝ) * survivalSeq n) atTop (nhds S))
    (hexcess :
      Tendsto (fun n : ℕ ↦ (n : ℝ) * excessSeq n) atTop (nhds E))
    (hidentity : ∀ n : ℕ,
      (m : ℝ) * (excessSeq n - excessSeq (n + 1)) =
        ((m : ℝ) - 1) * (1 - (1 - survivalSeq n) ^ m) -
          ((1 + excessSeq n) ^ m - 1 - (m : ℝ) * excessSeq n)) :
    False := by
  have hsurvivalPower :=
    natCast_mul_survivalPower_tendsto m survivalSeq S hsurvival
  have hexcessPower :=
    natCast_mul_excessPowerRemainder_tendsto_zero m excessSeq E hexcess
  have hrhs :
      Tendsto
        (fun n : ℕ ↦
          ((m : ℝ) - 1) * ((n : ℝ) * (1 - (1 - survivalSeq n) ^ m)) -
            (n : ℝ) * ((1 + excessSeq n) ^ m - 1 - (m : ℝ) * excessSeq n))
        atTop (nhds (((m : ℝ) - 1) * ((m : ℝ) * S))) := by
    convert (hsurvivalPower.const_mul ((m : ℝ) - 1)).sub hexcessPower using 1
    · ring_nf
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  have hdecrement :
      Tendsto
        (fun n : ℕ ↦ (n : ℝ) * (excessSeq n - excessSeq (n + 1)))
        atTop (nhds (((m : ℝ) - 1) * S)) := by
    convert hrhs.div_const (m : ℝ) using 1
    · funext n
      rw [eq_div_iff hm0]
      symm
      calc
        ((m : ℝ) - 1) * ((n : ℝ) * (1 - (1 - survivalSeq n) ^ m)) -
              (n : ℝ) *
                ((1 + excessSeq n) ^ m - 1 - (m : ℝ) * excessSeq n) =
            (n : ℝ) *
              (((m : ℝ) - 1) * (1 - (1 - survivalSeq n) ^ m) -
                ((1 + excessSeq n) ^ m - 1 - (m : ℝ) * excessSeq n)) := by
          ring
        _ = (n : ℝ) * ((m : ℝ) *
              (excessSeq n - excessSeq (n + 1))) := by rw [hidentity n]
        _ = (n : ℝ) * (excessSeq n - excessSeq (n + 1)) * (m : ℝ) := by ring
    · field_simp [hm0]
      ring
  have hzero := natCast_mul_forwardDifference_tendsto_zero excessSeq E hexcess
  have hlimitEq := tendsto_nhds_unique hzero hdecrement
  have hmReal : (1 : ℝ) < (m : ℝ) := by exact_mod_cast (show 1 < m by omega)
  nlinarith

/-- General algebraic decrement limit.  The exact recursion is exposed as an
ordinary equality at every index, and the two input scales are independent. -/
theorem decrement_tendsto_of_exact_identity
    (m : ℕ) (hm : 1 ≤ m) (survivalSeq excessSeq : ℕ → ℝ) (P E : ℝ)
    (hsurvival :
      Tendsto (fun n : ℕ ↦ (n : ℝ) ^ 2 * survivalSeq n) atTop (nhds P))
    (hexcess :
      Tendsto (fun n : ℕ ↦ (n : ℝ) * excessSeq n) atTop (nhds E))
    (hidentity : ∀ n : ℕ,
      (m : ℝ) * (excessSeq n - excessSeq (n + 1)) =
        ((m : ℝ) - 1) * (1 - (1 - survivalSeq n) ^ m) -
          ((1 + excessSeq n) ^ m - 1 - (m : ℝ) * excessSeq n)) :
    Tendsto
      (fun n : ℕ ↦ (n : ℝ) ^ 2 * (excessSeq n - excessSeq (n + 1)))
      atTop
      (nhds
        ((((m : ℝ) - 1) * ((m : ℝ) * P) - (m.choose 2 : ℝ) * E ^ 2) /
          (m : ℝ))) := by
  have hsurvivalPower :=
    natSquare_mul_survivalPower_tendsto m survivalSeq P hsurvival
  have hexcessPower :=
    natSquare_mul_excessPowerRemainder_tendsto m excessSeq E hexcess
  have hrhs :
      Tendsto
        (fun n : ℕ ↦
          ((m : ℝ) - 1) *
              ((n : ℝ) ^ 2 * (1 - (1 - survivalSeq n) ^ m)) -
            (n : ℝ) ^ 2 *
              ((1 + excessSeq n) ^ m - 1 - (m : ℝ) * excessSeq n))
        atTop
        (nhds
          (((m : ℝ) - 1) * ((m : ℝ) * P) - (m.choose 2 : ℝ) * E ^ 2)) :=
    (hsurvivalPower.const_mul ((m : ℝ) - 1)).sub hexcessPower
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hm))
  apply Tendsto.congr' _ (hrhs.div_const (m : ℝ))
  filter_upwards with n
  rw [div_eq_iff hm0]
  calc
    ((m : ℝ) - 1) * ((n : ℝ) ^ 2 * (1 - (1 - survivalSeq n) ^ m)) -
          (n : ℝ) ^ 2 *
            ((1 + excessSeq n) ^ m - 1 - (m : ℝ) * excessSeq n) =
        (n : ℝ) ^ 2 *
          (((m : ℝ) - 1) * (1 - (1 - survivalSeq n) ^ m) -
            ((1 + excessSeq n) ^ m - 1 - (m : ℝ) * excessSeq n)) := by
      ring
    _ = (n : ℝ) ^ 2 * ((m : ℝ) * (excessSeq n - excessSeq (n + 1))) := by
      rw [hidentity n]
    _ = (n : ℝ) ^ 2 * (excessSeq n - excessSeq (n + 1)) * (m : ℝ) := by
      ring

/-- Source-specialized decrement limit.  The required survival hypothesis is
the manuscript's actual second-order limit, not a first-order substitute. -/
theorem excess_orbit_decrement_tendsto
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m) (hcrit : Critical m p₀)
    (hsurvival :
      Tendsto
        (fun n : ℕ ↦ (n : ℝ) ^ 2 * survival (orbit m p₀ n))
        atTop (nhds (4 / ((m : ℝ) - 1) ^ 2)))
    (hexcess :
      Tendsto
        (fun n : ℕ ↦ (n : ℝ) * excess m (orbit m p₀ n))
        atTop (nhds (2 / ((m : ℝ) - 1)))) :
    Tendsto
      (fun n : ℕ ↦ (n : ℝ) ^ 2 *
        (excess m (orbit m p₀ n) - excess m (orbit m p₀ (n + 1))))
      atTop (nhds (2 / ((m : ℝ) - 1))) := by
  have hgeneral := decrement_tendsto_of_exact_identity
    m (by omega)
    (fun n : ℕ ↦ survival (orbit m p₀ n))
    (fun n : ℕ ↦ excess m (orbit m p₀ n))
    (4 / ((m : ℝ) - 1) ^ 2)
    (2 / ((m : ℝ) - 1))
    hsurvival hexcess
    (fun n ↦ excess_orbit_decrement m p₀ (by omega) hcrit n)
  convert hgeneral using 1
  have hmReal : (1 : ℝ) < (m : ℝ) := by exact_mod_cast (show 1 < m by omega)
  have hfactor : (m : ℝ) - 1 ≠ 0 := by linarith
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  rw [Nat.cast_choose_two ℝ]
  field_simp [hfactor, hm0]
  ring

/-- The two first-order limits stated in the rejected premise are incompatible
with the exact orbit decrement identity.  In the source, survival is genuinely
second order. -/
theorem firstOrder_orbit_survival_excess_limits_false
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m) (hcrit : Critical m p₀)
    (hsurvival :
      Tendsto
        (fun n : ℕ ↦ (n : ℝ) * survival (orbit m p₀ n))
        atTop (nhds (2 / ((m : ℝ) - 1))))
    (hexcess :
      Tendsto
        (fun n : ℕ ↦ (n : ℝ) * excess m (orbit m p₀ n))
        atTop (nhds (2 / ((m : ℝ) - 1)))) :
    False := by
  have hmReal : (1 : ℝ) < (m : ℝ) := by exact_mod_cast (show 1 < m by omega)
  have hconstant : 0 < 2 / ((m : ℝ) - 1) := div_pos (by norm_num) (by linarith)
  exact firstOrder_survival_incompatible_with_exact_decrement
    m hm
    (fun n : ℕ ↦ survival (orbit m p₀ n))
    (fun n : ℕ ↦ excess m (orbit m p₀ n))
    (2 / ((m : ℝ) - 1))
    (2 / ((m : ℝ) - 1))
    hconstant hsurvival hexcess
    (fun n ↦ excess_orbit_decrement m p₀ (by omega) hcrit n)

end

end DerridaRetaux
