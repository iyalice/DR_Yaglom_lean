import DerridaRetaux.Analysis.DecrementLimit
import DerridaRetaux.Sharpness.LogCesaro

set_option autoImplicit false

open Filter Topology
open scoped BigOperators

namespace DerridaRetaux

noncomputable section

/-- A cutoff estimate using only criticality, without any third-moment hypothesis. -/
theorem positiveTiltMass_le_survival_cutoff
    (m : ℕ) (p : ProbabilityMass) (hm : 2 ≤ m) (hcrit : Critical m p) (K : ℕ) :
    positiveTiltMass m p ≤ (m : ℝ) ^ K * survival p +
      (1 / ((m : ℝ) - 1)) / ((K : ℝ) + 1) := by
  have hm1 : 1 ≤ m := by omega
  have hG := tiltedPartition_one_le_of_critical m p hm1 hcrit
  have hq := normalizedTilt_nonneg m p hm1 hcrit
  have hmean : HasSum
      (fun k : ℕ ↦ ((k + 1 : ℕ) : ℝ) * normalizedTilt m p (k + 1))
      (1 / ((m : ℝ) - 1)) := by
    simpa using (hasSum_nat_add_iff'
      (f := fun k : ℕ ↦ (k : ℝ) * normalizedTilt m p k) 1).2
      (normalizedTilt_mean_hasSum m p hm1 hcrit)
  have hmajor := ((survival_hasSum p).mul_left ((m : ℝ) ^ K)).add
    (hmean.div_const ((K : ℝ) + 1))
  rw [positiveTiltMass_eq_tsum_succ m p hm1 hcrit]
  apply (Summable.tsum_le_tsum _
    ((summable_nat_add_iff 1).2 (normalizedTilt_summable m p hm1 hcrit))
    hmajor.summable).trans_eq hmajor.tsum_eq
  intro k
  have hden : 0 < (K : ℝ) + 1 := by positivity
  have hp := p.nonneg (k + 1)
  have hpow : 0 ≤ (m : ℝ) ^ K := by positivity
  by_cases hk : k + 1 ≤ K
  · have hqle : normalizedTilt m p (k + 1) ≤ (m : ℝ) ^ K * p (k + 1) := by
      calc
        normalizedTilt m p (k + 1) ≤ (m : ℝ) ^ (k + 1) * p (k + 1) := by
          exact div_le_self (mul_nonneg (by positivity) hp) hG
        _ ≤ (m : ℝ) ^ K * p (k + 1) := by
          exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by exact_mod_cast hm1) hk) hp
    exact hqle.trans (le_add_of_nonneg_right (div_nonneg (mul_nonneg (by positivity)
      (hq (k + 1))) hden.le))
  · have hk' : (K : ℝ) + 1 ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : K + 1 ≤ k + 1)
    have htail : normalizedTilt m p (k + 1) ≤
        ((k + 1 : ℕ) : ℝ) * normalizedTilt m p (k + 1) / ((K : ℝ) + 1) := by
      apply (le_div_iff₀ hden).2
      nlinarith [hq (k + 1)]
    exact htail.trans (le_add_of_nonneg_left (mul_nonneg hpow hp))

/-- Vanishing survival forces the normalized positive tilted mass to vanish. -/
theorem positiveTiltMass_tendsto_zero_of_survival
    (m : ℕ) (p : ℕ → ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : ∀ n, Critical m (p n))
    (hs : Tendsto (fun n ↦ survival (p n)) atTop (𝓝 0)) :
    Tendsto (fun n ↦ positiveTiltMass m (p n)) atTop (𝓝 0) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    exact Filter.Eventually.of_forall fun n ↦
      ha.trans_le (positiveTiltMass_nonneg m (p n) (by omega) (hcrit n))
  · intro b hb
    have hlim : Tendsto (fun K : ℕ ↦ (1 / ((m : ℝ) - 1)) / ((K : ℝ) + 1))
        atTop (𝓝 0) := by
      simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using
        (tendsto_const_div_atTop_nhds_zero_nat (1 / ((m : ℝ) - 1))).comp
          (tendsto_add_atTop_nat 1)
    obtain ⟨K, hK⟩ := (hlim.eventually (gt_mem_nhds (half_pos hb))).exists
    have hscaled : Tendsto (fun n ↦ (m : ℝ) ^ K * survival (p n)) atTop (𝓝 0) := by
      simpa using hs.const_mul ((m : ℝ) ^ K)
    filter_upwards [hscaled.eventually (gt_mem_nhds (half_pos hb))] with n hn
    have h := positiveTiltMass_le_survival_cutoff m (p n) hm (hcrit n) K
    linarith

/-- The partition tends to one when survival vanishes, under criticality alone. -/
theorem partition_tendsto_one_of_survival
    (m : ℕ) (p : ℕ → ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : ∀ n, Critical m (p n))
    (hs : Tendsto (fun n ↦ survival (p n)) atTop (𝓝 0)) :
    Tendsto (fun n ↦ tiltedPartition m (p n)) atTop (𝓝 1) := by
  have htheta := positiveTiltMass_tendsto_zero_of_survival m p hm hcrit hs
  have hzero : Tendsto (fun n ↦ (p n) 0) atTop (𝓝 1) := by
    simpa only [survival_eq_one_sub_zero, sub_sub_cancel, sub_zero] using
      (tendsto_const_nhds (x := (1 : ℝ))).sub hs
  have hden : Tendsto (fun n ↦ 1 - positiveTiltMass m (p n)) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub htheta
  have heq : ∀ n, tiltedPartition m (p n) * (1 - positiveTiltMass m (p n)) = (p n) 0 := by
    intro n
    have hG := tiltedPartition_pos_of_critical m (p n) (by omega) (hcrit n)
    simp only [positiveTiltMass, sub_sub_cancel, zeroTilt_eq]
    field_simp
  have hdenne : ∀ᶠ n in atTop, 1 - positiveTiltMass m (p n) ≠ 0 :=
    hden.eventually_ne (by norm_num)
  have hquot := hzero.div hden (by norm_num : (1 : ℝ) ≠ 0)
  apply Tendsto.congr' _ (by simpa using hquot)
  filter_upwards [hdenne] with n hn
  exact (eq_div_iff hn).2 (heq n) |>.symm

/-- The scalar recursion map for the excess. -/
def excessRecursionMap (m : ℕ) (p x : ℝ) : ℝ :=
  ((1 + x) ^ m + ((m : ℝ) - 1) * (1 - p) ^ m) / (m : ℝ) - 1

/-- The scalar recursion, with no higher-moment assumption. -/
theorem excess_orbit_recursionMap
    (m : ℕ) (p : ProbabilityMass) (hm : 2 ≤ m) (hcrit : Critical m p) (n : ℕ) :
    excess m (orbit m p (n + 1)) =
      excessRecursionMap m (survival (orbit m p n)) (excess m (orbit m p n)) := by
  have h := excess_orbit_decrement m p (by omega) hcrit n
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  dsimp [excessRecursionMap]
  apply (eq_sub_iff_add_eq).2
  apply (eq_div_iff hm0).2
  simp only [orbit_succ] at h
  nlinarith

/-- Expansiveness of powers to the right of one. -/
theorem one_add_pow_sub_lower (m : ℕ) (x y : ℝ) (hx : 0 ≤ x) (hxy : x ≤ y) :
    (m : ℝ) * (y - x) ≤ (1 + y) ^ m - (1 + x) ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hy : 0 ≤ y := hx.trans hxy
    have hpow := one_le_pow₀ (show (1 : ℝ) ≤ 1 + x by linarith) (n := m)
    have hd : 0 ≤ (1 + y) ^ m - (1 + x) ^ m :=
      sub_nonneg.mpr (pow_le_pow_left₀ (by linarith) (by linarith) m)
    simp only [pow_succ, Nat.cast_succ]
    nlinarith [mul_nonneg hy hd, mul_nonneg (sub_nonneg.mpr hxy) (sub_nonneg.mpr hpow)]

/-- The scalar recursion expands nonnegative differences by at least one. -/
theorem excessRecursionMap_sub_ge
    (m : ℕ) (p x y : ℝ) (hm : 2 ≤ m) (hx : 0 ≤ x) (hxy : x ≤ y) :
    y - x ≤ excessRecursionMap m p y - excessRecursionMap m p x := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have h := one_add_pow_sub_lower m x y hx hxy
  dsimp [excessRecursionMap]
  rw [sub_sub_sub_cancel_right, ← sub_div]
  apply (le_div_iff₀ hmpos).2
  nlinarith


/-- A sequence tending to zero cannot stay above zero and strictly increase thereafter. -/
theorem negative_of_nonnegative_strict_growth
    (d : ℕ → ℝ) (N : ℕ) (hlim : Tendsto d atTop (𝓝 0))
    (hstep : ∀ n, N ≤ n → 0 ≤ d n → d n < d (n + 1)) :
    ∀ n, N ≤ n → d n < 0 := by
  intro n hn
  by_contra hneg
  have hnonneg : 0 ≤ d n := le_of_not_gt hneg
  have hpos : 0 < d (n + 1) := lt_of_le_of_lt hnonneg (hstep n hn hnonneg)
  have htail : ∀ k, n + 1 ≤ k → d (n + 1) ≤ d k := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => exact le_rfl
    | succ k hk ih =>
      exact ih.trans (hstep k (by omega) (hpos.le.trans ih)).le
  have hle : d (n + 1) ≤ 0 := ge_of_tendsto hlim
    (Filter.eventually_atTop.2 ⟨n + 1, htail⟩)
  linarith

/-- Limit of the reciprocal barrier on the first-order scale. -/
theorem nat_mul_reciprocal_barrier_tendsto (b : ℝ) :
    Tendsto (fun n : ℕ ↦ (n : ℝ) * (b / (n : ℝ))) atTop (𝓝 b) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  field_simp

/-- Exact second-order asymptotics of the reciprocal-barrier defect. -/
theorem excessRecursionMap_barrier_tendsto
    (m : ℕ) (p : ℕ → ℝ) (hm : 2 ≤ m) (b : ℝ)
    (hs : Tendsto (fun n : ℕ ↦ (n : ℝ) ^ 2 * p n) atTop
      (𝓝 (4 / ((m : ℝ) - 1) ^ 2))) :
    Tendsto (fun n : ℕ ↦ (n : ℝ) ^ 2 *
      (excessRecursionMap m (p n) (b / (n : ℝ)) - b / ((n : ℝ) + 1)))
      atTop (𝓝 (((m : ℝ) - 1) / 2 * b ^ 2 + b - 4 / ((m : ℝ) - 1))) := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  have hfactor : (m : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  have he := natSquare_mul_excessPowerRemainder_tendsto m
    (fun n : ℕ ↦ b / (n : ℝ)) b (nat_mul_reciprocal_barrier_tendsto b)
  have hp := natSquare_mul_survivalPower_tendsto m p _ hs
  have hr : Tendsto (fun n : ℕ ↦ b * ((n : ℝ) / ((n : ℝ) + 1))) atTop (𝓝 b) := by
    simpa using (tendsto_natCast_div_add_atTop (1 : ℝ)).const_mul b
  have h := ((he.sub (hp.const_mul ((m : ℝ) - 1))).div_const (m : ℝ)).add hr
  have hchoose : (m.choose 2 : ℝ) = (m : ℝ) * ((m : ℝ) - 1) / 2 := by
    rw [Nat.cast_choose_two]
  have hvalue : ((m.choose 2 : ℝ) * b ^ 2 -
      ((m : ℝ) - 1) * ((m : ℝ) * (4 / ((m : ℝ) - 1) ^ 2))) / (m : ℝ) + b =
      ((m : ℝ) - 1) / 2 * b ^ 2 + b - 4 / ((m : ℝ) - 1) := by
    rw [hchoose]
    field_simp
    <;> ring
  rw [hvalue] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hnp : (n : ℝ) + 1 ≠ 0 := by positivity
  dsimp [excessRecursionMap]
  field_simp
  <;> ring

/-- The polynomial controlling the barrier defect factors at its positive root. -/
theorem survivalBarrierPolynomial_factor (a b : ℝ) (ha : a ≠ 0) :
    a / 2 * b ^ 2 + b - 4 / a = (a * b - 2) * (b / 2 + 2 / a) := by
  field_simp
  <;> ring

/-- The survival asymptotic forces the excess asymptotic, with no third moment. -/
theorem excess_tendsto_of_survival_asymptotic
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m) (hcrit : Critical m p₀)
    (hs : Tendsto (fun n : ℕ ↦ (n : ℝ) ^ 2 * survival (orbit m p₀ n)) atTop
      (𝓝 (4 / ((m : ℝ) - 1) ^ 2))) :
    Tendsto (fun n : ℕ ↦ (n : ℝ) * excess m (orbit m p₀ n)) atTop
      (𝓝 (2 / ((m : ℝ) - 1))) := by
  let e : ℕ → ℝ := fun n ↦ excess m (orbit m p₀ n)
  let a : ℝ := (m : ℝ) - 1
  have ha : 0 < a := by dsimp [a]; exact_mod_cast (by omega : 0 < (m : ℤ) - 1)
  have he0 : Tendsto e atTop (𝓝 0) := by
    have hpart := partition_tendsto_one_of_survival m (orbit m p₀) hm
      (orbit_critical m p₀ (by omega) hcrit)
      (tendsto_zero_of_natSquare_mul_tendsto _ _ hs)
    simpa [e, excess] using hpart.sub_const 1
  have henonneg : ∀ n, 0 ≤ e n := fun n ↦
    excess_nonneg m _ (by omega) (orbit_critical m p₀ (by omega) hcrit n).1
  have hrec := excess_orbit_recursionMap m p₀ hm hcrit
  have hupper : ∀ b : ℝ, 2 / a < b → ∀ᶠ n in atTop, e n < b / (n : ℝ) := by
    intro b hb
    have hbpos : 0 < b := (div_pos (by norm_num) ha).trans hb
    have hpoly : 0 < a / 2 * b ^ 2 + b - 4 / a := by
      rw [survivalBarrierPolynomial_factor a b ha.ne']
      apply mul_pos
      · have := (div_lt_iff₀ ha).1 hb
        nlinarith
      · positivity
    have hlim := excessRecursionMap_barrier_tendsto m
      (fun n ↦ survival (orbit m p₀ n)) hm b hs
    have hsign : ∀ᶠ n in atTop,
        0 < excessRecursionMap m (survival (orbit m p₀ n)) (b / (n : ℝ)) -
          b / ((n : ℝ) + 1) := by
      filter_upwards [hlim.eventually (lt_mem_nhds hpoly)] with n hn
      exact pos_of_mul_pos_right hn (sq_nonneg (n : ℝ))
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hsign
    have hdlim : Tendsto (fun n : ℕ ↦ e n - b / (n : ℝ)) atTop (𝓝 0) := by
      simpa using he0.sub (tendsto_const_div_atTop_nhds_zero_nat b)
    have hneg := negative_of_nonnegative_strict_growth
      (fun n : ℕ ↦ e n - b / (n : ℝ)) N hdlim (by
        intro n hn hd
        have hx : 0 ≤ b / (n : ℝ) := div_nonneg hbpos.le (Nat.cast_nonneg n)
        have hg := excessRecursionMap_sub_ge m (survival (orbit m p₀ n))
          (b / (n : ℝ)) (e n) hm hx (by linarith)
        have hs' := hN n hn
        have hr := hrec n
        change e (n + 1) = excessRecursionMap m (survival (orbit m p₀ n)) (e n) at hr
        dsimp only
        rw [hr]
        push_cast
        linarith)
    exact Filter.eventually_atTop.2 ⟨N, fun n hn ↦ sub_neg.mp (hneg n hn)⟩
  have hlower : ∀ b : ℝ, 0 < b → b < 2 / a →
      ∀ᶠ (n : ℕ) in atTop, b / (n : ℝ) < e n := by
    intro b hb hbroot
    have hpoly : a / 2 * b ^ 2 + b - 4 / a < 0 := by
      rw [survivalBarrierPolynomial_factor a b ha.ne']
      apply mul_neg_of_neg_of_pos
      · have := (lt_div_iff₀ ha).1 hbroot
        nlinarith
      · positivity
    have hlim := excessRecursionMap_barrier_tendsto m
      (fun n ↦ survival (orbit m p₀ n)) hm b hs
    have hsign : ∀ᶠ n in atTop,
        excessRecursionMap m (survival (orbit m p₀ n)) (b / (n : ℝ)) -
          b / ((n : ℝ) + 1) < 0 := by
      filter_upwards [hlim.eventually (gt_mem_nhds hpoly)] with n hn
      exact neg_of_mul_neg_right hn (sq_nonneg (n : ℝ))
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hsign
    have hdlim : Tendsto (fun n : ℕ ↦ b / (n : ℝ) - e n) atTop (𝓝 0) := by
      simpa using (tendsto_const_div_atTop_nhds_zero_nat b).sub he0
    have hneg := negative_of_nonnegative_strict_growth
      (fun n : ℕ ↦ b / (n : ℝ) - e n) N hdlim (by
        intro n hn hd
        have hg := excessRecursionMap_sub_ge m (survival (orbit m p₀ n))
          (e n) (b / (n : ℝ)) hm (henonneg n) (by linarith)
        have hs' := hN n hn
        have hr := hrec n
        change e (n + 1) = excessRecursionMap m (survival (orbit m p₀ n)) (e n) at hr
        dsimp only
        rw [hr]
        push_cast
        linarith)
    exact Filter.eventually_atTop.2 ⟨N, fun n hn ↦ sub_neg.mp (hneg n hn)⟩
  apply tendsto_order.2
  constructor
  · intro c hc
    obtain ⟨b, hb1, hb2⟩ := exists_between
      (show max c 0 < 2 / a from max_lt hc (div_pos (by norm_num) ha))
    have hb : 0 < b := (le_max_right c 0).trans_lt hb1
    have hcb : c < b := (le_max_left c 0).trans_lt hb1
    filter_upwards [hlower b hb hb2, eventually_ge_atTop (1 : ℕ)] with n hn hn1
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have h := (div_lt_iff₀ hnpos).1 hn
    change c < (n : ℝ) * e n
    nlinarith
  · intro c hc
    filter_upwards [hupper c hc, eventually_ge_atTop (1 : ℕ)] with n hn hn1
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have h := (lt_div_iff₀ hnpos).1 hn
    change (n : ℝ) * e n < c
    nlinarith

/-- Lemma A.2: survival asymptotics imply logarithmic product exponent two. -/
theorem criticalProduct_log_limit_of_survival
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m) (hcrit : Critical m p₀)
    (hs : Tendsto (fun n : ℕ ↦ (n : ℝ) ^ 2 * survival (orbit m p₀ n)) atTop
      (𝓝 (4 / ((m : ℝ) - 1) ^ 2))) :
    Tendsto (fun n : ℕ ↦ Real.log (criticalProduct m p₀ n) / Real.log (n : ℝ))
      atTop (𝓝 2) :=
  orbit_criticalProduct_log_div_log_tendsto_two m p₀ hm hcrit
    (excess_tendsto_of_survival_asymptotic m p₀ hm hcrit hs)

end
end DerridaRetaux
