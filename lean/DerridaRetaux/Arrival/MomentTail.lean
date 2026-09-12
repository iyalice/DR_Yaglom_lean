import DerridaRetaux.Analysis.ConvolutionNorms
import DerridaRetaux.Arrival.InitialTail
import DerridaRetaux.Model.TransportLimit
import DerridaRetaux.Prelim.WeightedMassOrbit
import Mathlib.Tactic

set_option autoImplicit false

open scoped BigOperators

namespace DerridaRetaux

noncomputable section

/-!
# Quantitative arrival moments and tails

This file proves the two estimates following `lem:arrival`.  The exponent
`3 - r` is represented by an integer power, so the statement retains the
decay asserted by the source when `r > 3`.
-/

/-- The cubic moment used for the coefficients of `F_s ^ r`. -/
def shiftedCubicMoment (r : ℕ) (a : Seq) : ℝ :=
  ∑' k : ℕ, ((k + r : ℕ) : ℝ) ^ 3 * a k

/-- The coefficient sum `F_s(1)` in the source arrival coordinates. -/
def arrivalValueAtOne (m : ℕ) (p₀ : ProbabilityMass) (s : ℕ) : ℝ :=
  ∑' N : ℕ, arrivalCoeff m p₀ s N

/-- At the source scale `L = s + 1`, shifting an index to the right by `s`
costs at most the absolute constant eight in the cubic weight. -/
theorem cubicWeight_add_generation_le
    (s j : ℕ) :
    cubicWeight ((s + 1 : ℕ) : ℝ) (j + s) ≤
      8 * cubicWeight ((s + 1 : ℕ) : ℝ) j := by
  let L : ℝ := ((s + 1 : ℕ) : ℝ)
  have hL : 1 ≤ L := by
    dsimp [L]
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le s)
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hsDiv : (s : ℝ) / L ≤ 1 := by
    apply (div_le_one hLpos).2
    dsimp [L]
    exact_mod_cast Nat.le_succ s
  have hsWeight : cubicWeight L s ≤ 8 := by
    unfold cubicWeight
    calc
      (1 + (s : ℝ) / L) ^ 3 ≤ (2 : ℝ) ^ 3 := by
        gcongr
        linarith
      _ = 8 := by norm_num
  calc
    cubicWeight ((s + 1 : ℕ) : ℝ) (j + s) ≤
        cubicWeight ((s + 1 : ℕ) : ℝ) j *
          cubicWeight ((s + 1 : ℕ) : ℝ) s :=
      cubicWeight_add_le_mul L hL j s
    _ ≤ cubicWeight ((s + 1 : ℕ) : ℝ) j * 8 :=
      mul_le_mul_of_nonneg_left hsWeight (cubicWeight_nonneg L hLpos j)
    _ = 8 * cubicWeight ((s + 1 : ℕ) : ℝ) j := by ring

/-- A nonnegative sequence with finite cubic weighted `l1` norm is summable,
and its total mass is bounded by that norm. -/
theorem tsum_le_weightedL1Three
    (L : ℝ) (hL : 1 ≤ L) (a : Seq) (ha : ∀ k : ℕ, 0 ≤ a k)
    (hweighted : Summable (weightedAbs L a)) :
    Summable a ∧ (∑' k : ℕ, a k) ≤ weightedL1Three L a := by
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hpoint : ∀ k : ℕ, a k ≤ weightedAbs L a k := by
    intro k
    rw [weightedAbs, abs_of_nonneg (ha k)]
    have hone : 1 ≤ cubicWeight L k := by
      unfold cubicWeight
      have hk : 0 ≤ (k : ℝ) / L := div_nonneg (Nat.cast_nonneg k) hLpos.le
      nlinarith [sq_nonneg (1 + (k : ℝ) / L)]
    calc
      a k = 1 * a k := by ring
      _ ≤ cubicWeight L k * a k := mul_le_mul_of_nonneg_right hone (ha k)
  have hsum : Summable a :=
    Summable.of_nonneg_of_le ha hpoint hweighted
  refine ⟨hsum, ?_⟩
  rw [weightedL1Three_eq_tsum_weightedAbs]
  exact Summable.tsum_le_tsum hpoint hsum hweighted

/-- A cubic weighted bound on a nonnegative sequence gives the shifted cubic
moment bound for every positive convolution power. -/
theorem shiftedCubicMoment_convPow_summable_and_le
    (L A : ℝ) (hL : 1 ≤ L) (a : Seq)
    (ha : ∀ k : ℕ, 0 ≤ a k) (hweighted : Summable (weightedAbs L a))
    (hnorm : weightedL1Three L a ≤ A / L) (r : ℕ) (hr : 1 ≤ r) :
    Summable
        (fun k : ℕ ↦ ((k + r : ℕ) : ℝ) ^ 3 * convPow r a k) ∧
      shiftedCubicMoment r (convPow r a) ≤
        (r : ℝ) ^ 3 * A ^ r * (L ^ 3 / L ^ r) := by
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hrReal : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hpowNonneg : ∀ k : ℕ, 0 ≤ convPow r a k :=
    convPow_nonneg r a ha
  have hpowWeighted : Summable (weightedAbs L (convPow r a)) :=
    weightedAbs_convPow_summable L hL a hweighted r
  let D : ℝ := (r : ℝ) ^ 3 * L ^ 3
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hpoint : ∀ k : ℕ,
      ((k + r : ℕ) : ℝ) ^ 3 * convPow r a k ≤
        D * weightedAbs L (convPow r a) k := by
    intro k
    have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
    have hbase :
        ((k + r : ℕ) : ℝ) ≤
          (r : ℝ) * L * (1 + (k : ℝ) / L) := by
      push_cast
      have hrk : (k : ℝ) ≤ (r : ℝ) * (k : ℝ) := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hrReal) hk]
      have hrL : (r : ℝ) ≤ (r : ℝ) * L := by
        exact le_mul_of_one_le_right (Nat.cast_nonneg r) hL
      calc
        (k : ℝ) + (r : ℝ) ≤
            (r : ℝ) * (k : ℝ) + (r : ℝ) := add_le_add hrk le_rfl
        _ ≤ (r : ℝ) * (k : ℝ) + (r : ℝ) * L :=
          add_le_add_left hrL _
        _ = (r : ℝ) * L * (1 + (k : ℝ) / L) := by
          field_simp
          ring
    have hcube :
        ((k + r : ℕ) : ℝ) ^ 3 ≤
          D * cubicWeight L k := by
      unfold cubicWeight
      dsimp [D]
      calc
        ((k + r : ℕ) : ℝ) ^ 3 ≤
            ((r : ℝ) * L * (1 + (k : ℝ) / L)) ^ 3 := by
          exact pow_le_pow_left₀ (Nat.cast_nonneg _) hbase 3
        _ = (r : ℝ) ^ 3 * L ^ 3 * (1 + (k : ℝ) / L) ^ 3 := by ring
    rw [weightedAbs, abs_of_nonneg (hpowNonneg k)]
    calc
      ((k + r : ℕ) : ℝ) ^ 3 * convPow r a k ≤
          (D * cubicWeight L k) * convPow r a k :=
        mul_le_mul_of_nonneg_right hcube (hpowNonneg k)
      _ = D * (cubicWeight L k * convPow r a k) := by ring
  have hmoment :
      Summable (fun k : ℕ ↦ ((k + r : ℕ) : ℝ) ^ 3 * convPow r a k) := by
    apply Summable.of_nonneg_of_le
      (fun k ↦ mul_nonneg (pow_nonneg (Nat.cast_nonneg _) 3) (hpowNonneg k))
      hpoint
    exact hpowWeighted.mul_left D
  refine ⟨hmoment, ?_⟩
  rw [shiftedCubicMoment]
  calc
    (∑' k : ℕ, ((k + r : ℕ) : ℝ) ^ 3 * convPow r a k) ≤
        ∑' k : ℕ, D * weightedAbs L (convPow r a) k :=
      Summable.tsum_le_tsum hpoint hmoment (hpowWeighted.mul_left D)
    _ = D * weightedL1Three L (convPow r a) := by
      rw [weightedL1Three_eq_tsum_weightedAbs]
      exact hpowWeighted.tsum_const_smul D
    _ ≤ D * weightedL1Three L a ^ r := by
      exact mul_le_mul_of_nonneg_left
        (weightedL1Three_convPow_le_pow L hL a hweighted r) hD
    _ ≤ D * (A / L) ^ r := by
      have hnormNonneg : 0 ≤ weightedL1Three L a :=
        weightedL1Three_nonneg L hLpos a
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hnormNonneg hnorm r) hD
    _ = (r : ℝ) ^ 3 * A ^ r * (L ^ 3 / L ^ r) := by
      dsimp [D]
      rw [div_pow]
      ring

/-- The elementary cubic Markov inequality for coefficient tails. -/
theorem coefficientTail_le_shiftedCubicMoment_div
    (r K : ℕ) (hr : 1 ≤ r) (hK : 1 ≤ K) (a : Seq)
    (ha : ∀ k : ℕ, 0 ≤ a k)
    (hmoment : Summable (fun k : ℕ ↦ ((k + r : ℕ) : ℝ) ^ 3 * a k)) :
    coefficientTail a K ≤ shiftedCubicMoment r a / (K : ℝ) ^ 3 := by
  have hsum : Summable a := by
    apply Summable.of_nonneg_of_le ha
      (fun k ↦ ?_)
      hmoment
    have hone : (1 : ℝ) ≤ ((k + r : ℕ) : ℝ) ^ 3 := by
      have hkr : (1 : ℝ) ≤ ((k + r : ℕ) : ℝ) := by exact_mod_cast (by omega)
      nlinarith [sq_nonneg (((k + r : ℕ) : ℝ))]
    calc
      a k = 1 * a k := by ring
      _ ≤ ((k + r : ℕ) : ℝ) ^ 3 * a k :=
        mul_le_mul_of_nonneg_right hone (ha k)
  have htail : Summable (fun j : ℕ ↦ a (j + K)) :=
    (summable_nat_add_iff K).2 hsum
  have htailMoment :
      Summable (fun j : ℕ ↦ ((j + K + r : ℕ) : ℝ) ^ 3 * a (j + K)) :=
    (summable_nat_add_iff K).2 hmoment
  have hKpos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hK)
  apply (le_div_iff₀ (pow_pos hKpos 3)).2
  rw [coefficientTail, shiftedCubicMoment, mul_comm]
  rw [← htail.tsum_mul_left]
  calc
    (∑' j : ℕ, (K : ℝ) ^ 3 * a (j + K)) ≤
        ∑' j : ℕ, ((j + K + r : ℕ) : ℝ) ^ 3 * a (j + K) := by
      apply Summable.tsum_le_tsum _ (htail.mul_left ((K : ℝ) ^ 3)) htailMoment
      intro j
      exact mul_le_mul_of_nonneg_right (by gcongr; exact_mod_cast (show K ≤ j + K + r by omega))
        (ha (j + K))
    _ ≤ ∑' k : ℕ, ((k + r : ℕ) : ℝ) ^ 3 * a k := by
      rw [← hmoment.sum_add_tsum_nat_add K]
      exact le_add_of_nonneg_left <| Finset.sum_nonneg fun k _ ↦
        mul_nonneg (pow_nonneg (Nat.cast_nonneg _) 3) (ha k)

/-- Pointwise comparison of the shifted arrival coefficients with the positive
tilted density.  The factor eight is the generation-shift weight cost. -/
theorem weightedAbs_arrivalCoeff_add_le
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m) (hcrit : Critical m p₀)
    (hnotBinaryFixedPoint : ¬ (m = 2 ∧ p₀ = diracMass 1))
    (B : ℝ) (hB : 0 ≤ B)
    (hBinv : ∀ s : ℕ, (arrivalProduct m p₀ s)⁻¹ ≤ B)
    (s j : ℕ) :
    weightedAbs ((s + 1 : ℕ) : ℝ) (arrivalCoeff m p₀ s) (j + s) ≤
      8 * B * weightedAbs ((s + 1 : ℕ) : ℝ)
        (positiveTiltedDensity m (orbit m p₀ s)) j := by
  let L : ℝ := ((s + 1 : ℕ) : ℝ)
  let q : Seq := normalizedTilt m (orbit m p₀ s)
  let rhoS : Seq := positiveTiltedDensity m (orbit m p₀ s)
  have hscrit := orbit_critical m p₀ (by omega) hcrit s
  have hqNonneg : 0 ≤ q (j + 1) :=
    normalizedTilt_nonneg m (orbit m p₀ s) (by omega) hscrit (j + 1)
  have hrhoNonneg : 0 ≤ rhoS j :=
    positiveTiltedDensity_nonneg m (orbit m p₀ s) (by omega) hscrit j
  have hfactor : (1 : ℝ) ≤ (m : ℝ) - 1 := by
    have hmReal : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    linarith
  have hqRho : q (j + 1) ≤ rhoS j := by
    change q (j + 1) ≤ ((m : ℝ) - 1) * q (j + 1)
    calc
      q (j + 1) = 1 * q (j + 1) := by ring
      _ ≤ ((m : ℝ) - 1) * q (j + 1) :=
        mul_le_mul_of_nonneg_right hfactor hqNonneg
  have hCpos : 0 < arrivalProduct m p₀ s :=
    transportProduct_pos m p₀ hm hcrit hnotBinaryFixedPoint s
  have harrEq :
      arrivalCoeff m p₀ s (j + s) = q (j + 1) / arrivalProduct m p₀ s := by
    rw [arrivalCoeff_eq_of_le m p₀ s (j + s) (by omega)]
    congr 2
    omega
  have harrNonneg : 0 ≤ arrivalCoeff m p₀ s (j + s) :=
    arrivalCoeff_nonneg m p₀ hm hcrit hnotBinaryFixedPoint s (j + s)
  have harrLe : arrivalCoeff m p₀ s (j + s) ≤ B * rhoS j := by
    rw [harrEq, div_eq_inv_mul]
    calc
      (arrivalProduct m p₀ s)⁻¹ * q (j + 1) ≤
          (arrivalProduct m p₀ s)⁻¹ * rhoS j :=
        mul_le_mul_of_nonneg_left hqRho (inv_nonneg.mpr hCpos.le)
      _ ≤ B * rhoS j := mul_le_mul_of_nonneg_right (hBinv s) hrhoNonneg
  rw [weightedAbs, weightedAbs, abs_of_nonneg harrNonneg, abs_of_nonneg hrhoNonneg]
  calc
    cubicWeight L (j + s) * arrivalCoeff m p₀ s (j + s) ≤
        cubicWeight L (j + s) * (B * rhoS j) :=
      mul_le_mul_of_nonneg_left harrLe
        (cubicWeight_nonneg L (by dsimp [L]; positivity) (j + s))
    _ ≤ (8 * cubicWeight L j) * (B * rhoS j) :=
      mul_le_mul_of_nonneg_right (cubicWeight_add_generation_le s j)
        (mul_nonneg hB hrhoNonneg)
    _ = 8 * B * (cubicWeight L j * rhoS j) := by ring

/-- A weighted density bound and a uniform inverse transport-product bound
transfer to the arrival coefficients at the same source scale. -/
theorem weightedL1Three_arrivalCoeff_le
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m) (hcrit : Critical m p₀)
    (hnotBinaryFixedPoint : ¬ (m = 2 ∧ p₀ = diracMass 1))
    (B C : ℝ) (hB : 0 ≤ B)
    (hBinv : ∀ s : ℕ, (arrivalProduct m p₀ s)⁻¹ ≤ B)
    (s : ℕ)
    (hrhoSum : Summable
      (weightedAbs ((s + 1 : ℕ) : ℝ)
        (positiveTiltedDensity m (orbit m p₀ s))))
    (hrhoBound :
      weightedL1Three ((s + 1 : ℕ) : ℝ)
          (positiveTiltedDensity m (orbit m p₀ s)) ≤
        C / ((s + 1 : ℕ) : ℝ)) :
    Summable (weightedAbs ((s + 1 : ℕ) : ℝ) (arrivalCoeff m p₀ s)) ∧
      weightedL1Three ((s + 1 : ℕ) : ℝ) (arrivalCoeff m p₀ s) ≤
        (8 * B * C) / ((s + 1 : ℕ) : ℝ) := by
  let L : ℝ := ((s + 1 : ℕ) : ℝ)
  let a : Seq := arrivalCoeff m p₀ s
  let rhoS : Seq := positiveTiltedDensity m (orbit m p₀ s)
  let D : ℝ := 8 * B
  have hLpos : 0 < L := by dsimp [L]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hpoint : ∀ j : ℕ, weightedAbs L a (j + s) ≤ D * weightedAbs L rhoS j := by
    intro j
    exact weightedAbs_arrivalCoeff_add_le m p₀ hm hcrit hnotBinaryFixedPoint
      B hB hBinv s j
  have htail : Summable (fun j : ℕ ↦ weightedAbs L a (j + s)) := by
    apply Summable.of_nonneg_of_le
      (fun j ↦ weightedAbs_nonneg L hLpos a (j + s))
      hpoint
    exact hrhoSum.mul_left D
  have haWeighted : Summable (weightedAbs L a) :=
    (summable_nat_add_iff s).1 htail
  refine ⟨haWeighted, ?_⟩
  have hprefix : ∑ j ∈ Finset.range s, weightedAbs L a j = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    have hjs : j < s := Finset.mem_range.mp hj
    change weightedAbs L (arrivalCoeff m p₀ s) j = 0
    rw [weightedAbs, arrivalCoeff_eq_zero_of_lt m p₀ s j hjs, abs_zero, mul_zero]
  have hdecomp := haWeighted.sum_add_tsum_nat_add s
  rw [hprefix, zero_add] at hdecomp
  rw [weightedL1Three_eq_tsum_weightedAbs]
  calc
    (∑' j : ℕ, weightedAbs L a j) =
        ∑' j : ℕ, weightedAbs L a (j + s) := hdecomp.symm
    _ ≤ ∑' j : ℕ, D * weightedAbs L rhoS j :=
      Summable.tsum_le_tsum hpoint htail (hrhoSum.mul_left D)
    _ = D * weightedL1Three L rhoS := by
      rw [weightedL1Three_eq_tsum_weightedAbs]
      exact hrhoSum.tsum_const_smul D
    _ ≤ D * (C / L) := mul_le_mul_of_nonneg_left hrhoBound hD
    _ = (8 * B * C) / L := by dsimp [D]; ring

/-- Division by a positive natural power is the integer power occurring in
the source exponent `3 - r`. -/
theorem cube_div_pow_eq_zpow_sub (L : ℝ) (hL : 0 < L) (r : ℕ) :
    L ^ 3 / L ^ r = L ^ ((3 : ℤ) - (r : ℤ)) := by
  exact (zpow_natCast_sub_natCast₀ hL.ne' 3 r).symm

/-- Complete quantitative package for `U21`, equivalently `eq:Fmoment` and
`eq:Ftail`.  The upper range `r ≤ m²` is retained verbatim, although the
deterministic weighted-Young argument proves the estimate for every `r ≥ 1`.

`hExcess` and `hProduct` are precisely the frozen H1a and H1b fact values; no
human-input module is imported here. -/
theorem arrivalMomentTail_bounds
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p₀) (hthird : TiltSummable m 3 p₀)
    (hnonconstant : ¬ IsDirac p₀)
    (hExcess : CDHLSExcessFact m p₀ hm hcrit hthird hnonconstant)
    (hProduct : CDHLSProductFact m p₀ hm hcrit hnonconstant) :
    ∃ C : ℝ, 0 < C ∧
      (∀ s : ℕ,
        arrivalValueAtOne m p₀ s ≤ C / ((s + 1 : ℕ) : ℝ)) ∧
      ∀ r : ℕ, 1 ≤ r → r ≤ m ^ 2 →
        (∀ s : ℕ,
          shiftedCubicMoment r (convPow r (arrivalCoeff m p₀ s)) ≤
            (r : ℝ) ^ 3 * C ^ r *
              (((s + 1 : ℕ) : ℝ) ^ ((3 : ℤ) - (r : ℤ)))) ∧
        ∀ s K : ℕ, 1 ≤ K →
          coefficientTail (convPow r (arrivalCoeff m p₀ s)) K ≤
            ((r : ℝ) ^ 3 * C ^ r *
              (((s + 1 : ℕ) : ℝ) ^ ((3 : ℤ) - (r : ℤ)))) /
                (K : ℝ) ^ 3 := by
  have hnotBinaryFixedPoint : ¬ (m = 2 ∧ p₀ = diracMass 1) := by
    rintro ⟨_, hp₀⟩
    exact hnonconstant ⟨1, hp₀⟩
  rcases weightedL1Three_orbit_bound
      m p₀ hm hcrit hthird hnonconstant hExcess hProduct with ⟨A, hA, hrhoBound⟩
  have hdefectOrbit := orbitTransportDefect_summable
    m p₀ hm hcrit hthird hnonconstant hExcess
  have hdefect :
      Summable (fun n : ℕ ↦ 1 - transportCoeff m (orbit m p₀ n)) := by
    simpa only [orbitTransportDefect] using hdefectOrbit
  rcases transportProduct_inverse_uniform
      m p₀ hm hcrit hnotBinaryFixedPoint hdefect with ⟨B, hB, hBinvProduct⟩
  have hBinv : ∀ s : ℕ, (arrivalProduct m p₀ s)⁻¹ ≤ B := by
    simpa only [arrivalProduct] using hBinvProduct
  let C : ℝ := 8 * B * A
  have hC : 0 < C := by
    dsimp [C]
    positivity
  have hArrivalWeighted : ∀ s : ℕ,
      Summable (weightedAbs ((s + 1 : ℕ) : ℝ) (arrivalCoeff m p₀ s)) ∧
        weightedL1Three ((s + 1 : ℕ) : ℝ) (arrivalCoeff m p₀ s) ≤
          C / ((s + 1 : ℕ) : ℝ) := by
    intro s
    have hscrit := orbit_critical m p₀ (by omega) hcrit s
    have hsthird := orbit_tiltSummable_three m p₀ (by omega) hcrit hthird s
    have hrhoSum := weightedL1Three_positiveTiltedDensity_summable
      m (orbit m p₀ s) ((s + 1 : ℕ) : ℝ) (by omega) hscrit hsthird (by positivity)
    simpa only [C] using weightedL1Three_arrivalCoeff_le
      m p₀ hm hcrit hnotBinaryFixedPoint B A hB.le hBinv s hrhoSum (hrhoBound s)
  refine ⟨C, hC, ?_, ?_⟩
  · intro s
    have hL : (1 : ℝ) ≤ ((s + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le s)
    have harrNonneg := arrivalCoeff_nonneg
      m p₀ hm hcrit hnotBinaryFixedPoint s
    exact (tsum_le_weightedL1Three ((s + 1 : ℕ) : ℝ) hL
      (arrivalCoeff m p₀ s) harrNonneg (hArrivalWeighted s).1).2.trans
        (hArrivalWeighted s).2
  · intro r hr _hrUpper
    constructor
    · intro s
      have hL : (1 : ℝ) ≤ ((s + 1 : ℕ) : ℝ) := by
        exact_mod_cast Nat.succ_le_succ (Nat.zero_le s)
      have hbound := (shiftedCubicMoment_convPow_summable_and_le
        ((s + 1 : ℕ) : ℝ) C hL (arrivalCoeff m p₀ s)
        (arrivalCoeff_nonneg m p₀ hm hcrit hnotBinaryFixedPoint s)
        (hArrivalWeighted s).1 (hArrivalWeighted s).2 r hr).2
      rw [cube_div_pow_eq_zpow_sub ((s + 1 : ℕ) : ℝ) (by positivity) r] at hbound
      exact hbound
    · intro s K hK
      have hL : (1 : ℝ) ≤ ((s + 1 : ℕ) : ℝ) := by
        exact_mod_cast Nat.succ_le_succ (Nat.zero_le s)
      have hmomentPackage := shiftedCubicMoment_convPow_summable_and_le
        ((s + 1 : ℕ) : ℝ) C hL (arrivalCoeff m p₀ s)
        (arrivalCoeff_nonneg m p₀ hm hcrit hnotBinaryFixedPoint s)
        (hArrivalWeighted s).1 (hArrivalWeighted s).2 r hr
      have hmarkov := coefficientTail_le_shiftedCubicMoment_div r K hr hK
        (convPow r (arrivalCoeff m p₀ s))
        (convPow_nonneg r (arrivalCoeff m p₀ s)
          (arrivalCoeff_nonneg m p₀ hm hcrit hnotBinaryFixedPoint s))
        hmomentPackage.1
      have hmomentBound := hmomentPackage.2
      rw [cube_div_pow_eq_zpow_sub ((s + 1 : ℕ) : ℝ) (by positivity) r]
        at hmomentBound
      exact hmarkov.trans <| (div_le_div_iff_of_pos_right (by positivity : 0 < (K : ℝ) ^ 3)).2
        hmomentBound

end

end DerridaRetaux
