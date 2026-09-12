import DerridaRetaux.Analysis.OrbitConvolutionBounds
import DerridaRetaux.Analysis.SmoothingAlgebra
import Mathlib.Tactic

/-!
# Reusable weighted bounds for the smoothing remainder

This file supplies only deterministic norm bookkeeping.  Every coefficient estimate
and every orbit/convolution estimate used by a source-shaped bound remains an explicit
theorem parameter.  No conclusion here asserts the full smoothing proposition.
-/

set_option autoImplicit false

open scoped BigOperators

namespace DerridaRetaux

noncomputable section

/-- Weighted pointwise bounds add. -/
theorem weightedSupThree_add
    (L A B : ℝ) (hL : 0 < L) (f g : Seq)
    (hf : WeightedSupThreeLE L f A) (hg : WeightedSupThreeLE L g B) :
    WeightedSupThreeLE L (f + g) (A + B) := by
  intro j
  have hw := cubicWeight_nonneg L hL j
  calc
    cubicWeight L j * |(f + g) j| ≤
        cubicWeight L j * (|f j| + |g j|) := by
      exact mul_le_mul_of_nonneg_left (abs_add_le (f j) (g j)) hw
    _ = cubicWeight L j * |f j| + cubicWeight L j * |g j| := by ring
    _ ≤ A + B := add_le_add (hf j) (hg j)

/-- Weighted pointwise bounds scale by the absolute value of a scalar. -/
theorem weightedSupThree_smul
    (L A c : ℝ) (f : Seq) (hf : WeightedSupThreeLE L f A) :
    WeightedSupThreeLE L (c • f) (|c| * A) := by
  intro j
  calc
    cubicWeight L j * |(c • f) j| = |c| * (cubicWeight L j * |f j|) := by
      simp only [Pi.smul_apply, smul_eq_mul, abs_mul]
      ring
    _ ≤ |c| * A := mul_le_mul_of_nonneg_left (hf j) (abs_nonneg c)

/-- A finite sum of weighted pointwise bounds is bounded by the sum of its witnesses. -/
theorem weightedSupThree_finset_sum
    {I : Type*} (s : Finset I) (L : ℝ) (C : I → ℝ) (f : I → Seq)
    (hL : 0 < L) (hf : ∀ i ∈ s, WeightedSupThreeLE L (f i) (C i)) :
    WeightedSupThreeLE L (∑ i ∈ s, f i) (∑ i ∈ s, C i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [WeightedSupThreeLE, cubicWeight_nonneg L hL]
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi]
      exact weightedSupThree_add L (C i) (∑ k ∈ s, C k) hL (f i)
        (∑ k ∈ s, f k) (hf i (Finset.mem_insert_self i s))
        (ih fun k hk ↦ hf k (Finset.mem_insert_of_mem hk))

/-- Absolute weighted summands of a scalar multiple. -/
theorem weightedAbs_smul (L c : ℝ) (f : Seq) :
    weightedAbs L (c • f) = |c| • weightedAbs L f := by
  funext j
  simp only [weightedAbs, Pi.smul_apply, smul_eq_mul, abs_mul]
  ring

/-- Cubic weighted `l1` mass scales exactly by the scalar absolute value. -/
theorem weightedL1Three_smul (L c : ℝ) (f : Seq)
    (hf : Summable (weightedAbs L f)) :
    weightedL1Three L (c • f) = |c| * weightedL1Three L f := by
  rw [weightedL1Three_eq_tsum_weightedAbs, weightedAbs_smul,
    weightedL1Three_eq_tsum_weightedAbs]
  simpa only [smul_eq_mul] using hf.tsum_const_smul |c|

/-- Absolute weighted summands are subadditive. -/
theorem weightedAbs_add_le
    (L : ℝ) (hL : 0 < L) (f g : Seq) (j : ℕ) :
    weightedAbs L (f + g) j ≤ weightedAbs L f j + weightedAbs L g j := by
  have hw := cubicWeight_nonneg L hL j
  simp only [weightedAbs, Pi.add_apply]
  calc
    cubicWeight L j * |f j + g j| ≤ cubicWeight L j * (|f j| + |g j|) :=
      mul_le_mul_of_nonneg_left (abs_add_le _ _) hw
    _ = cubicWeight L j * |f j| + cubicWeight L j * |g j| := by ring

/-- Summability of absolute weighted terms is preserved by addition. -/
theorem weightedAbs_add_summable
    (L : ℝ) (hL : 0 < L) (f g : Seq)
    (hf : Summable (weightedAbs L f)) (hg : Summable (weightedAbs L g)) :
    Summable (weightedAbs L (f + g)) := by
  apply Summable.of_nonneg_of_le
    (f := fun j : ℕ ↦ weightedAbs L f j + weightedAbs L g j)
  · exact weightedAbs_nonneg L hL (f + g)
  · exact weightedAbs_add_le L hL f g
  · exact hf.add hg

/-- Cubic weighted `l1` mass is subadditive when both displayed masses are finite. -/
theorem weightedL1Three_add_le
    (L : ℝ) (hL : 0 < L) (f g : Seq)
    (hf : Summable (weightedAbs L f)) (hg : Summable (weightedAbs L g)) :
    weightedL1Three L (f + g) ≤
      weightedL1Three L f + weightedL1Three L g := by
  rw [weightedL1Three_eq_tsum_weightedAbs, weightedL1Three_eq_tsum_weightedAbs,
    weightedL1Three_eq_tsum_weightedAbs]
  calc
    (∑' j : ℕ, weightedAbs L (f + g) j) ≤
        ∑' j : ℕ, (weightedAbs L f j + weightedAbs L g j) :=
      Summable.tsum_le_tsum (weightedAbs_add_le L hL f g)
        (weightedAbs_add_summable L hL f g hf hg) (hf.add hg)
    _ = (∑' j : ℕ, weightedAbs L f j) + ∑' j : ℕ, weightedAbs L g j :=
      hf.tsum_add hg

/-- Summability of absolute weighted terms is preserved by a finite sum. -/
theorem weightedAbs_finset_sum_summable
    {I : Type*} (s : Finset I) (L : ℝ) (f : I → Seq) (hL : 0 < L)
    (hf : ∀ i ∈ s, Summable (weightedAbs L (f i))) :
    Summable (weightedAbs L (∑ i ∈ s, f i)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      have hzero : weightedAbs L (0 : Seq) = 0 := by
        funext j
        simp [weightedAbs]
      rw [Finset.sum_empty, hzero]
      exact summable_zero
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact weightedAbs_add_summable L hL (f i) (∑ k ∈ s, f k)
        (hf i (Finset.mem_insert_self i s))
        (ih fun k hk ↦ hf k (Finset.mem_insert_of_mem hk))

/-- Finite sums satisfy the corresponding weighted `l1` triangle inequality. -/
theorem weightedL1Three_finset_sum_le
    {I : Type*} (s : Finset I) (L : ℝ) (f : I → Seq) (hL : 0 < L)
    (hf : ∀ i ∈ s, Summable (weightedAbs L (f i))) :
    weightedL1Three L (∑ i ∈ s, f i) ≤
      ∑ i ∈ s, weightedL1Three L (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [weightedL1Three]
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi]
      exact (weightedL1Three_add_le L hL (f i) (∑ k ∈ s, f k)
        (hf i (Finset.mem_insert_self i s))
        (weightedAbs_finset_sum_summable s L f hL
          fun k hk ↦ hf k (Finset.mem_insert_of_mem hk))).trans
        (add_le_add_left (ih fun k hk ↦ hf k (Finset.mem_insert_of_mem hk)) _)

/-- Iterated right shift agrees with the existing integer-shift implementation. -/
theorem shiftRightPow_eq_shiftByInt (d : ℕ) (f : Seq) :
    shiftRightPow d f = shiftByInt (d : ℤ) f := by
  funext n
  induction d generalizing f n with
  | zero => simp
  | succ d ih =>
      rw [shiftRightPow_succ, ih]
      by_cases hnlt : n < d
      · rw [shiftByInt_eq_zero_of_lt d n (shiftRight f) hnlt,
          shiftByInt_eq_zero_of_lt (d + 1) n f (by omega)]
      by_cases hneq : n = d
      · subst n
        rw [shiftByInt_of_le d d (shiftRight f) (by omega),
          shiftByInt_eq_zero_of_lt (d + 1) d f (by omega)]
        simp
      · have hsucc : d + 1 ≤ n := by omega
        rw [shiftByInt_of_le d n (shiftRight f) (by omega),
          shiftByInt_of_le (d + 1) n f hsucc]
        have hpos : 0 < n - d := by omega
        obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n - d ≠ 0)
        rw [hk, shiftRight_succ]
        congr 1
        omega

/-- Source bound for a fixed right shift in the weighted pointwise predicate. -/
theorem weightedSupThree_shiftRightPow
    (L C : ℝ) (d : ℕ) (hL : 1 ≤ L) (hC : 0 ≤ C) (f : Seq)
    (hf : WeightedSupThreeLE L f C) :
    WeightedSupThreeLE L (shiftRightPow d f) (((1 + d : ℕ) : ℝ) ^ 3 * C) := by
  rw [shiftRightPow_eq_shiftByInt]
  exact weightedSupThree_shiftByInt_nat L C d hL hC f hf

/-- The weight increase under a right shift is at most the source factor `(1+d)^3`. -/
theorem cubicWeight_add_le_shiftFactor
    (L : ℝ) (d j : ℕ) (hL : 1 ≤ L) :
    cubicWeight L (j + d) ≤ ((1 + d : ℕ) : ℝ) ^ 3 * cubicWeight L j := by
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hddiv : (d : ℝ) / L ≤ (d : ℝ) := by
    apply (div_le_iff₀ hLpos).2
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hL (Nat.cast_nonneg d)
  have hdweight : cubicWeight L d ≤ ((1 + d : ℕ) : ℝ) ^ 3 := by
    unfold cubicWeight
    push_cast
    exact pow_le_pow_left₀ (by positivity) (by linarith) 3
  calc
    cubicWeight L (j + d) ≤ cubicWeight L j * cubicWeight L d :=
      cubicWeight_add_le_mul L hL j d
    _ ≤ cubicWeight L j * ((1 + d : ℕ) : ℝ) ^ 3 :=
      mul_le_mul_of_nonneg_left hdweight (cubicWeight_nonneg L hLpos j)
    _ = ((1 + d : ℕ) : ℝ) ^ 3 * cubicWeight L j := by ring

/-- Absolute weighted summability is preserved by every fixed iterated right shift. -/
theorem weightedAbs_shiftRightPow_summable
    (L : ℝ) (d : ℕ) (hL : 1 ≤ L) (f : Seq)
    (hf : Summable (weightedAbs L f)) :
    Summable (weightedAbs L (shiftRightPow d f)) := by
  let K : ℝ := ((1 + d : ℕ) : ℝ) ^ 3
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have htailPoint : ∀ j : ℕ,
      weightedAbs L (shiftRightPow d f) (j + d) ≤ K * weightedAbs L f j := by
    intro j
    rw [shiftRightPow_eq_shiftByInt, weightedAbs,
      shiftByInt_of_le d (j + d) f (Nat.le_add_left d j)]
    have hsub : j + d - d = j := by omega
    rw [hsub, weightedAbs]
    dsimp [K]
    calc
      cubicWeight L (j + d) * |f j| ≤
          (((1 + d : ℕ) : ℝ) ^ 3 * cubicWeight L j) * |f j| :=
        mul_le_mul_of_nonneg_right (cubicWeight_add_le_shiftFactor L d j hL)
          (abs_nonneg (f j))
      _ = ((1 + d : ℕ) : ℝ) ^ 3 * (cubicWeight L j * |f j|) := by ring
  have hscaled : Summable (fun j : ℕ ↦ K * weightedAbs L f j) := hf.mul_left K
  have htail : Summable (fun j : ℕ ↦ weightedAbs L (shiftRightPow d f) (j + d)) := by
    apply Summable.of_nonneg_of_le
      (f := fun j : ℕ ↦ K * weightedAbs L f j)
    · exact fun j ↦ weightedAbs_nonneg L hLpos (shiftRightPow d f) (j + d)
    · exact htailPoint
    · exact hscaled
  exact (summable_nat_add_iff d).1 htail

/-- Source bound for a fixed right shift in cubic weighted `l1`. -/
theorem weightedL1Three_shiftRightPow_le
    (L : ℝ) (d : ℕ) (hL : 1 ≤ L) (f : Seq)
    (hf : Summable (weightedAbs L f)) :
    weightedL1Three L (shiftRightPow d f) ≤
      ((1 + d : ℕ) : ℝ) ^ 3 * weightedL1Three L f := by
  let K : ℝ := ((1 + d : ℕ) : ℝ) ^ 3
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hg := weightedAbs_shiftRightPow_summable L d hL f hf
  have htailPoint : ∀ j : ℕ,
      weightedAbs L (shiftRightPow d f) (j + d) ≤ K * weightedAbs L f j := by
    intro j
    rw [shiftRightPow_eq_shiftByInt, weightedAbs,
      shiftByInt_of_le d (j + d) f (Nat.le_add_left d j)]
    have hsub : j + d - d = j := by omega
    rw [hsub, weightedAbs]
    dsimp [K]
    calc
      cubicWeight L (j + d) * |f j| ≤
          (((1 + d : ℕ) : ℝ) ^ 3 * cubicWeight L j) * |f j| :=
        mul_le_mul_of_nonneg_right (cubicWeight_add_le_shiftFactor L d j hL)
          (abs_nonneg (f j))
      _ = ((1 + d : ℕ) : ℝ) ^ 3 * (cubicWeight L j * |f j|) := by ring
  have htail := (summable_nat_add_iff d).2 hg
  have hscaled : Summable (fun j : ℕ ↦ K * weightedAbs L f j) := hf.mul_left K
  have hprefix :
      ∑ j ∈ Finset.range d, weightedAbs L (shiftRightPow d f) j = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    have hjd : j < d := Finset.mem_range.mp hj
    rw [weightedAbs, shiftRightPow_eq_shiftByInt,
      shiftByInt_eq_zero_of_lt d j f hjd, abs_zero, mul_zero]
  have hdecomp := hg.sum_add_tsum_nat_add d
  rw [hprefix, zero_add] at hdecomp
  rw [weightedL1Three_eq_tsum_weightedAbs,
    weightedL1Three_eq_tsum_weightedAbs]
  calc
    (∑' j : ℕ, weightedAbs L (shiftRightPow d f) j) =
        ∑' j : ℕ, weightedAbs L (shiftRightPow d f) (j + d) := hdecomp.symm
    _ ≤ ∑' j : ℕ, K * weightedAbs L f j :=
      Summable.tsum_le_tsum htailPoint htail hscaled
    _ = K * ∑' j : ℕ, weightedAbs L f j := hf.tsum_const_smul K

/-- A pointwise witness may always be enlarged. -/
theorem weightedSupThree_mono
    (L A B : ℝ) (f : Seq) (hf : WeightedSupThreeLE L f A) (hAB : A ≤ B) :
    WeightedSupThreeLE L f B := fun j ↦ (hf j).trans hAB

/-- Absolute weighted summability is preserved by scalar multiplication. -/
theorem weightedAbs_smul_summable
    (L c : ℝ) (f : Seq) (hf : Summable (weightedAbs L f)) :
    Summable (weightedAbs L (c • f)) := by
  rw [weightedAbs_smul]
  exact hf.const_smul |c|

/-- `E_s` as a genuine finite sum of shifted, scaled convolution powers. -/
theorem densityE_eq_finset_sum_smul (m : ℕ) (p₀ : ProbabilityMass) (s : ℕ) :
    densityE m p₀ s =
      ∑ r ∈ Finset.Ico 3 (m + 1),
        densityCoeff m r (orbit m p₀ s) •
          shiftRightPow (r - 2)
            (convPow r (positiveTiltedDensity m (orbit m p₀ s))) := by
  funext j
  simp only [densityE, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

/-- Explicit conditional weighted-supremum bound for the source sum `E_s`.
`C r` and `P r` are respectively the supplied coefficient and convolution bounds. -/
theorem densityE_weightedSup_bound
    (m : ℕ) (p₀ : ProbabilityMass) (s : ℕ) (L : ℝ) (hL : 1 ≤ L)
    (C P : ℕ → ℝ)
    (hP : ∀ r ∈ Finset.Ico 3 (m + 1), 0 ≤ P r)
    (hCoeff : ∀ r ∈ Finset.Ico 3 (m + 1),
      |densityCoeff m r (orbit m p₀ s)| ≤ C r)
    (hPow : ∀ r ∈ Finset.Ico 3 (m + 1),
      WeightedSupThreeLE L
        (convPow r (positiveTiltedDensity m (orbit m p₀ s))) (P r)) :
    WeightedSupThreeLE L (densityE m p₀ s)
      (∑ r ∈ Finset.Ico 3 (m + 1),
        C r * (((1 + (r - 2) : ℕ) : ℝ) ^ 3 * P r)) := by
  classical
  rw [densityE_eq_finset_sum_smul]
  apply weightedSupThree_finset_sum (Finset.Ico 3 (m + 1)) L
    (fun r ↦ C r * (((1 + (r - 2) : ℕ) : ℝ) ^ 3 * P r))
    (fun r ↦ densityCoeff m r (orbit m p₀ s) •
      shiftRightPow (r - 2)
        (convPow r (positiveTiltedDensity m (orbit m p₀ s))))
    (lt_of_lt_of_le zero_lt_one hL)
  intro r hr
  have hshift := weightedSupThree_shiftRightPow L (P r) (r - 2) hL (hP r hr)
    (convPow r (positiveTiltedDensity m (orbit m p₀ s))) (hPow r hr)
  have hscaled := weightedSupThree_smul L
    (((1 + (r - 2) : ℕ) : ℝ) ^ 3 * P r)
    (densityCoeff m r (orbit m p₀ s))
    (shiftRightPow (r - 2)
      (convPow r (positiveTiltedDensity m (orbit m p₀ s)))) hshift
  apply weightedSupThree_mono L _ _ _ hscaled
  exact mul_le_mul_of_nonneg_right (hCoeff r hr)
    (mul_nonneg (pow_nonneg (by positivity) 3) (hP r hr))

/-- Explicit conditional cubic weighted `l1` bound for `E_s`.
All convolution summability and magnitude bounds are exposed term by term. -/
theorem densityE_weightedL1_bound
    (m : ℕ) (p₀ : ProbabilityMass) (s : ℕ) (L : ℝ) (hL : 1 ≤ L)
    (C Q : ℕ → ℝ)
    (hQ : ∀ r ∈ Finset.Ico 3 (m + 1), 0 ≤ Q r)
    (hCoeff : ∀ r ∈ Finset.Ico 3 (m + 1),
      |densityCoeff m r (orbit m p₀ s)| ≤ C r)
    (hPowSum : ∀ r ∈ Finset.Ico 3 (m + 1),
      Summable (weightedAbs L
        (convPow r (positiveTiltedDensity m (orbit m p₀ s)))))
    (hPowL1 : ∀ r ∈ Finset.Ico 3 (m + 1),
      weightedL1Three L
          (convPow r (positiveTiltedDensity m (orbit m p₀ s))) ≤ Q r) :
    weightedL1Three L (densityE m p₀ s) ≤
      ∑ r ∈ Finset.Ico 3 (m + 1),
        C r * (((1 + (r - 2) : ℕ) : ℝ) ^ 3 * Q r) := by
  classical
  rw [densityE_eq_finset_sum_smul]
  let term : ℕ → Seq := fun r ↦
    densityCoeff m r (orbit m p₀ s) •
      shiftRightPow (r - 2)
        (convPow r (positiveTiltedDensity m (orbit m p₀ s)))
  have htermSum : ∀ r ∈ Finset.Ico 3 (m + 1),
      Summable (weightedAbs L (term r)) := by
    intro r hr
    apply weightedAbs_smul_summable
    exact weightedAbs_shiftRightPow_summable L (r - 2) hL _ (hPowSum r hr)
  calc
    weightedL1Three L (∑ r ∈ Finset.Ico 3 (m + 1), term r) ≤
        ∑ r ∈ Finset.Ico 3 (m + 1), weightedL1Three L (term r) :=
      weightedL1Three_finset_sum_le (Finset.Ico 3 (m + 1)) L term
        (lt_of_lt_of_le zero_lt_one hL) htermSum
    _ ≤ ∑ r ∈ Finset.Ico 3 (m + 1),
          C r * (((1 + (r - 2) : ℕ) : ℝ) ^ 3 * Q r) := by
      apply Finset.sum_le_sum
      intro r hr
      dsimp only [term]
      rw [weightedL1Three_smul]
      · have hshift := weightedL1Three_shiftRightPow_le L (r - 2) hL
          (convPow r (positiveTiltedDensity m (orbit m p₀ s))) (hPowSum r hr)
        calc
          |densityCoeff m r (orbit m p₀ s)| *
              weightedL1Three L
                (shiftRightPow (r - 2)
                  (convPow r (positiveTiltedDensity m (orbit m p₀ s)))) ≤
              |densityCoeff m r (orbit m p₀ s)| *
                (((1 + (r - 2) : ℕ) : ℝ) ^ 3 *
                  weightedL1Three L
                    (convPow r (positiveTiltedDensity m (orbit m p₀ s)))) :=
            mul_le_mul_of_nonneg_left hshift (abs_nonneg _)
          _ ≤ |densityCoeff m r (orbit m p₀ s)| *
                (((1 + (r - 2) : ℕ) : ℝ) ^ 3 * Q r) := by
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left (hPowL1 r hr) (pow_nonneg (by positivity) 3))
              (abs_nonneg _)
          _ ≤ C r * (((1 + (r - 2) : ℕ) : ℝ) ^ 3 * Q r) :=
            mul_le_mul_of_nonneg_right (hCoeff r hr)
              (mul_nonneg (pow_nonneg (by positivity) 3) (hQ r hr))
      · exact weightedAbs_shiftRightPow_summable L (r - 2) hL _ (hPowSum r hr)

/-- The finite source sum `E_s` is weighted-summable whenever each displayed
convolution power is. -/
theorem densityE_weightedAbs_summable
    (m : ℕ) (p₀ : ProbabilityMass) (s : ℕ) (L : ℝ) (hL : 1 ≤ L)
    (hPowSum : ∀ r ∈ Finset.Ico 3 (m + 1),
      Summable (weightedAbs L
        (convPow r (positiveTiltedDensity m (orbit m p₀ s))))) :
    Summable (weightedAbs L (densityE m p₀ s)) := by
  classical
  rw [densityE_eq_finset_sum_smul]
  apply weightedAbs_finset_sum_summable (Finset.Ico 3 (m + 1)) L _
    (lt_of_lt_of_le zero_lt_one hL)
  intro r hr
  apply weightedAbs_smul_summable
  exact weightedAbs_shiftRightPow_summable L (r - 2) hL _ (hPowSum r hr)

/-- Weighted-supremum bookkeeping for all six terms of the abstract remainder.
No decay rate is built into the statement: the five component bounds and weighted
summability of `E` are explicit hypotheses. -/
theorem smoothingRemainder_weightedSup_bound
    (L c d : ℝ) (rho E : Seq) (hL : 1 ≤ L)
    (RhoSup BSup ConvThreeSup ConvFourSup ESup : ℝ)
    (hRhoSup : 0 ≤ RhoSup) (hBSup : 0 ≤ BSup)
    (hESup : 0 ≤ ESup)
    (hrho : WeightedSupThreeLE L rho RhoSup)
    (hB : WeightedSupThreeLE L (conv rho rho) BSup)
    (hthree : WeightedSupThreeLE L (convPow 3 rho) ConvThreeSup)
    (hfour : WeightedSupThreeLE L (convPow 4 rho) ConvFourSup)
    (hE : WeightedSupThreeLE L E ESup)
    (hESum : Summable (weightedAbs L E)) :
    WeightedSupThreeLE L (smoothingRemainder c d rho E)
      (|-2 * c ^ 2 * rho 0| * RhoSup +
        |2 * c * d| * ConvThreeSup +
        |-2 * c * d * rho 0| * BSup +
        |d ^ 2| * ConvFourSup +
        2 * ((|c| * RhoSup + |d| * BSup) * weightedL1Three L E) +
        ESup * weightedL1Three L E) := by
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hEL1 : 0 ≤ weightedL1Three L E := weightedL1Three_nonneg L hLpos E
  have hrhoShift : WeightedSupThreeLE L (shiftLeft rho) RhoSup :=
    weightedSupThree_shiftLeft L RhoSup hLpos rho hrho
  have hrhoShiftTwo : WeightedSupThreeLE L (shiftLeft (shiftLeft rho)) RhoSup :=
    weightedSupThree_shiftLeft L RhoSup hLpos (shiftLeft rho) hrhoShift
  have hBShift : WeightedSupThreeLE L (shiftLeft (conv rho rho)) BSup :=
    weightedSupThree_shiftLeft L BSup hLpos (conv rho rho) hB
  have hthreeShift : WeightedSupThreeLE L (shiftLeft (convPow 3 rho)) ConvThreeSup :=
    weightedSupThree_shiftLeft L ConvThreeSup hLpos (convPow 3 rho) hthree
  have htermOne := weightedSupThree_smul L RhoSup (-2 * c ^ 2 * rho 0)
    (shiftLeft (shiftLeft rho)) hrhoShiftTwo
  have htermTwo := weightedSupThree_smul L ConvThreeSup (2 * c * d)
    (shiftLeft (convPow 3 rho)) hthreeShift
  have htermThree := weightedSupThree_smul L BSup (-2 * c * d * rho 0)
    (shiftLeft (conv rho rho)) hBShift
  have htermFour := weightedSupThree_smul L ConvFourSup (d ^ 2)
    (convPow 4 rho) hfour
  have hcRho := weightedSupThree_smul L RhoSup c (shiftLeft rho) hrhoShift
  have hdB := weightedSupThree_smul L BSup d (conv rho rho) hB
  have hbase := weightedSupThree_add L (|c| * RhoSup) (|d| * BSup) hLpos
    (c • shiftLeft rho) (d • conv rho rho) hcRho hdB
  have hbaseNonneg : 0 ≤ |c| * RhoSup + |d| * BSup :=
    add_nonneg (mul_nonneg (abs_nonneg c) hRhoSup)
      (mul_nonneg (abs_nonneg d) hBSup)
  have hmixed := weightedSupThree_conv_le L
    (|c| * RhoSup + |d| * BSup) hL hbaseNonneg
    (c • shiftLeft rho + d • conv rho rho) E hbase hESum
  have htermFive := weightedSupThree_smul L
    ((|c| * RhoSup + |d| * BSup) * weightedL1Three L E) 2
    (conv (c • shiftLeft rho + d • conv rho rho) E) hmixed
  have htermSix := weightedSupThree_conv_le L ESup hL hESup E E hE hESum
  have hsumTwo := weightedSupThree_add L _ _ hLpos _ _ htermOne htermTwo
  have hsumThree := weightedSupThree_add L _ _ hLpos _ _ hsumTwo htermThree
  have hsumFour := weightedSupThree_add L _ _ hLpos _ _ hsumThree htermFour
  have hsumFive := weightedSupThree_add L _ _ hLpos _ _ hsumFour htermFive
  have hsumSix := weightedSupThree_add L _ _ hLpos _ _ hsumFive htermSix
  simpa [smoothingRemainder, abs_mul, abs_pow, two_smul] using hsumSix

/-- Source-shaped conditional weighted-supremum bound for the complete `R_s`.
Every required bound on `rho_s`, `B_s`, the cubic and quartic convolutions, and `E_s`
is a separate theorem argument. -/
theorem densityR_weightedSup_bound
    (m : ℕ) (p₀ : ProbabilityMass) (s : ℕ) (L : ℝ) (hL : 1 ≤ L)
    (RhoSup BSup ConvThreeSup ConvFourSup ESup : ℝ)
    (hRhoSup : 0 ≤ RhoSup) (hBSup : 0 ≤ BSup)
    (hESup : 0 ≤ ESup)
    (hrho : WeightedSupThreeLE L
      (positiveTiltedDensity m (orbit m p₀ s)) RhoSup)
    (hB : WeightedSupThreeLE L (densityB m p₀ s) BSup)
    (hthree : WeightedSupThreeLE L
      (convPow 3 (positiveTiltedDensity m (orbit m p₀ s))) ConvThreeSup)
    (hfour : WeightedSupThreeLE L
      (convPow 4 (positiveTiltedDensity m (orbit m p₀ s))) ConvFourSup)
    (hE : WeightedSupThreeLE L (densityE m p₀ s) ESup)
    (hESum : Summable (weightedAbs L (densityE m p₀ s))) :
    WeightedSupThreeLE L (densityR m p₀ s)
      (|-2 * transportCoeff m (orbit m p₀ s) ^ 2 * densityBeta m p₀ s| *
          RhoSup +
        |2 * transportCoeff m (orbit m p₀ s) * densityD m p₀ s| *
          ConvThreeSup +
        |-2 * transportCoeff m (orbit m p₀ s) * densityD m p₀ s *
            densityBeta m p₀ s| * BSup +
        |densityD m p₀ s ^ 2| * ConvFourSup +
        2 * ((|transportCoeff m (orbit m p₀ s)| * RhoSup +
            |densityD m p₀ s| * BSup) *
          weightedL1Three L (densityE m p₀ s)) +
        ESup * weightedL1Three L (densityE m p₀ s)) := by
  simpa only [densityR, densityBeta, densityB, densityD] using
    smoothingRemainder_weightedSup_bound L
      (transportCoeff m (orbit m p₀ s)) (densityD m p₀ s)
      (positiveTiltedDensity m (orbit m p₀ s)) (densityE m p₀ s) hL
      RhoSup BSup ConvThreeSup ConvFourSup ESup hRhoSup hBSup
      hESup hrho hB hthree hfour hE hESum

/-- A coefficientwise form of the complete six-term `R_s` estimate.
The three scalar coefficient bounds, five weighted-supremum bounds, and the
weighted `l1` bound for `E_s` are all separate hypotheses. -/
theorem densityR_weightedSup_bound_of_component_bounds
    (m : ℕ) (p₀ : ProbabilityMass) (s : ℕ) (L : ℝ) (hL : 1 ≤ L)
    (CSup DSup BetaSup RhoSup BSup ConvThreeSup ConvFourSup ESup EL1 : ℝ)
    (hCSup : 0 ≤ CSup) (hDSup : 0 ≤ DSup)
    (hRhoSup : 0 ≤ RhoSup) (hBSup : 0 ≤ BSup)
    (hConvThreeSup : 0 ≤ ConvThreeSup) (hConvFourSup : 0 ≤ ConvFourSup)
    (hESup : 0 ≤ ESup)
    (hc : |transportCoeff m (orbit m p₀ s)| ≤ CSup)
    (hd : |densityD m p₀ s| ≤ DSup)
    (hbeta : |densityBeta m p₀ s| ≤ BetaSup)
    (hrho : WeightedSupThreeLE L
      (positiveTiltedDensity m (orbit m p₀ s)) RhoSup)
    (hB : WeightedSupThreeLE L (densityB m p₀ s) BSup)
    (hthree : WeightedSupThreeLE L
      (convPow 3 (positiveTiltedDensity m (orbit m p₀ s))) ConvThreeSup)
    (hfour : WeightedSupThreeLE L
      (convPow 4 (positiveTiltedDensity m (orbit m p₀ s))) ConvFourSup)
    (hE : WeightedSupThreeLE L (densityE m p₀ s) ESup)
    (hESum : Summable (weightedAbs L (densityE m p₀ s)))
    (hEL1Bound : weightedL1Three L (densityE m p₀ s) ≤ EL1) :
    WeightedSupThreeLE L (densityR m p₀ s)
      (2 * CSup ^ 2 * BetaSup * RhoSup +
        2 * CSup * DSup * ConvThreeSup +
        2 * CSup * DSup * BetaSup * BSup +
        DSup ^ 2 * ConvFourSup +
        2 * ((CSup * RhoSup + DSup * BSup) * EL1) +
        ESup * EL1) := by
  have hexact := densityR_weightedSup_bound m p₀ s L hL
    RhoSup BSup ConvThreeSup ConvFourSup ESup hRhoSup hBSup hESup
    hrho hB hthree hfour hE hESum
  apply weightedSupThree_mono L _ _ _ hexact
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hEL1nonneg : 0 ≤ weightedL1Three L (densityE m p₀ s) :=
    weightedL1Three_nonneg L hLpos (densityE m p₀ s)
  have habsNegTwo : |(-2 : ℝ)| = 2 := by norm_num
  have habsTwo : |(2 : ℝ)| = 2 := by norm_num
  have htermOne :
      |-2 * transportCoeff m (orbit m p₀ s) ^ 2 * densityBeta m p₀ s| *
          RhoSup ≤
        2 * CSup ^ 2 * BetaSup * RhoSup := by
    rw [abs_mul, abs_mul, habsNegTwo, abs_pow]
    gcongr
  have htermTwo :
      |2 * transportCoeff m (orbit m p₀ s) * densityD m p₀ s| *
          ConvThreeSup ≤
        2 * CSup * DSup * ConvThreeSup := by
    rw [abs_mul, abs_mul, habsTwo]
    gcongr
  have htermThree :
      |-2 * transportCoeff m (orbit m p₀ s) * densityD m p₀ s *
          densityBeta m p₀ s| * BSup ≤
        2 * CSup * DSup * BetaSup * BSup := by
    rw [abs_mul, abs_mul, abs_mul, habsNegTwo]
    gcongr
  have htermFour :
      |densityD m p₀ s ^ 2| * ConvFourSup ≤
        DSup ^ 2 * ConvFourSup := by
    rw [abs_pow]
    gcongr
  have htermFive :
      2 * ((|transportCoeff m (orbit m p₀ s)| * RhoSup +
          |densityD m p₀ s| * BSup) *
        weightedL1Three L (densityE m p₀ s)) ≤
        2 * ((CSup * RhoSup + DSup * BSup) * EL1) := by
    gcongr
  have htermSix :
      ESup * weightedL1Three L (densityE m p₀ s) ≤ ESup * EL1 :=
    mul_le_mul_of_nonneg_left hEL1Bound hESup
  exact add_le_add
    (add_le_add
      (add_le_add
        (add_le_add
          (add_le_add htermOne htermTwo)
          htermThree)
        htermFour)
      htermFive)
    htermSix

end

end DerridaRetaux
