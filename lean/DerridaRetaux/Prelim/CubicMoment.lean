import DerridaRetaux.Model.MomentPropagation
import DerridaRetaux.Model.TiltedRecursion
import Mathlib.Tactic

set_option autoImplicit false

open scoped BigOperators

namespace DerridaRetaux

noncomputable section

/-!
# The cubic carrier

This file isolates the axiom-free algebraic part of source equation `eq:cubic` and
Lemma `lem:cubic`.  The growth estimate for `J_n` is deliberately absent: it is the
only part of the source lemma that may use the published input H1b.
-/

/-- The coefficient `chi_m = 1 - 1 / (m - 1)` from source equation `eq:cubic`. -/
def cubicChi (m : ℕ) : ℝ :=
  1 - 1 / ((m : ℝ) - 1)

/-- The real-valued falling factorial `(k)_2` evaluated at a natural number. -/
def fallingFactorialTwo (k : ℕ) : ℝ :=
  (k : ℝ) * ((k : ℝ) - 1)

/-- The real-valued falling factorial `(k)_3` evaluated at a natural number. -/
def fallingFactorialThree (k : ℕ) : ℝ :=
  (k : ℝ) * ((k : ℝ) - 1) * ((k : ℝ) - 2)

/-- The cubic carrier `h_m(k) = k (k + 1) (k - 1 / (m - 1))`. -/
def cubicCarrier (m k : ℕ) : ℝ :=
  (k : ℝ) * ((k : ℝ) + 1) * ((k : ℝ) - 1 / ((m : ℝ) - 1))

/-- The normalized tilted expectation `J(p) = sum_k h_m(k) q_p(k)`. -/
def normalizedCubicMoment (m : ℕ) (p : ProbabilityMass) : ℝ :=
  ∑' k : ℕ, cubicCarrier m k * normalizedTilt m p k

/-- Raw second and third moments of an iid convolution power.  This is finite
coefficient algebra plus the Cauchy-product theorem, not differentiation of a series. -/
private theorem secondThirdMomentScale_convPow_hasSum
    (r : ℕ) (a : Seq) (muOne muTwo muThree : ℝ)
    (hmass : HasSum a 1)
    (hone : HasSum (firstMomentScale 1 a) muOne)
    (htwo : HasSum (secondMomentScale 1 a) muTwo)
    (hthree : HasSum (thirdMomentScale 1 a) muThree) :
    HasSum (secondMomentScale 1 (convPow r a))
        ((r : ℝ) * muTwo + (r : ℝ) * ((r : ℝ) - 1) * muOne ^ 2) ∧
      HasSum (thirdMomentScale 1 (convPow r a))
        ((r : ℝ) * muThree +
          3 * (r : ℝ) * ((r : ℝ) - 1) * muTwo * muOne +
            (r : ℝ) * ((r : ℝ) - 1) * ((r : ℝ) - 2) * muOne ^ 3) := by
  have hpower : HasSum (powerScale 1 a) 1 := by
    convert hmass using 1
    funext k
    simp [powerScale]
  induction r with
  | zero =>
      have hsecondZero :
          secondMomentScale 1 (convPow 0 a) = fun _ : ℕ ↦ 0 := by
        funext k
        cases k <;> simp [secondMomentScale, convPow, diracSeq]
      have hthirdZero :
          thirdMomentScale 1 (convPow 0 a) = fun _ : ℕ ↦ 0 := by
        funext k
        cases k <;> simp [thirdMomentScale, convPow, diracSeq]
      constructor
      · rw [hsecondZero]
        simpa using (hasSum_zero : HasSum (fun _ : ℕ ↦ (0 : ℝ)) 0)
      · rw [hthirdZero]
        simpa using (hasSum_zero : HasSum (fun _ : ℕ ↦ (0 : ℝ)) 0)
  | succ r ih =>
      rcases ih with ⟨ihtwo, ihthree⟩
      have hrmass : HasSum (powerScale 1 (convPow r a)) 1 := by
        simpa using powerScale_convPow_hasSum r 1 a 1 hpower
      have hrone :
          HasSum (firstMomentScale 1 (convPow r a)) ((r : ℝ) * muOne) := by
        simpa using firstMomentScale_convPow_hasSum r 1 a 1 muOne hpower hone
      constructor
      · rw [convPow_succ, secondMomentScale_conv]
        have hleft := conv_hasSum (secondMomentScale 1 (convPow r a))
          (powerScale 1 a) _ _ ihtwo hpower
        have hmiddle := conv_hasSum (firstMomentScale 1 (convPow r a))
          (firstMomentScale 1 a) _ _ hrone hone
        have hright := conv_hasSum (powerScale 1 (convPow r a))
          (secondMomentScale 1 a) _ _ hrmass htwo
        have hsum := (hleft.add (hmiddle.mul_left 2)).add hright
        convert hsum using 1
        push_cast
        ring
      · rw [convPow_succ, thirdMomentScale_conv]
        have hleft := conv_hasSum (thirdMomentScale 1 (convPow r a))
          (powerScale 1 a) _ _ ihthree hpower
        have hmiddleLeft := conv_hasSum (secondMomentScale 1 (convPow r a))
          (firstMomentScale 1 a) _ _ ihtwo hone
        have hmiddleRight := conv_hasSum (firstMomentScale 1 (convPow r a))
          (secondMomentScale 1 a) _ _ hrone htwo
        have hright := conv_hasSum (powerScale 1 (convPow r a))
          (thirdMomentScale 1 a) _ _ hrmass hthree
        have hsum :=
          ((hleft.add (hmiddleLeft.mul_left 3)).add
            (hmiddleRight.mul_left 3)).add hright
        convert hsum using 1
        push_cast
        ring

@[simp]
theorem cubicCarrier_zero (m : ℕ) : cubicCarrier m 0 = 0 := by
  simp [cubicCarrier]

@[simp]
theorem fallingFactorialTwo_zero : fallingFactorialTwo 0 = 0 := by
  simp [fallingFactorialTwo]

@[simp]
theorem fallingFactorialTwo_one : fallingFactorialTwo 1 = 0 := by
  norm_num [fallingFactorialTwo]

@[simp]
theorem fallingFactorialThree_zero : fallingFactorialThree 0 = 0 := by
  simp [fallingFactorialThree]

@[simp]
theorem fallingFactorialThree_one : fallingFactorialThree 1 = 0 := by
  norm_num [fallingFactorialThree]

@[simp]
theorem fallingFactorialThree_two : fallingFactorialThree 2 = 0 := by
  norm_num [fallingFactorialThree]

/-- The falling-factorial expansion in source equation `eq:cubic`. -/
theorem cubicCarrier_eq_fallingFactorials (m k : ℕ) :
    cubicCarrier m k =
      fallingFactorialThree k +
        (3 + cubicChi m) * fallingFactorialTwo k + 2 * cubicChi m * (k : ℝ) := by
  simp only [cubicCarrier, cubicChi, fallingFactorialTwo, fallingFactorialThree]
  ring

/-- A polynomial form convenient for coefficient comparisons. -/
theorem cubicCarrier_eq_cube_add (m k : ℕ) :
    cubicCarrier m k =
      (k : ℝ) ^ 3 +
        (k : ℝ) * (cubicChi m * ((k : ℝ) + 1) - 1) := by
  simp only [cubicCarrier, cubicChi]
  ring

/-- The carrier in ordinary raw-moment coordinates. -/
theorem cubicCarrier_eq_rawMoments (m k : ℕ) :
    cubicCarrier m k =
      (k : ℝ) ^ 3 + cubicChi m * (k : ℝ) ^ 2 +
        (cubicChi m - 1) * (k : ℝ) := by
  simp only [cubicCarrier, cubicChi]
  ring

/-- The ordinary cube in falling-factorial coordinates. -/
theorem cube_eq_fallingFactorials (k : ℕ) :
    (k : ℝ) ^ 3 =
      fallingFactorialThree k + 3 * fallingFactorialTwo k + (k : ℝ) := by
  simp only [fallingFactorialTwo, fallingFactorialThree]
  ring

/-- The square in falling-factorial coordinates. -/
theorem square_eq_fallingFactorialTwo (k : ℕ) :
    (k : ℝ) ^ 2 = fallingFactorialTwo k + (k : ℝ) := by
  simp only [fallingFactorialTwo]
  ring

theorem fallingFactorialTwo_nonneg (k : ℕ) : 0 ≤ fallingFactorialTwo k := by
  cases k with
  | zero => simp
  | succ k =>
      simp [fallingFactorialTwo]
      positivity

theorem fallingFactorialThree_nonneg (k : ℕ) : 0 ≤ fallingFactorialThree k := by
  cases k with
  | zero => simp
  | succ k =>
      cases k with
      | zero => norm_num [fallingFactorialThree]
      | succ k =>
          rw [show fallingFactorialThree (Nat.succ (Nat.succ k)) =
            ((k : ℝ) + 2) * ((k : ℝ) + 1) * (k : ℝ) by
              simp only [fallingFactorialThree, Nat.cast_succ]
              ring]
          positivity

theorem cubicChi_nonneg (m : ℕ) (hm : 2 ≤ m) : 0 ≤ cubicChi m := by
  have hmReal : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hden : (1 : ℝ) ≤ (m : ℝ) - 1 := by linarith
  have hdenPos : 0 < (m : ℝ) - 1 := lt_of_lt_of_le zero_lt_one hden
  have hinv : 1 / ((m : ℝ) - 1) ≤ (1 : ℝ) := by
    apply (div_le_iff₀ hdenPos).2
    simpa using hden
  simp only [cubicChi]
  linarith

theorem cubicChi_le_one (m : ℕ) (hm : 2 ≤ m) : cubicChi m ≤ 1 := by
  have hmReal : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hdenPos : 0 < (m : ℝ) - 1 := by linarith
  have hinv : 0 ≤ 1 / ((m : ℝ) - 1) := by positivity
  simp only [cubicChi]
  linarith

theorem one_half_le_cubicChi (m : ℕ) (hm : 3 ≤ m) : (1 : ℝ) / 2 ≤ cubicChi m := by
  have hmReal : (3 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hden : (2 : ℝ) ≤ (m : ℝ) - 1 := by linarith
  have hdenPos : 0 < (m : ℝ) - 1 := by linarith
  have hinv : 1 / ((m : ℝ) - 1) ≤ (1 : ℝ) / 2 := by
    apply (div_le_iff₀ hdenPos).2
    nlinarith
  simp only [cubicChi]
  linarith

theorem cubicChi_pos (m : ℕ) (hm : 3 ≤ m) : 0 < cubicChi m := by
  linarith [one_half_le_cubicChi m hm]

/-- All coefficients in the falling-factorial expansion are nonnegative for `m ≥ 2`. -/
theorem cubicCarrier_nonneg (m k : ℕ) (hm : 2 ≤ m) : 0 ≤ cubicCarrier m k := by
  rw [cubicCarrier_eq_fallingFactorials]
  have hchi := cubicChi_nonneg m hm
  have htwo := fallingFactorialTwo_nonneg k
  have hthree := fallingFactorialThree_nonneg k
  have hk : 0 ≤ (k : ℝ) := by positivity
  have hcoeff : 0 ≤ 3 + cubicChi m := by linarith
  exact add_nonneg (add_nonneg hthree (mul_nonneg hcoeff htwo))
    (mul_nonneg (mul_nonneg (by norm_num) hchi) hk)

/-- The pointwise estimate giving the source second-moment bound. -/
theorem square_le_cubicCarrier_add_natCast (m k : ℕ) (hm : 2 ≤ m) :
    (k : ℝ) ^ 2 ≤ cubicCarrier m k + (k : ℝ) := by
  rw [square_eq_fallingFactorialTwo, cubicCarrier_eq_fallingFactorials]
  have hchi := cubicChi_nonneg m hm
  have htwo := fallingFactorialTwo_nonneg k
  have hthree := fallingFactorialThree_nonneg k
  have hk : 0 ≤ (k : ℝ) := by positivity
  have hcoeff : 0 ≤ 2 + cubicChi m := by linarith
  have hrest :
      0 ≤ fallingFactorialThree k +
        (2 + cubicChi m) * fallingFactorialTwo k +
          2 * cubicChi m * (k : ℝ) :=
    add_nonneg (add_nonneg hthree (mul_nonneg hcoeff htwo))
      (mul_nonneg (mul_nonneg (by norm_num) hchi) hk)
  linarith

/-- For `m ≥ 3`, the source comparison `k^3 ≤ h_m(k)` holds on all naturals. -/
theorem cube_le_cubicCarrier (m k : ℕ) (hm : 3 ≤ m) :
    (k : ℝ) ^ 3 ≤ cubicCarrier m k := by
  rw [cubicCarrier_eq_cube_add]
  have hk : 0 ≤ (k : ℝ) := by positivity
  have hchi := one_half_le_cubicChi m hm
  by_cases hkZero : k = 0
  · simp [hkZero]
  · have hkOne : (1 : ℝ) ≤ (k : ℝ) := by
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hkZero)
    have hinner : 0 ≤ cubicChi m * ((k : ℝ) + 1) - 1 := by
      nlinarith
    exact le_add_of_nonneg_right (mul_nonneg hk hinner)

/-- For `m ≥ 3`, the carrier also dominates the first moment. -/
theorem natCast_le_cubicCarrier (m k : ℕ) (hm : 3 ≤ m) :
    (k : ℝ) ≤ cubicCarrier m k := by
  apply le_trans _ (cube_le_cubicCarrier m k hm)
  by_cases hkZero : k = 0
  · simp [hkZero]
  · have hkOne : (1 : ℝ) ≤ (k : ℝ) := by
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hkZero)
    have hfactor :
        0 ≤ (k : ℝ) * ((k : ℝ) - 1) * ((k : ℝ) + 1) := by
      exact mul_nonneg
        (mul_nonneg (by positivity) (sub_nonneg.mpr hkOne)) (by positivity)
    nlinarith

/-- A uniform cubic upper comparison used to transfer third-moment summability. -/
theorem cubicCarrier_le_two_mul_cube (m k : ℕ) (hm : 2 ≤ m) :
    cubicCarrier m k ≤ 2 * (k : ℝ) ^ 3 := by
  rw [cubicCarrier_eq_cube_add]
  by_cases hkZero : k = 0
  · simp [hkZero]
  · have hkOne : (1 : ℝ) ≤ (k : ℝ) := by
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hkZero)
    have hk : 0 ≤ (k : ℝ) := by positivity
    have hchi := cubicChi_le_one m hm
    have hinner : cubicChi m * ((k : ℝ) + 1) - 1 ≤ (k : ℝ) := by
      have hmul : cubicChi m * ((k : ℝ) + 1) ≤ 1 * ((k : ℝ) + 1) :=
        mul_le_mul_of_nonneg_right hchi (by positivity)
      linarith
    have hmul :
        (k : ℝ) * (cubicChi m * ((k : ℝ) + 1) - 1) ≤ (k : ℝ) ^ 2 := by
      calc
        (k : ℝ) * (cubicChi m * ((k : ℝ) + 1) - 1) ≤ (k : ℝ) * (k : ℝ) :=
          mul_le_mul_of_nonneg_left hinner hk
        _ = (k : ℝ) ^ 2 := by ring
    have hsquare : (k : ℝ) ^ 2 ≤ (k : ℝ) ^ 3 := by
      nlinarith [mul_nonneg (sq_nonneg (k : ℝ)) (sub_nonneg.mpr hkOne)]
    nlinarith

/-- The binary carrier is exactly `k^3 - k`. -/
theorem cubicCarrier_two (k : ℕ) :
    cubicCarrier 2 k = (k : ℝ) ^ 3 - (k : ℝ) := by
  norm_num [cubicCarrier]
  ring

@[simp]
theorem cubicCarrier_two_one : cubicCarrier 2 1 = 0 := by
  norm_num [cubicCarrier_two]

theorem cubicCarrier_two_pos (k : ℕ) (hk : 2 ≤ k) : 0 < cubicCarrier 2 k := by
  rw [cubicCarrier_two]
  have hkReal : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hkPos : 0 < (k : ℝ) := by linarith
  have hkSubPos : 0 < (k : ℝ) - 1 := by linarith
  have hkAddPos : 0 < (k : ℝ) + 1 := by linarith
  have hprod : 0 < (k : ℝ) * ((k : ℝ) - 1) * ((k : ℝ) + 1) :=
    mul_pos (mul_pos hkPos hkSubPos) hkAddPos
  nlinarith

theorem cubicCarrier_two_pos_iff (k : ℕ) : 0 < cubicCarrier 2 k ↔ 2 ≤ k := by
  constructor
  · intro h
    by_contra hk
    have hkSmall : k = 0 ∨ k = 1 := by omega
    rcases hkSmall with rfl | rfl
    · simp at h
    · simp at h
  · exact cubicCarrier_two_pos k

/-- For `m ≥ 3`, the carrier is strictly positive exactly away from `k = 0`. -/
theorem cubicCarrier_pos_of_three_le (m k : ℕ) (hm : 3 ≤ m) (hk : 1 ≤ k) :
    0 < cubicCarrier m k := by
  have hkReal : 0 < (k : ℝ) ^ 3 := by
    positivity
  exact hkReal.trans_le (cube_le_cubicCarrier m k hm)

theorem cubicCarrier_pos_iff_of_three_le (m k : ℕ) (hm : 3 ≤ m) :
    0 < cubicCarrier m k ↔ 1 ≤ k := by
  constructor
  · intro h
    by_contra hk
    have hkZero : k = 0 := by omega
    simp [hkZero] at h
  · exact cubicCarrier_pos_of_three_le m k hm

/-- The binary comparison used in the cubic-moment estimate above the atom at one. -/
theorem cube_le_four_thirds_mul_cubicCarrier_two (k : ℕ) (hk : 2 ≤ k) :
    (k : ℝ) ^ 3 ≤ (4 / 3 : ℝ) * cubicCarrier 2 k := by
  rw [cubicCarrier_two]
  have hkReal : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hkNonneg : 0 ≤ (k : ℝ) := by linarith
  have hkSub : 0 ≤ (k : ℝ) - 2 := by linarith
  have hkAdd : 0 ≤ (k : ℝ) + 2 := by linarith
  have hsquare : 0 ≤ (k : ℝ) ^ 2 - 4 := by
    nlinarith [mul_nonneg hkSub hkAdd]
  have hfactor : 0 ≤ (k : ℝ) * ((k : ℝ) ^ 2 - 4) :=
    mul_nonneg hkNonneg hsquare
  nlinarith

/-- A global binary comparison; the only correction is the atom at `k = 1`. -/
theorem cube_le_four_thirds_mul_cubicCarrier_two_add_indicator (k : ℕ) :
    (k : ℝ) ^ 3 ≤
      (4 / 3 : ℝ) * cubicCarrier 2 k + if k = 1 then 1 else 0 := by
  by_cases hkZero : k = 0
  · simp [hkZero]
  by_cases hkOne : k = 1
  · simp [hkOne, cubicCarrier_two]
  have hk : 2 ≤ k := by omega
  simpa [hkOne] using cube_le_four_thirds_mul_cubicCarrier_two k hk

/-- The pointwise predecessor identity used before taking expectations. -/
theorem cubicCarrier_natPred (m V : ℕ) :
    cubicCarrier m (V - 1) =
      fallingFactorialThree V + cubicChi m * fallingFactorialTwo V := by
  cases V with
  | zero => simp
  | succ V =>
      cases V with
      | zero => norm_num [cubicCarrier, fallingFactorialTwo, fallingFactorialThree]
      | succ V =>
          simp only [Nat.succ_sub_one, cubicCarrier, fallingFactorialTwo,
            fallingFactorialThree, cubicChi, Nat.cast_add, Nat.cast_one]
          ring

/-- Finite nonnegative expectations of the cubic carrier. -/
theorem sum_cubicCarrier_nonneg
    (m : ℕ) (hm : 2 ≤ m) (s : Finset ℕ) (w : ℕ → ℝ)
    (hw : ∀ k : ℕ, 0 ≤ w k) :
    0 ≤ ∑ k ∈ s, cubicCarrier m k * w k := by
  exact Finset.sum_nonneg fun k _ ↦ mul_nonneg (cubicCarrier_nonneg m k hm) (hw k)

/-- Finite weighted form of `k^3 ≤ h_m(k)` for `m ≥ 3`. -/
theorem sum_cube_le_sum_cubicCarrier
    (m : ℕ) (hm : 3 ≤ m) (s : Finset ℕ) (w : ℕ → ℝ)
    (hw : ∀ k : ℕ, 0 ≤ w k) :
    (∑ k ∈ s, (k : ℝ) ^ 3 * w k) ≤ ∑ k ∈ s, cubicCarrier m k * w k := by
  apply Finset.sum_le_sum
  intro k hk
  exact mul_le_mul_of_nonneg_right (cube_le_cubicCarrier m k hm) (hw k)

/-- The predecessor identity may be transported through any convergent expectation. -/
theorem hasSum_cubicCarrier_natPred
    (m : ℕ) (w : ℕ → ℝ) (a : ℝ)
    (h : HasSum
      (fun V : ℕ ↦
        (fallingFactorialThree V + cubicChi m * fallingFactorialTwo V) * w V) a) :
    HasSum (fun V : ℕ ↦ cubicCarrier m (V - 1) * w V) a := by
  simpa only [cubicCarrier_natPred] using h

/-- Cubic-carrier summability follows from a nonnegative weighted third moment. -/
theorem summable_cubicCarrier_mul_of_summable_cube
    (m : ℕ) (hm : 2 ≤ m) (w : ℕ → ℝ)
    (hw : ∀ k : ℕ, 0 ≤ w k)
    (hs : Summable (fun k : ℕ ↦ (k : ℝ) ^ 3 * w k)) :
    Summable (fun k : ℕ ↦ cubicCarrier m k * w k) := by
  apply Summable.of_nonneg_of_le
    (f := fun k : ℕ ↦ 2 * ((k : ℝ) ^ 3 * w k))
  · exact fun k ↦ mul_nonneg (cubicCarrier_nonneg m k hm) (hw k)
  · intro k
    calc
      cubicCarrier m k * w k ≤ (2 * (k : ℝ) ^ 3) * w k :=
        mul_le_mul_of_nonneg_right (cubicCarrier_le_two_mul_cube m k hm) (hw k)
      _ = 2 * ((k : ℝ) ^ 3 * w k) := by ring
  · simpa only [mul_assoc] using hs.mul_left 2

/-- A third tilted moment gives a finite normalized tilted second moment. -/
theorem normalizedTilt_square_summable
    (m : ℕ) (p : ProbabilityMass) (hthird : TiltSummable m 3 p) :
    Summable (fun k : ℕ ↦ (k : ℝ) ^ 2 * normalizedTilt m p k) := by
  have htwo := tiltSummable_two_of_three m p hthird
  simpa only [normalizedTilt, div_eq_mul_inv, mul_assoc] using
    htwo.div_const (tiltedPartition m p)

/-- Third tilted summability transfers to the normalized tilted law. -/
theorem normalizedTilt_cube_summable
    (m : ℕ) (p : ProbabilityMass) (hthird : TiltSummable m 3 p) :
    Summable (fun k : ℕ ↦ (k : ℝ) ^ 3 * normalizedTilt m p k) := by
  simpa only [normalizedTilt, div_eq_mul_inv, mul_assoc] using
    hthird.div_const (tiltedPartition m p)

/-- The normalized cubic moment is finite under the manuscript's third-moment premise. -/
theorem normalizedCubicMoment_summable
    (m : ℕ) (p : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p) (hthird : TiltSummable m 3 p) :
    Summable (fun k : ℕ ↦ cubicCarrier m k * normalizedTilt m p k) := by
  apply summable_cubicCarrier_mul_of_summable_cube m hm
  · intro k
    exact normalizedTilt_nonneg m p (by omega) hcrit k
  · exact normalizedTilt_cube_summable m p hthird

theorem normalizedCubicMoment_hasSum
    (m : ℕ) (p : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p) (hthird : TiltSummable m 3 p) :
    HasSum (fun k : ℕ ↦ cubicCarrier m k * normalizedTilt m p k)
      (normalizedCubicMoment m p) := by
  exact (normalizedCubicMoment_summable m p hm hcrit hthird).hasSum

/-- The full iid factorial-moment expansion behind the one-step cubic identity.

The proof uses finite Cauchy-product algebra and explicit `HasSum` witnesses.  In
particular, it does not differentiate an infinite generating series. -/
theorem hasSum_cubicCarrier_natPred_convPow
    (m : ℕ) (p : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p) (hthird : TiltSummable m 3 p) :
    HasSum
      (fun V : ℕ ↦
        cubicCarrier m (V - 1) * convPow m (normalizedTilt m p) V)
      ((m : ℝ) * normalizedCubicMoment m p) := by
  let muOne : ℝ := 1 / ((m : ℝ) - 1)
  let muTwo : ℝ := ∑' k : ℕ, (k : ℝ) ^ 2 * normalizedTilt m p k
  let muThree : ℝ := ∑' k : ℕ, (k : ℝ) ^ 3 * normalizedTilt m p k
  have hmass : HasSum (normalizedTilt m p) 1 :=
    normalizedTilt_hasSum m p (by omega) hcrit
  have hpower : HasSum (powerScale 1 (normalizedTilt m p)) 1 := by
    convert hmass using 1
    funext k
    simp [powerScale]
  have hone :
      HasSum (firstMomentScale 1 (normalizedTilt m p)) muOne := by
    convert normalizedTilt_mean_hasSum m p (by omega) hcrit using 1
    funext k
    simp [firstMomentScale]
  have htwo :
      HasSum (secondMomentScale 1 (normalizedTilt m p)) muTwo := by
    convert (normalizedTilt_square_summable m p hthird).hasSum using 1
    funext k
    simp [secondMomentScale]
  have hthree :
      HasSum (thirdMomentScale 1 (normalizedTilt m p)) muThree := by
    convert (normalizedTilt_cube_summable m p hthird).hasSum using 1
    funext k
    simp [thirdMomentScale]
  have hconvOne :
      HasSum (firstMomentScale 1 (convPow m (normalizedTilt m p)))
        ((m : ℝ) * muOne) := by
    simpa using firstMomentScale_convPow_hasSum m 1 (normalizedTilt m p) 1 muOne
      hpower hone
  rcases secondThirdMomentScale_convPow_hasSum m (normalizedTilt m p)
      muOne muTwo muThree hmass hone htwo hthree with ⟨hconvTwo, hconvThree⟩
  have hfactorialTwo := hconvTwo.sub hconvOne
  have hfactorialThree :=
    (hconvThree.sub (hconvTwo.mul_left 3)).add (hconvOne.mul_left 2)
  have hpredecessor := hfactorialThree.add (hfactorialTwo.mul_left (cubicChi m))
  have hcarrierRaw :=
    (hthree.add (htwo.mul_left (cubicChi m))).add
      (hone.mul_left (cubicChi m - 1))
  have hcarrierValue :
      normalizedCubicMoment m p =
        muThree + cubicChi m * muTwo + (cubicChi m - 1) * muOne := by
    apply (normalizedCubicMoment_hasSum m p hm hcrit hthird).unique
    convert hcarrierRaw using 1
    · funext k
      simp only [thirdMomentScale_apply, secondMomentScale_apply,
        firstMomentScale_apply, one_pow, one_mul]
      rw [cubicCarrier_eq_rawMoments]
      ring
  convert hpredecessor using 1
  · funext V
    simp only [thirdMomentScale_apply, secondMomentScale_apply,
      firstMomentScale_apply, one_pow, one_mul]
    rw [cubicCarrier_natPred]
    simp only [fallingFactorialThree, fallingFactorialTwo]
    ring
  · rw [hcarrierValue]
    have hdenPos : 0 < (m : ℝ) - 1 := by
      have hmReal : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
      linarith
    dsimp only [muOne]
    simp only [cubicChi]
    field_simp [hdenPos.ne']
    ring

/-- Exact one-step recurrence `D J(next) = m J`, proved independently of H1b. -/
theorem normalizedCubicMoment_drStepProb_cross
    (m : ℕ) (p : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p) (hthird : TiltSummable m 3 p) :
    tiltDenom m p * normalizedCubicMoment m (drStepProb m p) =
      (m : ℝ) * normalizedCubicMoment m p := by
  have hnextCrit := critical_drStepProb m p (by omega) hcrit
  have hnextThird := tiltSummable_three_drStepProb m p (by omega) hcrit hthird
  have hnext := normalizedCubicMoment_hasSum m (drStepProb m p) hm
    hnextCrit hnextThird
  have hscaled := hnext.mul_left (tiltDenom m p)
  have hscaledConv :
      HasSum
        (fun k : ℕ ↦
          cubicCarrier m k * convPow m (normalizedTilt m p) (k + 1))
        (tiltDenom m p * normalizedCubicMoment m (drStepProb m p)) := by
    convert hscaled using 1
    funext k
    calc
      cubicCarrier m k * convPow m (normalizedTilt m p) (k + 1) =
          cubicCarrier m k *
            (tiltDenom m p * normalizedTilt m (drStepProb m p) k) := by
        rw [normalizedTilt_drStepProb_coeff_cross m p (by omega) hcrit k]
        by_cases hk : k = 0
        · simp [hk]
        · simp [hk]
      _ = tiltDenom m p *
          (cubicCarrier m k * normalizedTilt m (drStepProb m p) k) := by
        ring
  have hall := hasSum_cubicCarrier_natPred_convPow m p hm hcrit hthird
  have htail :
      HasSum
        (fun k : ℕ ↦
          cubicCarrier m k * convPow m (normalizedTilt m p) (k + 1))
        ((m : ℝ) * normalizedCubicMoment m p) := by
    simpa using
      (hasSum_nat_add_iff'
        (f := fun V : ℕ ↦
          cubicCarrier m (V - 1) * convPow m (normalizedTilt m p) V) 1).2 hall
  exact hscaledConv.unique htail

/-- Paper-step wrapper for the exact cubic recurrence. -/
theorem normalizedCubicMoment_drStep_cross
    (m : ℕ) (p : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p) (hthird : TiltSummable m 3 p) :
    tiltDenom m p * normalizedCubicMoment m (drStep m p) =
      (m : ℝ) * normalizedCubicMoment m p := by
  rw [drStep_eq_drStepProb]
  exact normalizedCubicMoment_drStepProb_cross m p hm hcrit hthird

/-- Divided paper-step form; positivity of `D` is established before division. -/
theorem normalizedCubicMoment_drStep
    (m : ℕ) (p : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p) (hthird : TiltSummable m 3 p) :
    normalizedCubicMoment m (drStep m p) =
      ((m : ℝ) * normalizedCubicMoment m p) / tiltDenom m p := by
  apply (eq_div_iff (tiltDenom_pos m p (by omega) hcrit).ne').2
  simpa [mul_comm] using normalizedCubicMoment_drStep_cross m p hm hcrit hthird

/-- Strict positivity of `J` propagates through one paper step without H1b. -/
theorem normalizedCubicMoment_drStep_pos_of_pos
    (m : ℕ) (p : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p) (hthird : TiltSummable m 3 p)
    (hpos : 0 < normalizedCubicMoment m p) :
    0 < normalizedCubicMoment m (drStep m p) := by
  rw [normalizedCubicMoment_drStep m p hm hcrit hthird]
  exact div_pos (mul_pos (by positivity) hpos) (tiltDenom_pos m p (by omega) hcrit)

/-- Source-indexed orbit form of the exact cubic recurrence. -/
theorem normalizedCubicMoment_orbit_succ_cross
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p₀) (hthird : TiltSummable m 3 p₀) (n : ℕ) :
    tiltDenom m (orbit m p₀ n) * normalizedCubicMoment m (orbit m p₀ (n + 1)) =
      (m : ℝ) * normalizedCubicMoment m (orbit m p₀ n) := by
  rw [orbit_succ]
  exact normalizedCubicMoment_drStep_cross m (orbit m p₀ n) hm
    (orbit_critical m p₀ (by omega) hcrit n)
    (orbit_tiltSummable_three m p₀ (by omega) hcrit hthird n)

/-- Once positive initially, the cubic moment stays positive along every finite orbit. -/
theorem normalizedCubicMoment_orbit_pos
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p₀) (hthird : TiltSummable m 3 p₀)
    (hpos : 0 < normalizedCubicMoment m p₀) (n : ℕ) :
    0 < normalizedCubicMoment m (orbit m p₀ n) := by
  induction n with
  | zero => simpa using hpos
  | succ n ih =>
      rw [orbit_succ]
      exact normalizedCubicMoment_drStep_pos_of_pos m (orbit m p₀ n) hm
        (orbit_critical m p₀ (by omega) hcrit n)
        (orbit_tiltSummable_three m p₀ (by omega) hcrit hthird n) ih

/-- Exact product formula for `J_n`; the later quadratic growth bound remains H1b-only. -/
theorem normalizedCubicMoment_orbit_eq
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p₀) (hthird : TiltSummable m 3 p₀) (n : ℕ) :
    normalizedCubicMoment m (orbit m p₀ n) =
      normalizedCubicMoment m p₀ *
        (tiltedPartition m p₀ / tiltedPartition m (orbit m p₀ n)) *
          criticalProduct m p₀ n := by
  induction n with
  | zero =>
      have hG := tiltedPartition_pos_of_critical m p₀ (by omega) hcrit
      simp [criticalProduct_zero, hG.ne']
  | succ n ih =>
      have hncrit := orbit_critical m p₀ (by omega) hcrit n
      have hnthird := orbit_tiltSummable_three m p₀ (by omega) hcrit hthird n
      have hGn := tiltedPartition_pos_of_critical m (orbit m p₀ n) (by omega) hncrit
      have hDn := tiltDenom_pos m (orbit m p₀ n) (by omega) hncrit
      have hmReal : (0 : ℝ) < (m : ℝ) := by positivity
      have hpow :
          tiltedPartition m (orbit m p₀ n) ^ m =
            tiltedPartition m (orbit m p₀ n) ^ (m - 1) *
              tiltedPartition m (orbit m p₀ n) := by
        rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ m)]
      rw [criticalProduct_succ,
        tiltedPartition_orbit_succ_eq m p₀ (by omega) hcrit n]
      rw [orbit_succ, normalizedCubicMoment_drStep m (orbit m p₀ n) hm
        hncrit hnthird, ih]
      rw [hpow]
      field_simp [hGn.ne', hDn.ne', hmReal.ne']
      ring

theorem normalizedCubicMoment_nonneg
    (m : ℕ) (p : ProbabilityMass) (hm : 2 ≤ m) (hcrit : Critical m p) :
    0 ≤ normalizedCubicMoment m p := by
  apply tsum_nonneg
  intro k
  exact mul_nonneg (cubicCarrier_nonneg m k hm)
    (normalizedTilt_nonneg m p (by omega) hcrit k)

/-- The normalized second moment is at most `J + 1 / (m - 1)`. -/
theorem normalizedTilt_square_tsum_le_cubicMoment_add_mean
    (m : ℕ) (p : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p) (hthird : TiltSummable m 3 p) :
    (∑' k : ℕ, (k : ℝ) ^ 2 * normalizedTilt m p k) ≤
      normalizedCubicMoment m p + 1 / ((m : ℝ) - 1) := by
  have hsquare := normalizedTilt_square_summable m p hthird
  have hcarrier := normalizedCubicMoment_hasSum m p hm hcrit hthird
  have hmean := normalizedTilt_mean_hasSum m p (by omega) hcrit
  have hrhs := hcarrier.add hmean
  calc
    (∑' k : ℕ, (k : ℝ) ^ 2 * normalizedTilt m p k) ≤
        ∑' k : ℕ,
          (cubicCarrier m k * normalizedTilt m p k +
            (k : ℝ) * normalizedTilt m p k) := by
      apply hsquare.tsum_le_tsum _ hrhs.summable
      intro k
      have hq := normalizedTilt_nonneg m p (by omega) hcrit k
      calc
        (k : ℝ) ^ 2 * normalizedTilt m p k ≤
            (cubicCarrier m k + (k : ℝ)) * normalizedTilt m p k :=
          mul_le_mul_of_nonneg_right (square_le_cubicCarrier_add_natCast m k hm) hq
        _ = cubicCarrier m k * normalizedTilt m p k +
              (k : ℝ) * normalizedTilt m p k := by ring
    _ = normalizedCubicMoment m p + 1 / ((m : ℝ) - 1) := hrhs.tsum_eq

/-- For `m ≥ 3`, the normalized third moment is bounded above by `J`. -/
theorem normalizedTilt_cube_tsum_le_normalizedCubicMoment
    (m : ℕ) (p : ProbabilityMass) (hm : 3 ≤ m)
    (hcrit : Critical m p) (hthird : TiltSummable m 3 p) :
    (∑' k : ℕ, (k : ℝ) ^ 3 * normalizedTilt m p k) ≤
      normalizedCubicMoment m p := by
  have hcube := normalizedTilt_cube_summable m p hthird
  have hcubic := normalizedCubicMoment_summable m p (by omega) hcrit hthird
  unfold normalizedCubicMoment
  exact hcube.tsum_le_tsum
    (fun k ↦ mul_le_mul_of_nonneg_right (cube_le_cubicCarrier m k hm)
      (normalizedTilt_nonneg m p (by omega) hcrit k))
    hcubic

/-- At arity at least three, the normalized first moment is bounded above by `J`. -/
theorem normalizedTilt_mean_tsum_le_normalizedCubicMoment
    (m : ℕ) (p : ProbabilityMass) (hm : 3 ≤ m)
    (hcrit : Critical m p) (hthird : TiltSummable m 3 p) :
    (∑' k : ℕ, (k : ℝ) * normalizedTilt m p k) ≤
      normalizedCubicMoment m p := by
  have hmean := (normalizedTilt_mean_hasSum m p (by omega) hcrit).summable
  have hcubic := normalizedCubicMoment_summable m p (by omega) hcrit hthird
  unfold normalizedCubicMoment
  exact hmean.tsum_le_tsum
    (fun k ↦ mul_le_mul_of_nonneg_right (natCast_le_cubicCarrier m k hm)
      (normalizedTilt_nonneg m p (by omega) hcrit k))
    hcubic

/-- For `m ≥ 3`, criticality makes the finite normalized cubic moment strictly positive. -/
theorem normalizedCubicMoment_pos_of_three_le
    (m : ℕ) (p : ProbabilityMass) (hm : 3 ≤ m)
    (hcrit : Critical m p) (hthird : TiltSummable m 3 p) :
    0 < normalizedCubicMoment m p := by
  have hle := normalizedTilt_mean_tsum_le_normalizedCubicMoment m p hm hcrit hthird
  rw [normalizedTilt_mean m p (by omega) hcrit] at hle
  have hmReal : (1 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 1 < m)
  exact (one_div_pos.mpr (by linarith)).trans_le hle

/-- At binary arity, any positive atom at `k ≥ 2` makes `J` strictly positive. -/
theorem normalizedCubicMoment_two_pos_of_mass
    (p : ProbabilityMass) (hcrit : Critical 2 p) (hthird : TiltSummable 2 3 p)
    (k : ℕ) (hk : 2 ≤ k) (hpk : 0 < p k) :
    0 < normalizedCubicMoment 2 p := by
  have hs := normalizedCubicMoment_summable 2 p (by norm_num) hcrit hthird
  unfold normalizedCubicMoment
  apply hs.tsum_pos (i := k)
  · intro j
    exact mul_nonneg (cubicCarrier_nonneg 2 j (by norm_num))
      (normalizedTilt_nonneg 2 p (by norm_num) hcrit j)
  · apply mul_pos (cubicCarrier_two_pos k hk)
    exact div_pos (mul_pos (pow_pos (by norm_num) k) hpk)
      (normalizedTilt_denominator_pos 2 p (by norm_num) hcrit)

/-- A non-fixed binary critical law must put positive mass above one. -/
theorem exists_mass_ge_two_of_critical_two_not_fixed
    (p : ProbabilityMass) (hcrit : Critical 2 p) (hnot : p ≠ diracMass 1) :
    ∃ k : ℕ, 2 ≤ k ∧ 0 < p k := by
  by_contra hexists
  push_neg at hexists
  have htail : ∀ k : ℕ, 2 ≤ k → p k = 0 := by
    intro k hk
    exact le_antisymm (hexists k hk) (p.nonneg k)
  have hmomentZero : tiltedMoment 2 0 p = p 0 + 2 * p 1 := by
    rw [tiltedMoment, tsum_eq_sum (s := Finset.range 2)]
    · norm_num [Finset.sum_range_succ]
    · intro k hk
      simp only [Finset.mem_range, not_lt] at hk
      rw [htail k hk]
      ring
  have hmomentOne : tiltedMoment 2 1 p = 2 * p 1 := by
    rw [tiltedMoment, tsum_eq_sum (s := Finset.range 2)]
    · norm_num [Finset.sum_range_succ]
    · intro k hk
      simp only [Finset.mem_range, not_lt] at hk
      rw [htail k hk]
      ring
  have hpZero : p 0 = 0 := by
    have heq := hcrit.2.2
    rw [hmomentZero, hmomentOne] at heq
    norm_num at heq ⊢
    linarith
  have hmass : p 0 + p 1 = 1 := by
    have htotal := p.tsum_eq_one
    rw [tsum_eq_sum (s := Finset.range 2)] at htotal
    · norm_num [Finset.sum_range_succ] at htotal ⊢
      exact htotal
    · intro k hk
      simp only [Finset.mem_range, not_lt] at hk
      exact htail k hk
  have hpOne : p 1 = 1 := by linarith
  apply hnot
  apply ProbabilityMass.ext
  intro k
  by_cases hkZero : k = 0
  · subst k
    simp [hpZero]
  by_cases hkOne : k = 1
  · subst k
    simp [hpOne]
  have hk : 2 ≤ k := by omega
  rw [htail k hk]
  simp [hkOne]

/-- The excluded binary fixed point is exactly the remaining positivity obstruction. -/
theorem normalizedCubicMoment_two_pos_of_not_fixed
    (p : ProbabilityMass) (hcrit : Critical 2 p) (hthird : TiltSummable 2 3 p)
    (hnot : p ≠ diracMass 1) :
    0 < normalizedCubicMoment 2 p := by
  rcases exists_mass_ge_two_of_critical_two_not_fixed p hcrit hnot with
    ⟨k, hk, hpk⟩
  exact normalizedCubicMoment_two_pos_of_mass p hcrit hthird k hk hpk

/-- Every admissible profile datum has a finite, strictly positive initial `J`. -/
theorem normalizedCubicMoment_pos_of_profileInitialData
    (m : ℕ) (data : ProfileInitialData m) :
    0 < normalizedCubicMoment m data.law := by
  by_cases hmTwo : m = 2
  · subst m
    apply normalizedCubicMoment_two_pos_of_not_fixed data.law data.critical data.third
    intro hfixed
    exact data.notBinaryFixedPoint ⟨rfl, hfixed⟩
  · have hmLower : 2 ≤ m := data.arity
    have hmThree : 3 ≤ m := by omega
    exact normalizedCubicMoment_pos_of_three_le m data.law hmThree
      data.critical data.third

/-- Consequently `J_n` is positive at every finite generation of profile data. -/
theorem normalizedCubicMoment_profile_orbit_pos
    (m : ℕ) (data : ProfileInitialData m) (n : ℕ) :
    0 < normalizedCubicMoment m (orbit m data.law n) :=
  normalizedCubicMoment_orbit_pos m data.law data.arity data.critical data.third
    (normalizedCubicMoment_pos_of_profileInitialData m data) n

/-- The source binary third-moment comparison, with its unavoidable atom at one. -/
theorem normalizedTilt_cube_tsum_le_four_thirds_mul_cubicMoment_add_atom_one
    (p : ProbabilityMass) (hcrit : Critical 2 p) (hthird : TiltSummable 2 3 p) :
    (∑' k : ℕ, (k : ℝ) ^ 3 * normalizedTilt 2 p k) ≤
      (4 / 3 : ℝ) * normalizedCubicMoment 2 p + normalizedTilt 2 p 1 := by
  have hcube := normalizedTilt_cube_summable 2 p hthird
  have hcarrier := normalizedCubicMoment_hasSum 2 p (by norm_num) hcrit hthird
  have hatom :
      HasSum (fun k : ℕ ↦ if k = 1 then normalizedTilt 2 p 1 else 0)
        (normalizedTilt 2 p 1) :=
    hasSum_ite_eq 1 (normalizedTilt 2 p 1)
  have hrhs :
      HasSum
        (fun k : ℕ ↦
          (4 / 3 : ℝ) * (cubicCarrier 2 k * normalizedTilt 2 p k) +
            if k = 1 then normalizedTilt 2 p 1 else 0)
        ((4 / 3 : ℝ) * normalizedCubicMoment 2 p + normalizedTilt 2 p 1) :=
    (hcarrier.mul_left (4 / 3 : ℝ)).add hatom
  calc
    (∑' k : ℕ, (k : ℝ) ^ 3 * normalizedTilt 2 p k) ≤
        ∑' k : ℕ,
          ((4 / 3 : ℝ) * (cubicCarrier 2 k * normalizedTilt 2 p k) +
            if k = 1 then normalizedTilt 2 p 1 else 0) := by
      apply hcube.tsum_le_tsum _ hrhs.summable
      intro k
      have hq := normalizedTilt_nonneg 2 p (by norm_num) hcrit k
      have hbase := cube_le_four_thirds_mul_cubicCarrier_two_add_indicator k
      calc
        (k : ℝ) ^ 3 * normalizedTilt 2 p k ≤
            ((4 / 3 : ℝ) * cubicCarrier 2 k + if k = 1 then 1 else 0) *
              normalizedTilt 2 p k := mul_le_mul_of_nonneg_right hbase hq
        _ = (4 / 3 : ℝ) * (cubicCarrier 2 k * normalizedTilt 2 p k) +
              if k = 1 then normalizedTilt 2 p 1 else 0 := by
          by_cases hk : k = 1
          · simp [hk]
          · simp [hk]
            ring
    _ = (4 / 3 : ℝ) * normalizedCubicMoment 2 p + normalizedTilt 2 p 1 :=
      hrhs.tsum_eq

end

end DerridaRetaux
