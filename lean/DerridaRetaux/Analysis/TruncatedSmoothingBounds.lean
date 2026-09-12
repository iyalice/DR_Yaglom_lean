import DerridaRetaux.Analysis.CoefficientVariation
import DerridaRetaux.Analysis.LogSmoothingArithmetic
import DerridaRetaux.Analysis.PointwiseFromFar
import DerridaRetaux.Analysis.TruncatedTelescope
import Mathlib.Tactic

/-!
# Bounds for the concrete truncated smoothing decomposition

This module connects the exact `I/Q/W/V` decomposition in `TruncatedTelescope` to the
weighted estimates used by `LogSmoothingArithmetic`.  The two published H1 facts and the
pointwise estimate remain explicit theorem parameters.
-/

set_option autoImplicit false

open scoped BigOperators

namespace DerridaRetaux

noncomputable section

/-- Every interval product of critical-orbit transport coefficients is nonnegative. -/
theorem transportBetween_orbit_nonneg
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m) (hcrit : Critical m p₀)
    (a n : ℕ) :
    0 ≤ transportBetween (fun s ↦ transportCoeff m (orbit m p₀ s)) a n := by
  apply Finset.prod_nonneg
  intro s _hs
  exact transportCoeff_nonneg m (orbit m p₀ s) (by omega)
    (orbit_critical m p₀ (by omega) hcrit s)

/-- Every interval product of critical-orbit transport coefficients is at most one. -/
theorem transportBetween_orbit_le_one
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m) (hcrit : Critical m p₀)
    (a n : ℕ) :
    transportBetween (fun s ↦ transportCoeff m (orbit m p₀ s)) a n ≤ 1 := by
  apply Finset.prod_le_one
  · intro s _hs
    exact transportCoeff_nonneg m (orbit m p₀ s) (by omega)
      (orbit_critical m p₀ (by omega) hcrit s)
  · intro s _hs
    exact transportCoeff_le_one m (orbit m p₀ s) (by omega)
      (orbit_critical m p₀ (by omega) hcrit s)

/-- Absolute-value form of the preceding interval-product bound. -/
theorem abs_transportBetween_orbit_le_one
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m) (hcrit : Critical m p₀)
    (a n : ℕ) :
    |transportBetween (fun s ↦ transportCoeff m (orbit m p₀ s)) a n| ≤ 1 := by
  rw [abs_of_nonneg (transportBetween_orbit_nonneg m p₀ hm hcrit a n)]
  exact transportBetween_orbit_le_one m p₀ hm hcrit a n

/-- The zero sequence satisfies every nonnegative weighted supremum bound. -/
theorem weightedSupThree_zero (L C : ℝ) (hC : 0 ≤ C) :
    WeightedSupThreeLE L (0 : Seq) C := by
  intro j
  simpa using hC

@[simp]
theorem discreteDerivative_zero : discreteDerivative (0 : Seq) = 0 := by
  funext j
  simp [discreteDerivative]

/-- The transported homogeneous term has the exact early-time size required by the
logarithmic smoothing split. -/
theorem densityInitialSegment_weightedSup_bound
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m) (hcrit : Critical m p₀)
    (B : ℝ) (hB : 0 ≤ B)
    (hSup : ∀ s : ℕ,
      WeightedSupThreeLE (profileScale s)
        (positiveTiltedDensity m (orbit m p₀ s))
        (B / profileScale s ^ 2))
    {a n : ℕ} (_han : a ≤ n) (hn : 2 ≤ n) :
    WeightedSupThreeLE (profileScale n) (densityInitialSegment m p₀ a n)
      (27 * B / profileScale n ^ 3 * ((a + 1 : ℕ) : ℝ)) := by
  have hshift := weightedSupThree_shiftLeft_iterate_gain
    a n (n - a) (B / profileScale a ^ 2) hn (by omega)
    (positiveTiltedDensity m (orbit m p₀ a)) (hSup a)
  have hscaled := weightedSupThree_smul (profileScale n)
    (27 * (profileScale a / profileScale n) ^ 3 *
      (B / profileScale a ^ 2))
    (transportBetween (fun s ↦ transportCoeff m (orbit m p₀ s)) a n)
    ((shiftLeft^[n - a]) (positiveTiltedDensity m (orbit m p₀ a))) hshift
  rw [densityInitialSegment, truncatedInitialTerm]
  apply weightedSupThree_mono (profileScale n) _ _ _ hscaled
  have htransport := abs_transportBetween_orbit_le_one m p₀ hm hcrit a n
  have hsource :
      0 ≤ 27 * (profileScale a / profileScale n) ^ 3 *
        (B / profileScale a ^ 2) := by
    exact mul_nonneg
      (mul_nonneg (by norm_num)
        (pow_nonneg (div_nonneg (profileScale_pos a).le (profileScale_pos n).le) 3))
      (div_nonneg hB (sq_nonneg _))
  calc
    |transportBetween (fun s ↦ transportCoeff m (orbit m p₀ s)) a n| *
          (27 * (profileScale a / profileScale n) ^ 3 *
            (B / profileScale a ^ 2)) ≤
        1 * (27 * (profileScale a / profileScale n) ^ 3 *
          (B / profileScale a ^ 2)) :=
      mul_le_mul_of_nonneg_right htransport hsource
    _ = 27 * B / profileScale n ^ 3 * ((a + 1 : ℕ) : ℝ) := by
      have ha : profileScale a = ((a + 1 : ℕ) : ℝ) := rfl
      have hLa : profileScale a ≠ 0 := (profileScale_pos a).ne'
      have hLn : profileScale n ≠ 0 := (profileScale_pos n).ne'
      rw [ha]
      field_simp
      ring

/-- For the finitely many terminal generations `n<4`, the unsplit density itself obeys
the early estimate after enlarging the constant by four. -/
theorem positiveTiltedDensity_small_weightedSup_bound
    (m : ℕ) (p₀ : ProbabilityMass) (B : ℝ) (hB : 0 ≤ B)
    (hSup : ∀ s : ℕ,
      WeightedSupThreeLE (profileScale s)
        (positiveTiltedDensity m (orbit m p₀ s))
        (B / profileScale s ^ 2))
    {a n : ℕ} (_ha : a ≤ n / 2) (hn : n < 4) :
    WeightedSupThreeLE (profileScale n)
      (positiveTiltedDensity m (orbit m p₀ n))
      (4 * B / profileScale n ^ 3 * ((a + 1 : ℕ) : ℝ)) := by
  apply weightedSupThree_mono (profileScale n) (B / profileScale n ^ 2) _ _ (hSup n)
  have hLn : 0 < profileScale n := profileScale_pos n
  have hscale : profileScale n ≤ 4 * ((a + 1 : ℕ) : ℝ) := by
    dsimp only [profileScale]
    exact_mod_cast (show n + 1 ≤ 4 * (a + 1) by omega)
  have hden : 0 < profileScale n ^ 3 := pow_pos hLn 3
  have hnum : B * profileScale n ≤ B * (4 * ((a + 1 : ℕ) : ℝ)) :=
    mul_le_mul_of_nonneg_left hscale hB
  calc
    B / profileScale n ^ 2 =
        (B * profileScale n) / profileScale n ^ 3 := by
      field_simp
      ring
    _ ≤ (B * (4 * ((a + 1 : ℕ) : ℝ))) / profileScale n ^ 3 :=
      div_le_div_of_nonneg_right hnum hden.le
    _ = 4 * B / profileScale n ^ 3 * ((a + 1 : ℕ) : ℝ) := by ring

/-- The higher-order Duhamel term is a literal finite weighted kernel sum. -/
theorem densityHigherSegment_eq_weightedKernelSum
    (m : ℕ) (p₀ : ProbabilityMass) (a n : ℕ) :
    densityHigherSegment m p₀ a n =
      weightedKernelSum
        (fun s ↦ terminalTransportWeight
          (fun i ↦ transportCoeff m (orbit m p₀ i)) s n)
        (fun s ↦ (shiftLeft^[n - 1 - s]) (densityE m p₀ s)) a n := by
  funext j
  simp [densityHigherSegment, truncatedForcingTerm, weightedKernelSum_apply]

/-- A shifted order-four `E_s` source contributes an order-three harmonic summand after
taking one discrete derivative at terminal scale. -/
theorem densityHigherSegment_derivative_weightedSup_bound
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m) (hcrit : Critical m p₀)
    (CE : ℝ) (hCE : 0 ≤ CE)
    (hE : ∀ s : ℕ,
      WeightedSupThreeLE (profileScale s) (densityE m p₀ s)
        (CE / profileScale s ^ 4))
    {a n : ℕ} (_han : a ≤ n) (hn : 2 ≤ n) :
    WeightedSupThreeLE (profileScale n)
      (discreteDerivative (densityHigherSegment m p₀ a n))
      (54 * CE / profileScale n ^ 3 *
        ∑ s ∈ Finset.Ico a n, (profileScale s)⁻¹) := by
  rw [densityHigherSegment_eq_weightedKernelSum,
    discreteDerivative_weightedKernelSum]
  let c : ℕ → ℝ := fun s ↦ transportCoeff m (orbit m p₀ s)
  let termBound : ℕ → ℝ := fun s ↦
    54 * CE / profileScale n ^ 3 * (profileScale s)⁻¹
  have hterm : ∀ s ∈ Finset.Ico a n,
      WeightedSupThreeLE (profileScale n)
        (terminalTransportWeight c s n •
          discreteDerivative ((shiftLeft^[n - 1 - s]) (densityE m p₀ s)))
        (termBound s) := by
    intro s hs
    have hsn : s < n := (Finset.mem_Ico.mp hs).2
    have hshift := weightedSupThree_shiftLeft_iterate_gain
      s n (n - 1 - s) (CE / profileScale s ^ 4) hn (by omega)
      (densityE m p₀ s) (hE s)
    have hderiv := weightedSupThree_discreteDerivative
      (profileScale n)
      (27 * (profileScale s / profileScale n) ^ 3 *
        (CE / profileScale s ^ 4))
      (profileScale_pos n)
      ((shiftLeft^[n - 1 - s]) (densityE m p₀ s)) hshift
    have hscaled := weightedSupThree_smul (profileScale n)
      (2 * (27 * (profileScale s / profileScale n) ^ 3 *
        (CE / profileScale s ^ 4)))
      (terminalTransportWeight c s n)
      (discreteDerivative ((shiftLeft^[n - 1 - s]) (densityE m p₀ s))) hderiv
    apply weightedSupThree_mono (profileScale n) _ (termBound s) _ hscaled
    have hweight : |terminalTransportWeight c s n| ≤ 1 := by
      simpa only [c, terminalTransportWeight] using
        abs_transportBetween_orbit_le_one m p₀ hm hcrit (s + 1) n
    have hbase :
        0 ≤ 2 * (27 * (profileScale s / profileScale n) ^ 3 *
          (CE / profileScale s ^ 4)) := by
      exact mul_nonneg (by norm_num)
        (mul_nonneg
          (mul_nonneg (by norm_num)
            (pow_nonneg (div_nonneg (profileScale_pos s).le
              (profileScale_pos n).le) 3))
          (div_nonneg hCE (pow_nonneg (profileScale_pos s).le 4)))
    calc
      |terminalTransportWeight c s n| *
          (2 * (27 * (profileScale s / profileScale n) ^ 3 *
            (CE / profileScale s ^ 4))) ≤
        1 * (2 * (27 * (profileScale s / profileScale n) ^ 3 *
          (CE / profileScale s ^ 4))) :=
        mul_le_mul_of_nonneg_right hweight hbase
      _ = termBound s := by
        dsimp only [termBound]
        have hLs : profileScale s ≠ 0 := (profileScale_pos s).ne'
        have hLn : profileScale n ≠ 0 := (profileScale_pos n).ne'
        field_simp
        ring
  have hsum := weightedSupThree_finset_sum (Finset.Ico a n)
    (profileScale n) termBound
    (fun s ↦ terminalTransportWeight c s n •
      discreteDerivative ((shiftLeft^[n - 1 - s]) (densityE m p₀ s)))
    (profileScale_pos n) hterm
  apply weightedSupThree_mono (profileScale n) _ _ _ hsum
  dsimp only [termBound]
  rw [Finset.mul_sum]

/-- Terminal-scale shift gain for an order-three source term. -/
theorem weightedSupThree_shift_order_three
    (s n d : ℕ) (C : ℝ) (_hC : 0 ≤ C) (hn : 2 ≤ n)
    (hd : n - 2 - s ≤ d) (f : Seq)
    (hf : WeightedSupThreeLE (profileScale s) f (C / profileScale s ^ 3)) :
    WeightedSupThreeLE (profileScale n) ((shiftLeft^[d]) f)
      (27 * C / profileScale n ^ 3) := by
  have hshift := weightedSupThree_shiftLeft_iterate_gain
    s n d (C / profileScale s ^ 3) hn hd f hf
  have heq :
      27 * (profileScale s / profileScale n) ^ 3 *
          (C / profileScale s ^ 3) =
        27 * C / profileScale n ^ 3 := by
    field_simp [profileScale]
    ring
  rw [← heq]
  exact hshift

/-- Terminal-scale shift gain for an order-four source term. -/
theorem weightedSupThree_shift_order_four
    (s n d : ℕ) (C : ℝ) (_hC : 0 ≤ C) (hn : 2 ≤ n)
    (hd : n - 2 - s ≤ d) (f : Seq)
    (hf : WeightedSupThreeLE (profileScale s) f (C / profileScale s ^ 4)) :
    WeightedSupThreeLE (profileScale n) ((shiftLeft^[d]) f)
      (27 * C / profileScale n ^ 3 * (profileScale s)⁻¹) := by
  have hshift := weightedSupThree_shiftLeft_iterate_gain
    s n d (C / profileScale s ^ 4) hn hd f hf
  have heq :
      27 * (profileScale s / profileScale n) ^ 3 *
          (C / profileScale s ^ 4) =
        27 * C / profileScale n ^ 3 * (profileScale s)⁻¹ := by
    field_simp [profileScale]
    ring
  rw [← heq]
  exact hshift

/-- The actual transported quadratic kernel has a terminal-scale order-three bound. -/
theorem densityQuadraticKernel_weightedSup_bound
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m) (hcrit : Critical m p₀)
    (hthird : TiltSummable m 3 p₀)
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hL1 : ∀ s : ℕ,
      weightedL1Three (profileScale s)
          (positiveTiltedDensity m (orbit m p₀ s)) ≤ A / profileScale s)
    (hSup : ∀ s : ℕ,
      WeightedSupThreeLE (profileScale s)
        (positiveTiltedDensity m (orbit m p₀ s))
        (B / profileScale s ^ 2))
    {s n : ℕ} (hn : 2 ≤ n) :
    WeightedSupThreeLE (profileScale n) (densityQuadraticKernel m p₀ n s)
      (27 * (B * A) / profileScale n ^ 3) := by
  have hpowers := weightedConvolutionPowers_orbit_bounds
    m p₀ hm hcrit hthird A B hA hB hL1 hSup
  have hBsource : WeightedSupThreeLE (profileScale s) (densityB m p₀ s)
      ((B * A) / profileScale s ^ 3) := by
    have hraw := (hpowers s 1).2
    have hraw' : WeightedSupThreeLE (profileScale s) (densityB m p₀ s)
        ((B / profileScale s ^ 2) * (A / profileScale s)) := by
      simpa only [profileScale, one_add_one_eq_two, pow_one, densityB,
        convPow_two_eq] using hraw
    apply weightedSupThree_mono (profileScale s) _ _ _ hraw'
    ring_nf
    exact le_rfl
  exact weightedSupThree_shift_order_three s n (n - 1 - s)
    (B * A) (mul_nonneg hB hA) hn (by omega) (densityB m p₀ s) hBsource

/-- The scalar quadratic Duhamel weight is uniformly bounded by the binomial
coefficient `choose m 2`. -/
theorem abs_densityQuadraticWeight_le
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m) (hcrit : Critical m p₀)
    (s n : ℕ) :
    |densityQuadraticWeight m p₀ s n| ≤ (Nat.choose m 2 : ℝ) := by
  rw [densityQuadraticWeight, abs_mul]
  have htransport := abs_transportBetween_orbit_le_one m p₀ hm hcrit (s + 1) n
  have hd := (smoothing_coefficients_orbit_bounds m p₀ hm hcrit s).2
  calc
    |terminalTransportWeight
          (fun i ↦ transportCoeff m (orbit m p₀ i)) s n| *
        |densityD m p₀ s| ≤ 1 * |densityD m p₀ s| :=
      mul_le_mul_of_nonneg_right (by
        simpa only [terminalTransportWeight] using htransport) (abs_nonneg _)
    _ ≤ (Nat.choose m 2 : ℝ) := by simpa using hd

/-- Removing the left endpoint of a terminal transport interval exposes one factor. -/
theorem terminalTransportWeight_prev
    (c : ℕ → ℝ) {s n : ℕ} (hs : 1 ≤ s) (hsn : s < n) :
    terminalTransportWeight c (s - 1) n = c s * terminalTransportWeight c s n := by
  unfold terminalTransportWeight transportBetween
  rw [Nat.sub_add_cancel hs]
  exact Finset.prod_eq_prod_Ico_succ_bot hsn c

/-- Changing a reciprocal-square denominator from `s` to `s+1` costs at most four. -/
theorem div_nat_sq_le_four_div_succ_sq
    (C : ℝ) (hC : 0 ≤ C) {s : ℕ} (hs : 1 ≤ s) :
    C / (s : ℝ) ^ 2 ≤ 4 * C / profileScale s ^ 2 := by
  have hsPos : (0 : ℝ) < (s : ℝ) := by exact_mod_cast Nat.zero_lt_of_lt hs
  have hLs : (0 : ℝ) < profileScale s := profileScale_pos s
  have hscale : profileScale s ≤ 2 * (s : ℝ) := by
    dsimp only [profileScale]
    exact_mod_cast (show s + 1 ≤ 2 * s by omega)
  have hsq : profileScale s ^ 2 ≤ 4 * (s : ℝ) ^ 2 := by nlinarith
  apply (div_le_div_iff₀ (sq_pos_of_pos hsPos) (sq_pos_of_pos hLs)).2
  nlinarith [mul_le_mul_of_nonneg_left hsq hC]

/-- The transport factor appearing in the quadratic telescope varies at reciprocal-square
speed. -/
theorem abs_one_sub_transport_mul_prev_inv_sq_le
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m) (hcrit : Critical m p₀)
    (hnotBinaryFixedPoint : ¬(m = 2 ∧ p₀ = diracMass 1))
    (K Cv : ℝ) (_hK : 0 < K) (hCv : 0 ≤ Cv)
    (hinv : ∀ r : ℕ, (transportCoeff m (orbit m p₀ r))⁻¹ ≤ K)
    (hdefect : ∀ r : ℕ,
      |1 - transportCoeff m (orbit m p₀ r)| ≤ Cv / profileScale r ^ 2)
    {s : ℕ} (hs : 1 ≤ s) :
    |1 - transportCoeff m (orbit m p₀ s) *
        (transportCoeff m (orbit m p₀ (s - 1)))⁻¹ ^ 2| ≤
      9 * K ^ 2 * Cv / profileScale s ^ 2 := by
  let cs : ℝ := transportCoeff m (orbit m p₀ s)
  let cp : ℝ := transportCoeff m (orbit m p₀ (s - 1))
  have hcs0 : 0 ≤ cs := by
    dsimp only [cs]
    exact transportCoeff_nonneg m (orbit m p₀ s) (by omega)
      (orbit_critical m p₀ (by omega) hcrit s)
  have hcs1 : cs ≤ 1 := by
    dsimp only [cs]
    exact transportCoeff_le_one m (orbit m p₀ s) (by omega)
      (orbit_critical m p₀ (by omega) hcrit s)
  have hcp0 : 0 ≤ cp := by
    dsimp only [cp]
    exact transportCoeff_nonneg m (orbit m p₀ (s - 1)) (by omega)
      (orbit_critical m p₀ (by omega) hcrit (s - 1))
  have hcp1 : cp ≤ 1 := by
    dsimp only [cp]
    exact transportCoeff_le_one m (orbit m p₀ (s - 1)) (by omega)
      (orbit_critical m p₀ (by omega) hcrit (s - 1))
  have hcpPos : 0 < cp := by
    dsimp only [cp]
    exact transportCoeff_pos m (orbit m p₀ (s - 1)) (by omega)
      (orbit_critical m p₀ (by omega) hcrit (s - 1))
      (orbit_zeroTilt_pos m p₀ hm hcrit hnotBinaryFixedPoint (s - 1))
  have hinvAbs : |cp⁻¹| ≤ K := by
    rw [abs_of_pos (inv_pos.mpr hcpPos)]
    simpa only [cp] using hinv (s - 1)
  have hinvSq : |cp⁻¹ ^ 2| ≤ K ^ 2 := by
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) hinvAbs 2
  have hcsDefect : |1 - cs| ≤ Cv / profileScale s ^ 2 := by
    simpa only [cs] using hdefect s
  have hcpDefectRaw : |1 - cp| ≤ Cv / (s : ℝ) ^ 2 := by
    simpa only [cp, profileScale, Nat.sub_add_cancel hs] using hdefect (s - 1)
  have hcpDefect : |1 - cp| ≤ 4 * Cv / profileScale s ^ 2 :=
    hcpDefectRaw.trans (div_nat_sq_le_four_div_succ_sq Cv hCv hs)
  have honePlus : |1 + cp| ≤ 2 := by
    rw [abs_of_nonneg (by linarith)]
    linarith
  have hsecondEq :
      |1 - cp⁻¹ ^ 2| = |1 - cp| * |1 + cp| * |cp⁻¹ ^ 2| := by
    have hid : 1 - cp⁻¹ ^ 2 = -((1 - cp) * (1 + cp) * cp⁻¹ ^ 2) := by
      field_simp [hcpPos.ne']
      ring
    rw [hid, abs_neg, abs_mul, abs_mul]
  have hfirst :
      |(1 - cs) * cp⁻¹ ^ 2| ≤
        (Cv / profileScale s ^ 2) * K ^ 2 := by
    rw [abs_mul]
    exact mul_le_mul hcsDefect hinvSq (abs_nonneg _) (by positivity)
  have hsecond :
      |1 - cp⁻¹ ^ 2| ≤
        (4 * Cv / profileScale s ^ 2) * 2 * K ^ 2 := by
    rw [hsecondEq]
    exact mul_le_mul
      (mul_le_mul hcpDefect honePlus (abs_nonneg _) (by positivity))
      hinvSq (by positivity) (by positivity)
  have hdecomp :
      1 - cs * cp⁻¹ ^ 2 = (1 - cs) * cp⁻¹ ^ 2 + (1 - cp⁻¹ ^ 2) := by ring
  rw [hdecomp]
  calc
    |(1 - cs) * cp⁻¹ ^ 2 + (1 - cp⁻¹ ^ 2)| ≤
        |(1 - cs) * cp⁻¹ ^ 2| + |1 - cp⁻¹ ^ 2| := abs_add_le _ _
    _ ≤ (Cv / profileScale s ^ 2) * K ^ 2 +
        (4 * Cv / profileScale s ^ 2) * 2 * K ^ 2 := add_le_add hfirst hsecond
    _ = 9 * K ^ 2 * Cv / profileScale s ^ 2 := by ring

/-- Numerator for the interior coefficient variation in the quadratic telescope. -/
def densityQuadraticWeightVariationConstant (m : ℕ) (K Cv : ℝ) : ℝ :=
  Cv * (1 + 9 * (Nat.choose m 2 : ℝ) * K ^ 2)

theorem densityQuadraticWeightVariationConstant_nonneg
    (m : ℕ) (K Cv : ℝ) (hCv : 0 ≤ Cv) :
    0 ≤ densityQuadraticWeightVariationConstant m K Cv := by
  unfold densityQuadraticWeightVariationConstant
  positivity

/-- The exact interior coefficient in `eq:telescope` has reciprocal-square variation. -/
theorem abs_densityQuadraticWeight_telescopeCoeff_le
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m) (hcrit : Critical m p₀)
    (hnotBinaryFixedPoint : ¬(m = 2 ∧ p₀ = diracMass 1))
    (K Cv : ℝ) (hK : 0 < K) (hCv : 0 ≤ Cv)
    (hinv : ∀ r : ℕ, (transportCoeff m (orbit m p₀ r))⁻¹ ≤ K)
    (hdefect : ∀ r : ℕ,
      |1 - transportCoeff m (orbit m p₀ r)| ≤ Cv / profileScale r ^ 2)
    (hdVariation : ∀ r : ℕ, 1 ≤ r →
      |densityD m p₀ r - densityD m p₀ (r - 1)| ≤ Cv / profileScale r ^ 2)
    {s n : ℕ} (hs : 1 ≤ s) (hsn : s < n) :
    |densityQuadraticWeight m p₀ s n -
        densityQuadraticWeight m p₀ (s - 1) n *
          (transportCoeff m (orbit m p₀ (s - 1)))⁻¹ ^ 2| ≤
      densityQuadraticWeightVariationConstant m K Cv / profileScale s ^ 2 := by
  let c : ℕ → ℝ := fun r ↦ transportCoeff m (orbit m p₀ r)
  let P : ℝ := terminalTransportWeight c s n
  let cs : ℝ := c s
  let cp : ℝ := c (s - 1)
  let ds : ℝ := densityD m p₀ s
  let dp : ℝ := densityD m p₀ (s - 1)
  have hidentity :
      densityQuadraticWeight m p₀ s n -
          densityQuadraticWeight m p₀ (s - 1) n * cp⁻¹ ^ 2 =
        P * (ds - cs * cp⁻¹ ^ 2 * dp) := by
    rw [densityQuadraticWeight, densityQuadraticWeight]
    change terminalTransportWeight c s n * ds -
        terminalTransportWeight c (s - 1) n * dp * cp⁻¹ ^ 2 = _
    rw [terminalTransportWeight_prev c hs hsn]
    dsimp only [P, cs]
    ring
  rw [show transportCoeff m (orbit m p₀ (s - 1)) = cp by rfl, hidentity, abs_mul]
  have hP : |P| ≤ 1 := by
    dsimp only [P, c]
    simpa only [terminalTransportWeight] using
      abs_transportBetween_orbit_le_one m p₀ hm hcrit (s + 1) n
  have htransport :
      |1 - cs * cp⁻¹ ^ 2| ≤ 9 * K ^ 2 * Cv / profileScale s ^ 2 := by
    simpa only [cs, cp, c] using
      abs_one_sub_transport_mul_prev_inv_sq_le
        m p₀ hm hcrit hnotBinaryFixedPoint K Cv hK hCv hinv hdefect hs
  have hdp : |dp| ≤ (Nat.choose m 2 : ℝ) := by
    dsimp only [dp]
    exact (smoothing_coefficients_orbit_bounds m p₀ hm hcrit (s - 1)).2
  have hinnerIdentity :
      ds - cs * cp⁻¹ ^ 2 * dp =
        (ds - dp) + dp * (1 - cs * cp⁻¹ ^ 2) := by ring
  have hinner :
      |ds - cs * cp⁻¹ ^ 2 * dp| ≤
        Cv / profileScale s ^ 2 +
          (Nat.choose m 2 : ℝ) *
            (9 * K ^ 2 * Cv / profileScale s ^ 2) := by
    rw [hinnerIdentity]
    calc
      |ds - dp + dp * (1 - cs * cp⁻¹ ^ 2)| ≤
          |ds - dp| + |dp * (1 - cs * cp⁻¹ ^ 2)| := abs_add_le _ _
      _ = |ds - dp| + |dp| * |1 - cs * cp⁻¹ ^ 2| := by rw [abs_mul]
      _ ≤ Cv / profileScale s ^ 2 +
          (Nat.choose m 2 : ℝ) *
            (9 * K ^ 2 * Cv / profileScale s ^ 2) :=
        add_le_add (by simpa only [ds, dp] using hdVariation s hs)
          (mul_le_mul hdp htransport (abs_nonneg _) (by positivity))
  have htarget :
      Cv / profileScale s ^ 2 +
          (Nat.choose m 2 : ℝ) *
            (9 * K ^ 2 * Cv / profileScale s ^ 2) =
        densityQuadraticWeightVariationConstant m K Cv / profileScale s ^ 2 := by
    unfold densityQuadraticWeightVariationConstant
    ring
  rw [← htarget]
  exact (mul_le_mul_of_nonneg_right hP (abs_nonneg _)).trans (by
    simpa only [one_mul] using hinner)

/-- Weighted pointwise bounds subtract with the sum of the two witnesses. -/
theorem weightedSupThree_sub
    (L A B : ℝ) (hL : 0 < L) (f g : Seq)
    (hf : WeightedSupThreeLE L f A) (hg : WeightedSupThreeLE L g B) :
    WeightedSupThreeLE L (f - g) (A + B) := by
  intro j
  have hw := cubicWeight_nonneg L hL j
  calc
    cubicWeight L j * |(f - g) j| ≤
        cubicWeight L j * (|f j| + |g j|) := by
      exact mul_le_mul_of_nonneg_left (abs_sub _ _) hw
    _ = cubicWeight L j * |f j| + cubicWeight L j * |g j| := by ring
    _ ≤ A + B := add_le_add (hf j) (hg j)

/-- A scalar bounded in absolute value may replace the exact scalar witness. -/
theorem weightedSupThree_smul_of_abs_le
    (L A C c : ℝ) (hA : 0 ≤ A) (f : Seq)
    (hf : WeightedSupThreeLE L f A) (hc : |c| ≤ C) :
    WeightedSupThreeLE L (c • f) (C * A) := by
  have hscaled := weightedSupThree_smul L A c f hf
  exact weightedSupThree_mono L (|c| * A) (C * A) _ hscaled
    (mul_le_mul_of_nonneg_right hc hA)

/-- The supplied inverse-coefficient bound also controls its squared absolute value. -/
theorem abs_transportCoeff_inv_sq_le
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m) (hcrit : Critical m p₀)
    (hnotBinaryFixedPoint : ¬(m = 2 ∧ p₀ = diracMass 1))
    (K : ℝ) (hinv : ∀ r : ℕ, (transportCoeff m (orbit m p₀ r))⁻¹ ≤ K)
    (r : ℕ) :
    |(transportCoeff m (orbit m p₀ r))⁻¹ ^ 2| ≤ K ^ 2 := by
  have hcPos := transportCoeff_pos m (orbit m p₀ r) (by omega)
    (orbit_critical m p₀ (by omega) hcrit r)
    (orbit_zeroTilt_pos m p₀ hm hcrit hnotBinaryFixedPoint r)
  rw [abs_pow, abs_of_pos (inv_pos.mpr hcPos)]
  exact pow_le_pow_left₀ (inv_nonneg.mpr hcPos.le) (hinv r) 2

/-- A convenient nonnegative numerator for the complete quadratic-segment derivative. -/
def densityQuadraticSegmentDerivativeConstant
    (m : ℕ) (A B K Cv CR : ℝ) : ℝ :=
  let D : ℝ := Nat.choose m 2
  27 * (B * A) * (3 * D + D * K ^ 2 + densityQuadraticWeightVariationConstant m K Cv) +
    27 * D * K ^ 2 * CR

theorem densityQuadraticSegmentDerivativeConstant_nonneg
    (m : ℕ) (A B K Cv CR : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hCv : 0 ≤ Cv) (hCR : 0 ≤ CR) :
    0 ≤ densityQuadraticSegmentDerivativeConstant m A B K Cv CR := by
  have hvar := densityQuadraticWeightVariationConstant_nonneg m K Cv hCv
  unfold densityQuadraticSegmentDerivativeConstant
  dsimp only
  positivity

/-- The concrete quadratic segment has an order-three derivative bound with the only
non-summable accumulation recorded by the finite harmonic sum. -/
theorem densityQuadraticSegment_derivative_weightedSup_bound
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m) (hcrit : Critical m p₀)
    (hthird : TiltSummable m 3 p₀)
    (hnotBinaryFixedPoint : ¬(m = 2 ∧ p₀ = diracMass 1))
    (A B K Cv CR : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hK : 0 < K)
    (hCv : 0 ≤ Cv) (hCR : 0 ≤ CR)
    (hL1 : ∀ s : ℕ,
      weightedL1Three (profileScale s)
          (positiveTiltedDensity m (orbit m p₀ s)) ≤ A / profileScale s)
    (hSup : ∀ s : ℕ,
      WeightedSupThreeLE (profileScale s)
        (positiveTiltedDensity m (orbit m p₀ s))
        (B / profileScale s ^ 2))
    (hinv : ∀ r : ℕ, (transportCoeff m (orbit m p₀ r))⁻¹ ≤ K)
    (hdefect : ∀ r : ℕ,
      |1 - transportCoeff m (orbit m p₀ r)| ≤ Cv / profileScale r ^ 2)
    (hdVariation : ∀ r : ℕ, 1 ≤ r →
      |densityD m p₀ r - densityD m p₀ (r - 1)| ≤ Cv / profileScale r ^ 2)
    (hR : ∀ s : ℕ,
      WeightedSupThreeLE (profileScale s) (densityR m p₀ s)
        (CR / profileScale s ^ 4))
    {a n : ℕ} (hspan : a + 1 < n) (hn : 2 ≤ n) :
    WeightedSupThreeLE (profileScale n)
      (discreteDerivative (densityQuadraticSegment m p₀ a n))
      (densityQuadraticSegmentDerivativeConstant m A B K Cv CR /
        profileScale n ^ 3 *
          (1 + ∑ s ∈ Finset.Ico a n, (profileScale s)⁻¹)) := by
  let L : ℝ := profileScale n
  let D : ℝ := Nat.choose m 2
  let kernelBound : ℝ := 27 * (B * A) / L ^ 3
  let variationBound : ℝ := densityQuadraticWeightVariationConstant m K Cv
  let harmonic : ℝ := ∑ s ∈ Finset.Ico a n, (profileScale s)⁻¹
  let interiorFactor : ℝ := 27 * (B * A) * variationBound / L ^ 3
  let remainderFactor : ℝ := 27 * D * K ^ 2 * CR / L ^ 3
  have hL : 0 < L := by simpa only [L] using profileScale_pos n
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hkernelBound : 0 ≤ kernelBound := by
    dsimp only [kernelBound]
    positivity
  have hvariationBound : 0 ≤ variationBound := by
    dsimp only [variationBound]
    exact densityQuadraticWeightVariationConstant_nonneg m K Cv hCv
  have hInteriorFactor : 0 ≤ interiorFactor := by
    dsimp only [interiorFactor]
    positivity
  have hRemainderFactor : 0 ≤ remainderFactor := by
    dsimp only [remainderFactor]
    positivity
  have hHarmonic : 0 ≤ harmonic := by
    dsimp only [harmonic]
    exact Finset.sum_nonneg fun s _hs ↦ inv_nonneg.mpr (profileScale_pos s).le
  have hkernel : ∀ s : ℕ,
      WeightedSupThreeLE L (densityQuadraticKernel m p₀ n s) kernelBound := by
    intro s
    simpa only [L, kernelBound] using
      densityQuadraticKernel_weightedSup_bound
        m p₀ hm hcrit hthird A B hA hB hL1 hSup (s := s) (n := n) hn
  have hOne :
      WeightedSupThreeLE L
        (densityQuadraticWeight m p₀ a n • densityQuadraticKernel m p₀ n a)
        (D * kernelBound) :=
    weightedSupThree_smul_of_abs_le L kernelBound D
      (densityQuadraticWeight m p₀ a n) hkernelBound
      (densityQuadraticKernel m p₀ n a) (hkernel a)
      (by simpa only [D] using abs_densityQuadraticWeight_le m p₀ hm hcrit a n)
  have hInvSq : ∀ r : ℕ,
      |(transportCoeff m (orbit m p₀ r))⁻¹ ^ 2| ≤ K ^ 2 :=
    abs_transportCoeff_inv_sq_le
      m p₀ hm hcrit hnotBinaryFixedPoint K hinv
  have hTwoScalar :
      |densityQuadraticWeight m p₀ (n - 2) n *
          (transportCoeff m (orbit m p₀ (n - 2)))⁻¹ ^ 2| ≤ D * K ^ 2 := by
    rw [abs_mul]
    exact mul_le_mul
      (by simpa only [D] using
        abs_densityQuadraticWeight_le m p₀ hm hcrit (n - 2) n)
      (hInvSq (n - 2)) (abs_nonneg _) (by positivity)
  have hTwo :
      WeightedSupThreeLE L
        ((densityQuadraticWeight m p₀ (n - 2) n *
            (transportCoeff m (orbit m p₀ (n - 2)))⁻¹ ^ 2) •
          densityQuadraticKernel m p₀ n (n - 1))
        ((D * K ^ 2) * kernelBound) :=
    weightedSupThree_smul_of_abs_le L kernelBound (D * K ^ 2)
      _ hkernelBound _ (hkernel (n - 1)) hTwoScalar
  have hKernelDerivative :
      WeightedSupThreeLE L
        (discreteDerivative (densityQuadraticKernel m p₀ n (n - 1)))
        (2 * kernelBound) :=
    weightedSupThree_discreteDerivative L kernelBound hL _ (hkernel (n - 1))
  have hThree :
      WeightedSupThreeLE L
        (densityQuadraticWeight m p₀ (n - 1) n •
          discreteDerivative (densityQuadraticKernel m p₀ n (n - 1)))
        (D * (2 * kernelBound)) :=
    weightedSupThree_smul_of_abs_le L (2 * kernelBound) D
      _ (mul_nonneg (by norm_num) hkernelBound) _ hKernelDerivative
      (by simpa only [D] using
        abs_densityQuadraticWeight_le m p₀ hm hcrit (n - 1) n)
  let interiorCoeff : ℕ → ℝ := fun s ↦
    densityQuadraticWeight m p₀ s n -
      densityQuadraticWeight m p₀ (s - 1) n *
        (transportCoeff m (orbit m p₀ (s - 1)))⁻¹ ^ 2
  let interiorTermBound : ℕ → ℝ := fun s ↦ interiorFactor * (profileScale s)⁻¹
  have hInteriorTerm : ∀ s ∈ Finset.Ico (a + 1) (n - 1),
      WeightedSupThreeLE L
        (interiorCoeff s • densityQuadraticKernel m p₀ n s)
        (interiorTermBound s) := by
    intro s hs
    have hsBounds := Finset.mem_Ico.mp hs
    have hsOne : 1 ≤ s := by omega
    have hsn : s < n := by omega
    have hcoeff : |interiorCoeff s| ≤ variationBound / profileScale s ^ 2 := by
      simpa only [interiorCoeff, variationBound] using
        abs_densityQuadraticWeight_telescopeCoeff_le
          m p₀ hm hcrit hnotBinaryFixedPoint K Cv hK hCv hinv hdefect hdVariation
          hsOne hsn
    have hscaled := weightedSupThree_smul_of_abs_le L kernelBound
      (variationBound / profileScale s ^ 2) (interiorCoeff s)
      hkernelBound (densityQuadraticKernel m p₀ n s) (hkernel s) hcoeff
    apply weightedSupThree_mono L _ (interiorTermBound s) _ hscaled
    have hInv0 : 0 ≤ (profileScale s)⁻¹ := inv_nonneg.mpr (profileScale_pos s).le
    have hInv1 : (profileScale s)⁻¹ ≤ 1 := by
      exact inv_le_one_of_one_le₀ (by
        dsimp only [profileScale]
        exact_mod_cast Nat.succ_le_succ (Nat.zero_le s))
    have hInvSqLe : (profileScale s)⁻¹ ^ 2 ≤ (profileScale s)⁻¹ := by
      nlinarith [mul_nonneg hInv0 (sub_nonneg.mpr hInv1)]
    have heq :
        (variationBound / profileScale s ^ 2) * kernelBound =
          interiorFactor * (profileScale s)⁻¹ ^ 2 := by
      dsimp only [kernelBound, interiorFactor, L]
      field_simp [profileScale]
      ring
    rw [heq]
    exact mul_le_mul_of_nonneg_left hInvSqLe hInteriorFactor
  have hFourRaw := weightedSupThree_finset_sum
    (Finset.Ico (a + 1) (n - 1)) L interiorTermBound
    (fun s ↦ interiorCoeff s • densityQuadraticKernel m p₀ n s)
    hL hInteriorTerm
  have hInteriorSum :
      (∑ s ∈ Finset.Ico (a + 1) (n - 1), (profileScale s)⁻¹) ≤ harmonic := by
    dsimp only [harmonic]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro s hs
      simp only [Finset.mem_Ico] at hs ⊢
      omega
    · intro s _hs _hnot
      exact inv_nonneg.mpr (profileScale_pos s).le
  have hFour :
      WeightedSupThreeLE L
        (∑ s ∈ Finset.Ico (a + 1) (n - 1),
          interiorCoeff s • densityQuadraticKernel m p₀ n s)
        (interiorFactor * harmonic) := by
    apply weightedSupThree_mono L _ _ _ hFourRaw
    dsimp only [interiorTermBound]
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left hInteriorSum hInteriorFactor
  let remainderScalar : ℕ → ℝ := fun s ↦
    densityQuadraticWeight m p₀ s n *
      (transportCoeff m (orbit m p₀ s))⁻¹ ^ 2
  let remainderTermBound : ℕ → ℝ := fun s ↦ remainderFactor * (profileScale s)⁻¹
  have hRemainderTerm : ∀ s ∈ Finset.Ico a (n - 1),
      WeightedSupThreeLE L
        (remainderScalar s • (shiftLeft^[n - 2 - s]) (densityR m p₀ s))
        (remainderTermBound s) := by
    intro s hs
    have hscalar : |remainderScalar s| ≤ D * K ^ 2 := by
      dsimp only [remainderScalar]
      rw [abs_mul]
      exact mul_le_mul
        (by simpa only [D] using abs_densityQuadraticWeight_le m p₀ hm hcrit s n)
        (hInvSq s) (abs_nonneg _) (by positivity)
    have hshiftR := weightedSupThree_shift_order_four
      s n (n - 2 - s) CR hCR hn (by omega) (densityR m p₀ s) (hR s)
    have hshiftRNonneg :
        0 ≤ 27 * CR / profileScale n ^ 3 * (profileScale s)⁻¹ := by
      exact mul_nonneg
        (div_nonneg (mul_nonneg (by norm_num) hCR)
          (pow_nonneg (profileScale_pos n).le 3))
        (inv_nonneg.mpr (profileScale_pos s).le)
    have hscaled := weightedSupThree_smul_of_abs_le L
      (27 * CR / profileScale n ^ 3 * (profileScale s)⁻¹)
      (D * K ^ 2) (remainderScalar s)
      hshiftRNonneg _ (by simpa only [L] using hshiftR) hscalar
    apply weightedSupThree_mono L _ (remainderTermBound s) _ hscaled
    dsimp only [remainderTermBound, remainderFactor, L, D]
    ring_nf
    exact le_rfl
  have hFiveRaw := weightedSupThree_finset_sum
    (Finset.Ico a (n - 1)) L remainderTermBound
    (fun s ↦ remainderScalar s •
      (shiftLeft^[n - 2 - s]) (densityR m p₀ s)) hL hRemainderTerm
  have hRemainderSum :
      (∑ s ∈ Finset.Ico a (n - 1), (profileScale s)⁻¹) ≤ harmonic := by
    dsimp only [harmonic]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro s hs
      simp only [Finset.mem_Ico] at hs ⊢
      omega
    · intro s _hs _hnot
      exact inv_nonneg.mpr (profileScale_pos s).le
  have hFive :
      WeightedSupThreeLE L
        (∑ s ∈ Finset.Ico a (n - 1), remainderScalar s •
          (shiftLeft^[n - 2 - s]) (densityR m p₀ s))
        (remainderFactor * harmonic) := by
    apply weightedSupThree_mono L _ _ _ hFiveRaw
    dsimp only [remainderTermBound]
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left hRemainderSum hRemainderFactor
  rw [discreteDerivative_densityQuadraticSegment_telescope
    m p₀ hm hcrit hnotBinaryFixedPoint hspan]
  change WeightedSupThreeLE L _ _
  have hTwelve := weightedSupThree_sub L
    (D * kernelBound) ((D * K ^ 2) * kernelBound) hL _ _ hOne hTwo
  have hThroughThree := weightedSupThree_add L
    (D * kernelBound + (D * K ^ 2) * kernelBound)
    (D * (2 * kernelBound)) hL _ _ hTwelve hThree
  have hThroughFour := weightedSupThree_add L
    (D * kernelBound + (D * K ^ 2) * kernelBound + D * (2 * kernelBound))
    (interiorFactor * harmonic) hL _ _ hThroughThree hFour
  have hAll := weightedSupThree_add L
    (D * kernelBound + (D * K ^ 2) * kernelBound + D * (2 * kernelBound) +
      interiorFactor * harmonic)
    (remainderFactor * harmonic) hL _ _ hThroughFour hFive
  have hAll' : WeightedSupThreeLE L
      (densityQuadraticWeight m p₀ a n • densityQuadraticKernel m p₀ n a -
          (densityQuadraticWeight m p₀ (n - 2) n *
            (transportCoeff m (orbit m p₀ (n - 2)))⁻¹ ^ 2) •
              densityQuadraticKernel m p₀ n (n - 1) +
        densityQuadraticWeight m p₀ (n - 1) n •
          discreteDerivative (densityQuadraticKernel m p₀ n (n - 1)) +
        (∑ s ∈ Finset.Ico (a + 1) (n - 1),
          (densityQuadraticWeight m p₀ s n -
            densityQuadraticWeight m p₀ (s - 1) n *
              (transportCoeff m (orbit m p₀ (s - 1)))⁻¹ ^ 2) •
                densityQuadraticKernel m p₀ n s) +
        ∑ s ∈ Finset.Ico a (n - 1),
          densityQuadraticWeight m p₀ s n •
            ((transportCoeff m (orbit m p₀ s))⁻¹ ^ 2 •
              (shiftLeft^[n - 2 - s]) (densityR m p₀ s)))
      (D * kernelBound + (D * K ^ 2) * kernelBound + D * (2 * kernelBound) +
        interiorFactor * harmonic + remainderFactor * harmonic) := by
    simpa only [interiorCoeff, remainderScalar, smul_smul] using hAll
  apply weightedSupThree_mono L _ _ _ hAll'
  let endpointNumerator : ℝ := 27 * (B * A) * (3 * D + D * K ^ 2)
  let harmonicNumerator : ℝ :=
    27 * (B * A) * variationBound + 27 * D * K ^ 2 * CR
  have hEndpointNumerator : 0 ≤ endpointNumerator := by
    dsimp only [endpointNumerator]
    positivity
  have hHarmonicNumerator : 0 ≤ harmonicNumerator := by
    dsimp only [harmonicNumerator]
    positivity
  have hRawEq :
      D * kernelBound + (D * K ^ 2) * kernelBound + D * (2 * kernelBound) +
          interiorFactor * harmonic + remainderFactor * harmonic =
        endpointNumerator / L ^ 3 +
          (harmonicNumerator / L ^ 3) * harmonic := by
    dsimp only [kernelBound, interiorFactor, remainderFactor,
      endpointNumerator, harmonicNumerator]
    ring
  rw [hRawEq]
  have hscalar :
      endpointNumerator + harmonicNumerator * harmonic ≤
        (endpointNumerator + harmonicNumerator) * (1 + harmonic) := by
    calc
      endpointNumerator + harmonicNumerator * harmonic ≤
          endpointNumerator + harmonicNumerator * harmonic +
            (harmonicNumerator + endpointNumerator * harmonic) := by
        exact le_add_of_nonneg_right
          (add_nonneg hHarmonicNumerator
            (mul_nonneg hEndpointNumerator hHarmonic))
      _ = (endpointNumerator + harmonicNumerator) * (1 + harmonic) := by ring
  have hden : 0 ≤ L ^ 3 := pow_nonneg hL.le 3
  calc
    endpointNumerator / L ^ 3 + (harmonicNumerator / L ^ 3) * harmonic =
        (endpointNumerator + harmonicNumerator * harmonic) / L ^ 3 := by ring
    _ ≤ ((endpointNumerator + harmonicNumerator) * (1 + harmonic)) / L ^ 3 :=
      div_le_div_of_nonneg_right hscalar hden
    _ = densityQuadraticSegmentDerivativeConstant m A B K Cv CR /
          profileScale n ^ 3 *
            (1 + ∑ s ∈ Finset.Ico a n, (profileScale s)⁻¹) := by
      dsimp only [endpointNumerator, harmonicNumerator, variationBound, harmonic,
        L, D, densityQuadraticSegmentDerivativeConstant]
      ring

/-- Logarithmic form of the preceding concrete `Q` estimate (`eq:lateQ`). -/
theorem densityQuadraticSegment_derivative_weightedSup_log_bound
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m) (hcrit : Critical m p₀)
    (hthird : TiltSummable m 3 p₀)
    (hnotBinaryFixedPoint : ¬(m = 2 ∧ p₀ = diracMass 1))
    (A B K Cv CR : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hK : 0 < K)
    (hCv : 0 ≤ Cv) (hCR : 0 ≤ CR)
    (hL1 : ∀ s : ℕ,
      weightedL1Three (profileScale s)
          (positiveTiltedDensity m (orbit m p₀ s)) ≤ A / profileScale s)
    (hSup : ∀ s : ℕ,
      WeightedSupThreeLE (profileScale s)
        (positiveTiltedDensity m (orbit m p₀ s))
        (B / profileScale s ^ 2))
    (hinv : ∀ r : ℕ, (transportCoeff m (orbit m p₀ r))⁻¹ ≤ K)
    (hdefect : ∀ r : ℕ,
      |1 - transportCoeff m (orbit m p₀ r)| ≤ Cv / profileScale r ^ 2)
    (hdVariation : ∀ r : ℕ, 1 ≤ r →
      |densityD m p₀ r - densityD m p₀ (r - 1)| ≤ Cv / profileScale r ^ 2)
    (hR : ∀ s : ℕ,
      WeightedSupThreeLE (profileScale s) (densityR m p₀ s)
        (CR / profileScale s ^ 4))
    {a n : ℕ} (han : a ≤ n) (hspan : a + 1 < n) (hn : 2 ≤ n) :
    WeightedSupThreeLE (profileScale n)
      (discreteDerivative (densityQuadraticSegment m p₀ a n))
      (2 * densityQuadraticSegmentDerivativeConstant m A B K Cv CR /
        profileScale n ^ 3 *
          (1 + Real.log (profileScale n / profileScale a))) := by
  let harmonic : ℝ := ∑ s ∈ Finset.Ico a n, (profileScale s)⁻¹
  let logTerm : ℝ := 1 + Real.log (profileScale n / profileScale a)
  let CQ : ℝ := densityQuadraticSegmentDerivativeConstant m A B K Cv CR
  have hQ := densityQuadraticSegment_derivative_weightedSup_bound
    m p₀ hm hcrit hthird hnotBinaryFixedPoint A B K Cv CR hA hB hK hCv hCR
    hL1 hSup hinv hdefect hdVariation hR hspan hn
  have hscale : profileScale a ≤ profileScale n := by
    dsimp only [profileScale]
    exact_mod_cast Nat.succ_le_succ han
  have hratio : 1 ≤ profileScale n / profileScale a :=
    (le_div_iff₀ (profileScale_pos a)).2 (by simpa using hscale)
  have hlog : 0 ≤ Real.log (profileScale n / profileScale a) := Real.log_nonneg hratio
  have hharmonic : harmonic ≤ logTerm := by
    dsimp only [harmonic, logTerm]
    simpa only [profileScale] using
      sum_Ico_inv_nat_succ_le_one_add_log_ratio a n han
  have hCQ : 0 ≤ CQ := by
    dsimp only [CQ]
    exact densityQuadraticSegmentDerivativeConstant_nonneg
      m A B K Cv CR hA hB hCv hCR
  apply weightedSupThree_mono (profileScale n)
    (CQ / profileScale n ^ 3 * (1 + harmonic)) _ _
    (by simpa only [CQ, harmonic] using hQ)
  have hfactor : 0 ≤ CQ / profileScale n ^ 3 :=
    div_nonneg hCQ (pow_nonneg (profileScale_pos n).le 3)
  have hlogTermOne : 1 ≤ logTerm := by
    dsimp only [logTerm]
    linarith
  have honeH : 1 + harmonic ≤ 2 * logTerm := by
    linarith
  calc
    CQ / profileScale n ^ 3 * (1 + harmonic) ≤
        CQ / profileScale n ^ 3 * (2 * logTerm) :=
      mul_le_mul_of_nonneg_left honeH hfactor
    _ = 2 * densityQuadraticSegmentDerivativeConstant m A B K Cv CR /
        profileScale n ^ 3 *
          (1 + Real.log (profileScale n / profileScale a)) := by
      dsimp only [CQ, logTerm]
      ring

@[simp]
theorem discreteDerivative_add (f g : Seq) :
    discreteDerivative (f + g) = discreteDerivative f + discreteDerivative g := by
  funext j
  simp [discreteDerivative]
  ring

/-- Numerator for the derivative of the full late segment `V=Q+W`. -/
def densityLateSegmentDerivativeConstant
    (m : ℕ) (A B K Cv CE CR : ℝ) : ℝ :=
  2 * densityQuadraticSegmentDerivativeConstant m A B K Cv CR + 54 * CE

theorem densityLateSegmentDerivativeConstant_nonneg
    (m : ℕ) (A B K Cv CE CR : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hCv : 0 ≤ Cv)
    (hCE : 0 ≤ CE) (hCR : 0 ≤ CR) :
    0 ≤ densityLateSegmentDerivativeConstant m A B K Cv CE CR := by
  unfold densityLateSegmentDerivativeConstant
  exact add_nonneg
    (mul_nonneg (by norm_num)
      (densityQuadraticSegmentDerivativeConstant_nonneg
        m A B K Cv CR hA hB hCv hCR))
    (mul_nonneg (by norm_num) hCE)

/-- Combining the concrete `Q` telescope and concrete `W` Duhamel sum gives the late
logarithmic derivative estimate. -/
theorem densityLateSegment_derivative_weightedSup_log_bound
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m) (hcrit : Critical m p₀)
    (hthird : TiltSummable m 3 p₀)
    (hnotBinaryFixedPoint : ¬(m = 2 ∧ p₀ = diracMass 1))
    (A B K Cv CE CR : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hK : 0 < K)
    (hCv : 0 ≤ Cv) (hCE : 0 ≤ CE) (hCR : 0 ≤ CR)
    (hL1 : ∀ s : ℕ,
      weightedL1Three (profileScale s)
          (positiveTiltedDensity m (orbit m p₀ s)) ≤ A / profileScale s)
    (hSup : ∀ s : ℕ,
      WeightedSupThreeLE (profileScale s)
        (positiveTiltedDensity m (orbit m p₀ s))
        (B / profileScale s ^ 2))
    (hinv : ∀ r : ℕ, (transportCoeff m (orbit m p₀ r))⁻¹ ≤ K)
    (hdefect : ∀ r : ℕ,
      |1 - transportCoeff m (orbit m p₀ r)| ≤ Cv / profileScale r ^ 2)
    (hdVariation : ∀ r : ℕ, 1 ≤ r →
      |densityD m p₀ r - densityD m p₀ (r - 1)| ≤ Cv / profileScale r ^ 2)
    (hE : ∀ s : ℕ,
      WeightedSupThreeLE (profileScale s) (densityE m p₀ s)
        (CE / profileScale s ^ 4))
    (hR : ∀ s : ℕ,
      WeightedSupThreeLE (profileScale s) (densityR m p₀ s)
        (CR / profileScale s ^ 4))
    {a n : ℕ} (han : a ≤ n) (hspan : a + 1 < n) (hn : 2 ≤ n) :
    WeightedSupThreeLE (profileScale n)
      (discreteDerivative (densityLateSegment m p₀ a n))
      (densityLateSegmentDerivativeConstant m A B K Cv CE CR /
        profileScale n ^ 3 *
          (1 + Real.log (profileScale n / profileScale a))) := by
  let harmonic : ℝ := ∑ s ∈ Finset.Ico a n, (profileScale s)⁻¹
  let logTerm : ℝ := 1 + Real.log (profileScale n / profileScale a)
  let CQ : ℝ := densityQuadraticSegmentDerivativeConstant m A B K Cv CR
  have hHarmonic : 0 ≤ harmonic := by
    dsimp only [harmonic]
    exact Finset.sum_nonneg fun s _hs ↦ inv_nonneg.mpr (profileScale_pos s).le
  have hscale : profileScale a ≤ profileScale n := by
    dsimp only [profileScale]
    exact_mod_cast Nat.succ_le_succ han
  have hratio : 1 ≤ profileScale n / profileScale a :=
    (le_div_iff₀ (profileScale_pos a)).2 (by simpa using hscale)
  have hlog : 0 ≤ Real.log (profileScale n / profileScale a) := Real.log_nonneg hratio
  have hlogTermOne : 1 ≤ logTerm := by dsimp only [logTerm]; linarith
  have hHarmonicLog : harmonic ≤ logTerm := by
    dsimp only [harmonic, logTerm]
    simpa only [profileScale] using
      sum_Ico_inv_nat_succ_le_one_add_log_ratio a n han
  have hQ := densityQuadraticSegment_derivative_weightedSup_bound
    m p₀ hm hcrit hthird hnotBinaryFixedPoint A B K Cv CR hA hB hK hCv hCR
    hL1 hSup hinv hdefect hdVariation hR hspan hn
  have hW := densityHigherSegment_derivative_weightedSup_bound
    m p₀ hm hcrit CE hCE hE han hn
  have hQ' : WeightedSupThreeLE (profileScale n)
      (discreteDerivative (densityQuadraticSegment m p₀ a n))
      (2 * CQ / profileScale n ^ 3 * logTerm) := by
    apply weightedSupThree_mono (profileScale n)
      (CQ / profileScale n ^ 3 * (1 + harmonic)) _ _
      (by simpa only [CQ, harmonic] using hQ)
    have hCQ : 0 ≤ CQ := by
      dsimp only [CQ]
      exact densityQuadraticSegmentDerivativeConstant_nonneg
        m A B K Cv CR hA hB hCv hCR
    have hfactor : 0 ≤ CQ / profileScale n ^ 3 :=
      div_nonneg hCQ (pow_nonneg (profileScale_pos n).le 3)
    have honeH : 1 + harmonic ≤ 2 * logTerm := by linarith
    calc
      CQ / profileScale n ^ 3 * (1 + harmonic) ≤
          CQ / profileScale n ^ 3 * (2 * logTerm) :=
        mul_le_mul_of_nonneg_left honeH hfactor
      _ = 2 * CQ / profileScale n ^ 3 * logTerm := by ring
  have hW' : WeightedSupThreeLE (profileScale n)
      (discreteDerivative (densityHigherSegment m p₀ a n))
      (54 * CE / profileScale n ^ 3 * logTerm) := by
    apply weightedSupThree_mono (profileScale n)
      (54 * CE / profileScale n ^ 3 * harmonic) _ _
      (by simpa only [harmonic] using hW)
    have hfactor : 0 ≤ 54 * CE / profileScale n ^ 3 :=
      div_nonneg (mul_nonneg (by norm_num) hCE)
        (pow_nonneg (profileScale_pos n).le 3)
    exact mul_le_mul_of_nonneg_left hHarmonicLog hfactor
  rw [densityLateSegment, discreteDerivative_add]
  have hadd := weightedSupThree_add (profileScale n)
    (2 * CQ / profileScale n ^ 3 * logTerm)
    (54 * CE / profileScale n ^ 3 * logTerm)
    (profileScale_pos n) _ _ hQ' hW'
  apply weightedSupThree_mono (profileScale n) _ _ _ hadd
  dsimp only [CQ, logTerm, densityLateSegmentDerivativeConstant]
  ring_nf
  exact le_rfl

/-- The coefficientwise pointwise form proved in `PointwiseFromFar` is exactly the
weighted-supremum input used by the smoothing modules. -/
theorem positiveTiltedDensity_weightedSup_of_pointwise
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m) (hcrit : Critical m p₀)
    (B : ℝ) (_hB : 0 ≤ B)
    (hpointwise : ∀ n j : ℕ,
      positiveTiltedDensity m (orbit m p₀ n) j ≤
        B * profileScale n / ((n + j + 1 : ℕ) : ℝ) ^ 3) :
    ∀ n : ℕ, WeightedSupThreeLE (profileScale n)
      (positiveTiltedDensity m (orbit m p₀ n))
      (B / profileScale n ^ 2) := by
  intro n j
  have hncrit := orbit_critical m p₀ (by omega) hcrit n
  have hrho : 0 ≤ positiveTiltedDensity m (orbit m p₀ n) j :=
    positiveTiltedDensity_nonneg m (orbit m p₀ n) (by omega) hncrit j
  rw [abs_of_nonneg hrho]
  have hw : 0 ≤ cubicWeight (profileScale n) j :=
    cubicWeight_nonneg (profileScale n) (profileScale_pos n) j
  calc
    cubicWeight (profileScale n) j * positiveTiltedDensity m (orbit m p₀ n) j ≤
        cubicWeight (profileScale n) j *
          (B * profileScale n / ((n + j + 1 : ℕ) : ℝ) ^ 3) :=
      mul_le_mul_of_nonneg_left (hpointwise n j) hw
    _ = B / profileScale n ^ 2 := by
      unfold cubicWeight profileScale
      field_simp
      ring

/-- Source-facing closure of the concrete early/late split required by
`LogSmoothingArithmetic`.  All constants are extracted from the two explicit H1 facts;
no smoothing estimate is assumed. -/
theorem truncatedSmoothingSplit_of_H1
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p₀) (hthird : TiltSummable m 3 p₀)
    (hnonconstant : ¬ IsDirac p₀)
    (hExcess : CDHLSExcessFact m p₀ hm hcrit hthird hnonconstant)
    (hProduct : CDHLSProductFact m p₀ hm hcrit hnonconstant) :
    ∃ C : ℝ, 0 < C ∧
      (∀ n : ℕ, WeightedSupThreeLE (profileScale n)
        (positiveTiltedDensity m (orbit m p₀ n))
        (C / profileScale n ^ 2)) ∧
      ∀ n a : ℕ, a ≤ n / 2 →
        ∃ early late : Seq,
          positiveTiltedDensity m (orbit m p₀ n) = early + late ∧
          WeightedSupThreeLE (profileScale n) early
            (C / profileScale n ^ 3 * ((a + 1 : ℕ) : ℝ)) ∧
          WeightedSupThreeLE (profileScale n) (discreteDerivative late)
            (C / profileScale n ^ 3 *
              (1 + Real.log (profileScale n / ((a + 1 : ℕ) : ℝ)))) := by
  have hnotBinaryFixedPoint : ¬(m = 2 ∧ p₀ = diracMass 1) := by
    rintro ⟨_hmTwo, hp₀⟩
    exact hnonconstant ⟨1, hp₀⟩
  rcases positiveTiltedDensity_pointwise_of_H1
      m p₀ hm hcrit hthird hnonconstant hExcess hProduct with
    ⟨B, hB, hpointwiseRaw⟩
  have hpointwise : ∀ n j : ℕ,
      positiveTiltedDensity m (orbit m p₀ n) j ≤
        B * profileScale n / ((n + j + 1 : ℕ) : ℝ) ^ 3 := by
    simpa only [profileScale] using hpointwiseRaw
  have hSup := positiveTiltedDensity_weightedSup_of_pointwise
    m p₀ hm hcrit B hB.le hpointwise
  rcases weightedL1Three_orbit_bound
      m p₀ hm hcrit hthird hnonconstant hExcess hProduct with
    ⟨A, hA, hL1Raw⟩
  have hL1 : ∀ s : ℕ,
      weightedL1Three (profileScale s)
          (positiveTiltedDensity m (orbit m p₀ s)) ≤ A / profileScale s := by
    simpa only [profileScale] using hL1Raw
  let CE : ℝ := densityEOrbitSupConstant m A B
  let CR : ℝ := densityROrbitSupConstant m A B
  have hEConstants := densityEOrbitConstants_nonneg m A B hA.le hB.le
  have hCE : 0 ≤ CE := by simpa only [CE] using hEConstants.1
  have hCR : 0 ≤ CR := by
    dsimp only [CR, densityROrbitSupConstant]
    have hD : 0 ≤ (Nat.choose m 2 : ℝ) := by positivity
    have hCESource : 0 ≤ densityEOrbitSupConstant m A B := hEConstants.1
    have hCE1 : 0 ≤ densityEOrbitL1Constant m A := hEConstants.2
    positivity
  have hE : ∀ s : ℕ,
      WeightedSupThreeLE (profileScale s) (densityE m p₀ s)
        (CE / profileScale s ^ 4) := by
    intro s
    simpa only [CE, profileScale] using
      densityE_orbit_weightedSup_order_four
        m p₀ hm hcrit hthird A B hA.le hB.le hL1 hSup s
  have hR : ∀ s : ℕ,
      WeightedSupThreeLE (profileScale s) (densityR m p₀ s)
        (CR / profileScale s ^ 4) := by
    intro s
    simpa only [CR, profileScale] using
      densityR_orbit_weightedSup_order_four
        m p₀ hm hcrit hthird A B hA.le hB.le hL1 hSup s
  rcases coefficientVariation_orbit_of_H1a_and_pointwise
      m p₀ hm hcrit hthird hnonconstant hExcess B hSup with
    ⟨Cv, hCv, _hmass, _hxLimit, _hdLimit, hdefectRaw, _hxVariation, hdVariationRaw⟩
  have hdefect : ∀ s : ℕ,
      |1 - transportCoeff m (orbit m p₀ s)| ≤ Cv / profileScale s ^ 2 := by
    simpa only [profileScale] using hdefectRaw
  have hdVariation : ∀ s : ℕ, 1 ≤ s →
      |densityD m p₀ s - densityD m p₀ (s - 1)| ≤ Cv / profileScale s ^ 2 := by
    simpa only [profileScale] using hdVariationRaw
  have hdefectSummableRaw := orbitTransportDefect_summable
    m p₀ hm hcrit hthird hnonconstant hExcess
  have hdefectSummable :
      Summable (fun s : ℕ ↦ 1 - transportCoeff m (orbit m p₀ s)) := by
    simpa only [orbitTransportDefect] using hdefectSummableRaw
  rcases transportCoeff_inverse_uniform
      m p₀ hm hcrit hnotBinaryFixedPoint hdefectSummable with ⟨K, hK, hinv⟩
  let CLate : ℝ := densityLateSegmentDerivativeConstant m A B K Cv CE CR
  have hCLate : 0 ≤ CLate := by
    dsimp only [CLate]
    exact densityLateSegmentDerivativeConstant_nonneg
      m A B K Cv CE CR hA.le hB.le hCv.le hCE hCR
  let C : ℝ := 1 + 31 * B + CLate
  have hC : 0 < C := by
    dsimp only [C]
    positivity
  have hBLe : B ≤ C := by dsimp only [C]; nlinarith
  have hFourBLe : 4 * B ≤ C := by dsimp only [C]; nlinarith
  have hTwentySevenBLe : 27 * B ≤ C := by dsimp only [C]; nlinarith
  have hCLateLe : CLate ≤ C := by dsimp only [C]; nlinarith
  refine ⟨C, hC, ?_, ?_⟩
  · intro n
    apply weightedSupThree_mono (profileScale n) (B / profileScale n ^ 2)
      (C / profileScale n ^ 2) _ (hSup n)
    exact div_le_div_of_nonneg_right hBLe (pow_nonneg (profileScale_pos n).le 2)
  · intro n a ha
    have han : a ≤ n := by omega
    have hratio : 1 ≤ profileScale n / ((a + 1 : ℕ) : ℝ) := by
      apply (le_div_iff₀ (by positivity : (0 : ℝ) < ((a + 1 : ℕ) : ℝ))).2
      have hcast : (((a + 1 : ℕ) : ℕ) : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
        exact_mod_cast Nat.succ_le_succ han
      simpa only [one_mul, profileScale] using hcast
    have hlogNonneg :
        0 ≤ Real.log (profileScale n / ((a + 1 : ℕ) : ℝ)) := Real.log_nonneg hratio
    by_cases hnSmall : n < 4
    · refine ⟨positiveTiltedDensity m (orbit m p₀ n), 0, by simp, ?_, ?_⟩
      · have hearly := positiveTiltedDensity_small_weightedSup_bound
          m p₀ B hB.le hSup ha hnSmall
        apply weightedSupThree_mono (profileScale n)
          (4 * B / profileScale n ^ 3 * ((a + 1 : ℕ) : ℝ)) _ _ hearly
        have hdiv := div_le_div_of_nonneg_right hFourBLe
          (pow_nonneg (profileScale_pos n).le 3)
        exact mul_le_mul_of_nonneg_right hdiv (by positivity)
      · rw [discreteDerivative_zero]
        apply weightedSupThree_zero
        exact mul_nonneg
          (div_nonneg hC.le (pow_nonneg (profileScale_pos n).le 3))
          (by linarith)
    · have hnFour : 4 ≤ n := by omega
      have hspan : a + 1 < n := by omega
      refine ⟨densityInitialSegment m p₀ a n, densityLateSegment m p₀ a n,
        (positiveTiltedDensity_eq_initial_add_late m p₀ hm hcrit han), ?_, ?_⟩
      · have hearly := densityInitialSegment_weightedSup_bound
          m p₀ hm hcrit B hB.le hSup han (by omega)
        apply weightedSupThree_mono (profileScale n)
          (27 * B / profileScale n ^ 3 * ((a + 1 : ℕ) : ℝ)) _ _ hearly
        have hdiv := div_le_div_of_nonneg_right hTwentySevenBLe
          (pow_nonneg (profileScale_pos n).le 3)
        exact mul_le_mul_of_nonneg_right hdiv (by positivity)
      · have hlate := densityLateSegment_derivative_weightedSup_log_bound
          m p₀ hm hcrit hthird hnotBinaryFixedPoint A B K Cv CE CR
          hA.le hB.le hK hCv.le hCE hCR hL1 hSup hinv hdefect hdVariation hE hR
          han hspan (by omega)
        apply weightedSupThree_mono (profileScale n)
          (CLate / profileScale n ^ 3 *
            (1 + Real.log (profileScale n / profileScale a))) _ _
          (by simpa only [CLate] using hlate)
        have hdiv := div_le_div_of_nonneg_right hCLateLe
          (pow_nonneg (profileScale_pos n).le 3)
        have hlogFactor :
            0 ≤ 1 + Real.log (profileScale n / ((a + 1 : ℕ) : ℝ)) := by linarith
        simpa only [profileScale] using mul_le_mul_of_nonneg_right hdiv hlogFactor

/-- The concrete split discharges the abstract inputs of `LogSmoothingArithmetic`,
yielding the spatial logarithmic modulus and its gradient specialization directly from
H1a/H1b. -/
theorem positiveTiltedDensity_spatialSmoothing_of_H1
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p₀) (hthird : TiltSummable m 3 p₀)
    (hnonconstant : ¬ IsDirac p₀)
    (hExcess : CDHLSExcessFact m p₀ hm hcrit hthird hnonconstant)
    (hProduct : CDHLSProductFact m p₀ hm hcrit hnonconstant) :
    ∃ C : ℝ, 0 < C ∧
      (∀ n h : ℕ, 1 ≤ h → h ≤ n + 1 →
        WeightedSupThreeLE (profileScale n)
          (positiveTiltedDensity m (orbit m p₀ n) -
            (shiftLeft^[h]) (positiveTiltedDensity m (orbit m p₀ n)))
          (5 * C * (h : ℝ) / profileScale n ^ 3 *
            (1 + Real.log (profileScale n / (h : ℝ))))) ∧
      ∀ n : ℕ,
        WeightedSupThreeLE (profileScale n)
          (discreteDerivative (positiveTiltedDensity m (orbit m p₀ n)))
          (5 * C / profileScale n ^ 3 * (1 + Real.log (profileScale n))) := by
  rcases truncatedSmoothingSplit_of_H1
      m p₀ hm hcrit hthird hnonconstant hExcess hProduct with
    ⟨C, hC, hSup, hsplit⟩
  refine ⟨C, hC, ?_, ?_⟩
  · intro n h hh hhL
    exact weightedSupThree_log_modulus_of_early_late
      n h C hC.le hh hhL (positiveTiltedDensity m (orbit m p₀ n)) (hSup n)
      (fun a ha ↦ hsplit n a ha)
  · intro n
    exact weightedSupThree_gradient_of_early_late
      n C hC.le (positiveTiltedDensity m (orbit m p₀ n)) (hSup n)
      (fun a ha ↦ hsplit n a ha)

end

end DerridaRetaux
