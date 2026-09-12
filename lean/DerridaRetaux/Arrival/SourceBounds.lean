import DerridaRetaux.Arrival.MomentTail
import DerridaRetaux.Arrival.SourceNormalForm
import DerridaRetaux.Prelim.TransportUniform
import Mathlib.Tactic

set_option autoImplicit false

open scoped BigOperators

namespace DerridaRetaux

noncomputable section

/-!
# Uniform coefficient bounds for the arrival-source expansion

This file supplies the analytic scalar estimates used between `eq:tag` and
`eq:tagbound`.  In particular, the recurrence for `kappa_s` is used directly;
no source-difference or tail estimate is assumed.
-/

/-- Absolute coefficient tail of a possibly signed sequence. -/
def absoluteCoefficientTail (a : Seq) (K : ℕ) : ℝ :=
  ∑' j : ℕ, |a (j + K)|

/-- Removing an integer monomial shift from a tail changes its starting index
by the corresponding integer amount. -/
theorem shiftByInt_tail_eq
    (a : Seq) (d : ℤ) (K T : ℕ)
    (hT : (K : ℤ) - d = (T : ℤ)) :
    (fun j : ℕ ↦ shiftByInt d a (j + K)) =
      fun j : ℕ ↦ a (j + T) := by
  funext j
  rw [shiftByInt, zeroExtend_eq_of_nonneg]
  · congr
    omega
  · omega

/-- Exact absolute-tail formula for a scalar multiple of a shifted
nonnegative summable coefficient sequence. -/
theorem absoluteCoefficientTail_const_mul_shiftByInt
    (a : Seq) (ha : ∀ n : ℕ, 0 ≤ a n) (hsum : Summable a)
    (c : ℝ) (d : ℤ) (K T : ℕ)
    (hT : (K : ℤ) - d = (T : ℤ)) :
    absoluteCoefficientTail
        (fun n : ℕ ↦ c * shiftByInt d a n) K =
      |c| * coefficientTail a T := by
  have hshift := shiftByInt_tail_eq a d K T hT
  have htail : Summable (fun j : ℕ ↦ shiftByInt d a (j + K)) := by
    rw [hshift]
    exact (summable_nat_add_iff T).2 hsum
  rw [absoluteCoefficientTail, coefficientTail]
  calc
    (∑' j : ℕ, |c * shiftByInt d a (j + K)|) =
        ∑' j : ℕ, |c| * shiftByInt d a (j + K) := by
      apply tsum_congr
      intro j
      rw [abs_mul]
      have hj := congrFun hshift j
      rw [hj, abs_of_nonneg (ha (j + T))]
    _ = |c| * ∑' j : ℕ, shiftByInt d a (j + K) :=
      htail.tsum_mul_left |c|
    _ = |c| * ∑' j : ℕ, a (j + T) := by rw [hshift]

/-- If `N < 2T`, replacing the tail threshold `T` by `N` costs at most the
factor eight in a cubic Markov bound. -/
theorem one_div_nat_cube_le_eight_div_nat_cube
    {N T : ℕ} (hN : 1 ≤ N) (hT : 1 ≤ T) (hNT : N < 2 * T) :
    1 / (T : ℝ) ^ 3 ≤ 8 / (N : ℝ) ^ 3 := by
  have hNpos : 0 < (N : ℝ) ^ 3 := by positivity
  have hTpos : 0 < (T : ℝ) ^ 3 := by positivity
  apply (div_le_div_iff₀ hTpos hNpos).2
  norm_num
  have hcast : (N : ℝ) < 2 * (T : ℝ) := by exact_mod_cast hNT
  have hcube : (N : ℝ) ^ 3 < (2 * (T : ℝ)) ^ 3 := by
    exact pow_lt_pow_left₀ hcast (Nat.cast_nonneg N) (by norm_num)
  nlinarith

/-- Dividing a nonnegative number by `1 + x*b` changes it by at most `x^2*b`.
This is the elementary estimate behind the variation of `alpha_(r,s)`. -/
theorem abs_div_one_add_mul_sub_le_sq_mul
    {x b : ℝ} (hx : 0 ≤ x) (hb : 0 ≤ b) :
    |x / (1 + x * b) - x| ≤ x ^ 2 * b := by
  have hxb : 0 ≤ x * b := mul_nonneg hx hb
  have hden : 0 < 1 + x * b := by linarith
  have hdivLe : x / (1 + x * b) ≤ x := by
    apply (div_le_iff₀ hden).2
    nlinarith [mul_nonneg hx hxb]
  rw [abs_of_nonpos (sub_nonpos.mpr hdivLe)]
  have heq : -(x / (1 + x * b) - x) = x ^ 2 * b / (1 + x * b) := by
    field_simp
    ring
  rw [heq]
  apply (div_le_iff₀ hden).2
  have hnum : 0 ≤ x ^ 2 * b := mul_nonneg (sq_nonneg x) hb
  nlinarith [mul_nonneg hnum hxb]

/-- A finite transport product is at most one, hence `kappa_s` is bounded by
the inverse zero tilted atom. -/
theorem arrivalKappa_le_orbitZeroTilt_inv
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p₀)
    (hnotBinaryFixedPoint : ¬ (m = 2 ∧ p₀ = diracMass 1)) (s : ℕ) :
    arrivalKappa m p₀ s ≤ (zeroTilt m (orbit m p₀ s))⁻¹ := by
  have hx : 0 < zeroTilt m (orbit m p₀ s) :=
    orbit_zeroTilt_pos m p₀ hm hcrit hnotBinaryFixedPoint s
  have hC : arrivalProduct m p₀ s ≤ 1 := by
    simpa only [arrivalProduct, transportProduct_zero] using
      (antitone_transportProduct m p₀ (by omega) hcrit (Nat.zero_le s))
  rw [arrivalKappa, arrivalZero, div_eq_mul_inv]
  simpa only [one_mul] using
    mul_le_mul_of_nonneg_right hC (inv_nonneg.mpr hx.le)

/-- `H1a` gives one positive, generation-independent upper bound for every
`kappa_s`.  The returned bound is also at least one for later power estimates. -/
theorem arrivalKappa_uniform_of_excess
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p₀) (hthird : TiltSummable m 3 p₀)
    (hnonconstant : ¬ IsDirac p₀)
    (hExcess : CDHLSExcessFact m p₀ hm hcrit hthird hnonconstant) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ s : ℕ, arrivalKappa m p₀ s ≤ B := by
  have hnotBinaryFixedPoint : ¬ (m = 2 ∧ p₀ = diracMass 1) := by
    rintro ⟨_, hp₀⟩
    exact hnonconstant ⟨1, hp₀⟩
  have hdefectOrbit := orbitTransportDefect_summable
    m p₀ hm hcrit hthird hnonconstant hExcess
  have hdefect :
      Summable (fun n : ℕ ↦ 1 - transportCoeff m (orbit m p₀ n)) := by
    simpa only [orbitTransportDefect] using hdefectOrbit
  rcases orbitZeroTilt_inverse_uniform
      m p₀ hm hcrit hnotBinaryFixedPoint hdefect with ⟨B, hB, hBinv⟩
  refine ⟨max 1 B, le_max_left _ _, ?_⟩
  intro s
  exact (arrivalKappa_le_orbitZeroTilt_inv
    m p₀ hm hcrit hnotBinaryFixedPoint s).trans <|
      (hBinv s).trans (le_max_right _ _)

/-- The concrete arrival coefficient sequence is summable. -/
theorem arrivalCoeff_summable
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p₀)
    (hnotBinaryFixedPoint : ¬ (m = 2 ∧ p₀ = diracMass 1)) (s : ℕ) :
    Summable (arrivalCoeff m p₀ s) := by
  have hscrit := orbit_critical m p₀ (by omega) hcrit s
  have hq : Summable (normalizedTilt m (orbit m p₀ s)) :=
    normalizedTilt_summable m (orbit m p₀ s) (by omega) hscrit
  have hqTail : Summable
      (fun j : ℕ ↦ normalizedTilt m (orbit m p₀ s) (j + 1)) :=
    (summable_nat_add_iff 1).2 hq
  have hC : 0 < arrivalProduct m p₀ s :=
    transportProduct_pos m p₀ hm hcrit hnotBinaryFixedPoint s
  have harrTail : Summable
      (fun j : ℕ ↦ arrivalCoeff m p₀ s (j + s)) := by
    have hscaled := hqTail.mul_left (arrivalProduct m p₀ s)⁻¹
    convert hscaled using 1
    funext j
    rw [arrivalCoeff_eq_of_le m p₀ s (j + s) (by omega)]
    simp only [orbitTilt]
    have hindex : j + s - s + 1 = j + 1 := by omega
    rw [hindex, div_eq_inv_mul]
  exact (summable_nat_add_iff s).1 harrTail

/-- The boundary coefficient is no larger than the total mass `F_s(1)`. -/
theorem arrivalBoundary_le_arrivalValueAtOne
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p₀)
    (hnotBinaryFixedPoint : ¬ (m = 2 ∧ p₀ = diracMass 1)) (s : ℕ) :
    arrivalBoundary m p₀ s ≤ arrivalValueAtOne m p₀ s := by
  rw [arrivalBoundary, arrivalValueAtOne]
  exact (arrivalCoeff_summable
    m p₀ hm hcrit hnotBinaryFixedPoint s).le_tsum s <|
      fun j _hjs ↦ arrivalCoeff_nonneg
        m p₀ hm hcrit hnotBinaryFixedPoint s j

/-- The `F_s(1)` estimate from U21 immediately controls the literal boundary
coefficient used by every source tag. -/
theorem arrivalBoundary_bound_of_H1
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p₀) (hthird : TiltSummable m 3 p₀)
    (hnonconstant : ¬ IsDirac p₀)
    (hExcess : CDHLSExcessFact m p₀ hm hcrit hthird hnonconstant)
    (hProduct : CDHLSProductFact m p₀ hm hcrit hnonconstant) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℕ,
      arrivalBoundary m p₀ s ≤ C / ((s + 1 : ℕ) : ℝ) := by
  have hnotBinaryFixedPoint : ¬ (m = 2 ∧ p₀ = diracMass 1) := by
    rintro ⟨_, hp₀⟩
    exact hnonconstant ⟨1, hp₀⟩
  rcases arrivalMomentTail_bounds
      m p₀ hm hcrit hthird hnonconstant hExcess hProduct with
    ⟨C, hC, hvalue, _htails⟩
  refine ⟨C, hC, ?_⟩
  intro s
  exact (arrivalBoundary_le_arrivalValueAtOne
    m p₀ hm hcrit hnotBinaryFixedPoint s).trans (hvalue s)

/-- The exact `kappa` recursion gives a one-step Lipschitz bound with the
uniform envelope supplied by `H1a`. -/
theorem arrivalKappa_succ_sub_le_boundary
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p₀)
    (hnotBinaryFixedPoint : ¬ (m = 2 ∧ p₀ = diracMass 1))
    (B : ℝ) (hKappa : ∀ s : ℕ, arrivalKappa m p₀ s ≤ B) (s : ℕ) :
    |arrivalKappa m p₀ (s + 1) - arrivalKappa m p₀ s| ≤
      B ^ 2 * arrivalBoundary m p₀ s := by
  have hk0 : 0 ≤ arrivalKappa m p₀ s :=
    (arrivalKappa_pos m p₀ hm hcrit hnotBinaryFixedPoint s).le
  have hb0 : 0 ≤ arrivalBoundary m p₀ s :=
    arrivalBoundary_nonneg m p₀ hm hcrit hnotBinaryFixedPoint s
  rw [arrivalKappa_succ m p₀ hm hcrit hnotBinaryFixedPoint s]
  calc
    |arrivalKappa m p₀ s /
          (1 + arrivalKappa m p₀ s * arrivalBoundary m p₀ s) -
        arrivalKappa m p₀ s| ≤
        arrivalKappa m p₀ s ^ 2 * arrivalBoundary m p₀ s :=
      abs_div_one_add_mul_sub_le_sq_mul hk0 hb0
    _ ≤ B ^ 2 * arrivalBoundary m p₀ s := by
      gcongr
      exact hKappa s

/-- Power variation on a nonnegative bounded interval. -/
theorem abs_pow_sub_pow_le_of_nonneg_le
    {x y B : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hxB : x ≤ B) (hyB : y ≤ B) (n : ℕ) :
    |x ^ n - y ^ n| ≤
      (n : ℝ) * B ^ (n - 1) * |x - y| := by
  have hBx : |x| ≤ B := by simpa [abs_of_nonneg hx] using hxB
  have hBy : |y| ≤ B := by simpa [abs_of_nonneg hy] using hyB
  calc
    |x ^ n - y ^ n| ≤
        |x - y| * (n : ℝ) * max |x| |y| ^ (n - 1) :=
      abs_pow_sub_pow_le x y n
    _ ≤ |x - y| * (n : ℝ) * B ^ (n - 1) := by
      gcongr
      exact max_le hBx hBy
    _ = (n : ℝ) * B ^ (n - 1) * |x - y| := by ring

/-- A convenient finite envelope for all source coefficients at arities
`2, ..., m`.  The added one makes the envelope at least one. -/
def sourceAlphaBound (m : ℕ) (B : ℝ) : ℝ :=
  1 + ∑ r ∈ Finset.Icc 2 m,
    (1 / (m : ℝ)) * (m.choose r : ℝ) * B ^ (r - 1)

/-- Finite envelope for the one-step variation of all source coefficients. -/
def sourceAlphaVariationBound (m : ℕ) (B : ℝ) : ℝ :=
  ∑ r ∈ Finset.Icc 2 m,
    (1 / (m : ℝ)) * (m.choose r : ℝ) *
      (r - 1 : ℕ) * B ^ r

theorem sourceAlphaBound_one_le
    (m : ℕ) (B : ℝ) (hB : 0 ≤ B) :
    1 ≤ sourceAlphaBound m B := by
  unfold sourceAlphaBound
  have hsum : 0 ≤ ∑ r ∈ Finset.Icc 2 m,
      (1 / (m : ℝ)) * (m.choose r : ℝ) * B ^ (r - 1) := by
    positivity
  linarith

/-- Uniform boundedness of every `alpha_(r,s)` in the actual finite source
range. -/
theorem arrivalAlpha_le_sourceAlphaBound
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p₀)
    (hnotBinaryFixedPoint : ¬ (m = 2 ∧ p₀ = diracMass 1))
    (B : ℝ) (hB : 0 ≤ B)
    (hKappa : ∀ s : ℕ, arrivalKappa m p₀ s ≤ B)
    (s r : ℕ) (hr : r ∈ Finset.Icc 2 m) :
    arrivalAlpha m p₀ s r ≤ sourceAlphaBound m B := by
  have hk0 : 0 ≤ arrivalKappa m p₀ s :=
    (arrivalKappa_pos m p₀ hm hcrit hnotBinaryFixedPoint s).le
  have hterm :
      arrivalAlpha m p₀ s r ≤
        (1 / (m : ℝ)) * (m.choose r : ℝ) * B ^ (r - 1) := by
    unfold arrivalAlpha
    gcongr
    exact hKappa s
  have hnonneg : ∀ i ∈ Finset.Icc 2 m,
      0 ≤ (1 / (m : ℝ)) * (m.choose i : ℝ) * B ^ (i - 1) := by
    intro i _hi
    positivity
  have hsum :
      (1 / (m : ℝ)) * (m.choose r : ℝ) * B ^ (r - 1) ≤
        ∑ i ∈ Finset.Icc 2 m,
          (1 / (m : ℝ)) * (m.choose i : ℝ) * B ^ (i - 1) := by
    exact Finset.single_le_sum (fun i hi ↦ hnonneg i hi) hr
  unfold sourceAlphaBound
  linarith

/-- The coefficient recurrence has the source-stated variation
`|alpha_(r,s+1)-alpha_(r,s)| <= C_r b_s`, uniformly in the generation. -/
theorem arrivalAlpha_succ_sub_le_variationBound_mul_boundary
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p₀)
    (hnotBinaryFixedPoint : ¬ (m = 2 ∧ p₀ = diracMass 1))
    (B : ℝ) (hB : 1 ≤ B)
    (hKappa : ∀ s : ℕ, arrivalKappa m p₀ s ≤ B)
    (s r : ℕ) (hr : r ∈ Finset.Icc 2 m) :
    |arrivalAlpha m p₀ (s + 1) r - arrivalAlpha m p₀ s r| ≤
      sourceAlphaVariationBound m B * arrivalBoundary m p₀ s := by
  let c : ℝ := (1 / (m : ℝ)) * (m.choose r : ℝ)
  let x : ℝ := arrivalKappa m p₀ (s + 1)
  let y : ℝ := arrivalKappa m p₀ s
  have hx0 : 0 ≤ x :=
    (arrivalKappa_pos m p₀ hm hcrit hnotBinaryFixedPoint (s + 1)).le
  have hy0 : 0 ≤ y :=
    (arrivalKappa_pos m p₀ hm hcrit hnotBinaryFixedPoint s).le
  have hxB : x ≤ B := hKappa (s + 1)
  have hyB : y ≤ B := hKappa s
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hpower := abs_pow_sub_pow_le_of_nonneg_le
    hx0 hy0 hxB hyB (r - 1)
  have hkdiff := arrivalKappa_succ_sub_le_boundary
    m p₀ hm hcrit hnotBinaryFixedPoint B hKappa s
  have hrLower : 2 ≤ r := (Finset.mem_Icc.mp hr).1
  have hpowCombine : B ^ (r - 1 - 1) * B ^ 2 = B ^ r := by
    rw [← pow_add]
    congr 1
    omega
  have hlocal :
      |arrivalAlpha m p₀ (s + 1) r - arrivalAlpha m p₀ s r| ≤
        (c * (r - 1 : ℕ) * B ^ r) * arrivalBoundary m p₀ s := by
    have hrewrite :
        arrivalAlpha m p₀ (s + 1) r - arrivalAlpha m p₀ s r =
          c * (x ^ (r - 1) - y ^ (r - 1)) := by
      simp only [arrivalAlpha, c, x, y]
      ring
    rw [hrewrite, abs_mul, abs_of_nonneg hc]
    calc
      c * |x ^ (r - 1) - y ^ (r - 1)| ≤
          c * ((r - 1 : ℕ) * B ^ (r - 1 - 1) * |x - y|) :=
        mul_le_mul_of_nonneg_left hpower hc
      _ ≤ c * ((r - 1 : ℕ) * B ^ (r - 1 - 1) *
          (B ^ 2 * arrivalBoundary m p₀ s)) := by
        gcongr
      _ = (c * (r - 1 : ℕ) * B ^ r) *
          arrivalBoundary m p₀ s := by
        rw [← hpowCombine]
        ring
  have htermNonneg : ∀ i ∈ Finset.Icc 2 m,
      0 ≤ (1 / (m : ℝ)) * (m.choose i : ℝ) *
        (i - 1 : ℕ) * B ^ i := by
    intro i _hi
    positivity
  have hterm :
      c * (r - 1 : ℕ) * B ^ r ≤ sourceAlphaVariationBound m B := by
    unfold sourceAlphaVariationBound
    exact Finset.single_le_sum (fun i hi ↦ htermNonneg i hi) hr
  exact hlocal.trans <|
    mul_le_mul_of_nonneg_right hterm
      (arrivalBoundary_nonneg m p₀ hm hcrit hnotBinaryFixedPoint s)

/-- Indicator exponent for an explicit boundary factor `-B_s`. -/
def sourceFactorBoundaryPower {m : ℕ} (x : SourceFactorChoice m) : ℕ :=
  if x = .inl false then 1 else 0

theorem sum_sourceFactorBoundaryPower_eq_multiplicity
    {m R : ℕ} (choice : Fin R → SourceFactorChoice m) :
    (∑ i : Fin R, sourceFactorBoundaryPower (choice i)) =
      sourceFactorMultiplicity choice (.inl false) := by
  rfl

/-- Each literal factor scalar is bounded by one common alpha envelope and
one explicit power of the boundary coefficient. -/
theorem abs_sourceFactorScalar_le
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p₀)
    (hnotBinaryFixedPoint : ¬ (m = 2 ∧ p₀ = diracMass 1))
    (B : ℝ) (hB : 0 ≤ B)
    (hKappa : ∀ s : ℕ, arrivalKappa m p₀ s ≤ B)
    (s : ℕ) (x : SourceFactorChoice m) :
    |sourceFactorScalar m p₀ s x| ≤
      sourceAlphaBound m B *
        arrivalBoundary m p₀ s ^ sourceFactorBoundaryPower x := by
  have hA : 1 ≤ sourceAlphaBound m B :=
    sourceAlphaBound_one_le m B hB
  have hb : 0 ≤ arrivalBoundary m p₀ s :=
    arrivalBoundary_nonneg m p₀ hm hcrit hnotBinaryFixedPoint s
  cases x with
  | inl unchanged =>
      cases unchanged with
      | true => simpa [sourceFactorScalar, sourceFactorBoundaryPower] using hA
      | false =>
          rw [sourceFactorScalar, abs_neg, abs_of_nonneg hb]
          simp only [sourceFactorBoundaryPower, ↓reduceIte, pow_one]
          nlinarith [mul_nonneg (sub_nonneg.mpr hA) hb]
  | inr r =>
      have hr : sourceArityValue r ∈ Finset.Icc 2 m := by
        exact Finset.mem_Icc.mpr ⟨by simp [sourceArityValue],
          SourceMonomialTag.sourceArity_le r⟩
      have ha0 : 0 ≤ arrivalAlpha m p₀ s (sourceArityValue r) :=
        arrivalAlpha_nonneg m p₀ hm hcrit hnotBinaryFixedPoint s _
      rw [sourceFactorScalar, abs_of_nonneg ha0]
      simpa [sourceFactorBoundaryPower] using
        arrivalAlpha_le_sourceAlphaBound
          m p₀ hm hcrit hnotBinaryFixedPoint B hB hKappa s _ hr

/-- Literal ordered products carry at most the tagged explicit power `b_s^w`;
all remaining scalar factors are absorbed into a constant depending only on
the fixed outer degree and arity. -/
theorem abs_sourceChoiceScalar_le
    {m R : ℕ} (p₀ : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p₀)
    (hnotBinaryFixedPoint : ¬ (m = 2 ∧ p₀ = diracMass 1))
    (B : ℝ) (hB : 0 ≤ B)
    (hKappa : ∀ s : ℕ, arrivalKappa m p₀ s ≤ B)
    (s : ℕ) (choice : Fin R → SourceFactorChoice m) :
    |sourceChoiceScalar p₀ s choice| ≤
      sourceAlphaBound m B ^ R *
        arrivalBoundary m p₀ s ^
          sourceFactorMultiplicity choice (.inl false) := by
  have hb : 0 ≤ arrivalBoundary m p₀ s :=
    arrivalBoundary_nonneg m p₀ hm hcrit hnotBinaryFixedPoint s
  rw [sourceChoiceScalar, Finset.abs_prod]
  calc
    (∏ i : Fin R, |sourceFactorScalar m p₀ s (choice i)|) ≤
        ∏ i : Fin R, sourceAlphaBound m B *
          arrivalBoundary m p₀ s ^ sourceFactorBoundaryPower (choice i) := by
      apply Finset.prod_le_prod
      · intro i _hi
        exact abs_nonneg _
      · intro i _hi
        exact abs_sourceFactorScalar_le
          m p₀ hm hcrit hnotBinaryFixedPoint B hB hKappa s (choice i)
    _ = sourceAlphaBound m B ^ R *
          arrivalBoundary m p₀ s ^
            sourceFactorMultiplicity choice (.inl false) := by
      rw [Finset.prod_mul_distrib, Finset.prod_const,
        Finset.prod_pow_eq_pow_sum,
        sum_sourceFactorBoundaryPower_eq_multiplicity]
      simp

/-- Uniform tagged-tail estimate.  This is the analytic content of
`eq:tagbound`: after the exact normal form from U22, U21 controls every
positive-order tag, with the monomial-shift threshold costing only a factor
eight. -/
theorem taggedSourceTerm_tail_bound_of_H1
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p₀) (hthird : TiltSummable m 3 p₀)
    (hnonconstant : ¬ IsDirac p₀)
    (hExcess : CDHLSExcessFact m p₀ hm hcrit hthird hnonconstant)
    (hProduct : CDHLSProductFact m p₀ hm hcrit hnonconstant) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (t : SourceMonomialTag m), t.Valid →
        ∀ (c D : ℝ), 0 ≤ D →
          ∀ s N : ℕ, s + SourceMonomialTag.sourceDifferenceCutoff m < N → 1 ≤ t.q →
            |c| ≤ D * arrivalBoundary m p₀ s ^ t.w →
            absoluteCoefficientTail
                (fun k : ℕ ↦ c *
                  shiftByInt (t.sigma s)
                    (convPow t.q (arrivalCoeff m p₀ s)) k)
                (N + s) ≤
              (8 * D * (t.q : ℝ) ^ 3 * C ^ t.q *
                arrivalBoundary m p₀ s ^ t.w *
                (((s + 1 : ℕ) : ℝ) ^
                  ((3 : ℤ) - (t.q : ℤ)))) /
                (N : ℝ) ^ 3 := by
  have hnotBinaryFixedPoint : ¬ (m = 2 ∧ p₀ = diracMass 1) := by
    rintro ⟨_, hp₀⟩
    exact hnonconstant ⟨1, hp₀⟩
  rcases arrivalMomentTail_bounds
      m p₀ hm hcrit hthird hnonconstant hExcess hProduct with
    ⟨C, hC, _hvalue, htails⟩
  refine ⟨C, hC, ?_⟩
  intro t hvalid c D hD s N hN hq hc
  let T : ℕ := (t.tailThreshold N s).toNat
  have htwice := t.tailThreshold_twice_gt hvalid hq hN
  have hNpos : 1 ≤ N := by
    have hsN : s < N := by
      exact lt_of_le_of_lt
        (Nat.le_add_right s (SourceMonomialTag.sourceDifferenceCutoff m)) hN
    omega
  have hthresholdPos : 0 < t.tailThreshold N s := by
    have hNint : 0 < (N : ℤ) := by exact_mod_cast hNpos
    linarith
  have hTcast : (T : ℤ) = t.tailThreshold N s := by
    exact Int.toNat_of_nonneg hthresholdPos.le
  have hTpos : 1 ≤ T := by
    have : (0 : ℤ) < (T : ℤ) := by simpa [hTcast] using hthresholdPos
    exact_mod_cast this
  have hNT : N < 2 * T := by
    have : (N : ℤ) < 2 * (T : ℤ) := by simpa [hTcast] using htwice
    exact_mod_cast this
  have hshift : ((N + s : ℕ) : ℤ) - t.sigma s = (T : ℤ) := by
    rw [hTcast]
    simp only [SourceMonomialTag.tailThreshold]
    push_cast
    rfl
  have ha : ∀ k : ℕ,
      0 ≤ convPow t.q (arrivalCoeff m p₀ s) k :=
    convPow_nonneg t.q (arrivalCoeff m p₀ s)
      (arrivalCoeff_nonneg m p₀ hm hcrit hnotBinaryFixedPoint s)
  have hsum : Summable (convPow t.q (arrivalCoeff m p₀ s)) :=
    convPow_summable t.q (arrivalCoeff m p₀ s)
      (arrivalCoeff_summable m p₀ hm hcrit hnotBinaryFixedPoint s)
  rw [absoluteCoefficientTail_const_mul_shiftByInt
    (convPow t.q (arrivalCoeff m p₀ s)) ha hsum c
      (t.sigma s) (N + s) T hshift]
  have hqUpper : t.q ≤ m ^ 2 := t.q_le_arity_sq hvalid
  have htail := (htails t.q hq hqUpper).2 s T hTpos
  let Q : ℝ := (t.q : ℝ) ^ 3 * C ^ t.q *
    (((s + 1 : ℕ) : ℝ) ^ ((3 : ℤ) - (t.q : ℤ)))
  have hQ : 0 ≤ Q := by
    dsimp [Q]
    positivity
  have hinv := one_div_nat_cube_le_eight_div_nat_cube hNpos hTpos hNT
  have hrescale : Q / (T : ℝ) ^ 3 ≤ 8 * Q / (N : ℝ) ^ 3 := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    have hthis :
        Q * ((T : ℝ) ^ 3)⁻¹ ≤ Q * (8 * ((N : ℝ) ^ 3)⁻¹) := by
      simpa only [one_div, div_eq_mul_inv, one_mul] using
        mul_le_mul_of_nonneg_left hinv hQ
    calc
      Q * ((T : ℝ) ^ 3)⁻¹ ≤ Q * (8 * ((N : ℝ) ^ 3)⁻¹) := hthis
      _ = 8 * Q * ((N : ℝ) ^ 3)⁻¹ := by ring
  have hbpow : 0 ≤ arrivalBoundary m p₀ s ^ t.w :=
    pow_nonneg
      (arrivalBoundary_nonneg m p₀ hm hcrit hnotBinaryFixedPoint s) t.w
  calc
    |c| * coefficientTail (convPow t.q (arrivalCoeff m p₀ s)) T ≤
        |c| * (Q / (T : ℝ) ^ 3) := by
      exact mul_le_mul_of_nonneg_left htail (abs_nonneg c)
    _ ≤ |c| * (8 * Q / (N : ℝ) ^ 3) :=
      mul_le_mul_of_nonneg_left hrescale (abs_nonneg c)
    _ ≤ (D * arrivalBoundary m p₀ s ^ t.w) *
          (8 * Q / (N : ℝ) ^ 3) := by
      exact mul_le_mul_of_nonneg_right hc <|
        div_nonneg (mul_nonneg (by norm_num) hQ) (by positivity)
    _ = (8 * D * (t.q : ℝ) ^ 3 * C ^ t.q *
          arrivalBoundary m p₀ s ^ t.w *
          (((s + 1 : ℕ) : ℝ) ^ ((3 : ℤ) - (t.q : ℤ)))) /
          (N : ℝ) ^ 3 := by
      dsimp [Q]
      ring

end

end DerridaRetaux
