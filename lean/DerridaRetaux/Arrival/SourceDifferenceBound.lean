import DerridaRetaux.Arrival.SourceBounds
import DerridaRetaux.Arrival.VisitOnce
import DerridaRetaux.Arrival.InitialTail
import DerridaRetaux.Prelim.AtomTailAbel
import Mathlib.Tactic

set_option autoImplicit false

open scoped BigOperators Topology
open Filter

namespace DerridaRetaux

noncomputable section

/-!
# The concrete source-difference estimate

This module applies the exact finite normal form to the analytic tagged-tail
estimate.  It keeps summability beside every tail inequality, so all finite
triangle inequalities are justified before the actual source expansion is
collected.
-/

/-- A tail estimate bundled with the absolute summability needed to add it to
other estimates. -/
def TailControlled (a : Seq) (K : ℕ) (M : ℝ) : Prop :=
  Summable (fun j : ℕ ↦ |a (j + K)|) ∧ absoluteCoefficientTail a K ≤ M

theorem tailControlled_zero (K : ℕ) (M : ℝ) (hM : 0 ≤ M) :
    TailControlled (fun _n : ℕ ↦ 0) K M := by
  constructor
  · simpa using (summable_zero : Summable (fun _j : ℕ ↦ (0 : ℝ)))
  · simpa [absoluteCoefficientTail]

theorem TailControlled.add
    {a b : Seq} {K : ℕ} {A B : ℝ}
    (ha : TailControlled a K A) (hb : TailControlled b K B) :
    TailControlled (fun n : ℕ ↦ a n + b n) K (A + B) := by
  have hmajorant : Summable (fun j : ℕ ↦ |a (j + K)| + |b (j + K)|) :=
    ha.1.add hb.1
  have hsum : Summable (fun j : ℕ ↦ |a (j + K) + b (j + K)|) :=
    Summable.of_nonneg_of_le
      (fun j ↦ abs_nonneg (a (j + K) + b (j + K)))
      (fun j ↦ abs_add (a (j + K)) (b (j + K))) hmajorant
  constructor
  · simpa only [Pi.add_apply] using hsum
  · unfold absoluteCoefficientTail
    calc
      (∑' j : ℕ, |a (j + K) + b (j + K)|) ≤
          ∑' j : ℕ, (|a (j + K)| + |b (j + K)|) :=
        Summable.tsum_le_tsum
          (fun j ↦ abs_add (a (j + K)) (b (j + K))) hsum hmajorant
      _ = (∑' j : ℕ, |a (j + K)|) + ∑' j : ℕ, |b (j + K)| :=
        ha.1.tsum_add hb.1
      _ ≤ A + B := add_le_add ha.2 hb.2

theorem TailControlled.mono
    {a : Seq} {K : ℕ} {A B : ℝ}
    (ha : TailControlled a K A) (hAB : A ≤ B) : TailControlled a K B :=
  ⟨ha.1, ha.2.trans hAB⟩

theorem TailControlled.congr
    {a b : Seq} {K : ℕ} {A : ℝ}
    (ha : TailControlled a K A) (hab : a = b) : TailControlled b K A := by
  subst b
  exact ha

theorem tailControlled_finset_sum
    {ι : Type*} (S : Finset ι) (f : ι → Seq) (K : ℕ) (M : ι → ℝ)
    (h : ∀ i ∈ S, TailControlled (f i) K (M i)) :
    TailControlled (fun n : ℕ ↦ ∑ i ∈ S, f i n) K (∑ i ∈ S, M i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using tailControlled_zero K 0 (le_refl 0)
  | @insert i S hi ih =>
      have hhead := h i (Finset.mem_insert_self i S)
      have htail : ∀ j ∈ S, TailControlled (f j) K (M j) := by
        intro j hj
        exact h j (Finset.mem_insert_of_mem hj)
      have hadd := hhead.add (ih htail)
      simpa only [Finset.sum_insert hi] using hadd

/-- A valid `q=0` source tag is a shifted delta whose sole degree is `2s`,
strictly below the requested tail. -/
theorem taggedSourceTerm_tail_eq_zero_of_q_eq_zero
    {m : ℕ} (t : SourceMonomialTag m) (hvalid : t.Valid)
    (a : Seq) (c : ℝ) (s N : ℕ) (hN : s < N) (hq : t.q = 0) :
    (fun j : ℕ ↦
      c * shiftByInt (t.sigma s)
        (convPow t.q a) (j + (N + s))) = 0 := by
  funext j
  have hsigma := SourceMonomialTag.q_eq_zero_degree_below_tail hvalid hq hN
  have hindex : t.sigma s < ((j + (N + s) : ℕ) : ℤ) := by
    push_cast
    omega
  have hnonneg : 0 ≤ ((j + (N + s) : ℕ) : ℤ) - t.sigma s := by omega
  have htoNatNe : (((j + (N + s) : ℕ) : ℤ) - t.sigma s).toNat ≠ 0 := by
    intro hz
    have hzcast :
        ((((j + (N + s) : ℕ) : ℤ) - t.sigma s).toNat : ℕ) = 0 := hz
    have hback := Int.toNat_of_nonneg hnonneg
    omega
  change c * shiftByInt (t.sigma s) (convPow t.q a) (j + (N + s)) = 0
  simp only [hq, convPow_zero, shiftByInt, zeroExtend_eq_of_nonneg _ _ hnonneg,
    diracSeq_apply, if_neg htoNatNe, mul_zero]

/-- The `q=0` branch is not merely bounded: its absolute tail is identically
zero beyond `N+s`. -/
theorem taggedSourceTerm_tailControlled_of_q_eq_zero
    {m : ℕ} (t : SourceMonomialTag m) (hvalid : t.Valid)
    (a : Seq) (c : ℝ) (s N : ℕ) (hN : s < N) (hq : t.q = 0)
    (M : ℝ) (hM : 0 ≤ M) :
    TailControlled
      (fun k : ℕ ↦ c * shiftByInt (t.sigma s)
        (convPow t.q a) k)
      (N + s) M := by
  have hzero := taggedSourceTerm_tail_eq_zero_of_q_eq_zero
    t hvalid a c s N hN hq
  constructor
  · convert (summable_zero : Summable (fun _j : ℕ ↦ (0 : ℝ))) using 1
    funext j
    have hzeroj :
        c * shiftByInt (t.sigma s) (convPow t.q a) (j + (N + s)) = 0 := by
      simpa using congrFun hzero j
    change |c * shiftByInt (t.sigma s) (convPow t.q a) (j + (N + s))| = 0
    rw [hzeroj, abs_zero]
  · unfold absoluteCoefficientTail
    have hz : (fun j : ℕ ↦
        |(fun k : ℕ ↦ c * shiftByInt (t.sigma s) (convPow t.q a) k)
          (j + (N + s))|) = 0 := by
      funext j
      have hzeroj :
          c * shiftByInt (t.sigma s) (convPow t.q a) (j + (N + s)) = 0 := by
        simpa using congrFun hzero j
      change |c * shiftByInt (t.sigma s) (convPow t.q a) (j + (N + s))| = 0
      rw [hzeroj, abs_zero]
    rw [hz]
    change (∑' _j : ℕ, (0 : ℝ)) ≤ M
    simpa using hM

/-- Positive-order tagged tails are absolutely summable at the same shifted
threshold used by the analytic estimate. -/
theorem taggedSourceTerm_tail_summable_of_q_pos
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p₀)
    (hnotBinaryFixedPoint : ¬ (m = 2 ∧ p₀ = diracMass 1))
    (t : SourceMonomialTag m) (hvalid : t.Valid)
    (c : ℝ) (s N : ℕ)
    (hN : s + SourceMonomialTag.sourceDifferenceCutoff m < N)
    (hq : 1 ≤ t.q) :
    Summable (fun j : ℕ ↦
      |c * shiftByInt (t.sigma s)
        (convPow t.q (arrivalCoeff m p₀ s)) (j + (N + s))|) := by
  let T : ℕ := (t.tailThreshold N s).toNat
  have htwice := t.tailThreshold_twice_gt hvalid hq hN
  have hNpos : 1 ≤ N := by
    have hsN : s < N := lt_of_le_of_lt
      (Nat.le_add_right s (SourceMonomialTag.sourceDifferenceCutoff m)) hN
    omega
  have hthresholdPos : 0 < t.tailThreshold N s := by
    have hNint : 0 < (N : ℤ) := by exact_mod_cast hNpos
    linarith
  have hTcast : (T : ℤ) = t.tailThreshold N s :=
    Int.toNat_of_nonneg hthresholdPos.le
  have hshift : ((N + s : ℕ) : ℤ) - t.sigma s = (T : ℤ) := by
    rw [hTcast]
    simp only [SourceMonomialTag.tailThreshold]
    push_cast
    rfl
  have hrewrite := shiftByInt_tail_eq
    (convPow t.q (arrivalCoeff m p₀ s)) (t.sigma s) (N + s) T hshift
  have hnonneg : ∀ k : ℕ, 0 ≤ convPow t.q (arrivalCoeff m p₀ s) k :=
    convPow_nonneg t.q (arrivalCoeff m p₀ s)
      (arrivalCoeff_nonneg m p₀ hm hcrit hnotBinaryFixedPoint s)
  have hsum : Summable (convPow t.q (arrivalCoeff m p₀ s)) :=
    convPow_summable t.q (arrivalCoeff m p₀ s)
      (arrivalCoeff_summable m p₀ hm hcrit hnotBinaryFixedPoint s)
  have htail : Summable
      (fun j : ℕ ↦ convPow t.q (arrivalCoeff m p₀ s) (j + T)) :=
    (summable_nat_add_iff T).2 hsum
  have hscaled := htail.mul_left |c|
  convert hscaled using 1
  funext j
  rw [abs_mul, congrFun hrewrite j, abs_of_nonneg (hnonneg (j + T))]

/-- `taggedSourceTerm_tail_bound_of_H1` together with its previously implicit
summability side condition. -/
theorem taggedSourceTerm_tailControlled_of_q_pos
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p₀) (hnonconstant : ¬ IsDirac p₀)
    (C : ℝ)
    (htagged : ∀ (t : SourceMonomialTag m), t.Valid →
      ∀ (c D : ℝ), 0 ≤ D →
        ∀ s N : ℕ, s + SourceMonomialTag.sourceDifferenceCutoff m < N → 1 ≤ t.q →
          |c| ≤ D * arrivalBoundary m p₀ s ^ t.w →
          absoluteCoefficientTail
              (fun k : ℕ ↦ c * shiftByInt (t.sigma s)
                (convPow t.q (arrivalCoeff m p₀ s)) k)
              (N + s) ≤
            (8 * D * (t.q : ℝ) ^ 3 * C ^ t.q *
              arrivalBoundary m p₀ s ^ t.w *
              (((s + 1 : ℕ) : ℝ) ^ ((3 : ℤ) - (t.q : ℤ)))) /
              (N : ℝ) ^ 3)
    (t : SourceMonomialTag m) (hvalid : t.Valid)
    (c D : ℝ) (hD : 0 ≤ D) (s N : ℕ)
    (hN : s + SourceMonomialTag.sourceDifferenceCutoff m < N)
    (hq : 1 ≤ t.q)
    (hc : |c| ≤ D * arrivalBoundary m p₀ s ^ t.w) :
    TailControlled
      (fun k : ℕ ↦ c * shiftByInt (t.sigma s)
        (convPow t.q (arrivalCoeff m p₀ s)) k)
      (N + s)
      ((8 * D * (t.q : ℝ) ^ 3 * C ^ t.q *
          arrivalBoundary m p₀ s ^ t.w *
          (((s + 1 : ℕ) : ℝ) ^ ((3 : ℤ) - (t.q : ℤ)))) /
        (N : ℝ) ^ 3) := by
  constructor
  · exact taggedSourceTerm_tail_summable_of_q_pos
      m p₀ hm hcrit (by
        rintro ⟨hm2, hp₀⟩
        exact hnonconstant ⟨1, hp₀⟩) t hvalid c s N hN hq
  · exact htagged t hvalid c D hD s N hN hq hc

/-- A positive constant which absorbs all scalar and fixed tag data. -/
def sourceTagEnvelope
    {m : ℕ} (C Cb D : ℝ) (t : SourceMonomialTag m) : ℝ :=
  1 + 8 * D * (t.q : ℝ) ^ 3 * C ^ t.q * (max 1 Cb) ^ t.w

theorem sourceTagEnvelope_pos
    {m : ℕ} (C Cb D : ℝ) (t : SourceMonomialTag m)
    (hC : 0 < C) (hD : 0 ≤ D) :
    0 < sourceTagEnvelope C Cb D t := by
  unfold sourceTagEnvelope
  have hmax : 0 ≤ max 1 Cb := (by positivity : (0 : ℝ) ≤ max 1 Cb)
  have hterm :
      0 ≤ 8 * D * (t.q : ℝ) ^ 3 * C ^ t.q * (max 1 Cb) ^ t.w := by
    positivity
  linarith

/-- Exhaustive analytic form of `eq:tagbound`.  The three source branches are
handled separately: `q=0` vanishes; `q>0,w=0` has a nonpositive source
exponent; and `q>0,w>0` is absorbed by `b_s(s+1)^2`. -/
theorem taggedSourceTerm_tailControlled_of_H1
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p₀) (hnonconstant : ¬ IsDirac p₀)
    (C Cb : ℝ) (hC : 0 < C) (hCb : 0 < Cb)
    (htagged : ∀ (t : SourceMonomialTag m), t.Valid →
      ∀ (c D : ℝ), 0 ≤ D →
        ∀ s N : ℕ, s + SourceMonomialTag.sourceDifferenceCutoff m < N → 1 ≤ t.q →
          |c| ≤ D * arrivalBoundary m p₀ s ^ t.w →
          absoluteCoefficientTail
              (fun k : ℕ ↦ c * shiftByInt (t.sigma s)
                (convPow t.q (arrivalCoeff m p₀ s)) k)
              (N + s) ≤
            (8 * D * (t.q : ℝ) ^ 3 * C ^ t.q *
              arrivalBoundary m p₀ s ^ t.w *
              (((s + 1 : ℕ) : ℝ) ^ ((3 : ℤ) - (t.q : ℤ)))) /
              (N : ℝ) ^ 3)
    (hboundary : ∀ s : ℕ,
      arrivalBoundary m p₀ s ≤ Cb / ((s + 1 : ℕ) : ℝ))
    (t : SourceMonomialTag m) (hvalid : t.Valid)
    (c D : ℝ) (hD : 0 ≤ D) (s N : ℕ)
    (hN : s + SourceMonomialTag.sourceDifferenceCutoff m < N)
    (hc : |c| ≤ D * arrivalBoundary m p₀ s ^ t.w) :
    TailControlled
      (fun k : ℕ ↦ c * shiftByInt (t.sigma s)
        (convPow t.q (arrivalCoeff m p₀ s)) k)
      (N + s)
      (sourceTagEnvelope C Cb D t *
        (1 + arrivalBoundary m p₀ s * ((s + 1 : ℕ) : ℝ) ^ 2) /
        (N : ℝ) ^ 3) := by
  have hnotBinaryFixedPoint : ¬ (m = 2 ∧ p₀ = diracMass 1) := by
    rintro ⟨_, hp₀⟩
    exact hnonconstant ⟨1, hp₀⟩
  have hb : 0 ≤ arrivalBoundary m p₀ s :=
    arrivalBoundary_nonneg m p₀ hm hcrit hnotBinaryFixedPoint s
  have hL : (1 : ℝ) ≤ ((s + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le s)
  have hLpos : 0 < ((s + 1 : ℕ) : ℝ) := by positivity
  have hNpos : 0 < (N : ℝ) := by
    have : 0 < N := by omega
    positivity
  have henvPos := sourceTagEnvelope_pos C Cb D t hC hD
  rcases SourceMonomialTag.valid_branch_trichotomy hvalid with
    hqZero | hwZero | hwPos
  · exact taggedSourceTerm_tailControlled_of_q_eq_zero
      t hvalid (arrivalCoeff m p₀ s) c s N (by omega) hqZero _ (by positivity)
  · rcases hwZero with ⟨hq, hw, hqThree⟩
    have hraw := taggedSourceTerm_tailControlled_of_q_pos
      m p₀ hm hcrit hnonconstant C htagged t hvalid c D hD s N hN hq hc
    apply hraw.mono
    have hKnonneg : 0 ≤ 8 * D * (t.q : ℝ) ^ 3 * C ^ t.q := by positivity
    have hexp : (3 : ℤ) - (t.q : ℤ) ≤ 0 :=
      SourceMonomialTag.sourceExponent_nonpos_of_w_eq_zero hvalid hw
    have hzpow :
        ((s + 1 : ℕ) : ℝ) ^ ((3 : ℤ) - (t.q : ℤ)) ≤ 1 :=
      zpow_le_one_of_nonpos₀ hL hexp
    have hinner :
        8 * D * (t.q : ℝ) ^ 3 * C ^ t.q *
            arrivalBoundary m p₀ s ^ t.w *
            (((s + 1 : ℕ) : ℝ) ^ ((3 : ℤ) - (t.q : ℤ))) ≤
          sourceTagEnvelope C Cb D t *
            (1 + arrivalBoundary m p₀ s * ((s + 1 : ℕ) : ℝ) ^ 2) := by
      rw [hw, pow_zero]
      have hbase :
          8 * D * (t.q : ℝ) ^ 3 * C ^ t.q * 1 *
              (((s + 1 : ℕ) : ℝ) ^ ((3 : ℤ) - (t.q : ℤ))) ≤
            8 * D * (t.q : ℝ) ^ 3 * C ^ t.q := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hzpow hKnonneg
      have hKenv :
          8 * D * (t.q : ℝ) ^ 3 * C ^ t.q ≤ sourceTagEnvelope C Cb D t := by
        unfold sourceTagEnvelope
        rw [hw, pow_zero, mul_one]
        linarith
      have hone :
          1 ≤ 1 + arrivalBoundary m p₀ s * ((s + 1 : ℕ) : ℝ) ^ 2 := by
        nlinarith [mul_nonneg hb (pow_nonneg (Nat.cast_nonneg (s + 1)) 2)]
      exact hbase.trans <| hKenv.trans <|
        (by simpa only [mul_one] using
          mul_le_mul_of_nonneg_left hone henvPos.le)
    exact (div_le_div_iff_of_pos_right (pow_pos hNpos 3)).2 hinner

  · rcases hwPos with ⟨hq, hw, _hqw⟩
    have hraw := taggedSourceTerm_tailControlled_of_q_pos
      m p₀ hm hcrit hnonconstant C htagged t hvalid c D hD s N hN hq hc
    apply hraw.mono
    let M : ℝ := max 1 Cb
    have hMone : 1 ≤ M := le_max_left 1 Cb
    have hCbM : Cb ≤ M := le_max_right 1 Cb
    have hbCb : arrivalBoundary m p₀ s ≤ Cb := by
      exact (hboundary s).trans <| (div_le_iff₀ hLpos).2 <| by
        nlinarith [hCb.le, hL]
    have hbM : arrivalBoundary m p₀ s ≤ M := hbCb.trans hCbM
    have hpowB :
        arrivalBoundary m p₀ s ^ t.w ≤
          arrivalBoundary m p₀ s * M ^ t.w := by
      have hwDecomp : t.w = (t.w - 1) + 1 := by omega
      calc
        arrivalBoundary m p₀ s ^ t.w =
            arrivalBoundary m p₀ s ^ (t.w - 1) *
              arrivalBoundary m p₀ s := by
          conv_lhs => rw [hwDecomp, pow_succ]
        _ ≤ M ^ (t.w - 1) * arrivalBoundary m p₀ s := by
          exact mul_le_mul_of_nonneg_right
            (pow_le_pow_left₀ hb hbM (t.w - 1)) hb
        _ ≤ M ^ t.w * arrivalBoundary m p₀ s := by
          exact mul_le_mul_of_nonneg_right
            (pow_le_pow_right₀ hMone (Nat.sub_le t.w 1)) hb
        _ = arrivalBoundary m p₀ s * M ^ t.w := by ring
    have hexp : (3 : ℤ) - (t.q : ℤ) ≤ 2 := by
      have hqInt : (1 : ℤ) ≤ (t.q : ℤ) := by exact_mod_cast hq
      omega
    have hzpow :
        ((s + 1 : ℕ) : ℝ) ^ ((3 : ℤ) - (t.q : ℤ)) ≤
          ((s + 1 : ℕ) : ℝ) ^ (2 : ℤ) :=
      zpow_right_mono₀ hL hexp
    have hzpowTwo : ((s + 1 : ℕ) : ℝ) ^ (2 : ℤ) =
        ((s + 1 : ℕ) : ℝ) ^ 2 := rfl
    rw [hzpowTwo] at hzpow
    have hKnonneg : 0 ≤ 8 * D * (t.q : ℝ) ^ 3 * C ^ t.q := by positivity
    have hMpow : 0 ≤ M ^ t.w := by positivity
    have hfactor :
        arrivalBoundary m p₀ s ^ t.w *
            (((s + 1 : ℕ) : ℝ) ^ ((3 : ℤ) - (t.q : ℤ))) ≤
          M ^ t.w *
            (arrivalBoundary m p₀ s * ((s + 1 : ℕ) : ℝ) ^ 2) := by
      calc
        arrivalBoundary m p₀ s ^ t.w *
              (((s + 1 : ℕ) : ℝ) ^ ((3 : ℤ) - (t.q : ℤ))) ≤
            (arrivalBoundary m p₀ s * M ^ t.w) *
              (((s + 1 : ℕ) : ℝ) ^ ((3 : ℤ) - (t.q : ℤ))) := by
          exact mul_le_mul_of_nonneg_right hpowB (zpow_nonneg hLpos.le _)
        _ ≤ (arrivalBoundary m p₀ s * M ^ t.w) *
              ((s + 1 : ℕ) : ℝ) ^ 2 := by
          exact mul_le_mul_of_nonneg_left hzpow (mul_nonneg hb hMpow)
        _ = M ^ t.w *
              (arrivalBoundary m p₀ s * ((s + 1 : ℕ) : ℝ) ^ 2) := by ring
    have hKMenv :
        (8 * D * (t.q : ℝ) ^ 3 * C ^ t.q) * M ^ t.w ≤
          sourceTagEnvelope C Cb D t := by
      unfold sourceTagEnvelope
      dsimp [M]
      linarith
    have hinner :
        8 * D * (t.q : ℝ) ^ 3 * C ^ t.q *
            arrivalBoundary m p₀ s ^ t.w *
            (((s + 1 : ℕ) : ℝ) ^ ((3 : ℤ) - (t.q : ℤ))) ≤
          sourceTagEnvelope C Cb D t *
            (1 + arrivalBoundary m p₀ s * ((s + 1 : ℕ) : ℝ) ^ 2) := by
      calc
        8 * D * (t.q : ℝ) ^ 3 * C ^ t.q *
              arrivalBoundary m p₀ s ^ t.w *
              (((s + 1 : ℕ) : ℝ) ^ ((3 : ℤ) - (t.q : ℤ))) =
            (8 * D * (t.q : ℝ) ^ 3 * C ^ t.q) *
              (arrivalBoundary m p₀ s ^ t.w *
              (((s + 1 : ℕ) : ℝ) ^ ((3 : ℤ) - (t.q : ℤ)))) := by ring
        _ ≤ (8 * D * (t.q : ℝ) ^ 3 * C ^ t.q) * (M ^ t.w *
              (arrivalBoundary m p₀ s * ((s + 1 : ℕ) : ℝ) ^ 2)) := by
          exact mul_le_mul_of_nonneg_left hfactor hKnonneg
        _ = ((8 * D * (t.q : ℝ) ^ 3 * C ^ t.q) * M ^ t.w) *
              (arrivalBoundary m p₀ s * ((s + 1 : ℕ) : ℝ) ^ 2) := by ring
        _ ≤ sourceTagEnvelope C Cb D t *
              (arrivalBoundary m p₀ s * ((s + 1 : ℕ) : ℝ) ^ 2) := by
          gcongr
        _ ≤ sourceTagEnvelope C Cb D t *
              (1 + arrivalBoundary m p₀ s * ((s + 1 : ℕ) : ℝ) ^ 2) := by
          gcongr
          linarith
    exact (div_le_div_iff_of_pos_right (pow_pos hNpos 3)).2 hinner

/-- One finite envelope dominates every valid tag.  Using the sum over the
actual finite tag type avoids any hidden cardinality or exponent maximum. -/
def sourceUniformTagEnvelope (m : ℕ) (C Cb D : ℝ) : ℝ :=
  1 + ∑ t : SourceMonomialTag.ValidSourceMonomialTag m,
    sourceTagEnvelope C Cb D t.1

theorem sourceTagEnvelope_le_uniform
    {m : ℕ} (C Cb D : ℝ) (hC : 0 < C) (hD : 0 ≤ D)
    (t : SourceMonomialTag m) (hvalid : t.Valid) :
    sourceTagEnvelope C Cb D t ≤ sourceUniformTagEnvelope m C Cb D := by
  let tv : SourceMonomialTag.ValidSourceMonomialTag m := ⟨t, hvalid⟩
  have hnonneg : ∀ x : SourceMonomialTag.ValidSourceMonomialTag m,
      0 ≤ sourceTagEnvelope C Cb D x.1 := by
    intro x
    exact (sourceTagEnvelope_pos C Cb D x.1 hC hD).le
  have hsingle : sourceTagEnvelope C Cb D tv.1 ≤
      ∑ x : SourceMonomialTag.ValidSourceMonomialTag m,
        sourceTagEnvelope C Cb D x.1 := by
    exact Finset.single_le_sum (fun x _hx ↦ hnonneg x) (Finset.mem_univ tv)
  unfold sourceUniformTagEnvelope
  have hsumNonneg : 0 ≤ ∑ x : SourceMonomialTag.ValidSourceMonomialTag m,
      sourceTagEnvelope C Cb D x.1 := by
    exact Finset.sum_nonneg (fun x _hx ↦ hnonneg x)
  have hsumLe :
      (∑ x : SourceMonomialTag.ValidSourceMonomialTag m,
        sourceTagEnvelope C Cb D x.1) ≤
        1 + ∑ x : SourceMonomialTag.ValidSourceMonomialTag m,
          sourceTagEnvelope C Cb D x.1 := by linarith
  simpa only [tv] using hsingle.trans hsumLe

theorem sourceUniformTagEnvelope_pos
    (m : ℕ) (C Cb D : ℝ) (hC : 0 < C) (hD : 0 ≤ D) :
    0 < sourceUniformTagEnvelope m C Cb D := by
  unfold sourceUniformTagEnvelope
  have hsum : 0 ≤ ∑ t : SourceMonomialTag.ValidSourceMonomialTag m,
      sourceTagEnvelope C Cb D t.1 := by
    exact Finset.sum_nonneg (fun t _ht ↦
      (sourceTagEnvelope_pos C Cb D t.1 hC hD).le)
  linarith

/-- One scalar envelope covers alpha variation, the two shift coefficients,
and every ordered function-expansion product. -/
def sourceActualScalarEnvelope (m : ℕ) (B : ℝ) : ℝ :=
  max (sourceAlphaVariationBound m B) (sourceAlphaBound m B ^ (m + 1))

theorem sourceActualScalarEnvelope_nonneg
    (m : ℕ) (B : ℝ) (hB : 0 ≤ B) :
    0 ≤ sourceActualScalarEnvelope m B := by
  have hA0 : 0 ≤ sourceAlphaBound m B :=
    zero_le_one.trans (sourceAlphaBound_one_le m B hB)
  exact (pow_nonneg hA0 (m + 1)).trans (le_max_right _ _)

theorem sourceAlphaBound_le_actualScalarEnvelope
    (m : ℕ) (B : ℝ) (hB : 0 ≤ B) :
    sourceAlphaBound m B ≤ sourceActualScalarEnvelope m B := by
  have hA : 1 ≤ sourceAlphaBound m B := sourceAlphaBound_one_le m B hB
  have hpow : sourceAlphaBound m B ≤ sourceAlphaBound m B ^ (m + 1) := by
    calc
      sourceAlphaBound m B = sourceAlphaBound m B ^ 1 := by simp
      _ ≤ sourceAlphaBound m B ^ (m + 1) :=
        pow_le_pow_right₀ hA (by omega)
  exact hpow.trans (le_max_right _ _)

theorem coefficientChange_scalar_le_actualEnvelope
    {m R : ℕ} (p₀ : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p₀)
    (hnotBinaryFixedPoint : ¬ (m = 2 ∧ p₀ = diracMass 1))
    (B : ℝ) (hB : 1 ≤ B)
    (hKappa : ∀ s : ℕ, arrivalKappa m p₀ s ≤ B)
    (hR : R ∈ Finset.Icc 2 m) (s : ℕ) :
    |arrivalAlpha m p₀ (s + 1) R - arrivalAlpha m p₀ s R| ≤
      sourceActualScalarEnvelope m B *
        arrivalBoundary m p₀ s ^
          (coefficientChangeTag (Finset.mem_Icc.mp hR).2).w := by
  have hb : 0 ≤ arrivalBoundary m p₀ s :=
    arrivalBoundary_nonneg m p₀ hm hcrit hnotBinaryFixedPoint s
  have hvariation := arrivalAlpha_succ_sub_le_variationBound_mul_boundary
    m p₀ hm hcrit hnotBinaryFixedPoint B hB hKappa s R hR
  have hVD : sourceAlphaVariationBound m B ≤ sourceActualScalarEnvelope m B :=
    le_max_left _ _
  calc
    |arrivalAlpha m p₀ (s + 1) R - arrivalAlpha m p₀ s R| ≤
        sourceAlphaVariationBound m B * arrivalBoundary m p₀ s := hvariation
    _ ≤ sourceActualScalarEnvelope m B * arrivalBoundary m p₀ s :=
      mul_le_mul_of_nonneg_right hVD hb
    _ = sourceActualScalarEnvelope m B *
        arrivalBoundary m p₀ s ^
          (coefficientChangeTag (Finset.mem_Icc.mp hR).2).w := by
      simp [coefficientChangeTag, SourceMonomialTag.w]

theorem shift_scalar_le_actualEnvelope
    {m R : ℕ} (p₀ : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p₀)
    (hnotBinaryFixedPoint : ¬ (m = 2 ∧ p₀ = diracMass 1))
    (B : ℝ) (hB : 1 ≤ B)
    (hKappa : ∀ s : ℕ, arrivalKappa m p₀ s ≤ B)
    (hR : R ∈ Finset.Icc 2 m) (s : ℕ) :
    |arrivalAlpha m p₀ (s + 1) R| ≤
        sourceActualScalarEnvelope m B *
          arrivalBoundary m p₀ s ^
            (shiftNoExcessTag (Finset.mem_Icc.mp hR).2).w ∧
      |-arrivalAlpha m p₀ (s + 1) R| ≤
        sourceActualScalarEnvelope m B *
          arrivalBoundary m p₀ s ^
            (shiftWithExcessTag (Finset.mem_Icc.mp hR).2).w := by
  have ha0 : 0 ≤ arrivalAlpha m p₀ (s + 1) R :=
    arrivalAlpha_nonneg m p₀ hm hcrit hnotBinaryFixedPoint (s + 1) R
  have ha := arrivalAlpha_le_sourceAlphaBound
    m p₀ hm hcrit hnotBinaryFixedPoint B (zero_le_one.trans hB)
      hKappa (s + 1) R hR
  have hAD := sourceAlphaBound_le_actualScalarEnvelope m B (zero_le_one.trans hB)
  have hscalar : |arrivalAlpha m p₀ (s + 1) R| ≤ sourceActualScalarEnvelope m B := by
    rw [abs_of_nonneg ha0]
    exact ha.trans hAD
  constructor
  · simpa [shiftNoExcessTag, SourceMonomialTag.w] using hscalar
  · simpa [shiftWithExcessTag, SourceMonomialTag.w] using hscalar

theorem functionChange_scalar_le_actualEnvelope
    {m R : ℕ} (p₀ : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p₀)
    (hnotBinaryFixedPoint : ¬ (m = 2 ∧ p₀ = diracMass 1))
    (B : ℝ) (hB : 1 ≤ B)
    (hKappa : ∀ s : ℕ, arrivalKappa m p₀ s ≤ B)
    (hR : R ∈ Finset.Icc 2 m) (s : ℕ)
    (choice : Fin R → SourceFactorChoice m) :
    |arrivalAlpha m p₀ (s + 1) R * sourceChoiceScalar p₀ s choice| ≤
      sourceActualScalarEnvelope m B *
        arrivalBoundary m p₀ s ^
          (functionExpansionTag (Finset.mem_Icc.mp hR).2 choice).w := by
  let A : ℝ := sourceAlphaBound m B
  let D : ℝ := sourceActualScalarEnvelope m B
  have hA : 1 ≤ A := sourceAlphaBound_one_le m B (zero_le_one.trans hB)
  have hD : A ^ (m + 1) ≤ D := le_max_right _ _
  have hb : 0 ≤ arrivalBoundary m p₀ s :=
    arrivalBoundary_nonneg m p₀ hm hcrit hnotBinaryFixedPoint s
  have ha0 : 0 ≤ arrivalAlpha m p₀ (s + 1) R :=
    arrivalAlpha_nonneg m p₀ hm hcrit hnotBinaryFixedPoint (s + 1) R
  have ha : arrivalAlpha m p₀ (s + 1) R ≤ A := by
    exact arrivalAlpha_le_sourceAlphaBound
      m p₀ hm hcrit hnotBinaryFixedPoint B (zero_le_one.trans hB)
        hKappa (s + 1) R hR
  have hchoice := abs_sourceChoiceScalar_le
    p₀ hm hcrit hnotBinaryFixedPoint B (zero_le_one.trans hB) hKappa s choice
  have hpow : A ^ (R + 1) ≤ A ^ (m + 1) :=
    pow_le_pow_right₀ hA (Nat.add_le_add_right (Finset.mem_Icc.mp hR).2 1)
  rw [abs_mul, abs_of_nonneg ha0]
  calc
    arrivalAlpha m p₀ (s + 1) R * |sourceChoiceScalar p₀ s choice| ≤
        A * |sourceChoiceScalar p₀ s choice| :=
      mul_le_mul_of_nonneg_right ha (abs_nonneg _)
    _ ≤ A * (A ^ R * arrivalBoundary m p₀ s ^
          sourceFactorMultiplicity choice (.inl false)) :=
      mul_le_mul_of_nonneg_left hchoice (zero_le_one.trans hA)
    _ = A ^ (R + 1) * arrivalBoundary m p₀ s ^
          sourceFactorMultiplicity choice (.inl false) := by
      rw [pow_succ]
      ring
    _ ≤ A ^ (m + 1) * arrivalBoundary m p₀ s ^
          sourceFactorMultiplicity choice (.inl false) :=
      mul_le_mul_of_nonneg_right hpow (pow_nonneg hb _)
    _ ≤ D * arrivalBoundary m p₀ s ^
          sourceFactorMultiplicity choice (.inl false) :=
      mul_le_mul_of_nonneg_right hD (pow_nonneg hb _)
    _ = sourceActualScalarEnvelope m B *
          arrivalBoundary m p₀ s ^
            (functionExpansionTag (Finset.mem_Icc.mp hR).2 choice).w := by
      simp [D, functionExpansionTag, SourceMonomialTag.w]

/-- Uniform version of the exhaustive tag estimate. -/
theorem taggedSourceTerm_tailControlled_uniform
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p₀) (hnonconstant : ¬ IsDirac p₀)
    (C Cb D : ℝ) (hC : 0 < C) (hCb : 0 < Cb) (hD : 0 ≤ D)
    (htagged : ∀ (t : SourceMonomialTag m), t.Valid →
      ∀ (c D : ℝ), 0 ≤ D →
        ∀ s N : ℕ, s + SourceMonomialTag.sourceDifferenceCutoff m < N → 1 ≤ t.q →
          |c| ≤ D * arrivalBoundary m p₀ s ^ t.w →
          absoluteCoefficientTail
              (fun k : ℕ ↦ c * shiftByInt (t.sigma s)
                (convPow t.q (arrivalCoeff m p₀ s)) k)
              (N + s) ≤
            (8 * D * (t.q : ℝ) ^ 3 * C ^ t.q *
              arrivalBoundary m p₀ s ^ t.w *
              (((s + 1 : ℕ) : ℝ) ^ ((3 : ℤ) - (t.q : ℤ)))) /
              (N : ℝ) ^ 3)
    (hboundary : ∀ s : ℕ,
      arrivalBoundary m p₀ s ≤ Cb / ((s + 1 : ℕ) : ℝ))
    (t : SourceMonomialTag m) (hvalid : t.Valid)
    (c : ℝ) (s N : ℕ)
    (hN : s + SourceMonomialTag.sourceDifferenceCutoff m < N)
    (hc : |c| ≤ D * arrivalBoundary m p₀ s ^ t.w) :
    TailControlled
      (fun k : ℕ ↦ c * shiftByInt (t.sigma s)
        (convPow t.q (arrivalCoeff m p₀ s)) k)
      (N + s)
      (sourceUniformTagEnvelope m C Cb D *
        (1 + arrivalBoundary m p₀ s * ((s + 1 : ℕ) : ℝ) ^ 2) /
        (N : ℝ) ^ 3) := by
  have htag := taggedSourceTerm_tailControlled_of_H1
    m p₀ hm hcrit hnonconstant C Cb hC hCb htagged hboundary
      t hvalid c D hD s N hN hc
  apply htag.mono
  have hnotBinaryFixedPoint : ¬ (m = 2 ∧ p₀ = diracMass 1) := by
    rintro ⟨_, hp₀⟩
    exact hnonconstant ⟨1, hp₀⟩
  have hb : 0 ≤ arrivalBoundary m p₀ s :=
    arrivalBoundary_nonneg m p₀ hm hcrit hnotBinaryFixedPoint s
  have hnum : 0 ≤
      1 + arrivalBoundary m p₀ s * ((s + 1 : ℕ) : ℝ) ^ 2 := by positivity
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (sourceTagEnvelope_le_uniform C Cb D hC hD t hvalid) hnum)
    (pow_nonneg (Nat.cast_nonneg N) 3)

theorem sourceCoefficientChangeTerm_eq_knownTagNormalForm
    {m R : ℕ} (p₀ : ProbabilityMass) (hR : 2 ≤ R) (hRm : R ≤ m) (s : ℕ) :
    sourceCoefficientChangeTerm m p₀ s R =
      fun N : ℕ ↦
        (arrivalAlpha m p₀ (s + 1) R - arrivalAlpha m p₀ s R) *
          shiftByInt ((coefficientChangeTag hRm).sigma s)
            (convPow (coefficientChangeTag hRm).q (arrivalCoeff m p₀ s)) N := by
  funext N
  simp only [sourceCoefficientChangeTerm]
  rw [coefficientChangeTag_sigma hR hRm]
  simp [coefficientChangeTag, SourceMonomialTag.q]

theorem sourceShiftNoExcessTerm_eq_knownTagNormalForm
    {m R : ℕ} (p₀ : ProbabilityMass) (hRm : R ≤ m) (s : ℕ) :
    sourceShiftNoExcessTerm m p₀ s R =
      fun N : ℕ ↦ arrivalAlpha m p₀ (s + 1) R *
        shiftByInt ((shiftNoExcessTag hRm).sigma s)
          (convPow (shiftNoExcessTag hRm).q (arrivalCoeff m p₀ s)) N := by
  funext N
  simp only [sourceShiftNoExcessTerm]
  rw [shiftNoExcessTag_sigma hRm]
  simp [shiftNoExcessTag, SourceMonomialTag.q]

theorem sourceShiftWithExcessTerm_eq_knownTagNormalForm
    {m R : ℕ} (p₀ : ProbabilityMass) (hR : 2 ≤ R) (hRm : R ≤ m) (s : ℕ) :
    sourceShiftWithExcessTerm m p₀ s R =
      fun N : ℕ ↦ -arrivalAlpha m p₀ (s + 1) R *
        shiftByInt ((shiftWithExcessTag hRm).sigma s)
          (convPow (shiftWithExcessTag hRm).q (arrivalCoeff m p₀ s)) N := by
  funext N
  simp only [sourceShiftWithExcessTerm]
  rw [shiftWithExcessTag_sigma hR hRm]
  simp [shiftWithExcessTag, SourceMonomialTag.q]

/-- Short name for the analytic conclusion already supplied by SourceBounds. -/
abbrev SourceTaggedTailBound
    (m : ℕ) (p₀ : ProbabilityMass) (C : ℝ) : Prop :=
  ∀ (t : SourceMonomialTag m), t.Valid →
    ∀ (c D : ℝ), 0 ≤ D →
      ∀ s N : ℕ, s + SourceMonomialTag.sourceDifferenceCutoff m < N → 1 ≤ t.q →
        |c| ≤ D * arrivalBoundary m p₀ s ^ t.w →
        absoluteCoefficientTail
            (fun k : ℕ ↦ c * shiftByInt (t.sigma s)
              (convPow t.q (arrivalCoeff m p₀ s)) k)
            (N + s) ≤
          (8 * D * (t.q : ℝ) ^ 3 * C ^ t.q *
            arrivalBoundary m p₀ s ^ t.w *
            (((s + 1 : ℕ) : ℝ) ^ ((3 : ℤ) - (t.q : ℤ)))) /
            (N : ℝ) ^ 3

abbrev ArrivalBoundaryDecay
    (m : ℕ) (p₀ : ProbabilityMass) (Cb : ℝ) : Prop :=
  ∀ s : ℕ, arrivalBoundary m p₀ s ≤ Cb / ((s + 1 : ℕ) : ℝ)

theorem sourceCoefficientChangeTerm_tailControlled_uniform
    {m R : ℕ} (p₀ : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p₀) (hnonconstant : ¬ IsDirac p₀)
    (B C Cb : ℝ) (hB : 1 ≤ B) (hC : 0 < C) (hCb : 0 < Cb)
    (hKappa : ∀ s : ℕ, arrivalKappa m p₀ s ≤ B)
    (htagged : SourceTaggedTailBound m p₀ C)
    (hboundary : ArrivalBoundaryDecay m p₀ Cb)
    (hR : R ∈ Finset.Icc 2 m) (s N : ℕ)
    (hN : s + SourceMonomialTag.sourceDifferenceCutoff m < N) :
    TailControlled (sourceCoefficientChangeTerm m p₀ s R) (N + s)
      (sourceUniformTagEnvelope m C Cb (sourceActualScalarEnvelope m B) *
        (1 + arrivalBoundary m p₀ s * ((s + 1 : ℕ) : ℝ) ^ 2) /
        (N : ℝ) ^ 3) := by
  have hnotBinaryFixedPoint : ¬ (m = 2 ∧ p₀ = diracMass 1) := by
    rintro ⟨_, hp₀⟩
    exact hnonconstant ⟨1, hp₀⟩
  have htag := taggedSourceTerm_tailControlled_uniform
    m p₀ hm hcrit hnonconstant C Cb (sourceActualScalarEnvelope m B)
      hC hCb (sourceActualScalarEnvelope_nonneg m B (zero_le_one.trans hB))
      htagged hboundary (coefficientChangeTag (Finset.mem_Icc.mp hR).2)
      (coefficientChangeTag_valid (Finset.mem_Icc.mp hR).1 (Finset.mem_Icc.mp hR).2)
      (arrivalAlpha m p₀ (s + 1) R - arrivalAlpha m p₀ s R) s N hN
      (coefficientChange_scalar_le_actualEnvelope
        p₀ hm hcrit hnotBinaryFixedPoint B hB hKappa hR s)
  exact htag.congr
    (sourceCoefficientChangeTerm_eq_knownTagNormalForm
      p₀ (Finset.mem_Icc.mp hR).1 (Finset.mem_Icc.mp hR).2 s).symm

theorem sourceShiftNoExcessTerm_tailControlled_uniform
    {m R : ℕ} (p₀ : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p₀) (hnonconstant : ¬ IsDirac p₀)
    (B C Cb : ℝ) (hB : 1 ≤ B) (hC : 0 < C) (hCb : 0 < Cb)
    (hKappa : ∀ s : ℕ, arrivalKappa m p₀ s ≤ B)
    (htagged : SourceTaggedTailBound m p₀ C)
    (hboundary : ArrivalBoundaryDecay m p₀ Cb)
    (hR : R ∈ Finset.Icc 2 m) (hRthree : 3 ≤ R) (s N : ℕ)
    (hN : s + SourceMonomialTag.sourceDifferenceCutoff m < N) :
    TailControlled (sourceShiftNoExcessTerm m p₀ s R) (N + s)
      (sourceUniformTagEnvelope m C Cb (sourceActualScalarEnvelope m B) *
        (1 + arrivalBoundary m p₀ s * ((s + 1 : ℕ) : ℝ) ^ 2) /
        (N : ℝ) ^ 3) := by
  have hnotBinaryFixedPoint : ¬ (m = 2 ∧ p₀ = diracMass 1) := by
    rintro ⟨_, hp₀⟩
    exact hnonconstant ⟨1, hp₀⟩
  have hscalars := shift_scalar_le_actualEnvelope
    p₀ hm hcrit hnotBinaryFixedPoint B hB hKappa hR s
  have htag := taggedSourceTerm_tailControlled_uniform
    m p₀ hm hcrit hnonconstant C Cb (sourceActualScalarEnvelope m B)
      hC hCb (sourceActualScalarEnvelope_nonneg m B (zero_le_one.trans hB))
      htagged hboundary (shiftNoExcessTag (Finset.mem_Icc.mp hR).2)
      (shiftNoExcessTag_valid hRthree (Finset.mem_Icc.mp hR).2)
      (arrivalAlpha m p₀ (s + 1) R) s N hN hscalars.1
  exact htag.congr
    (sourceShiftNoExcessTerm_eq_knownTagNormalForm
      p₀ (Finset.mem_Icc.mp hR).2 s).symm

theorem sourceShiftWithExcessTerm_tailControlled_uniform
    {m R : ℕ} (p₀ : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p₀) (hnonconstant : ¬ IsDirac p₀)
    (B C Cb : ℝ) (hB : 1 ≤ B) (hC : 0 < C) (hCb : 0 < Cb)
    (hKappa : ∀ s : ℕ, arrivalKappa m p₀ s ≤ B)
    (htagged : SourceTaggedTailBound m p₀ C)
    (hboundary : ArrivalBoundaryDecay m p₀ Cb)
    (hR : R ∈ Finset.Icc 2 m) (hRthree : 3 ≤ R) (s N : ℕ)
    (hN : s + SourceMonomialTag.sourceDifferenceCutoff m < N) :
    TailControlled (sourceShiftWithExcessTerm m p₀ s R) (N + s)
      (sourceUniformTagEnvelope m C Cb (sourceActualScalarEnvelope m B) *
        (1 + arrivalBoundary m p₀ s * ((s + 1 : ℕ) : ℝ) ^ 2) /
        (N : ℝ) ^ 3) := by
  have hnotBinaryFixedPoint : ¬ (m = 2 ∧ p₀ = diracMass 1) := by
    rintro ⟨_, hp₀⟩
    exact hnonconstant ⟨1, hp₀⟩
  have hscalars := shift_scalar_le_actualEnvelope
    p₀ hm hcrit hnotBinaryFixedPoint B hB hKappa hR s
  have htag := taggedSourceTerm_tailControlled_uniform
    m p₀ hm hcrit hnonconstant C Cb (sourceActualScalarEnvelope m B)
      hC hCb (sourceActualScalarEnvelope_nonneg m B (zero_le_one.trans hB))
      htagged hboundary (shiftWithExcessTag (Finset.mem_Icc.mp hR).2)
      (shiftWithExcessTag_valid hRthree (Finset.mem_Icc.mp hR).2)
      (-arrivalAlpha m p₀ (s + 1) R) s N hN hscalars.2
  exact htag.congr
    (sourceShiftWithExcessTerm_eq_knownTagNormalForm
      p₀ (Finset.mem_Icc.mp hR).1 (Finset.mem_Icc.mp hR).2 s).symm

theorem sourceFunctionExpandedTerm_tailControlled_uniform
    {m R : ℕ} (p₀ : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p₀) (hnonconstant : ¬ IsDirac p₀)
    (B C Cb : ℝ) (hB : 1 ≤ B) (hC : 0 < C) (hCb : 0 < Cb)
    (hKappa : ∀ s : ℕ, arrivalKappa m p₀ s ≤ B)
    (htagged : SourceTaggedTailBound m p₀ C)
    (hboundary : ArrivalBoundaryDecay m p₀ Cb)
    (hR : R ∈ Finset.Icc 2 m) (s N : ℕ)
    (hN : s + SourceMonomialTag.sourceDifferenceCutoff m < N)
    (choice : Fin R → SourceFactorChoice m)
    (hchoice : choice ∈ nontrivialFunctionChoices m R) :
    TailControlled (sourceFunctionExpandedTerm m p₀ s R choice) (N + s)
      (sourceUniformTagEnvelope m C Cb (sourceActualScalarEnvelope m B) *
        (1 + arrivalBoundary m p₀ s * ((s + 1 : ℕ) : ℝ) ^ 2) /
        (N : ℝ) ^ 3) := by
  have hnotBinaryFixedPoint : ¬ (m = 2 ∧ p₀ = diracMass 1) := by
    rintro ⟨_, hp₀⟩
    exact hnonconstant ⟨1, hp₀⟩
  have hvalid := functionChange_summand_has_valid_tag
    (Finset.mem_Icc.mp hR).1 (Finset.mem_Icc.mp hR).2 hchoice
  have htag := taggedSourceTerm_tailControlled_uniform
    m p₀ hm hcrit hnonconstant C Cb (sourceActualScalarEnvelope m B)
      hC hCb (sourceActualScalarEnvelope_nonneg m B (zero_le_one.trans hB))
      htagged hboundary (functionExpansionTag (Finset.mem_Icc.mp hR).2 choice)
      hvalid (arrivalAlpha m p₀ (s + 1) R * sourceChoiceScalar p₀ s choice)
      s N hN (functionChange_scalar_le_actualEnvelope
        p₀ hm hcrit hnotBinaryFixedPoint B hB hKappa hR s choice)
  exact htag.congr
    (sourceFunctionExpandedTerm_eq_tagNormalForm
      p₀ (Finset.mem_Icc.mp hR).2 s choice).symm

/-- Number of summands in a deliberately coarse count of the exact source
expansion.  At degree two the two shift terms cancel, but counting both is
harmless and keeps one uniform formula. -/
def sourceDifferenceExpansionCount (m : ℕ) : ℕ :=
  (Finset.Icc 2 m).sum (fun R ↦ 3 + (nontrivialFunctionChoices m R).card)

theorem sourceDifferenceExpansionCount_pos (m : ℕ) (hm : 2 ≤ m) :
    0 < sourceDifferenceExpansionCount m := by
  have htwo : 2 ∈ Finset.Icc 2 m := Finset.mem_Icc.mpr ⟨le_rfl, hm⟩
  have hsingle : 3 + (nontrivialFunctionChoices m 2).card ≤
      (Finset.Icc 2 m).sum
        (fun R ↦ 3 + (nontrivialFunctionChoices m R).card) := by
    exact Finset.single_le_sum
      (fun R _hR ↦ Nat.zero_le (3 + (nontrivialFunctionChoices m R).card)) htwo
  unfold sourceDifferenceExpansionCount
  omega

/-- The actual source difference satisfies the manuscript's `N^{-3}` bound,
with all finite triangle inequalities and absolute summability included. -/
theorem arrivalFormulaSource_sub_tailControlled_of_H1
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p₀) (hthird : TiltSummable m 3 p₀)
    (hnonconstant : ¬ IsDirac p₀)
    (hExcess : CDHLSExcessFact m p₀ hm hcrit hthird hnonconstant)
    (hProduct : CDHLSProductFact m p₀ hm hcrit hnonconstant) :
    ∃ Csource : ℝ, 0 < Csource ∧
      ∀ s N : ℕ, s + SourceMonomialTag.sourceDifferenceCutoff m < N →
        TailControlled
          (fun k : ℕ ↦
            arrivalFormulaSource m p₀ (s + 1) k - arrivalFormulaSource m p₀ s k)
          (N + s)
          (Csource *
            (1 + arrivalBoundary m p₀ s * ((s + 1 : ℕ) : ℝ) ^ 2) /
            (N : ℝ) ^ 3) := by
  have hnotBinaryFixedPoint : ¬ (m = 2 ∧ p₀ = diracMass 1) := by
    rintro ⟨_, hp₀⟩
    exact hnonconstant ⟨1, hp₀⟩
  rcases arrivalKappa_uniform_of_excess
      m p₀ hm hcrit hthird hnonconstant hExcess with ⟨B, hB, hKappa⟩
  rcases taggedSourceTerm_tail_bound_of_H1
      m p₀ hm hcrit hthird hnonconstant hExcess hProduct with
    ⟨C, hC, htagged⟩
  rcases arrivalBoundary_bound_of_H1
      m p₀ hm hcrit hthird hnonconstant hExcess hProduct with
    ⟨Cb, hCb, hboundary⟩
  let D : ℝ := sourceActualScalarEnvelope m B
  let U : ℝ := sourceUniformTagEnvelope m C Cb D
  let count : ℕ := sourceDifferenceExpansionCount m
  let Csource : ℝ := (count : ℝ) * U
  have hD : 0 ≤ D := sourceActualScalarEnvelope_nonneg m B (zero_le_one.trans hB)
  have hU : 0 < U := sourceUniformTagEnvelope_pos m C Cb D hC hD
  have hcount : 0 < count := sourceDifferenceExpansionCount_pos m hm
  have hCsource : 0 < Csource := by
    dsimp only [Csource]
    exact mul_pos (Nat.cast_pos.mpr hcount) hU
  refine ⟨Csource, hCsource, ?_⟩
  intro s N hN
  let Q : ℝ := U *
    (1 + arrivalBoundary m p₀ s * ((s + 1 : ℕ) : ℝ) ^ 2) /
    (N : ℝ) ^ 3
  have hb : 0 ≤ arrivalBoundary m p₀ s :=
    arrivalBoundary_nonneg m p₀ hm hcrit hnotBinaryFixedPoint s
  have hQ : 0 ≤ Q := by
    dsimp only [Q]
    positivity
  have houter : ∀ R ∈ Finset.Icc 2 m,
      TailControlled
        (fun k : ℕ ↦
          sourceCoefficientChangeTerm m p₀ s R k +
            sourceShiftNoExcessTerm m p₀ s R k +
            sourceShiftWithExcessTerm m p₀ s R k +
            ∑ choice ∈ nontrivialFunctionChoices m R,
              sourceFunctionExpandedTerm m p₀ s R choice k)
        (N + s)
        ((3 + (nontrivialFunctionChoices m R).card : ℕ) * Q) := by
    intro R hR
    have hcoef := sourceCoefficientChangeTerm_tailControlled_uniform
      p₀ hm hcrit hnonconstant B C Cb hB hC hCb hKappa htagged hboundary
        hR s N hN
    have hcoefQ : TailControlled
        (sourceCoefficientChangeTerm m p₀ s R) (N + s) Q := by
      simpa only [Q, U, D] using hcoef
    have hshift : TailControlled
        (fun k : ℕ ↦
          sourceShiftNoExcessTerm m p₀ s R k +
            sourceShiftWithExcessTerm m p₀ s R k)
        (N + s) (2 * Q) := by
      by_cases hRtwo : R = 2
      · subst R
        have hzero :
            (fun k : ℕ ↦
              sourceShiftNoExcessTerm m p₀ s 2 k +
                sourceShiftWithExcessTerm m p₀ s 2 k) = 0 := by
          funext k
          simpa using sourceShiftChange_eq_zero_of_degree_two m p₀ s k
        exact (tailControlled_zero (N + s) (2 * Q) (by positivity)).congr hzero.symm
      · have hRthree : 3 ≤ R := by
          have hRtwoLower := (Finset.mem_Icc.mp hR).1
          omega
        have hfirst := sourceShiftNoExcessTerm_tailControlled_uniform
          p₀ hm hcrit hnonconstant B C Cb hB hC hCb hKappa htagged hboundary
            hR hRthree s N hN
        have hsecond := sourceShiftWithExcessTerm_tailControlled_uniform
          p₀ hm hcrit hnonconstant B C Cb hB hC hCb hKappa htagged hboundary
            hR hRthree s N hN
        have hadd := hfirst.add hsecond
        simpa only [Q, U, D, two_mul] using hadd
    have hfunctionRaw := tailControlled_finset_sum
      (nontrivialFunctionChoices m R)
      (fun choice ↦ sourceFunctionExpandedTerm m p₀ s R choice)
      (N + s) (fun _choice ↦ Q) (by
        intro choice hchoice
        have hterm := sourceFunctionExpandedTerm_tailControlled_uniform
          p₀ hm hcrit hnonconstant B C Cb hB hC hCb hKappa htagged hboundary
            hR s N hN choice hchoice
        simpa only [Q, U, D] using hterm)
    have hfunction : TailControlled
        (fun k : ℕ ↦ ∑ choice ∈ nontrivialFunctionChoices m R,
          sourceFunctionExpandedTerm m p₀ s R choice k)
        (N + s) ((nontrivialFunctionChoices m R).card * Q) := by
      simpa only [Finset.sum_const, nsmul_eq_mul] using hfunctionRaw
    have hall := (hcoefQ.add hshift).add hfunction
    have hseq :
        (fun k : ℕ ↦
          (sourceCoefficientChangeTerm m p₀ s R k +
            (sourceShiftNoExcessTerm m p₀ s R k +
              sourceShiftWithExcessTerm m p₀ s R k)) +
            ∑ choice ∈ nontrivialFunctionChoices m R,
              sourceFunctionExpandedTerm m p₀ s R choice k) =
        (fun k : ℕ ↦
          sourceCoefficientChangeTerm m p₀ s R k +
            sourceShiftNoExcessTerm m p₀ s R k +
            sourceShiftWithExcessTerm m p₀ s R k +
            ∑ choice ∈ nontrivialFunctionChoices m R,
              sourceFunctionExpandedTerm m p₀ s R choice k) := by
      funext k
      ring
    have hall' := hall.congr hseq
    apply hall'.mono
    push_cast
    ring_nf
    exact le_rfl
  have hsum := tailControlled_finset_sum
    (Finset.Icc 2 m)
    (fun R k ↦
      sourceCoefficientChangeTerm m p₀ s R k +
        sourceShiftNoExcessTerm m p₀ s R k +
        sourceShiftWithExcessTerm m p₀ s R k +
        ∑ choice ∈ nontrivialFunctionChoices m R,
          sourceFunctionExpandedTerm m p₀ s R choice k)
    (N + s)
    (fun R ↦ ((3 + (nontrivialFunctionChoices m R).card : ℕ) : ℝ) * Q)
    houter
  have hsumBound : TailControlled
      (fun k : ℕ ↦ ∑ R ∈ Finset.Icc 2 m,
        (sourceCoefficientChangeTerm m p₀ s R k +
          sourceShiftNoExcessTerm m p₀ s R k +
          sourceShiftWithExcessTerm m p₀ s R k +
          ∑ choice ∈ nontrivialFunctionChoices m R,
            sourceFunctionExpandedTerm m p₀ s R choice k))
      (N + s) ((count : ℝ) * Q) := by
    apply hsum.mono
    have hcast :
        (∑ R ∈ Finset.Icc 2 m,
          (((3 + (nontrivialFunctionChoices m R).card : ℕ) : ℝ))) =
          (sourceDifferenceExpansionCount m : ℝ) := by
      simp [sourceDifferenceExpansionCount]
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right (by simpa only [count] using hcast.le) hQ
  have hactual :
      (fun k : ℕ ↦
        arrivalFormulaSource m p₀ (s + 1) k - arrivalFormulaSource m p₀ s k) =
      (fun k : ℕ ↦ ∑ R ∈ Finset.Icc 2 m,
        (sourceCoefficientChangeTerm m p₀ s R k +
          sourceShiftNoExcessTerm m p₀ s R k +
          sourceShiftWithExcessTerm m p₀ s R k +
          ∑ choice ∈ nontrivialFunctionChoices m R,
            sourceFunctionExpandedTerm m p₀ s R choice k)) := by
    funext k
    exact arrivalFormulaSource_sub_eq_fullyExpanded
      m p₀ hm hcrit hnotBinaryFixedPoint s k
  have hcontrolled := hsumBound.congr hactual.symm
  apply hcontrolled.mono
  dsimp only [Csource, count, Q]
  ring_nf
  exact le_rfl

/-- Inequality-only form of the concrete source-difference estimate. -/
theorem arrivalFormulaSource_sub_tail_bound_of_H1
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p₀) (hthird : TiltSummable m 3 p₀)
    (hnonconstant : ¬ IsDirac p₀)
    (hExcess : CDHLSExcessFact m p₀ hm hcrit hthird hnonconstant)
    (hProduct : CDHLSProductFact m p₀ hm hcrit hnonconstant) :
    ∃ Csource : ℝ, 0 < Csource ∧
      ∀ s N : ℕ, s + SourceMonomialTag.sourceDifferenceCutoff m < N →
        absoluteCoefficientTail
          (fun k : ℕ ↦
            arrivalFormulaSource m p₀ (s + 1) k - arrivalFormulaSource m p₀ s k)
          (N + s) ≤
        Csource *
          (1 + arrivalBoundary m p₀ s * ((s + 1 : ℕ) : ℝ) ^ 2) /
          (N : ℝ) ^ 3 := by
  rcases arrivalFormulaSource_sub_tailControlled_of_H1
      m p₀ hm hcrit hthird hnonconstant hExcess hProduct with
    ⟨Csource, hCsource, hsource⟩
  exact ⟨Csource, hCsource, fun s N hN ↦ (hsource s N hN).2⟩

/-- A finite visit-once block beginning strictly after time `v` is contained
in the absolute coefficient tail whose cutoff is `N + v`. -/
theorem sum_Ico_abs_le_of_tailControlled
    (a : Seq) (N v s : ℕ) (M : ℝ)
    (ha : TailControlled a (N + v) M) :
    ∑ j ∈ Finset.Ico (v + 1) s, |a (N + j - 1)| ≤ M := by
  rw [Finset.sum_Ico_eq_sum_range]
  have hindex : ∀ k : ℕ,
      N + (v + 1 + k) - 1 = k + (N + v) := by
    intro k
    omega
  simp_rw [hindex]
  exact (ha.1.sum_le_tsum (Finset.range (s - (v + 1)))
    (fun k _hk ↦ abs_nonneg (a (k + (N + v))))).trans ha.2

/-- Finite telescoping of the source in the time variable. -/
theorem arrivalFormulaSource_time_telescope
    (m : ℕ) (p₀ : ProbabilityMass) (j k : ℕ) :
    arrivalFormulaSource m p₀ j k =
      arrivalFormulaSource m p₀ 0 k +
        ∑ v ∈ Finset.range j,
          (arrivalFormulaSource m p₀ (v + 1) k -
            arrivalFormulaSource m p₀ v k) := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [Finset.sum_range_succ]
      calc
        arrivalFormulaSource m p₀ (j + 1) k =
            arrivalFormulaSource m p₀ j k +
              (arrivalFormulaSource m p₀ (j + 1) k -
                arrivalFormulaSource m p₀ j k) := by ring
        _ = (arrivalFormulaSource m p₀ 0 k +
              ∑ v ∈ Finset.range j,
                (arrivalFormulaSource m p₀ (v + 1) k -
                  arrivalFormulaSource m p₀ v k)) +
              (arrivalFormulaSource m p₀ (j + 1) k -
                arrivalFormulaSource m p₀ j k) := by rw [ih]
        _ = arrivalFormulaSource m p₀ 0 k +
              (∑ v ∈ Finset.range j,
                (arrivalFormulaSource m p₀ (v + 1) k -
                  arrivalFormulaSource m p₀ v k) +
                (arrivalFormulaSource m p₀ (j + 1) k -
                  arrivalFormulaSource m p₀ j k)) := by ring

/-- Visit-once estimate for the triangular source-difference contribution.
Every fixed time `v` is sampled only in the tail beginning at `N + v`. -/
theorem sourceDifference_triangle_le_of_tailControlled
    (m : ℕ) (p₀ : ProbabilityMass) (Csource : ℝ)
    (hsource : ∀ v N : ℕ,
      v + SourceMonomialTag.sourceDifferenceCutoff m < N →
        TailControlled
          (fun k : ℕ ↦
            arrivalFormulaSource m p₀ (v + 1) k -
              arrivalFormulaSource m p₀ v k)
          (N + v)
          (Csource *
            (1 + arrivalBoundary m p₀ v * ((v + 1 : ℕ) : ℝ) ^ 2) /
            (N : ℝ) ^ 3))
    (s N : ℕ) (hN : s + SourceMonomialTag.sourceDifferenceCutoff m < N) :
    (∑ j ∈ Finset.range s, ∑ v ∈ Finset.range j,
        (arrivalFormulaSource m p₀ (v + 1) (N + j - 1) -
          arrivalFormulaSource m p₀ v (N + j - 1))) ≤
      ∑ v ∈ Finset.range s,
        Csource *
          (1 + arrivalBoundary m p₀ v * ((v + 1 : ℕ) : ℝ) ^ 2) /
          (N : ℝ) ^ 3 := by
  calc
    (∑ j ∈ Finset.range s, ∑ v ∈ Finset.range j,
        (arrivalFormulaSource m p₀ (v + 1) (N + j - 1) -
          arrivalFormulaSource m p₀ v (N + j - 1))) ≤
        ∑ j ∈ Finset.range s, ∑ v ∈ Finset.range j,
          |arrivalFormulaSource m p₀ (v + 1) (N + j - 1) -
            arrivalFormulaSource m p₀ v (N + j - 1)| := by
      apply Finset.sum_le_sum
      intro j hj
      apply Finset.sum_le_sum
      intro v hv
      exact le_abs_self _
    _ = ∑ v ∈ Finset.range s, ∑ j ∈ Finset.Ico (v + 1) s,
          |arrivalFormulaSource m p₀ (v + 1) (N + j - 1) -
            arrivalFormulaSource m p₀ v (N + j - 1)| := by
      exact sum_range_sum_range_triangle
        (fun v j ↦
          |arrivalFormulaSource m p₀ (v + 1) (N + j - 1) -
            arrivalFormulaSource m p₀ v (N + j - 1)|) s
    _ ≤ ∑ v ∈ Finset.range s,
        Csource *
          (1 + arrivalBoundary m p₀ v * ((v + 1 : ℕ) : ℝ) ^ 2) /
          (N : ℝ) ^ 3 := by
      apply Finset.sum_le_sum
      intro v hv
      have hvs : v < s := Finset.mem_range.mp hv
      have hvN : v + SourceMonomialTag.sourceDifferenceCutoff m < N := by omega
      exact sum_Ico_abs_le_of_tailControlled
        (a := fun k : ℕ ↦
          arrivalFormulaSource m p₀ (v + 1) k -
            arrivalFormulaSource m p₀ v k)
        (N := N) (v := v) (s := s)
        (M := Csource *
          (1 + arrivalBoundary m p₀ v * ((v + 1 : ℕ) : ℝ) ^ 2) /
          (N : ℝ) ^ 3)
        (hsource v N hvN)

/-- The square-weighted boundary values have at most linear cumulative growth.
The identity `b_v = q_{v,1}/C_v` combines the existing first-atom Abel bound
with the uniform inverse transport-product bound. -/
theorem arrivalBoundary_squareWeight_sum_linear_bound
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p₀) (hthird : TiltSummable m 3 p₀)
    (hnonconstant : ¬ IsDirac p₀)
    (hExcess : CDHLSExcessFact m p₀ hm hcrit hthird hnonconstant) :
    ∃ Cboundary : ℝ, 0 < Cboundary ∧ ∀ s : ℕ,
      ∑ v ∈ Finset.range s,
          ((v + 1 : ℕ) : ℝ) ^ 2 * arrivalBoundary m p₀ v ≤
        Cboundary * ((s + 1 : ℕ) : ℝ) := by
  have hnotBinaryFixedPoint : ¬ (m = 2 ∧ p₀ = diracMass 1) := by
    rintro ⟨_, hp₀⟩
    exact hnonconstant ⟨1, hp₀⟩
  have hdefectOrbit := orbitTransportDefect_summable
    m p₀ hm hcrit hthird hnonconstant hExcess
  have hdefect :
      Summable (fun n : ℕ ↦ 1 - transportCoeff m (orbit m p₀ n)) := by
    simpa only [orbitTransportDefect] using hdefectOrbit
  rcases transportProduct_inverse_uniform
      m p₀ hm hcrit hnotBinaryFixedPoint hdefect with
    ⟨B, hB, hBinv⟩
  rcases firstTiltedAtom_squareWeight_sum_linear_bound
      m p₀ hm hcrit hthird hnonconstant hnotBinaryFixedPoint hExcess with
    ⟨A, hA, hfirst⟩
  refine ⟨B * A, mul_pos hB hA, ?_⟩
  intro s
  calc
    (∑ v ∈ Finset.range s,
        ((v + 1 : ℕ) : ℝ) ^ 2 * arrivalBoundary m p₀ v) ≤
        ∑ v ∈ Finset.range s,
          B * (((v + 1 : ℕ) : ℝ) ^ 2 * firstTiltedAtom m p₀ v) := by
      apply Finset.sum_le_sum
      intro v hv
      have hfirstNonneg : 0 ≤ firstTiltedAtom m p₀ v := by
        exact normalizedTilt_nonneg m (orbit m p₀ v) (by omega)
          (orbit_critical m p₀ (by omega) hcrit v) 1
      have hweightNonneg : 0 ≤ ((v + 1 : ℕ) : ℝ) ^ 2 := sq_nonneg _
      have hboundaryEq :
          arrivalBoundary m p₀ v =
            firstTiltedAtom m p₀ v * (transportProduct m p₀ v)⁻¹ := by
        simp only [arrivalBoundary_eq, firstTiltedAtom, orbitTilt,
          arrivalProduct, div_eq_mul_inv]
      rw [hboundaryEq]
      calc
        ((v + 1 : ℕ) : ℝ) ^ 2 *
            (firstTiltedAtom m p₀ v * (transportProduct m p₀ v)⁻¹) =
            (((v + 1 : ℕ) : ℝ) ^ 2 * firstTiltedAtom m p₀ v) *
              (transportProduct m p₀ v)⁻¹ := by ring
        _ ≤ (((v + 1 : ℕ) : ℝ) ^ 2 * firstTiltedAtom m p₀ v) * B :=
          mul_le_mul_of_nonneg_left (hBinv v)
            (mul_nonneg hweightNonneg hfirstNonneg)
        _ = B * (((v + 1 : ℕ) : ℝ) ^ 2 * firstTiltedAtom m p₀ v) := by ring
    _ = B * ∑ v ∈ Finset.range s,
          (((v + 1 : ℕ) : ℝ) ^ 2 * firstTiltedAtom m p₀ v) := by
      rw [Finset.mul_sum]
    _ ≤ B * (A * ((s + 1 : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_left (hfirst s) hB.le
    _ = (B * A) * ((s + 1 : ℕ) : ℝ) := by ring

/-- The complete finite source block is the visit-once initial tail plus the
sum of the concrete source-difference bounds. -/
theorem arrivalFormulaSource_block_le_initialTail_add_difference
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p₀) (hthird : TiltSummable m 3 p₀)
    (hnonconstant : ¬ IsDirac p₀)
    (hExcess : CDHLSExcessFact m p₀ hm hcrit hthird hnonconstant)
    (hProduct : CDHLSProductFact m p₀ hm hcrit hnonconstant) :
    ∃ Csource : ℝ, 0 < Csource ∧ ∀ s N : ℕ,
      s + SourceMonomialTag.sourceDifferenceCutoff m < N →
        (∑ j ∈ Finset.range s,
            arrivalFormulaSource m p₀ j (N + j - 1)) ≤
          coefficientTail (arrivalFormulaSource m p₀ 0) (N - 1) +
            ∑ v ∈ Finset.range s,
              Csource *
                (1 + arrivalBoundary m p₀ v * ((v + 1 : ℕ) : ℝ) ^ 2) /
                (N : ℝ) ^ 3 := by
  rcases arrivalFormulaSource_sub_tailControlled_of_H1
      m p₀ hm hcrit hthird hnonconstant hExcess hProduct with
    ⟨Csource, hCsource, hsource⟩
  refine ⟨Csource, hCsource, ?_⟩
  intro s N hN
  have hnotBinaryFixedPoint : ¬ (m = 2 ∧ p₀ = diracMass 1) := by
    rintro ⟨_, hp₀⟩
    exact hnonconstant ⟨1, hp₀⟩
  have hqNonneg := orbitPositiveTilt_nonneg m p₀ (by omega) hcrit 0
  have hqThree := orbitPositiveTilt_zero_cubic_summable_of_tiltSummable
    m p₀ hthird
  have hphiNonneg : ∀ k : ℕ, 0 ≤ arrivalCoeff m p₀ 0 k :=
    arrivalCoeff_zero_nonneg_of_positiveTilt m p₀ hqNonneg
  have hphiThree := arrivalCoeff_zero_cubic_summable_of_positiveTilt
    m p₀ hqNonneg hqThree
  have hsourceZeroThree := arrivalFormulaSource_zero_cubic_summable
    m p₀ hphiNonneg hphiThree
  have hNpos : 1 ≤ N := by
    simp only [SourceMonomialTag.sourceDifferenceCutoff] at hN
    omega
  have hinitial := arrivalInitialBlock_le_coefficientTail_of_cubic
    (arrivalFormulaSource m p₀ 0)
    (arrivalFormulaSource_nonneg
      m p₀ hm hcrit hnotBinaryFixedPoint 0)
    hsourceZeroThree N s hNpos
  calc
    (∑ j ∈ Finset.range s,
        arrivalFormulaSource m p₀ j (N + j - 1)) =
        ∑ j ∈ Finset.range s,
          (arrivalFormulaSource m p₀ 0 (N + j - 1) +
            ∑ v ∈ Finset.range j,
              (arrivalFormulaSource m p₀ (v + 1) (N + j - 1) -
                arrivalFormulaSource m p₀ v (N + j - 1))) := by
      apply Finset.sum_congr rfl
      intro j hj
      exact arrivalFormulaSource_time_telescope m p₀ j (N + j - 1)
    _ = (∑ j ∈ Finset.range s,
          arrivalFormulaSource m p₀ 0 (N + j - 1)) +
        ∑ j ∈ Finset.range s, ∑ v ∈ Finset.range j,
          (arrivalFormulaSource m p₀ (v + 1) (N + j - 1) -
            arrivalFormulaSource m p₀ v (N + j - 1)) := by
      rw [Finset.sum_add_distrib]
    _ ≤ coefficientTail (arrivalFormulaSource m p₀ 0) (N - 1) +
        ∑ v ∈ Finset.range s,
          Csource *
            (1 + arrivalBoundary m p₀ v * ((v + 1 : ℕ) : ℝ) ^ 2) /
            (N : ℝ) ^ 3 :=
      add_le_add hinitial
        (sourceDifference_triangle_le_of_tailControlled
          m p₀ Csource hsource s N hN)

/-- The finite sum of source-difference bounds is `O((s+1)N⁻³)` once the
square-weighted boundary prefix is linear. -/
theorem sourceDifference_bound_sum_linear
    (m : ℕ) (p₀ : ProbabilityMass) (Csource Cboundary : ℝ)
    (hCsource : 0 ≤ Csource)
    (hboundary : ∀ s : ℕ,
      ∑ v ∈ Finset.range s,
          ((v + 1 : ℕ) : ℝ) ^ 2 * arrivalBoundary m p₀ v ≤
        Cboundary * ((s + 1 : ℕ) : ℝ))
    (s N : ℕ) (hN : 1 ≤ N) :
    (∑ v ∈ Finset.range s,
        Csource *
          (1 + arrivalBoundary m p₀ v * ((v + 1 : ℕ) : ℝ) ^ 2) /
          (N : ℝ) ^ 3) ≤
      (Csource * (1 + Cboundary)) * ((s + 1 : ℕ) : ℝ) /
        (N : ℝ) ^ 3 := by
  have hdenomPos : 0 < (N : ℝ) ^ 3 := by positivity
  have hfactorNonneg : 0 ≤ Csource / (N : ℝ) ^ 3 :=
    div_nonneg hCsource hdenomPos.le
  have hsumEq :
      (∑ v ∈ Finset.range s,
          Csource *
            (1 + arrivalBoundary m p₀ v * ((v + 1 : ℕ) : ℝ) ^ 2) /
            (N : ℝ) ^ 3) =
        (Csource / (N : ℝ) ^ 3) *
          (((s : ℕ) : ℝ) +
            ∑ v ∈ Finset.range s,
              ((v + 1 : ℕ) : ℝ) ^ 2 * arrivalBoundary m p₀ v) := by
    calc
      (∑ v ∈ Finset.range s,
          Csource *
            (1 + arrivalBoundary m p₀ v * ((v + 1 : ℕ) : ℝ) ^ 2) /
            (N : ℝ) ^ 3) =
          ∑ v ∈ Finset.range s,
            (Csource / (N : ℝ) ^ 3) *
              (1 + arrivalBoundary m p₀ v * ((v + 1 : ℕ) : ℝ) ^ 2) := by
        apply Finset.sum_congr rfl
        intro v hv
        ring
      _ = (Csource / (N : ℝ) ^ 3) *
          ∑ v ∈ Finset.range s,
            (1 + arrivalBoundary m p₀ v * ((v + 1 : ℕ) : ℝ) ^ 2) := by
        rw [Finset.mul_sum]
      _ = (Csource / (N : ℝ) ^ 3) *
          (((s : ℕ) : ℝ) +
            ∑ v ∈ Finset.range s,
              ((v + 1 : ℕ) : ℝ) ^ 2 * arrivalBoundary m p₀ v) := by
        congr 1
        rw [Finset.sum_add_distrib]
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
        congr 1
        apply Finset.sum_congr rfl
        intro v hv
        ring
  rw [hsumEq]
  have hsle : ((s : ℕ) : ℝ) ≤ ((s + 1 : ℕ) : ℝ) := by
    exact_mod_cast (Nat.le_succ s)
  calc
    (Csource / (N : ℝ) ^ 3) *
        (((s : ℕ) : ℝ) +
          ∑ v ∈ Finset.range s,
            ((v + 1 : ℕ) : ℝ) ^ 2 * arrivalBoundary m p₀ v) ≤
        (Csource / (N : ℝ) ^ 3) *
          (((s : ℕ) : ℝ) + Cboundary * ((s + 1 : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_left
        (add_le_add_left (hboundary s) ((s : ℕ) : ℝ)) hfactorNonneg
    _ ≤ (Csource / (N : ℝ) ^ 3) *
          ((1 + Cboundary) * ((s + 1 : ℕ) : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ hfactorNonneg
      nlinarith
    _ = (Csource * (1 + Cboundary)) * ((s + 1 : ℕ) : ℝ) /
          (N : ℝ) ^ 3 := by ring

/-- The exact bounded error function used in the manuscript's far-arrival
estimate. -/
def arrivalFarOmega (m : ℕ) (p₀ : ProbabilityMass) (N : ℕ) : ℝ :=
  (N : ℝ) ^ 3 *
    (arrivalCoeff m p₀ 0 N +
      coefficientTail (arrivalFormulaSource m p₀ 0) (N - 1))

theorem arrivalFarOmega_tendsto_zero
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p₀) (hthird : TiltSummable m 3 p₀)
    (hnonconstant : ¬ IsDirac p₀) :
    Tendsto (arrivalFarOmega m p₀) atTop (𝓝 0) := by
  have hnotBinaryFixedPoint : ¬ (m = 2 ∧ p₀ = diracMass 1) := by
    rintro ⟨_, hp₀⟩
    exact hnonconstant ⟨1, hp₀⟩
  simpa only [arrivalFarOmega] using
    initialArrivalU24_tendsto_zero
      m p₀ hm hcrit hnotBinaryFixedPoint hthird

theorem arrivalFarOmega_isBounded
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p₀) (hthird : TiltSummable m 3 p₀)
    (hnonconstant : ¬ IsDirac p₀) :
    Bornology.IsBounded (Set.range (arrivalFarOmega m p₀)) := by
  exact Metric.isBounded_range_of_tendsto (arrivalFarOmega m p₀)
    (arrivalFarOmega_tendsto_zero m p₀ hm hcrit hthird hnonconstant)

/-- Source-shaped completion of `prop:far`: the displayed `ω` is bounded and
tends to zero, and the arrival coefficients satisfy the uniform cubic tail
bound beyond the manuscript cutoff. -/
theorem arrivalCoeff_far_bound_of_H1
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p₀) (hthird : TiltSummable m 3 p₀)
    (hnonconstant : ¬ IsDirac p₀)
    (hExcess : CDHLSExcessFact m p₀ hm hcrit hthird hnonconstant)
    (hProduct : CDHLSProductFact m p₀ hm hcrit hnonconstant) :
    ∃ Cfar : ℝ, 0 < Cfar ∧
      Bornology.IsBounded (Set.range (arrivalFarOmega m p₀)) ∧
      Tendsto (arrivalFarOmega m p₀) atTop (𝓝 0) ∧
      ∀ s N : ℕ, s + SourceMonomialTag.sourceDifferenceCutoff m < N →
        arrivalCoeff m p₀ s N ≤
          (arrivalFarOmega m p₀ N +
            Cfar * ((s + 1 : ℕ) : ℝ)) / (N : ℝ) ^ 3 := by
  rcases arrivalFormulaSource_block_le_initialTail_add_difference
      m p₀ hm hcrit hthird hnonconstant hExcess hProduct with
    ⟨Csource, hCsource, hsourceBlock⟩
  rcases arrivalBoundary_squareWeight_sum_linear_bound
      m p₀ hm hcrit hthird hnonconstant hExcess with
    ⟨Cboundary, hCboundary, hboundary⟩
  let Cfar : ℝ := Csource * (1 + Cboundary)
  have hCfar : 0 < Cfar := by
    dsimp only [Cfar]
    exact mul_pos hCsource (by linarith)
  refine ⟨Cfar, hCfar,
    arrivalFarOmega_isBounded m p₀ hm hcrit hthird hnonconstant,
    arrivalFarOmega_tendsto_zero m p₀ hm hcrit hthird hnonconstant, ?_⟩
  intro s N hN
  have hsN : s ≤ N := by
    simp only [SourceMonomialTag.sourceDifferenceCutoff] at hN
    omega
  have hNpos : 1 ≤ N := by
    simp only [SourceMonomialTag.sourceDifferenceCutoff] at hN
    omega
  have hblock := hsourceBlock s N hN
  have hsum := sourceDifference_bound_sum_linear
    m p₀ Csource Cboundary hCsource.le hboundary s N hNpos
  rw [arrivalCoeff_duhamel
    m p₀ hm hcrit (by
      rintro ⟨_, hp₀⟩
      exact hnonconstant ⟨1, hp₀⟩) s N hsN]
  calc
    arrivalCoeff m p₀ 0 N +
        ∑ j ∈ Finset.range s,
          arrivalFormulaSource m p₀ j (N + j - 1) ≤
        arrivalCoeff m p₀ 0 N +
          (coefficientTail (arrivalFormulaSource m p₀ 0) (N - 1) +
            ∑ v ∈ Finset.range s,
              Csource *
                (1 + arrivalBoundary m p₀ v * ((v + 1 : ℕ) : ℝ) ^ 2) /
                (N : ℝ) ^ 3) := add_le_add_left hblock _
    _ = (arrivalCoeff m p₀ 0 N +
          coefficientTail (arrivalFormulaSource m p₀ 0) (N - 1)) +
        ∑ v ∈ Finset.range s,
          Csource *
            (1 + arrivalBoundary m p₀ v * ((v + 1 : ℕ) : ℝ) ^ 2) /
            (N : ℝ) ^ 3 := by ring
    _ ≤ (arrivalCoeff m p₀ 0 N +
          coefficientTail (arrivalFormulaSource m p₀ 0) (N - 1)) +
        (Csource * (1 + Cboundary)) * ((s + 1 : ℕ) : ℝ) /
          (N : ℝ) ^ 3 := add_le_add_left hsum _
    _ = (arrivalFarOmega m p₀ N +
          Cfar * ((s + 1 : ℕ) : ℝ)) / (N : ℝ) ^ 3 := by
      have hdenom : (N : ℝ) ^ 3 ≠ 0 := by positivity
      dsimp only [arrivalFarOmega, Cfar]
      field_simp [hdenom]
      ring

end

end DerridaRetaux
