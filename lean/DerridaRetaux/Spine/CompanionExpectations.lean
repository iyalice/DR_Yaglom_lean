import DerridaRetaux.Spine.FactorialCauchy
import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 2000000

open scoped BigOperators

namespace DerridaRetaux

noncomputable section

/-!
# Companion expectations for the cubic-spine allocation

This module proves the three iid companion identities used in the calculation
following `eq:incformula`.  No moment or independence statement is assumed:
all of them are consequences of the literal finite-product mass.
-/

/-- Product-weight expectation of a product of coordinate factors. -/
theorem iidTupleWeight_mul_coordinateFactors_hasSum
    (q : ProbabilityMass) (r : ℕ) (phi : Fin r → ℕ → ℝ) (M : Fin r → ℝ)
    (hphiNonneg : ∀ i k, 0 ≤ phi i k)
    (hphiSum : ∀ i, HasSum (fun k ↦ q k * phi i k) (M i)) :
    HasSum
      (fun y : Fin r → ℕ ↦ iidTupleWeight q y * ∏ i, phi i (y i))
      (∏ i, M i) := by
  have h := finitePiProduct_hasSum r
    (fun i k ↦ q k * phi i k) M
    (fun i k ↦ mul_nonneg (q.nonneg k) (hphiNonneg i k)) hphiSum
  convert h using 1
  funext y
  rw [iidTupleWeight, ← Finset.prod_mul_distrib]

/-- One marked coordinate may carry any nonnegative summable observable. -/
theorem iidTupleWeight_mul_coordinateFunction_hasSum
    (q : ProbabilityMass) (r : ℕ) (i : Fin r) (F : ℕ → ℝ) (A : ℝ)
    (hFNonneg : ∀ k, 0 ≤ F k) (hF : HasSum (fun k ↦ q k * F k) A) :
    HasSum (fun y : Fin r → ℕ ↦ iidTupleWeight q y * F (y i)) A := by
  let phi : Fin r → ℕ → ℝ := fun j k ↦ if j = i then F k else 1
  let M : Fin r → ℝ := fun j ↦ if j = i then A else 1
  have h := iidTupleWeight_mul_coordinateFactors_hasSum q r phi M
    (fun j k ↦ by
      by_cases hji : j = i
      · simp [phi, hji, hFNonneg k]
      · simp [phi, hji])
    (fun j ↦ by
      by_cases hji : j = i
      · simpa [phi, M, hji] using hF
      · simpa [phi, M, hji] using q.hasSum_coe)
  convert h using 1
  · funext y
    simp [phi, Fintype.prod_ite_eq']
  · simp [M, Fintype.prod_ite_eq']

/-- Two distinct marked coordinates factor. -/
theorem iidTupleWeight_mul_twoCoordinateFunctions_hasSum
    (q : ProbabilityMass) (r : ℕ) (i j : Fin r) (hij : i ≠ j)
    (F G : ℕ → ℝ) (A B : ℝ)
    (hFNonneg : ∀ k, 0 ≤ F k) (hGNonneg : ∀ k, 0 ≤ G k)
    (hF : HasSum (fun k ↦ q k * F k) A)
    (hG : HasSum (fun k ↦ q k * G k) B) :
    HasSum
      (fun y : Fin r → ℕ ↦ iidTupleWeight q y * F (y i) * G (y j))
      (A * B) := by
  let phi : Fin r → ℕ → ℝ := fun x k ↦
    (if x = i then F k else 1) * (if x = j then G k else 1)
  let M : Fin r → ℝ := fun x ↦
    (if x = i then A else 1) * (if x = j then B else 1)
  have h := iidTupleWeight_mul_coordinateFactors_hasSum q r phi M
    (fun x k ↦ mul_nonneg (by split_ifs <;> simp [hFNonneg k])
      (by split_ifs <;> simp [hGNonneg k]))
    (fun x ↦ by
      by_cases hxi : x = i
      · subst x
        simpa [phi, M, hij] using hF
      · by_cases hxj : x = j
        · subst x
          simpa [phi, M, hxi, hij] using hG
        · simpa [phi, M, hxi, hxj] using q.hasSum_coe)
  convert h using 1
  · funext y
    simp only [phi, Finset.prod_mul_distrib]
    simp [Fintype.prod_ite_eq']
    ring
  · simp only [M, Finset.prod_mul_distrib]
    simp [Fintype.prod_ite_eq', hij]

/-- Three pairwise-distinct marked coordinates factor. -/
theorem iidTupleWeight_mul_threeCoordinateFunctions_hasSum
    (q : ProbabilityMass) (r : ℕ) (i j l : Fin r)
    (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l)
    (F G H : ℕ → ℝ) (A B C : ℝ)
    (hFNonneg : ∀ k, 0 ≤ F k) (hGNonneg : ∀ k, 0 ≤ G k)
    (hHNonneg : ∀ k, 0 ≤ H k)
    (hF : HasSum (fun k ↦ q k * F k) A)
    (hG : HasSum (fun k ↦ q k * G k) B)
    (hH : HasSum (fun k ↦ q k * H k) C) :
    HasSum
      (fun y : Fin r → ℕ ↦
        iidTupleWeight q y * F (y i) * G (y j) * H (y l))
      (A * B * C) := by
  let phi : Fin r → ℕ → ℝ := fun x k ↦
    (if x = i then F k else 1) *
      (if x = j then G k else 1) * (if x = l then H k else 1)
  let M : Fin r → ℝ := fun x ↦
    (if x = i then A else 1) *
      (if x = j then B else 1) * (if x = l then C else 1)
  have h := iidTupleWeight_mul_coordinateFactors_hasSum q r phi M
    (fun x k ↦ mul_nonneg
      (mul_nonneg (by split_ifs <;> simp [hFNonneg k])
        (by split_ifs <;> simp [hGNonneg k]))
      (by split_ifs <;> simp [hHNonneg k]))
    (fun x ↦ by
      by_cases hxi : x = i
      · subst x
        simpa [phi, M, hij, hil] using hF
      · by_cases hxj : x = j
        · subst x
          simpa [phi, M, hxi, hij, hjl] using hG
        · by_cases hxl : x = l
          · subst x
            simpa [phi, M, hxi, hxj, hil, hjl] using hH
          · simpa [phi, M, hxi, hxj, hxl] using q.hasSum_coe)
  convert h using 1
  · funext y
    simp only [phi, Finset.prod_mul_distrib]
    simp [Fintype.prod_ite_eq']
    ring
  · simp only [M, Finset.prod_mul_distrib]
    simp [Fintype.prod_ite_eq', hij, hil, hjl]

/-- Natural positive part `(U-1)_+` of the companion total. -/
def companionExcess {r : ℕ} (y : Fin r → ℕ) : ℝ :=
  ((∑ i, y i) - 1 : ℕ)

/-- Indicator of the all-zero companion tuple. -/
def companionZeroIndicator {r : ℕ} (y : Fin r → ℕ) : ℝ :=
  if (∑ i, y i) = 0 then 1 else 0

theorem companionExcess_eq_sum_sub_one_add_zeroIndicator
    {r : ℕ} (y : Fin r → ℕ) :
    companionExcess y = companionSum y - 1 + companionZeroIndicator y := by
  let U : ℕ := ∑ i, y i
  have hsum : companionSum y = U := by simp [companionSum, U]
  rw [companionExcess, companionZeroIndicator, hsum]
  change (((U - 1 : ℕ) : ℝ)) = (U : ℝ) - 1 + (if U = 0 then 1 else 0)
  cases U with
  | zero => simp
  | succ U => simp

private theorem criticalCompanionMeanCoefficient'
    (m : ℕ) (hm : 2 ≤ m) :
    ((m - 1 : ℕ) : ℝ) * (1 / ((m : ℝ) - 1)) = 1 := by
  rw [Nat.cast_sub (by omega)]
  have hden : (m : ℝ) - 1 ≠ 0 := by
    have hmReal : (2 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  field_simp

theorem iidTupleWeight_mul_zeroIndicator_hasSum
    (q : ProbabilityMass) (r : ℕ) :
    HasSum
      (fun y : Fin r → ℕ ↦ iidTupleWeight q y * companionZeroIndicator y)
      ((q 0) ^ r) := by
  let phi : Fin r → ℕ → ℝ := fun _ k ↦ if k = 0 then 1 else 0
  let M : Fin r → ℝ := fun _ ↦ q 0
  have hcoord (i : Fin r) : HasSum (fun k ↦ q k * phi i k) (M i) := by
    convert hasSum_ite_eq 0 (q 0) using 1
    funext k
    by_cases hk : k = 0 <;> simp [phi, M, hk]
  have h := iidTupleWeight_mul_coordinateFactors_hasSum q r phi M
    (fun _ k ↦ by by_cases hk : k = 0 <;> simp [phi, hk]) hcoord
  convert h using 1
  · funext y
    congr 1
    have hiff : (∑ i, y i) = 0 ↔ ∀ i, y i = 0 := by
      constructor
      · intro hzero i
        have hle : y i ≤ ∑ j, y j := Finset.single_le_sum
          (fun j _ ↦ Nat.zero_le (y j)) (Finset.mem_univ i)
        omega
      · intro hy
        simp [hy]
    simp [phi, companionZeroIndicator, Fintype.prod_boole, hiff]
  · simp [M]

/-- First companion identity in the paper: `E[(U-1)_+] = x^(m-1)`. -/
theorem iidTupleWeight_mul_companionExcess_hasSum
    (m : ℕ) (p : ProbabilityMass) (hm : 2 ≤ m) (hcrit : Critical m p) :
    HasSum
      (fun y : Fin (m - 1) → ℕ ↦
        iidTupleWeight (criticalTiltLaw m p hm hcrit) y * companionExcess y)
      (zeroTilt m p ^ (m - 1)) := by
  let q := criticalTiltLaw m p hm hcrit
  let mu : ℝ := 1 / ((m : ℝ) - 1)
  have hmass := iidTupleWeight_hasSum q (m - 1)
  have hmean : HasSum (fun k : ℕ ↦ (k : ℝ) * q k) mu := by
    simpa [q, mu] using normalizedTilt_mean_hasSum m p (by omega) hcrit
  have hsumRaw := iidTupleWeight_mul_companionSum_hasSum q (m - 1) mu hmean
  have hsum : HasSum
      (fun y : Fin (m - 1) → ℕ ↦ iidTupleWeight q y * companionSum y) 1 := by
    convert hsumRaw using 1
    exact (criticalCompanionMeanCoefficient' m hm).symm
  have hzero := iidTupleWeight_mul_zeroIndicator_hasSum q (m - 1)
  have hcombined := (hsum.sub hmass).add hzero
  convert hcombined using 1
  · funext y
    rw [companionExcess_eq_sum_sub_one_add_zeroIndicator]
    ring
  · simp [q]

theorem companionSum_mul_companionExcess
    {r : ℕ} (y : Fin r → ℕ) :
    companionSum y * companionExcess y =
      (∑ i, fallingFactorialTwo (y i)) + 2 * companionPairSum y := by
  let U : ℕ := ∑ i, y i
  have hsum : companionSum y = U := by simp [companionSum, U]
  have hpred : (U : ℝ) * ((U - 1 : ℕ) : ℝ) = (U : ℝ) ^ 2 - U := by
    cases U with
    | zero => simp
    | succ U => simp; ring
  have hsq := companionSum_sq y
  rw [hsum] at hsq
  have hcast : (∑ i, (y i : ℝ)) = (U : ℝ) := by simp [U]
  rw [companionExcess, hsum]
  calc
    (U : ℝ) * ((U - 1 : ℕ) : ℝ) = (U : ℝ) ^ 2 - U := hpred
    _ = ((∑ i, (y i : ℝ) ^ 2) + 2 * companionPairSum y) - U := by rw [hsq]
    _ = (∑ i, fallingFactorialTwo (y i)) + 2 * companionPairSum y := by
      calc
        ((∑ i, (y i : ℝ) ^ 2) + 2 * companionPairSum y) - U =
            ((∑ i, (y i : ℝ) ^ 2) - ∑ i, (y i : ℝ)) +
              2 * companionPairSum y := by rw [hcast]; ring
        _ = (∑ i, ((y i : ℝ) ^ 2 - (y i : ℝ))) +
              2 * companionPairSum y := by rw [Finset.sum_sub_distrib]
        _ = (∑ i, fallingFactorialTwo (y i)) + 2 * companionPairSum y := by
          congr 1
          apply Finset.sum_congr rfl
          intro i _
          simp only [fallingFactorialTwo]
          ring

/-- Second companion identity: `E[U(U-1)] = (m-1)b + chi`. -/
theorem iidTupleWeight_mul_companionSum_companionExcess_hasSum
    (m : ℕ) (p : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p) (hthird : TiltSummable m 3 p) :
    HasSum
      (fun y : Fin (m - 1) → ℕ ↦
        iidTupleWeight (criticalTiltLaw m p hm hcrit) y *
          (companionSum y * companionExcess y))
      (((m : ℝ) - 1) * normalizedFactorialTwo m p + cubicChi m) := by
  let q := criticalTiltLaw m p hm hcrit
  let b := normalizedFactorialTwo m p
  let mu : ℝ := 1 / ((m : ℝ) - 1)
  have hb : HasSum (fun k : ℕ ↦ q k * fallingFactorialTwo k) b := by
    have hb' := (normalizedFactorialTwo_summable m p (by omega) hcrit hthird).hasSum
    convert hb' using 1
    · funext k
      simp only [q, criticalTiltLaw_apply]
      ring
  have hone (i : Fin (m - 1)) : HasSum
      (fun y : Fin (m - 1) → ℕ ↦
        iidTupleWeight q y * fallingFactorialTwo (y i)) b :=
    iidTupleWeight_mul_coordinateFunction_hasSum q (m - 1) i fallingFactorialTwo b
      fallingFactorialTwo_nonneg hb
  have hdiagRaw := hasSum_sum (s := Finset.univ) (fun i _ ↦ hone i)
  have hdiag : HasSum
      (fun y : Fin (m - 1) → ℕ ↦
        iidTupleWeight q y * ∑ i, fallingFactorialTwo (y i))
      (((m : ℝ) - 1) * b) := by
    convert hdiagRaw using 1
    · funext y
      simp [Finset.mul_sum]
    · simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      rw [Nat.cast_sub (by omega)]
      norm_num
  have hmean : HasSum (fun k : ℕ ↦ (k : ℝ) * q k) mu := by
    simpa [q, mu] using normalizedTilt_mean_hasSum m p (by omega) hcrit
  have hpairRaw := iidTupleWeight_mul_companionPairSum_hasSum_closed
    q (m - 1) (by omega) mu hmean
  have hpair : HasSum
      (fun y : Fin (m - 1) → ℕ ↦ iidTupleWeight q y * (2 * companionPairSum y))
      (cubicChi m) := by
    convert hpairRaw.mul_left 2 using 1
    · funext y
      ring
    · rw [Nat.cast_sub (by omega)]
      have hden : (m : ℝ) - 1 ≠ 0 := by
        have hmReal : (2 : ℝ) ≤ m := by exact_mod_cast hm
        linarith
      simp only [mu, cubicChi]
      field_simp
      ring
  have h := hdiag.add hpair
  convert h using 1
  · funext y
    rw [companionSum_mul_companionExcess]
    ring

/-- Coordinates other than a fixed distinct pair. -/
def companionOtherIndices {r : ℕ} (i j : Fin r) : Finset (Fin r) :=
  (Finset.univ.erase i).erase j

theorem companionSum_eq_pair_add_other
    {r : ℕ} (y : Fin r → ℕ) (i j : Fin r) (hij : i ≠ j) :
    companionSum y =
      (y i : ℝ) + (y j : ℝ) +
        ∑ l ∈ companionOtherIndices i j, (y l : ℝ) := by
  have hjmem : j ∈ Finset.univ.erase i := by simp [hij.symm]
  rw [companionSum, ← Finset.univ.sum_erase_add (fun l ↦ (y l : ℝ))
    (Finset.mem_univ i)]
  rw [← (Finset.univ.erase i).sum_erase_add (fun l ↦ (y l : ℝ)) hjmem]
  simp only [companionOtherIndices]
  ring

theorem companionOtherIndices_card
    {r : ℕ} (i j : Fin r) (hij : i ≠ j) :
    (companionOtherIndices i j).card = r - 2 := by
  have hjmem : j ∈ Finset.univ.erase i := by simp [hij.symm]
  rw [companionOtherIndices, Finset.card_erase_of_mem hjmem,
    Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
  omega

theorem pair_mul_companionExcess
    {r : ℕ} (y : Fin r → ℕ) (i j : Fin r) (hij : i ≠ j) :
    (y i : ℝ) * (y j : ℝ) * companionExcess y =
      fallingFactorialTwo (y i) * (y j : ℝ) +
        (y i : ℝ) * fallingFactorialTwo (y j) +
          (y i : ℝ) * (y j : ℝ) +
            ∑ l ∈ companionOtherIndices i j,
              (y i : ℝ) * (y j : ℝ) * (y l : ℝ) := by
  let U : ℕ := ∑ l, y l
  have hsum : companionSum y = U := by simp [companionSum, U]
  by_cases hU : U = 0
  · have hiZero : y i = 0 := by
      have hle : y i ≤ ∑ l, y l := Finset.single_le_sum
        (fun l _ ↦ Nat.zero_le (y l)) (Finset.mem_univ i)
      simp only [U] at hU
      omega
    simp [hiZero, fallingFactorialTwo]
  · have hUpos : 1 ≤ U := Nat.one_le_iff_ne_zero.mpr hU
    have hpairSum := companionSum_eq_pair_add_other y i j hij
    rw [hsum] at hpairSum
    rw [companionExcess, show (∑ l, y l) = U by rfl, Nat.cast_sub hUpos]
    simp only [fallingFactorialTwo]
    rw [hpairSum]
    simp only [← Finset.mul_sum]
    ring

theorem iidTupleWeight_mul_pair_companionExcess_hasSum
    (q : ProbabilityMass) (r : ℕ) (i j : Fin r) (hij : i ≠ j)
    (mu b : ℝ)
    (hmean : HasSum (fun k : ℕ ↦ q k * (k : ℝ)) mu)
    (hfallingTwo : HasSum (fun k : ℕ ↦ q k * fallingFactorialTwo k) b) :
    HasSum
      (fun y : Fin r → ℕ ↦
        iidTupleWeight q y * ((y i : ℝ) * (y j : ℝ) * companionExcess y))
      (b * mu + mu * b + mu ^ 2 + ((r - 2 : ℕ) : ℝ) * mu ^ 3) := by
  have hfi := iidTupleWeight_mul_twoCoordinateFunctions_hasSum
    q r i j hij fallingFactorialTwo (fun k ↦ (k : ℝ)) b mu
    fallingFactorialTwo_nonneg (fun k ↦ Nat.cast_nonneg k) hfallingTwo hmean
  have hfj := iidTupleWeight_mul_twoCoordinateFunctions_hasSum
    q r i j hij (fun k ↦ (k : ℝ)) fallingFactorialTwo mu b
    (fun k ↦ Nat.cast_nonneg k) fallingFactorialTwo_nonneg hmean hfallingTwo
  have hijMoment := iidTupleWeight_mul_twoCoordinateFunctions_hasSum
    q r i j hij (fun k ↦ (k : ℝ)) (fun k ↦ (k : ℝ)) mu mu
    (fun k ↦ Nat.cast_nonneg k) (fun k ↦ Nat.cast_nonneg k) hmean hmean
  have htriple (l : Fin r) (hl : l ∈ companionOtherIndices i j) :
      HasSum
        (fun y : Fin r → ℕ ↦
          iidTupleWeight q y * (y i : ℝ) * (y j : ℝ) * (y l : ℝ))
        (mu ^ 3) := by
    have hli : l ≠ i := by
      simp only [companionOtherIndices, Finset.mem_erase] at hl
      exact hl.2.1
    have hlj : l ≠ j := by
      simp only [companionOtherIndices, Finset.mem_erase] at hl
      exact hl.1
    convert iidTupleWeight_mul_threeCoordinateFunctions_hasSum
      q r i j l hij hli.symm hlj.symm
        (fun k ↦ (k : ℝ)) (fun k ↦ (k : ℝ)) (fun k ↦ (k : ℝ))
        mu mu mu
        (fun k ↦ Nat.cast_nonneg k) (fun k ↦ Nat.cast_nonneg k)
        (fun k ↦ Nat.cast_nonneg k) hmean hmean hmean using 1
    · ring
  have hrestRaw := hasSum_sum (s := companionOtherIndices i j) htriple
  have hrest : HasSum
      (fun y : Fin r → ℕ ↦
        iidTupleWeight q y *
          ∑ l ∈ companionOtherIndices i j,
            (y i : ℝ) * (y j : ℝ) * (y l : ℝ))
      (((r - 2 : ℕ) : ℝ) * mu ^ 3) := by
    convert hrestRaw using 1
    · funext y
      simp [Finset.mul_sum]
      ring_nf
    · rw [Finset.sum_const, nsmul_eq_mul, companionOtherIndices_card i j hij]
  have h := ((hfi.add hfj).add hijMoment).add hrest
  convert h using 1
  · funext y
    rw [pair_mul_companionExcess y i j hij]
    ring
  · ring

/-- Third companion identity: `E[V(U-1)] = (m-2)b + chi^2`. -/
theorem iidTupleWeight_mul_companionPairSum_companionExcess_hasSum
    (m : ℕ) (p : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p) (hthird : TiltSummable m 3 p) :
    HasSum
      (fun y : Fin (m - 1) → ℕ ↦
        iidTupleWeight (criticalTiltLaw m p hm hcrit) y *
          (companionPairSum y * companionExcess y))
      (((m : ℝ) - 2) * normalizedFactorialTwo m p + cubicChi m ^ 2) := by
  let q := criticalTiltLaw m p hm hcrit
  let r := m - 1
  let mu : ℝ := 1 / ((m : ℝ) - 1)
  let b := normalizedFactorialTwo m p
  have hmean : HasSum (fun k : ℕ ↦ q k * (k : ℝ)) mu := by
    convert normalizedTilt_mean_hasSum m p (by omega) hcrit using 1
    · funext k
      simp only [q, criticalTiltLaw_apply]
      ring
  have hfallingTwo : HasSum (fun k : ℕ ↦ q k * fallingFactorialTwo k) b := by
    have h := (normalizedFactorialTwo_summable m p (by omega) hcrit hthird).hasSum
    convert h using 1
    funext k
    simp only [q, criticalTiltLaw_apply]
    ring
  have hpair (i : Fin r) (j : Fin r) (hj : j ∈ Finset.Ioi i) :=
    iidTupleWeight_mul_pair_companionExcess_hasSum q r i j
      (ne_of_lt (Finset.mem_Ioi.mp hj)) mu b hmean hfallingTwo
  have hraw := hasSum_sum (s := Finset.univ) (fun i _ ↦
    hasSum_sum (s := Finset.Ioi i) (fun j hj ↦ hpair i j hj))
  have hcount :
      (∑ i : Fin r, ∑ _j ∈ Finset.Ioi i, (1 : ℝ)) =
        (r : ℝ) * ((r : ℝ) - 1) / 2 := by
    simpa using companionPairMoment_sum_eq r (by omega) 1
  have hcardCount :
      (∑ i : Fin r, ((Finset.Ioi i).card : ℝ)) =
        (r : ℝ) * ((r : ℝ) - 1) / 2 := by
    simpa [Finset.sum_const, nsmul_eq_mul] using hcount
  convert hraw using 1
  · funext y
    change iidTupleWeight q y *
        ((∑ i, ∑ j ∈ Finset.Ioi i, (y i : ℝ) * (y j : ℝ)) *
          companionExcess y) = _
    calc
      iidTupleWeight q y *
          ((∑ i, ∑ j ∈ Finset.Ioi i, (y i : ℝ) * (y j : ℝ)) *
            companionExcess y) =
          (iidTupleWeight q y * companionExcess y) *
            (∑ i, ∑ j ∈ Finset.Ioi i, (y i : ℝ) * (y j : ℝ)) := by ring
      _ = ∑ i, (iidTupleWeight q y * companionExcess y) *
            (∑ j ∈ Finset.Ioi i, (y i : ℝ) * (y j : ℝ)) := by
        rw [Finset.mul_sum]
      _ = ∑ i, ∑ j ∈ Finset.Ioi i,
            (iidTupleWeight q y * companionExcess y) *
              ((y i : ℝ) * (y j : ℝ)) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.mul_sum]
      _ = ∑ i, ∑ j ∈ Finset.Ioi i,
            iidTupleWeight q y *
              ((y i : ℝ) * (y j : ℝ) * companionExcess y) := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring
  · simp_rw [Finset.sum_const, nsmul_eq_mul]
    rw [← Finset.sum_mul, hcardCount]
    dsimp only [r, mu, b]
    by_cases hm2 : m = 2
    · subst m
      norm_num [cubicChi]
    · have hm3 : 3 ≤ m := by omega
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
      norm_num
      have hden : (m : ℝ) - 1 ≠ 0 := by
        have hmReal : (2 : ℝ) ≤ m := by exact_mod_cast hm
        linarith
      simp only [cubicChi]
      field_simp
      ring

end

end DerridaRetaux
