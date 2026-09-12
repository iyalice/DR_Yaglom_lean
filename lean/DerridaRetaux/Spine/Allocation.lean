import DerridaRetaux.Spine.SizeBiased
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 400000

open scoped BigOperators

namespace DerridaRetaux

noncomputable section

/-!
# Cubic-spine allocation weights

This file supplies the finite-product summation layer behind the allocation
density in `lem:spine`.  Companion configurations are literal functions
`Fin (m - 1) → ℕ`, with their iid product mass kept transparent.
-/

/-- A finite heterogeneous product of nonnegative summable coordinate weights. -/
theorem finitePiProduct_hasSum
    (r : ℕ) (a : Fin r → ℕ → ℝ) (s : Fin r → ℝ)
    (haNonneg : ∀ i k, 0 ≤ a i k)
    (haSum : ∀ i, HasSum (a i) (s i)) :
    HasSum (fun y : Fin r → ℕ ↦ ∏ i, a i (y i)) (∏ i, s i) := by
  induction r with
  | zero =>
      simp
  | succ r ih =>
      let e : (ℕ × (Fin r → ℕ)) ≃ (Fin (r + 1) → ℕ) :=
        Fin.insertNthEquiv (fun _ : Fin (r + 1) ↦ ℕ) 0
      have hhead : HasSum (a 0) (s 0) := haSum 0
      have htail :
          HasSum
            (fun y : Fin r → ℕ ↦ ∏ i, a i.succ (y i))
            (∏ i : Fin r, s i.succ) :=
        ih (fun i ↦ a i.succ) (fun i ↦ s i.succ)
          (fun i k ↦ haNonneg i.succ k) (fun i ↦ haSum i.succ)
      have hproductSummable :
          Summable (fun z : ℕ × (Fin r → ℕ) ↦
            a 0 z.1 * ∏ i, a i.succ (z.2 i)) := by
        apply (summable_prod_of_nonneg (fun z : ℕ × (Fin r → ℕ) ↦
          mul_nonneg (haNonneg 0 z.1)
          (Finset.prod_nonneg fun i _ ↦ haNonneg i.succ (z.2 i)))).2
        constructor
        · intro k
          exact htail.summable.mul_left (a 0 k)
        · convert hhead.summable.mul_right (∏ i : Fin r, s i.succ) using 1
          funext k
          simp only [Prod.fst, Prod.snd]
          rw [htail.summable.tsum_mul_left, htail.tsum_eq]
      have hproduct :
          HasSum (fun z : ℕ × (Fin r → ℕ) ↦
            a 0 z.1 * ∏ i, a i.succ (z.2 i))
            (s 0 * ∏ i : Fin r, s i.succ) := by
        convert hproductSummable.hasSum using 1
        calc
          s 0 * ∏ i : Fin r, s i.succ =
              (∑' k, a 0 k) * ∑' y : Fin r → ℕ, ∏ i, a i.succ (y i) := by
            rw [hhead.tsum_eq, htail.tsum_eq]
          _ = ∑' z : ℕ × (Fin r → ℕ),
              a 0 z.1 * ∏ i, a i.succ (z.2 i) :=
            hhead.summable.tsum_mul_tsum htail.summable hproductSummable
      apply (e.hasSum_iff).mp
      convert hproduct using 1
      · funext z
        simp [e, Function.comp_def, Fin.prod_univ_succ, Fin.insertNthEquiv_apply,
          Fin.insertNth_zero]
      · exact Fin.prod_univ_succ s

/-- Product mass of `r` independent copies of a probability mass. -/
def iidTupleWeight (q : ProbabilityMass) {r : ℕ} (y : Fin r → ℕ) : ℝ :=
  ∏ i, q (y i)

theorem iidTupleWeight_nonneg (q : ProbabilityMass) {r : ℕ} (y : Fin r → ℕ) :
    0 ≤ iidTupleWeight q y :=
  Finset.prod_nonneg fun i _ ↦ q.nonneg (y i)

theorem iidTupleWeight_hasSum (q : ProbabilityMass) (r : ℕ) :
    HasSum (fun y : Fin r → ℕ ↦ iidTupleWeight q y) 1 := by
  have h := finitePiProduct_hasSum r (fun _ ↦ q) (fun _ ↦ 1)
    (fun _ k ↦ q.nonneg k) (fun _ ↦ q.hasSum_coe)
  simpa [iidTupleWeight] using h

/-- Under the iid product mass, one marked coordinate has the original mean. -/
theorem iidTupleWeight_mul_coordinate_hasSum
    (q : ProbabilityMass) (r : ℕ) (i : Fin r) (mu : ℝ)
    (hmean : HasSum (fun k : ℕ ↦ (k : ℝ) * q k) mu) :
    HasSum (fun y : Fin r → ℕ ↦ iidTupleWeight q y * (y i : ℝ)) mu := by
  classical
  have h := finitePiProduct_hasSum r
    (fun j k ↦ if j = i then (k : ℝ) * q k else q k)
    (fun j ↦ if j = i then mu else 1)
    (fun j k ↦ by
      by_cases hji : j = i
      · simp only [hji, if_pos]
        exact mul_nonneg (Nat.cast_nonneg k) (q.nonneg k)
      · simp only [hji, if_neg]
        exact q.nonneg k)
    (fun j ↦ by
      by_cases hji : j = i
      · simpa [hji] using hmean
      · simpa [hji] using q.hasSum_coe)
  convert h using 1
  · funext y
    rw [Finset.prod_eq_mul_prod_diff_singleton (Finset.mem_univ i)]
    simp only [if_pos]
    rw [iidTupleWeight, Finset.prod_eq_mul_prod_diff_singleton (Finset.mem_univ i)]
    have hrest :
        ∏ x ∈ Finset.univ \ {i}, (if x = i then (y x : ℝ) * q (y x) else q (y x)) =
          ∏ x ∈ Finset.univ \ {i}, q (y x) := by
      apply Finset.prod_congr rfl
      intro j hj
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and,
        Finset.mem_singleton] at hj
      simp [hj]
    rw [hrest]
    ring
  · rw [Finset.prod_eq_mul_prod_diff_singleton (Finset.mem_univ i)]
    simp only [if_pos]
    have hrest :
        ∏ x ∈ Finset.univ \ {i}, (if x = i then mu else 1) = 1 := by
      apply Finset.prod_eq_one
      intro j hj
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and,
        Finset.mem_singleton] at hj
      simp [hj]
    rw [hrest, mul_one]

private theorem prod_if_eq_or_eq
    {r : ℕ} (i j : Fin r) (hij : i ≠ j) (f : Fin r → ℝ) :
    (∏ x, if x = i ∨ x = j then f x else 1) = f i * f j := by
  classical
  rw [Finset.prod_eq_mul_prod_diff_singleton (Finset.mem_univ i)]
  simp only [true_or, if_true]
  have hjmem : j ∈ Finset.univ \ {i} := by
    simp [hij.symm]
  rw [Finset.prod_eq_mul_prod_diff_singleton hjmem]
  simp only [or_true, if_true]
  have hrest :
      ∏ x ∈ (Finset.univ \ {i}) \ {j}, (if x = i ∨ x = j then f x else 1) = 1 := by
    apply Finset.prod_eq_one
    intro x hx
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and,
      Finset.mem_singleton] at hx
    simp [hx.1, hx.2]
  rw [hrest, mul_one]

/-- Two distinct marked iid coordinates factor into the square of the mean. -/
theorem iidTupleWeight_mul_two_coordinates_hasSum
    (q : ProbabilityMass) (r : ℕ) (i j : Fin r) (hij : i ≠ j) (mu : ℝ)
    (hmean : HasSum (fun k : ℕ ↦ (k : ℝ) * q k) mu) :
    HasSum
      (fun y : Fin r → ℕ ↦ iidTupleWeight q y * (y i : ℝ) * (y j : ℝ))
      (mu ^ 2) := by
  classical
  have h := finitePiProduct_hasSum r
    (fun x k ↦ if x = i ∨ x = j then (k : ℝ) * q k else q k)
    (fun x ↦ if x = i ∨ x = j then mu else 1)
    (fun x k ↦ by
      by_cases hx : x = i ∨ x = j
      · simp only [hx, if_pos]
        exact mul_nonneg (Nat.cast_nonneg k) (q.nonneg k)
      · simp only [hx, if_neg]
        exact q.nonneg k)
    (fun x ↦ by
      by_cases hx : x = i ∨ x = j
      · simpa [hx] using hmean
      · simpa [hx] using q.hasSum_coe)
  convert h using 1
  · funext y
    symm
    calc
      ∏ x, (if x = i ∨ x = j then (y x : ℝ) * q (y x) else q (y x)) =
          ∏ x, (if x = i ∨ x = j then (y x : ℝ) else 1) * q (y x) := by
        apply Finset.prod_congr rfl
        intro x _
        by_cases hx : x = i ∨ x = j <;> simp [hx]
      _ = (∏ x, if x = i ∨ x = j then (y x : ℝ) else 1) *
          ∏ x, q (y x) := by
        rw [Finset.prod_mul_distrib]
      _ = iidTupleWeight q y * (y i : ℝ) * (y j : ℝ) := by
        rw [prod_if_eq_or_eq i j hij]
        simp only [iidTupleWeight]
        ring
  · rw [prod_if_eq_or_eq i j hij]
    ring

/-- Sum of all companion values. -/
def companionSum {r : ℕ} (y : Fin r → ℕ) : ℝ :=
  ∑ i, (y i : ℝ)

/-- Sum of products over unordered pairs of distinct companions. -/
def companionPairSum {r : ℕ} (y : Fin r → ℕ) : ℝ :=
  ∑ i, ∑ j ∈ Finset.Ioi i, (y i : ℝ) * (y j : ℝ)

@[simp]
theorem companionSum_cons
    {r : ℕ} (x : ℕ) (y : Fin r → ℕ) :
    companionSum (Fin.cons x y) = (x : ℝ) + companionSum y := by
  simp [companionSum, Fin.sum_univ_succ]

@[simp]
theorem companionPairSum_cons
    {r : ℕ} (x : ℕ) (y : Fin r → ℕ) :
    companionPairSum (Fin.cons x y) =
      (x : ℝ) * companionSum y + companionPairSum y := by
  simp [companionPairSum, companionSum, Fin.sum_univ_succ,
    Fin.sum_Ioi_zero, Fin.sum_Ioi_succ, ← Finset.mul_sum]

/-- Elementary-symmetric relation between the companion sum and pair sum. -/
theorem companionSum_sq
    {r : ℕ} (y : Fin r → ℕ) :
    companionSum y ^ 2 =
      (∑ i, (y i : ℝ) ^ 2) + 2 * companionPairSum y := by
  induction r with
  | zero =>
      simp [companionSum, companionPairSum]
  | succ r ih =>
      rw [← Fin.cons_self_tail y]
      rw [companionSum_cons, companionPairSum_cons, Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      calc
        ((y 0 : ℝ) + companionSum (Fin.tail y)) ^ 2 =
            (y 0 : ℝ) ^ 2 + companionSum (Fin.tail y) ^ 2 +
              2 * (y 0 : ℝ) * companionSum (Fin.tail y) := by ring
        _ = (y 0 : ℝ) ^ 2 + (∑ x, (Fin.tail y x : ℝ) ^ 2) +
              2 * ((y 0 : ℝ) * companionSum (Fin.tail y) +
                companionPairSum (Fin.tail y)) := by
          rw [ih (Fin.tail y)]
          ring

theorem iidTupleWeight_mul_companionSum_hasSum
    (q : ProbabilityMass) (r : ℕ) (mu : ℝ)
    (hmean : HasSum (fun k : ℕ ↦ (k : ℝ) * q k) mu) :
    HasSum
      (fun y : Fin r → ℕ ↦ iidTupleWeight q y * companionSum y)
      ((r : ℝ) * mu) := by
  have h := hasSum_sum (s := Finset.univ) (fun i _ ↦
    iidTupleWeight_mul_coordinate_hasSum q r i mu hmean)
  convert h using 1
  · funext y
    simp [companionSum, Finset.mul_sum]
  · simp [nsmul_eq_mul]

theorem iidTupleWeight_mul_companionPairSum_hasSum
    (q : ProbabilityMass) (r : ℕ) (mu : ℝ)
    (hmean : HasSum (fun k : ℕ ↦ (k : ℝ) * q k) mu) :
    HasSum
      (fun y : Fin r → ℕ ↦ iidTupleWeight q y * companionPairSum y)
      (∑ i : Fin r, ∑ _j ∈ Finset.Ioi i, mu ^ 2) := by
  have h := hasSum_sum (s := Finset.univ) (fun i _ ↦
    hasSum_sum (s := Finset.Ioi i) (fun j hj ↦
      iidTupleWeight_mul_two_coordinates_hasSum q r i j
        (ne_of_lt (Finset.mem_Ioi.mp hj)) mu hmean))
  convert h using 1
  funext y
  simp only [companionPairSum, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem two_mul_companionPairCount (r : ℕ) :
    2 * (∑ i : Fin r, (Finset.Ioi i).card) = r * (r - 1) := by
  simp_rw [Fin.card_Ioi]
  rw [Fin.sum_univ_eq_sum_range]
  have hreflect := Finset.sum_range_reflect (fun i : ℕ ↦ i) r
  rw [hreflect]
  simpa [mul_comm] using Finset.sum_range_id_mul_two r

theorem companionPairMoment_sum_eq
    (r : ℕ) (hr : 1 ≤ r) (mu : ℝ) :
    (∑ i : Fin r, ∑ _j ∈ Finset.Ioi i, mu ^ 2) =
      ((r : ℝ) * ((r : ℝ) - 1) / 2) * mu ^ 2 := by
  have hcountNat := two_mul_companionPairCount r
  have hcountReal :
      (2 : ℝ) * (∑ i : Fin r, ((Finset.Ioi i).card : ℝ)) =
        (r : ℝ) * ((r : ℝ) - 1) := by
    rw [← Nat.cast_sum] at *
    exact_mod_cast hcountNat
  simp_rw [Finset.sum_const, nsmul_eq_mul]
  rw [← Finset.sum_mul]
  congr 1
  linarith

theorem iidTupleWeight_mul_companionPairSum_hasSum_closed
    (q : ProbabilityMass) (r : ℕ) (hr : 1 ≤ r) (mu : ℝ)
    (hmean : HasSum (fun k : ℕ ↦ (k : ℝ) * q k) mu) :
    HasSum
      (fun y : Fin r → ℕ ↦ iidTupleWeight q y * companionPairSum y)
      (((r : ℝ) * ((r : ℝ) - 1) / 2) * mu ^ 2) := by
  convert iidTupleWeight_mul_companionPairSum_hasSum q r mu hmean using 1
  exact (companionPairMoment_sum_eq r hr mu).symm

/-- The normalized critical tilt, bundled as an honest probability mass. -/
def criticalTiltLaw
    (m : ℕ) (p : ProbabilityMass) (hm : 2 ≤ m) (hcrit : Critical m p) :
    ProbabilityMass where
  mass := normalizedTilt m p
  nonneg := normalizedTilt_nonneg m p (by omega) hcrit
  hasSum_one := normalizedTilt_hasSum m p (by omega) hcrit

@[simp]
theorem criticalTiltLaw_apply
    (m : ℕ) (p : ProbabilityMass) (hm : 2 ≤ m) (hcrit : Critical m p) (k : ℕ) :
    criticalTiltLaw m p hm hcrit k = normalizedTilt m p k :=
  rfl

/-- The source allocation polynomial `A_m(k;y)`. -/
def cubicAllocation
    (m k : ℕ) (y : Fin (m - 1) → ℕ) : ℝ :=
  fallingFactorialThree k +
    fallingFactorialTwo k * (3 * companionSum y + cubicChi m) +
      (k : ℝ) * (2 * companionPairSum y + cubicChi m * companionSum y)

theorem cubicAllocation_nonneg
    (m k : ℕ) (hm : 2 ≤ m) (y : Fin (m - 1) → ℕ) :
    0 ≤ cubicAllocation m k y := by
  have hchi := cubicChi_nonneg m hm
  have hsum : 0 ≤ companionSum y := by
    exact Finset.sum_nonneg fun i _ ↦ Nat.cast_nonneg (y i)
  have hpairs : 0 ≤ companionPairSum y := by
    apply Finset.sum_nonneg
    intro i _
    exact Finset.sum_nonneg fun j _ ↦
      mul_nonneg (Nat.cast_nonneg (y i)) (Nat.cast_nonneg (y j))
  exact add_nonneg
    (add_nonneg (fallingFactorialThree_nonneg k)
      (mul_nonneg (fallingFactorialTwo_nonneg k)
        (add_nonneg (mul_nonneg (by norm_num) hsum) hchi)))
    (mul_nonneg (Nat.cast_nonneg k)
      (add_nonneg (mul_nonneg (by norm_num) hpairs) (mul_nonneg hchi hsum)))

private theorem criticalCompanionMeanCoefficient
    (m : ℕ) (hm : 2 ≤ m) :
    ((m - 1 : ℕ) : ℝ) * (1 / ((m : ℝ) - 1)) = 1 := by
  rw [Nat.cast_sub (by omega)]
  have hden : (m : ℝ) - 1 ≠ 0 := by
    have hmReal : (2 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  field_simp

private theorem criticalCompanionPairCoefficient
    (m : ℕ) (hm : 2 ≤ m) :
    (((m - 1 : ℕ) : ℝ) * (((m - 1 : ℕ) : ℝ) - 1) / 2) *
        (1 / ((m : ℝ) - 1)) ^ 2 = cubicChi m / 2 := by
  rw [Nat.cast_sub (by omega)]
  have hden : (m : ℝ) - 1 ≠ 0 := by
    have hmReal : (2 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  simp only [cubicChi]
  field_simp
  ring

/-- The allocation numerator integrates to the carrier `h_m(k)`. -/
theorem cubicAllocation_hasSum
    (m : ℕ) (p : ProbabilityMass) (hm : 2 ≤ m) (hcrit : Critical m p) (k : ℕ) :
    HasSum
      (fun y : Fin (m - 1) → ℕ ↦
        iidTupleWeight (criticalTiltLaw m p hm hcrit) y * cubicAllocation m k y)
      (cubicCarrier m k) := by
  let q := criticalTiltLaw m p hm hcrit
  let mu : ℝ := 1 / ((m : ℝ) - 1)
  have hmean : HasSum (fun j : ℕ ↦ (j : ℝ) * q j) mu := by
    simpa [q, mu] using normalizedTilt_mean_hasSum m p (by omega) hcrit
  have hmass : HasSum (fun y : Fin (m - 1) → ℕ ↦ iidTupleWeight q y) 1 :=
    iidTupleWeight_hasSum q (m - 1)
  have hsumRaw := iidTupleWeight_mul_companionSum_hasSum q (m - 1) mu hmean
  have hsum :
      HasSum
        (fun y : Fin (m - 1) → ℕ ↦ iidTupleWeight q y * companionSum y) 1 := by
    convert hsumRaw using 1
    exact (criticalCompanionMeanCoefficient m hm).symm
  have hpairRaw := iidTupleWeight_mul_companionPairSum_hasSum_closed
    q (m - 1) (by omega) mu hmean
  have hpair :
      HasSum
        (fun y : Fin (m - 1) → ℕ ↦ iidTupleWeight q y * companionPairSum y)
        (cubicChi m / 2) := by
    convert hpairRaw using 1
    exact (criticalCompanionPairCoefficient m hm).symm
  have hcombined :=
    ((((hmass.mul_left (fallingFactorialThree k)).add
      (hsum.mul_left (3 * fallingFactorialTwo k))).add
      (hmass.mul_left (cubicChi m * fallingFactorialTwo k))).add
      (hpair.mul_left (2 * (k : ℝ)))).add
      (hsum.mul_left (cubicChi m * (k : ℝ)))
  convert hcombined using 1
  · funext y
    simp only [q, cubicAllocation]
    ring
  · rw [cubicCarrier_eq_fallingFactorials]
    ring

/-- Product law tilted by the normalized allocation density. -/
def cubicAllocationWeight
    (m : ℕ) (p : ProbabilityMass) (hm : 2 ≤ m) (hcrit : Critical m p)
    (k : ℕ) (y : Fin (m - 1) → ℕ) : ℝ :=
  iidTupleWeight (criticalTiltLaw m p hm hcrit) y * cubicAllocation m k y /
    cubicCarrier m k

theorem cubicAllocationWeight_nonneg
    (m : ℕ) (p : ProbabilityMass) (hm : 2 ≤ m) (hcrit : Critical m p)
    (k : ℕ) (hk : 0 < cubicCarrier m k) (y : Fin (m - 1) → ℕ) :
    0 ≤ cubicAllocationWeight m p hm hcrit k y :=
  div_nonneg
    (mul_nonneg (iidTupleWeight_nonneg _ y) (cubicAllocation_nonneg m k hm y)) hk.le

theorem cubicAllocationWeight_hasSum_one
    (m : ℕ) (p : ProbabilityMass) (hm : 2 ≤ m) (hcrit : Critical m p)
    (k : ℕ) (hk : 0 < cubicCarrier m k) :
    HasSum (cubicAllocationWeight m p hm hcrit k) 1 := by
  have h := (cubicAllocation_hasSum m p hm hcrit k).div_const (cubicCarrier m k)
  simpa [cubicAllocationWeight, hk.ne'] using h

/-- Turn any nonnegative real mass of total mass one into a mathlib `PMF`. -/
def pmfOfRealHasSum
    {α : Type*} (w : α → ℝ) (hw : ∀ a, 0 ≤ w a) (hsum : HasSum w 1) : PMF α :=
  ⟨fun a ↦ ENNReal.ofReal (w a), ENNReal.summable.hasSum_iff.mpr (by
    rw [← ENNReal.ofReal_tsum_of_nonneg hw hsum.summable]
    simp [hsum.tsum_eq])⟩

@[simp]
theorem pmfOfRealHasSum_apply_toReal
    {α : Type*} (w : α → ℝ) (hw : ∀ a, 0 ≤ w a) (hsum : HasSum w 1) (a : α) :
    (pmfOfRealHasSum w hw hsum a).toReal = w a :=
  ENNReal.toReal_ofReal (hw a)

/-- The normalized companion-allocation law at a positive carrier state. -/
def cubicAllocationPMF
    (m : ℕ) (p : ProbabilityMass) (hm : 2 ≤ m) (hcrit : Critical m p)
    (k : ℕ) (hk : 0 < cubicCarrier m k) : PMF (Fin (m - 1) → ℕ) :=
  pmfOfRealHasSum
    (cubicAllocationWeight m p hm hcrit k)
    (cubicAllocationWeight_nonneg m p hm hcrit k hk)
    (cubicAllocationWeight_hasSum_one m p hm hcrit k hk)

@[simp]
theorem cubicAllocationPMF_apply_toReal
    (m : ℕ) (p : ProbabilityMass) (hm : 2 ≤ m) (hcrit : Critical m p)
    (k : ℕ) (hk : 0 < cubicCarrier m k) (y : Fin (m - 1) → ℕ) :
    (cubicAllocationPMF m p hm hcrit k hk y).toReal =
      cubicAllocationWeight m p hm hcrit k y := by
  exact pmfOfRealHasSum_apply_toReal _ _ _ y

/-- Pointwise factorial identity obtained by summing over the distinguished
carrier.  This is source equation (the unnumbered identity following
`eq:allocation`) before any averaging. -/
theorem cubicAllocation_carrier_identity
    (r : ℕ) (z : Fin (r + 1) → ℕ) :
    (∑ i, cubicAllocation (r + 1) (z i) (i.removeNth z)) =
      cubicCarrier (r + 1) ((∑ i, z i) - 1) := by
  let V : ℕ := ∑ i, z i
  let S : ℝ := (V : ℝ)
  let Q : ℝ := ∑ i, (z i : ℝ) ^ 2
  have hsumRemove (i : Fin (r + 1)) :
      companionSum (i.removeNth z) = S - (z i : ℝ) := by
    have h := Fin.sum_univ_succAbove (fun j ↦ (z j : ℝ)) i
    simp only [companionSum, Fin.removeNth] at ⊢
    rw [show S = ∑ j, (z j : ℝ) by simp [S, V]]
    linarith
  have hsqRemove (i : Fin (r + 1)) :
      (∑ j : Fin r, ((i.removeNth z j : ℕ) : ℝ) ^ 2) =
        Q - (z i : ℝ) ^ 2 := by
    have h := Fin.sum_univ_succAbove (fun j ↦ (z j : ℝ) ^ 2) i
    simp only [Fin.removeNth] at ⊢
    rw [show Q = ∑ j, (z j : ℝ) ^ 2 by rfl]
    linarith
  have hpairRemove (i : Fin (r + 1)) :
      2 * companionPairSum (i.removeNth z) =
        (S - (z i : ℝ)) ^ 2 - (Q - (z i : ℝ) ^ 2) := by
    have h := companionSum_sq (i.removeNth z)
    rw [hsumRemove i, hsqRemove i] at h
    linarith
  have hterm (i : Fin (r + 1)) :
      cubicAllocation (r + 1) (z i) (i.removeNth z) =
        S * (z i : ℝ) ^ 2 +
          (S ^ 2 - Q - 3 * S + 2) * (z i : ℝ) +
            cubicChi (r + 1) * (S - 1) * (z i : ℝ) := by
    rw [cubicAllocation, hsumRemove i, hpairRemove i]
    simp only [fallingFactorialTwo, fallingFactorialThree]
    ring
  calc
    ∑ i, cubicAllocation (r + 1) (z i) (i.removeNth z) =
        ∑ i, (S * (z i : ℝ) ^ 2 +
          (S ^ 2 - Q - 3 * S + 2) * (z i : ℝ) +
            cubicChi (r + 1) * (S - 1) * (z i : ℝ)) := by
      apply Finset.sum_congr rfl
      intro i _
      exact hterm i
    _ = S * Q + (S ^ 2 - Q - 3 * S + 2) * S +
          cubicChi (r + 1) * (S - 1) * S := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
      rw [show (∑ i, (z i : ℝ) ^ 2) = Q by rfl]
      rw [show (∑ i, (z i : ℝ)) = S by simp [S, V]]
    _ = fallingFactorialThree V + cubicChi (r + 1) * fallingFactorialTwo V := by
      simp only [fallingFactorialTwo, fallingFactorialThree, S]
      ring
    _ = cubicCarrier (r + 1) (V - 1) :=
      (cubicCarrier_natPred (r + 1) V).symm
    _ = cubicCarrier (r + 1) ((∑ i, z i) - 1) := by
      rfl

end

end DerridaRetaux
