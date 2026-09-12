import DerridaRetaux.Spine.OutputMarginal
import DerridaRetaux.Spine.FactorialCauchy
import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 4000000

open scoped BigOperators ENNReal

namespace DerridaRetaux

noncomputable section

/-!
# The total cubic-spine transition kernel

The allocation density is defined on positive carrier rows.  This module extends
it to a total Markov kernel on `ℕ` by assigning a pure fallback law to every
zero-carrier row.  Those rows have zero mass under every cubic size-biased
marginal, so the extension does not affect the coupled chain.
-/

/-- The natural-valued sum of a companion tuple. -/
def companionNatSum {r : ℕ} (y : Fin r → ℕ) : ℕ :=
  ∑ i, y i

theorem companionSum_eq_companionNatSum {r : ℕ} (y : Fin r → ℕ) :
    companionSum y = companionNatSum y := by
  simp [companionSum, companionNatSum]

@[simp]
theorem companionNatSum_cons {r : ℕ} (k : ℕ) (y : Fin r → ℕ) :
    companionNatSum (Fin.cons k y) = k + companionNatSum y := by
  simp [companionNatSum, Fin.sum_univ_succ]

@[simp]
theorem iidTupleWeight_cons (q : ProbabilityMass) {r : ℕ} (k : ℕ) (y : Fin r → ℕ) :
    iidTupleWeight q (Fin.cons k y) = q k * iidTupleWeight q y := by
  simp [iidTupleWeight, Fin.prod_univ_succ]

/-- The real iid weight restricted to tuples with a fixed coordinate sum. -/
def iidTupleFiberWeight
    (q : ProbabilityMass) (n : ℕ) {r : ℕ} (y : Fin r → ℕ) : ℝ :=
  if companionNatSum y = n then iidTupleWeight q y else 0

theorem iidTupleFiberWeight_nonneg
    (q : ProbabilityMass) (n : ℕ) {r : ℕ} (y : Fin r → ℕ) :
    0 ≤ iidTupleFiberWeight q n y := by
  simp only [iidTupleFiberWeight]
  split_ifs
  · exact iidTupleWeight_nonneg q y
  · exact le_rfl

theorem iidTupleFiberWeight_summable
    (q : ProbabilityMass) (n r : ℕ) :
    Summable (fun y : Fin r → ℕ ↦ iidTupleFiberWeight q n y) := by
  apply (iidTupleWeight_hasSum q r).summable.of_nonneg_of_le
  · exact iidTupleFiberWeight_nonneg q n
  · intro y
    simp only [iidTupleFiberWeight]
    split_ifs
    · exact le_rfl
    · exact iidTupleWeight_nonneg q y

/-- Fixed-total iid tuple weights are the coefficients of the convolution power. -/
theorem tsum_iidTupleFiberWeight_eq_convPow
    (q : ProbabilityMass) (r n : ℕ) :
    (∑' y : Fin r → ℕ, iidTupleFiberWeight q n y) = convPow r q n := by
  induction r generalizing n with
  | zero =>
      by_cases hn : n = 0
      · simp [iidTupleFiberWeight, iidTupleWeight, companionNatSum, convPow, diracSeq, hn]
      · simp [iidTupleFiberWeight, iidTupleWeight, companionNatSum, convPow, diracSeq, hn,
          Ne.symm hn]
  | succ r ih =>
      let e : (ℕ × (Fin r → ℕ)) ≃ (Fin (r + 1) → ℕ) :=
        Fin.consEquiv (fun _ : Fin (r + 1) ↦ ℕ)
      have hproduct : Summable
          (fun c : ℕ × (Fin r → ℕ) ↦ q c.1 * iidTupleWeight q c.2) := by
        apply (summable_prod_of_nonneg fun c ↦
          mul_nonneg (q.nonneg c.1) (iidTupleWeight_nonneg q c.2)).2
        constructor
        · intro k
          exact (iidTupleWeight_hasSum q r).summable.mul_left (q k)
        · convert q.summable using 1
          funext k
          simp only [Prod.fst, Prod.snd]
          rw [(iidTupleWeight_hasSum q r).summable.tsum_mul_left,
            (iidTupleWeight_hasSum q r).tsum_eq, mul_one]
      have hs : Summable
          (fun c : ℕ × (Fin r → ℕ) ↦ iidTupleFiberWeight q n (e c)) := by
        apply hproduct.of_nonneg_of_le
        · intro c
          exact iidTupleFiberWeight_nonneg q n (e c)
        · rintro ⟨k, y⟩
          change iidTupleFiberWeight q n (Fin.cons k y) ≤
            q k * iidTupleWeight q y
          simp only [iidTupleFiberWeight, iidTupleWeight_cons]
          split_ifs
          · exact le_rfl
          · exact mul_nonneg (q.nonneg k) (iidTupleWeight_nonneg q y)
      rw [← e.tsum_eq]
      simp only [e, Function.comp_apply, Fin.consEquiv_apply]
      rw [hs.tsum_prod]
      change (∑' k : ℕ, ∑' y : Fin r → ℕ,
        iidTupleFiberWeight q n (Fin.cons k y)) = _
      rw [convPow_succ, conv_comm, conv_apply]
      rw [tsum_eq_sum (s := Finset.range (n + 1))]
      · apply Finset.sum_congr rfl
        intro k hk
        simp only [iidTupleFiberWeight, iidTupleWeight_cons]
        have hk' : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
        have hfun :
            (fun y : Fin r → ℕ ↦
              if companionNatSum (Fin.cons k y) = n then
                q k * iidTupleWeight q y
              else 0) =
            (fun y ↦ q k * iidTupleFiberWeight q (n - k) y) := by
          funext y
          rw [companionNatSum_cons]
          simp only [iidTupleFiberWeight]
          by_cases hsum : companionNatSum y = n - k
          · have : k + companionNatSum y = n := by omega
            rw [if_pos this, if_pos hsum]
          · have : k + companionNatSum y ≠ n := by omega
            rw [if_neg this, if_neg hsum, mul_zero]
        rw [hfun, tsum_mul_left, ih]
      · intro k hk
        have hk' : n < k := by
          simpa [Finset.mem_range] using hk
        have hfun :
            (fun y : Fin r → ℕ ↦ iidTupleFiberWeight q n (Fin.cons k y)) = 0 := by
          funext y
          have hne : k + companionNatSum y ≠ n := by omega
          simp [iidTupleFiberWeight, companionNatSum_cons, hne]
        rw [hfun]
        exact tsum_zero

theorem companionNatSum_insertNth
    {r : ℕ} (i : Fin (r + 1)) (k : ℕ) (y : Fin r → ℕ) :
    companionNatSum (i.insertNth k y) = k + companionNatSum y := by
  rw [companionNatSum, Fin.sum_univ_succAbove (fun j ↦ i.insertNth k y j) i]
  simp [companionNatSum]

theorem iidTupleWeight_insertNth
    (q : ProbabilityMass) {r : ℕ} (i : Fin (r + 1)) (k : ℕ) (y : Fin r → ℕ) :
    iidTupleWeight q (i.insertNth k y) = q k * iidTupleWeight q y := by
  let z : Fin (r + 1) → ℕ := i.insertNth k y
  change iidTupleWeight q z = q k * iidTupleWeight q y
  simpa [z, iidTupleWeight] using
    (Fin.prod_univ_succAbove (fun j : Fin (r + 1) ↦ q (z j)) i)

/-- The fixed-distinguished-coordinate joint mass before division by the cubic moment. -/
def cubicDistinguishedFiberWeight
    (m : ℕ) (p : ProbabilityMass) (hm : 2 ≤ m) (hcrit : Critical m p)
    (ell k : ℕ) (y : Fin (m - 1) → ℕ) : ℝ :=
  if k + companionNatSum y = ell + 1 then
    criticalTiltLaw m p hm hcrit k *
      iidTupleWeight (criticalTiltLaw m p hm hcrit) y * cubicAllocation m k y
  else
    0

/-- The same contribution written on a full tuple with distinguished coordinate `i`. -/
def cubicFullAllocationFiberWeight
    (r : ℕ) (p : ProbabilityMass) (hm : 2 ≤ r + 1) (hcrit : Critical (r + 1) p)
    (ell : ℕ) (i : Fin (r + 1)) (z : Fin (r + 1) → ℕ) : ℝ :=
  if companionNatSum z = ell + 1 then
    iidTupleWeight (criticalTiltLaw (r + 1) p hm hcrit) z *
      cubicAllocation (r + 1) (z i) (i.removeNth z)
  else
    0

theorem cubicFullAllocationFiberWeight_insertNth
    (r : ℕ) (p : ProbabilityMass) (hm : 2 ≤ r + 1) (hcrit : Critical (r + 1) p)
    (ell : ℕ) (i : Fin (r + 1)) (k : ℕ) (y : Fin r → ℕ) :
    cubicFullAllocationFiberWeight r p hm hcrit ell i (i.insertNth k y) =
      cubicDistinguishedFiberWeight (r + 1) p hm hcrit ell k y := by
  rw [cubicFullAllocationFiberWeight, cubicDistinguishedFiberWeight,
    companionNatSum_insertNth, iidTupleWeight_insertNth]
  simp

theorem cubicDistinguishedFiberWeight_nonneg
    (m : ℕ) (p : ProbabilityMass) (hm : 2 ≤ m) (hcrit : Critical m p)
    (ell k : ℕ) (y : Fin (m - 1) → ℕ) :
    0 ≤ cubicDistinguishedFiberWeight m p hm hcrit ell k y := by
  simp only [cubicDistinguishedFiberWeight]
  split_ifs
  · exact mul_nonneg
      (mul_nonneg ((criticalTiltLaw m p hm hcrit).nonneg k)
        (iidTupleWeight_nonneg _ y))
      (cubicAllocation_nonneg m k hm y)
  · exact le_rfl

theorem cubicDistinguishedFiberWeight_summable
    (m : ℕ) (p : ProbabilityMass) (hm : 2 ≤ m) (hcrit : Critical m p)
    (hthird : TiltSummable m 3 p) (ell : ℕ) :
    Summable (fun c : ℕ × (Fin (m - 1) → ℕ) ↦
      cubicDistinguishedFiberWeight m p hm hcrit ell c.1 c.2) := by
  let q := criticalTiltLaw m p hm hcrit
  have hraw : Summable (fun c : ℕ × (Fin (m - 1) → ℕ) ↦
      q c.1 * iidTupleWeight q c.2 * cubicAllocation m c.1 c.2) := by
    apply (summable_prod_of_nonneg fun c ↦
      mul_nonneg
        (mul_nonneg (q.nonneg c.1) (iidTupleWeight_nonneg q c.2))
        (cubicAllocation_nonneg m c.1 hm c.2)).2
    constructor
    · intro k
      have hk := (cubicAllocation_hasSum m p hm hcrit k).summable.mul_left (q k)
      convert hk using 1
      funext y
      ring
    · have houter := normalizedCubicMoment_summable m p hm hcrit hthird
      convert houter using 1
      funext k
      have hsum := cubicAllocation_hasSum m p hm hcrit k
      simp only [Prod.fst, Prod.snd]
      calc
        (∑' y : Fin (m - 1) → ℕ,
            q k * iidTupleWeight q y * cubicAllocation m k y) =
            ∑' y : Fin (m - 1) → ℕ,
              q k * (iidTupleWeight q y * cubicAllocation m k y) := by
          apply tsum_congr
          intro y
          ring
        _ = q k * cubicCarrier m k := by
          rw [hsum.summable.tsum_mul_left, hsum.tsum_eq]
        _ = cubicCarrier m k * normalizedTilt m p k := by
          simp only [q, criticalTiltLaw_apply]
          ring
  apply hraw.of_nonneg_of_le
  · rintro ⟨k, y⟩
    exact cubicDistinguishedFiberWeight_nonneg m p hm hcrit ell k y
  · rintro ⟨k, y⟩
    simp only [cubicDistinguishedFiberWeight]
    split_ifs
    · exact le_rfl
    · exact mul_nonneg
        (mul_nonneg (q.nonneg k) (iidTupleWeight_nonneg q y))
        (cubicAllocation_nonneg m k hm y)

theorem tsum_cubicFullAllocationFiberWeight_eq_distinguished
    (r : ℕ) (p : ProbabilityMass) (hm : 2 ≤ r + 1) (hcrit : Critical (r + 1) p)
    (ell : ℕ) (i : Fin (r + 1)) :
    (∑' z : Fin (r + 1) → ℕ,
      cubicFullAllocationFiberWeight r p hm hcrit ell i z) =
    ∑' c : ℕ × (Fin r → ℕ),
      cubicDistinguishedFiberWeight (r + 1) p hm hcrit ell c.1 c.2 := by
  let e : (ℕ × (Fin r → ℕ)) ≃ (Fin (r + 1) → ℕ) :=
    i.insertNthEquiv (fun _ : Fin (r + 1) ↦ ℕ)
  rw [← e.tsum_eq]
  apply tsum_congr
  rintro ⟨k, y⟩
  exact cubicFullAllocationFiberWeight_insertNth r p hm hcrit ell i k y

theorem cubicFullAllocationFiberWeight_summable
    (r : ℕ) (p : ProbabilityMass) (hm : 2 ≤ r + 1) (hcrit : Critical (r + 1) p)
    (hthird : TiltSummable (r + 1) 3 p) (ell : ℕ) (i : Fin (r + 1)) :
    Summable (cubicFullAllocationFiberWeight r p hm hcrit ell i) := by
  let e : (ℕ × (Fin r → ℕ)) ≃ (Fin (r + 1) → ℕ) :=
    i.insertNthEquiv (fun _ : Fin (r + 1) ↦ ℕ)
  rw [← e.summable_iff]
  apply (cubicDistinguishedFiberWeight_summable
    (r + 1) p hm hcrit hthird ell).congr
  rintro ⟨k, y⟩
  exact (cubicFullAllocationFiberWeight_insertNth r p hm hcrit ell i k y).symm

theorem sum_cubicFullAllocationFiberWeight
    (r : ℕ) (p : ProbabilityMass) (hm : 2 ≤ r + 1) (hcrit : Critical (r + 1) p)
    (ell : ℕ) (z : Fin (r + 1) → ℕ) :
    (∑ i, cubicFullAllocationFiberWeight r p hm hcrit ell i z) =
      if companionNatSum z = ell + 1 then
        iidTupleWeight (criticalTiltLaw (r + 1) p hm hcrit) z *
          cubicCarrier (r + 1) ell
      else
        0 := by
  by_cases hsum : companionNatSum z = ell + 1
  · simp only [cubicFullAllocationFiberWeight, if_pos hsum]
    rw [← Finset.mul_sum, cubicAllocation_carrier_identity r z]
    rw [show (∑ i, z i) - 1 = ell by
      rw [← companionNatSum, hsum]; omega]
  · simp [cubicFullAllocationFiberWeight, hsum]

/-- The allocation averaged over the distinguished carrier has exactly the
source output coefficient before division by the cubic moment. -/
theorem tsum_cubicDistinguishedFiberWeight_eq
    (r : ℕ) (p : ProbabilityMass) (hm : 2 ≤ r + 1) (hcrit : Critical (r + 1) p)
    (hthird : TiltSummable (r + 1) 3 p) (ell : ℕ) :
    (∑' c : ℕ × (Fin r → ℕ),
      cubicDistinguishedFiberWeight (r + 1) p hm hcrit ell c.1 c.2) =
      cubicCarrier (r + 1) ell *
        convPow (r + 1) (normalizedTilt (r + 1) p) (ell + 1) /
          (r + 1 : ℕ) := by
  let q := criticalTiltLaw (r + 1) p hm hcrit
  let pairSum : ℝ := ∑' c : ℕ × (Fin r → ℕ),
    cubicDistinguishedFiberWeight (r + 1) p hm hcrit ell c.1 c.2
  have hcomm := hasSum_sum (s := Finset.univ) (fun i _ ↦
    (cubicFullAllocationFiberWeight_summable
      r p hm hcrit hthird ell i).hasSum)
  have hidentity : (r + 1 : ℝ) * pairSum =
      cubicCarrier (r + 1) ell *
        convPow (r + 1) (normalizedTilt (r + 1) p) (ell + 1) := by
    calc
      (r + 1 : ℝ) * pairSum = ∑ _i : Fin (r + 1), pairSum := by
        simp [nsmul_eq_mul]
      _ = ∑ i : Fin (r + 1),
          ∑' z : Fin (r + 1) → ℕ,
            cubicFullAllocationFiberWeight r p hm hcrit ell i z := by
        apply Finset.sum_congr rfl
        intro i _
        exact (tsum_cubicFullAllocationFiberWeight_eq_distinguished
          r p hm hcrit ell i).symm
      _ = ∑' z : Fin (r + 1) → ℕ,
          ∑ i : Fin (r + 1),
            cubicFullAllocationFiberWeight r p hm hcrit ell i z :=
        hcomm.tsum_eq.symm
      _ = ∑' z : Fin (r + 1) → ℕ,
          if companionNatSum z = ell + 1 then
            iidTupleWeight q z * cubicCarrier (r + 1) ell
          else 0 := by
        apply tsum_congr
        intro z
        rw [sum_cubicFullAllocationFiberWeight]
      _ = ∑' z : Fin (r + 1) → ℕ,
          cubicCarrier (r + 1) ell * iidTupleFiberWeight q (ell + 1) z := by
        apply tsum_congr
        intro z
        simp only [iidTupleFiberWeight]
        split_ifs <;> ring
      _ = cubicCarrier (r + 1) ell *
          ∑' z : Fin (r + 1) → ℕ, iidTupleFiberWeight q (ell + 1) z := by
        rw [(iidTupleFiberWeight_summable q (ell + 1) (r + 1)).tsum_mul_left]
      _ = cubicCarrier (r + 1) ell * convPow (r + 1) q (ell + 1) := by
        rw [tsum_iidTupleFiberWeight_eq_convPow]
      _ = cubicCarrier (r + 1) ell *
          convPow (r + 1) (normalizedTilt (r + 1) p) (ell + 1) := by
        rfl
  change pairSum = _
  have hr : (r + 1 : ℝ) ≠ 0 := by positivity
  rw [Nat.cast_add, Nat.cast_one]
  apply (eq_div_iff hr).2
  simpa [mul_comm] using hidentity

/-- The offspring value produced from a carrier and its companions. -/
def cubicSpineOutput {m : ℕ} (k : ℕ) (y : Fin (m - 1) → ℕ) : ℕ :=
  k + companionNatSum y - 1

/-- The allocation output law on a positive carrier row. -/
def cubicAllocationOutputPMF
    (m : ℕ) (p : ProbabilityMass) (hm : 2 ≤ m) (hcrit : Critical m p)
    (k : ℕ) (hk : 0 < cubicCarrier m k) : PMF ℕ :=
  (cubicAllocationPMF m p hm hcrit k hk).map (cubicSpineOutput k)

/-- A total transition kernel.  The pure fallback on a zero-carrier row is
mathematically irrelevant because the source size-biased law gives that row
mass zero. -/
def cubicSpineKernel
    (m : ℕ) (p : ProbabilityMass) (hm : 2 ≤ m) (hcrit : Critical m p)
    (k : ℕ) : PMF ℕ :=
  if hk : 0 < cubicCarrier m k then
    cubicAllocationOutputPMF m p hm hcrit k hk
  else
    PMF.pure 0

theorem cubicSpineKernel_eq_allocation
    (m : ℕ) (p : ProbabilityMass) (hm : 2 ≤ m) (hcrit : Critical m p)
    (k : ℕ) (hk : 0 < cubicCarrier m k) :
    cubicSpineKernel m p hm hcrit k =
      cubicAllocationOutputPMF m p hm hcrit k hk := by
  simp [cubicSpineKernel, hk]

theorem cubicSpineKernel_eq_pure_zero_of_carrier_eq_zero
    (m : ℕ) (p : ProbabilityMass) (hm : 2 ≤ m) (hcrit : Critical m p)
    (k : ℕ) (hk : cubicCarrier m k = 0) :
    cubicSpineKernel m p hm hcrit k = PMF.pure 0 := by
  have hnot : ¬0 < cubicCarrier m k := by simp [hk]
  simp [cubicSpineKernel, hnot]

@[simp]
theorem cubicSpineKernel_zero
    (m : ℕ) (p : ProbabilityMass) (hm : 2 ≤ m) (hcrit : Critical m p) :
    cubicSpineKernel m p hm hcrit 0 = PMF.pure 0 :=
  cubicSpineKernel_eq_pure_zero_of_carrier_eq_zero
    m p hm hcrit 0 (cubicCarrier_zero m)

/-- At binary arity the additional exceptional row is also a fallback row. -/
@[simp]
theorem cubicSpineKernel_two_one
    (p : ProbabilityMass) (hcrit : Critical 2 p) :
    cubicSpineKernel 2 p (by norm_num) hcrit 1 = PMF.pure 0 :=
  cubicSpineKernel_eq_pure_zero_of_carrier_eq_zero
    2 p (by norm_num) hcrit 1 cubicCarrier_two_one

/-- The generation-dependent total kernel for admissible profile data. -/
def spineKernel (m : ℕ) (data : ProfileInitialData m) (n k : ℕ) : PMF ℕ :=
  cubicSpineKernel m (orbit m data.law n) data.arity
    (orbit_critical m data.law (le_trans (by norm_num) data.arity) data.critical n) k

theorem spineKernel_eq_pure_zero_of_carrier_eq_zero
    (m : ℕ) (data : ProfileInitialData m) (n k : ℕ)
    (hk : cubicCarrier m k = 0) :
    spineKernel m data n k = PMF.pure 0 := by
  exact cubicSpineKernel_eq_pure_zero_of_carrier_eq_zero
    m (orbit m data.law n) data.arity
      (orbit_critical m data.law (le_trans (by norm_num) data.arity) data.critical n) k hk

theorem pmf_bind_apply_toReal
    {α β : Type*} (μ : PMF α) (K : α → PMF β) (b : β) :
    (μ.bind K b).toReal = ∑' a, (μ a).toReal * (K a b).toReal := by
  rw [PMF.bind_apply,
    ENNReal.tsum_toReal_eq (fun a ↦ ENNReal.mul_ne_top (μ.apply_ne_top a) ((K a).apply_ne_top b))]
  apply tsum_congr
  intro a
  exact ENNReal.toReal_mul

theorem pmf_map_apply_toReal
    {α β : Type*} [DecidableEq β] (μ : PMF α) (f : α → β) (b : β) :
    (μ.map f b).toReal = ∑' a, if b = f a then (μ a).toReal else 0 := by
  classical
  rw [PMF.map_apply,
    ENNReal.tsum_toReal_eq (fun a ↦ by split_ifs <;> simp [μ.apply_ne_top a])]
  apply tsum_congr
  intro a
  by_cases h : b = f a <;> simp [h]

theorem iidTupleWeight_mul_cubicAllocation_eq_zero_of_carrier_eq_zero
    (m : ℕ) (p : ProbabilityMass) (hm : 2 ≤ m) (hcrit : Critical m p)
    (k : ℕ) (hk : cubicCarrier m k = 0) (y : Fin (m - 1) → ℕ) :
    iidTupleWeight (criticalTiltLaw m p hm hcrit) y * cubicAllocation m k y = 0 := by
  have hsum := cubicAllocation_hasSum m p hm hcrit k
  have hnonneg : 0 ≤
      iidTupleWeight (criticalTiltLaw m p hm hcrit) y * cubicAllocation m k y :=
    mul_nonneg (iidTupleWeight_nonneg _ y) (cubicAllocation_nonneg m k hm y)
  have hle := hsum.summable.le_tsum y (fun j _ ↦
    mul_nonneg (iidTupleWeight_nonneg _ j) (cubicAllocation_nonneg m k hm j))
  rw [hsum.tsum_eq, hk] at hle
  exact le_antisymm hle hnonneg

theorem cubicDistinguishedFiberWeight_summable_fixedCarrier
    (m : ℕ) (p : ProbabilityMass) (hm : 2 ≤ m) (hcrit : Critical m p)
    (ell k : ℕ) :
    Summable (cubicDistinguishedFiberWeight m p hm hcrit ell k) := by
  let q := criticalTiltLaw m p hm hcrit
  have hraw := (cubicAllocation_hasSum m p hm hcrit k).summable.mul_left (q k)
  apply hraw.of_nonneg_of_le
  · exact cubicDistinguishedFiberWeight_nonneg m p hm hcrit ell k
  · intro y
    simp only [cubicDistinguishedFiberWeight]
    split_ifs
    · simp only [q]
      ring_nf
      exact le_rfl
    · exact mul_nonneg (q.nonneg k)
        (mul_nonneg (iidTupleWeight_nonneg _ y) (cubicAllocation_nonneg m k hm y))

theorem cubicAllocationOutputPMF_apply_toReal
    (m : ℕ) (p : ProbabilityMass) (hm : 2 ≤ m) (hcrit : Critical m p)
    (k : ℕ) (hk : 0 < cubicCarrier m k) (ell : ℕ) :
    (cubicAllocationOutputPMF m p hm hcrit k hk ell).toReal =
      ∑' y : Fin (m - 1) → ℕ,
        if ell = cubicSpineOutput k y then
          cubicAllocationWeight m p hm hcrit k y
        else 0 := by
  rw [cubicAllocationOutputPMF, pmf_map_apply_toReal]
  apply tsum_congr
  intro y
  rw [cubicAllocationPMF_apply_toReal]

/-- A source atom times one transition row is the corresponding normalized
distinguished-coordinate joint mass. -/
theorem cubicSizeBiasedPMF_mul_kernel_apply_toReal
    (m : ℕ) (p : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p) (hthird : TiltSummable m 3 p)
    (hJ : 0 < normalizedCubicMoment m p) (k ell : ℕ) :
    (cubicSizeBiasedPMF m p hm hcrit hthird hJ k).toReal *
        (cubicSpineKernel m p hm hcrit k ell).toReal =
      (∑' y : Fin (m - 1) → ℕ,
        cubicDistinguishedFiberWeight m p hm hcrit ell k y) /
          normalizedCubicMoment m p := by
  by_cases hk : 0 < cubicCarrier m k
  · rw [cubicSizeBiasedPMF_apply_toReal,
      cubicSpineKernel_eq_allocation m p hm hcrit k hk,
      cubicAllocationOutputPMF_apply_toReal]
    let f : (Fin (m - 1) → ℕ) → ℝ := fun y ↦
      if ell = cubicSpineOutput k y then
        cubicAllocationWeight m p hm hcrit k y
      else 0
    have hf : Summable f := by
      apply (cubicAllocationWeight_hasSum_one m p hm hcrit k hk).summable.of_nonneg_of_le
      · intro y
        simp only [f]
        split_ifs
        · exact cubicAllocationWeight_nonneg m p hm hcrit k hk y
        · exact le_rfl
      · intro y
        simp only [f]
        split_ifs
        · exact le_rfl
        · exact cubicAllocationWeight_nonneg m p hm hcrit k hk y
    have hpair := cubicDistinguishedFiberWeight_summable_fixedCarrier
      m p hm hcrit ell k
    change
      (cubicCarrier m k * normalizedTilt m p k / normalizedCubicMoment m p) *
          (∑' y, f y) = _
    calc
      (cubicCarrier m k * normalizedTilt m p k / normalizedCubicMoment m p) *
          (∑' y, f y) =
          ∑' y, (cubicCarrier m k * normalizedTilt m p k /
            normalizedCubicMoment m p) * f y := by
        rw [hf.tsum_mul_left]
      _ = ∑' y, cubicDistinguishedFiberWeight m p hm hcrit ell k y /
          normalizedCubicMoment m p := by
        apply tsum_congr
        intro y
        have hkNat : 1 ≤ k := by
          by_contra hkn
          have hkZero : k = 0 := by omega
          subst k
          simp [cubicCarrier_zero] at hk
        have hout : ell = cubicSpineOutput k y ↔
            k + companionNatSum y = ell + 1 := by
          unfold cubicSpineOutput
          omega
        by_cases h : ell = cubicSpineOutput k y
        · simp only [f, h, if_pos, cubicAllocationWeight,
            cubicDistinguishedFiberWeight, hout.mp h]
          have hcancel :
              (cubicCarrier m k * (criticalTiltLaw m p hm hcrit k) /
                  normalizedCubicMoment m p) *
                    ((iidTupleWeight (criticalTiltLaw m p hm hcrit) y *
                      cubicAllocation m k y) / cubicCarrier m k) =
                ((criticalTiltLaw m p hm hcrit k) *
                  (iidTupleWeight (criticalTiltLaw m p hm hcrit) y *
                    cubicAllocation m k y)) / normalizedCubicMoment m p := by
            rw [div_eq_mul_inv]
            calc
              cubicCarrier m k * (criticalTiltLaw m p hm hcrit k) *
                    (normalizedCubicMoment m p)⁻¹ *
                  ((iidTupleWeight (criticalTiltLaw m p hm hcrit) y *
                    cubicAllocation m k y) * (cubicCarrier m k)⁻¹) =
                  (cubicCarrier m k * (cubicCarrier m k)⁻¹) *
                    ((criticalTiltLaw m p hm hcrit k) *
                      (iidTupleWeight (criticalTiltLaw m p hm hcrit) y *
                        cubicAllocation m k y) *
                          (normalizedCubicMoment m p)⁻¹) := by ring
              _ = (criticalTiltLaw m p hm hcrit k) *
                    (iidTupleWeight (criticalTiltLaw m p hm hcrit) y *
                      cubicAllocation m k y) *
                        (normalizedCubicMoment m p)⁻¹ := by
                  rw [mul_inv_cancel₀ hk.ne', one_mul]
          simpa only [criticalTiltLaw_apply, mul_assoc] using hcancel
        · simp only [f, h, if_neg, cubicDistinguishedFiberWeight,
            if_neg (fun hs ↦ h (hout.mpr hs))]
          simp
      _ = (∑' y, cubicDistinguishedFiberWeight m p hm hcrit ell k y) /
          normalizedCubicMoment m p := by
        rw [tsum_div_const]
  · have hk0 : cubicCarrier m k = 0 :=
      le_antisymm (le_of_not_gt hk) (cubicCarrier_nonneg m k hm)
    rw [cubicSizeBiasedPMF_apply_toReal]
    have hzero :
        (fun y : Fin (m - 1) → ℕ ↦
          cubicDistinguishedFiberWeight m p hm hcrit ell k y) = 0 := by
      funext y
      simp only [cubicDistinguishedFiberWeight]
      split_ifs
      · have halloc := iidTupleWeight_mul_cubicAllocation_eq_zero_of_carrier_eq_zero
          m p hm hcrit k hk0 y
        calc
          (criticalTiltLaw m p hm hcrit k) *
              iidTupleWeight (criticalTiltLaw m p hm hcrit) y *
                cubicAllocation m k y =
              (criticalTiltLaw m p hm hcrit k) *
                (iidTupleWeight (criticalTiltLaw m p hm hcrit) y *
                  cubicAllocation m k y) := by ring
          _ = 0 := by rw [halloc, mul_zero]
      · rfl
    rw [hk0, zero_mul, zero_div, zero_mul, hzero]
    have htsumZero : (∑' _y : Fin (m - 1) → ℕ, (0 : ℝ)) = 0 := tsum_zero
    change (0 : ℝ) = (∑' _y : Fin (m - 1) → ℕ, (0 : ℝ)) /
      normalizedCubicMoment m p
    rw [htsumZero, zero_div]

/-- Binding the total kernel to the cubic size-biased source law gives the
allocation output law.  This is the concrete `PMF.bind`/`PMF.map` marginal
calculation omitted by the earlier coefficient-only module. -/
theorem cubicSizeBiasedPMF_bind_cubicSpineKernel
    (r : ℕ) (p : ProbabilityMass) (hm : 2 ≤ r + 1)
    (hcrit : Critical (r + 1) p) (hthird : TiltSummable (r + 1) 3 p)
    (hJ : 0 < normalizedCubicMoment (r + 1) p) :
    (cubicSizeBiasedPMF (r + 1) p hm hcrit hthird hJ).bind
        (cubicSpineKernel (r + 1) p hm hcrit) =
      (cubicSpineOutputLaw (r + 1) p hm hcrit hthird hJ).toPMF := by
  apply PMF.ext
  intro ell
  apply (ENNReal.toReal_eq_toReal
    (((cubicSizeBiasedPMF (r + 1) p hm hcrit hthird hJ).bind
      (cubicSpineKernel (r + 1) p hm hcrit)).apply_ne_top ell)
    ((cubicSpineOutputLaw (r + 1) p hm hcrit hthird hJ).toPMF.apply_ne_top ell)).mp
  rw [pmf_bind_apply_toReal, ProbabilityMass.toPMF_apply_toReal,
    cubicSpineOutputLaw_apply]
  simp_rw [cubicSizeBiasedPMF_mul_kernel_apply_toReal
    (r + 1) p hm hcrit hthird hJ]
  have hpair := cubicDistinguishedFiberWeight_summable
    (r + 1) p hm hcrit hthird ell
  have hpair' : Summable (fun c : ℕ × (Fin r → ℕ) ↦
      cubicDistinguishedFiberWeight (r + 1) p hm hcrit ell c.1 c.2) := by
    simpa using hpair
  calc
    (∑' k : ℕ,
        (∑' y : Fin r → ℕ,
          cubicDistinguishedFiberWeight (r + 1) p hm hcrit ell k y) /
            normalizedCubicMoment (r + 1) p) =
        (∑' k : ℕ, ∑' y : Fin r → ℕ,
          cubicDistinguishedFiberWeight (r + 1) p hm hcrit ell k y) /
            normalizedCubicMoment (r + 1) p := by
      rw [tsum_div_const]
    _ = (∑' c : ℕ × (Fin r → ℕ),
        cubicDistinguishedFiberWeight (r + 1) p hm hcrit ell c.1 c.2) /
          normalizedCubicMoment (r + 1) p := by
      rw [hpair'.tsum_prod]
    _ = (cubicCarrier (r + 1) ell *
        convPow (r + 1) (normalizedTilt (r + 1) p) (ell + 1) /
          (r + 1 : ℕ)) / normalizedCubicMoment (r + 1) p := by
      rw [tsum_cubicDistinguishedFiberWeight_eq r p hm hcrit hthird ell]
    _ = cubicSpineOutputMass (r + 1) p ell := by
      rw [cubicSpineOutputMass]
      ring

/-- Orbit form of the one-step marginal identity. -/
theorem spineMarginalPMF_bind_spineKernel
    (r : ℕ) (data : ProfileInitialData (r + 1)) (n : ℕ) :
    (spineMarginalPMF (r + 1) data n).bind (spineKernel (r + 1) data n) =
      spineMarginalPMF (r + 1) data (n + 1) := by
  let p := orbit (r + 1) data.law n
  let hcrit : Critical (r + 1) p :=
    orbit_critical (r + 1) data.law (le_trans (by norm_num) data.arity) data.critical n
  let hthird : TiltSummable (r + 1) 3 p :=
    orbit_tiltSummable_three (r + 1) data.law
      (le_trans (by norm_num) data.arity) data.critical data.third n
  let hJ : 0 < normalizedCubicMoment (r + 1) p :=
    normalizedCubicMoment_profile_orbit_pos (r + 1) data n
  have hbind := cubicSizeBiasedPMF_bind_cubicSpineKernel
    r p data.arity hcrit hthird hJ
  have hout := cubicSpineOutputLaw_eq_nextSizeBiased
    (r + 1) p data.arity hcrit hthird hJ
  rw [hout] at hbind
  simpa [p, hcrit, hthird, hJ, spineMarginalPMF, spineMarginal, spineKernel] using hbind

end

end DerridaRetaux
