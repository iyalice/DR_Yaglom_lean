import DerridaRetaux.Spine.Kernel
import DerridaRetaux.Spine.CompanionExpectations
import DerridaRetaux.Spine.PathTail
import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 4000000

open scoped BigOperators ENNReal

namespace DerridaRetaux

noncomputable section

/-!
# The cubic-spine coupling and its positive-increment estimate

This module turns the total kernel from `Kernel` into the actual finite-path
coupling used in the paper.  The expectation calculation is performed against
the concrete allocation law; no abstract coupling or moment premise is used.
-/

/-- Positive part of the increment between two natural-valued states. -/
def positiveNatIncrement (k ell : ℕ) : ℝ :=
  max ((ell : ℝ) - (k : ℝ)) 0

theorem positiveNatIncrement_nonneg (k ell : ℕ) :
    0 ≤ positiveNatIncrement k ell := by
  simp [positiveNatIncrement]

/-- For the allocation output, the positive increment is exactly `(U-1)_+`. -/
theorem positiveNatIncrement_cubicSpineOutput
    {m : ℕ} (k : ℕ) (y : Fin (m - 1) → ℕ) :
    positiveNatIncrement k (cubicSpineOutput k y) = companionExcess y := by
  let U : ℕ := companionNatSum y
  have hU : companionExcess y = ((U - 1 : ℕ) : ℝ) := by
    simp [companionExcess, companionNatSum, U]
  rw [hU]
  change max (((k + U - 1 : ℕ) : ℝ) - (k : ℝ)) 0 = ((U - 1 : ℕ) : ℝ)
  cases U with
  | zero =>
      simp [positiveNatIncrement, cubicSpineOutput]
  | succ U =>
      simp [positiveNatIncrement, cubicSpineOutput]

/-- The unnormalised conditional positive-increment contribution at carrier `k`. -/
def cubicAllocationIncrementMass
    (m : ℕ) (p : ProbabilityMass) (hm : 2 ≤ m) (hcrit : Critical m p)
    (k : ℕ) (y : Fin (m - 1) → ℕ) : ℝ :=
  iidTupleWeight (criticalTiltLaw m p hm hcrit) y *
    cubicAllocation m k y * companionExcess y

/-- The value of the preceding conditional numerator after the companions are
integrated out. -/
def cubicAllocationIncrementValue
    (m k : ℕ) (x b : ℝ) : ℝ :=
  fallingFactorialThree k * x ^ (m - 1) +
    fallingFactorialTwo k *
      (3 * (((m : ℝ) - 1) * b + cubicChi m) +
        cubicChi m * x ^ (m - 1)) +
    (k : ℝ) *
      (2 * (((m : ℝ) - 2) * b + cubicChi m ^ 2) +
        cubicChi m * (((m : ℝ) - 1) * b + cubicChi m))

/-- Literal integration of `A_m(k;y) (U-1)_+` under the iid companion law. -/
theorem cubicAllocationIncrementMass_hasSum
    (m : ℕ) (p : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p) (hthird : TiltSummable m 3 p) (k : ℕ) :
    HasSum (cubicAllocationIncrementMass m p hm hcrit k)
      (cubicAllocationIncrementValue m k (zeroTilt m p)
        (normalizedFactorialTwo m p)) := by
  let q := criticalTiltLaw m p hm hcrit
  let x := zeroTilt m p
  let b := normalizedFactorialTwo m p
  have hW := iidTupleWeight_mul_companionExcess_hasSum m p hm hcrit
  have hUW := iidTupleWeight_mul_companionSum_companionExcess_hasSum
    m p hm hcrit hthird
  have hVW := iidTupleWeight_mul_companionPairSum_companionExcess_hasSum
    m p hm hcrit hthird
  have hcombined :=
    (((hW.mul_left (fallingFactorialThree k)).add
      (hUW.mul_left (3 * fallingFactorialTwo k))).add
      (hW.mul_left (cubicChi m * fallingFactorialTwo k))).add
      ((hVW.mul_left (2 * (k : ℝ))).add
        (hUW.mul_left (cubicChi m * (k : ℝ))))
  convert hcombined using 1
  · funext y
    simp only [cubicAllocationIncrementMass, cubicAllocation]
    ring
  · simp only [x, b, cubicAllocationIncrementValue]
    ring

/-- The cubic moment is the denominator displayed in `eq:incformula`. -/
theorem normalizedCubicMoment_eq_spineIncrementDenominator
    (m : ℕ) (p : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p) (hthird : TiltSummable m 3 p) :
    normalizedCubicMoment m p =
      spineIncrementDenominator m (normalizedFactorialTwo m p)
        (normalizedFactorialThree m p) := by
  have hg := (normalizedFactorialThree_summable
    m p (by omega) hcrit hthird).hasSum
  have hb := (normalizedFactorialTwo_summable
    m p (by omega) hcrit hthird).hasSum
  have hmean := normalizedTilt_mean_hasSum m p (by omega) hcrit
  have hsum := (hg.add (hb.mul_left (3 + cubicChi m))).add
    (hmean.mul_left (2 * cubicChi m))
  apply (normalizedCubicMoment_hasSum m p hm hcrit hthird).unique
  convert hsum using 1
  · funext k
    rw [cubicCarrier_eq_fallingFactorials]
    ring
  · simp only [spineIncrementDenominator, normalizedFactorialTwo,
      normalizedFactorialThree]
    ring

/-- Averaging the literal allocation increment over the carrier gives the
numerator in `eq:incformula`. -/
theorem criticalTilt_mul_cubicAllocationIncrementValue_hasSum
    (m : ℕ) (p : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p) (hthird : TiltSummable m 3 p) :
    HasSum
      (fun k : ℕ ↦
        criticalTiltLaw m p hm hcrit k *
          cubicAllocationIncrementValue m k (zeroTilt m p)
            (normalizedFactorialTwo m p))
      (spineIncrementNumerator m (zeroTilt m p)
        (normalizedFactorialTwo m p) (normalizedFactorialThree m p)) := by
  let q := criticalTiltLaw m p hm hcrit
  let x := zeroTilt m p
  let b := normalizedFactorialTwo m p
  let g := normalizedFactorialThree m p
  have hg : HasSum (fun k : ℕ ↦ q k * fallingFactorialThree k) g := by
    have h := (normalizedFactorialThree_summable
      m p (by omega) hcrit hthird).hasSum
    convert h using 1
    funext k
    simp only [q, criticalTiltLaw_apply]
    ring
  have hb : HasSum (fun k : ℕ ↦ q k * fallingFactorialTwo k) b := by
    have h := (normalizedFactorialTwo_summable
      m p (by omega) hcrit hthird).hasSum
    convert h using 1
    funext k
    simp only [q, criticalTiltLaw_apply]
    ring
  let mu : ℝ := 1 / ((m : ℝ) - 1)
  have hmu : HasSum (fun k : ℕ ↦ q k * (k : ℝ)) mu := by
    have h := normalizedTilt_mean_hasSum m p (by omega) hcrit
    convert h using 1
    funext k
    simp only [q, criticalTiltLaw_apply]
    ring
  have hcombined :=
    ((hg.mul_left (x ^ (m - 1))).add
      (hb.mul_left
        (3 * (((m : ℝ) - 1) * b + cubicChi m) +
          cubicChi m * x ^ (m - 1)))).add
      (hmu.mul_left
        (2 * (((m : ℝ) - 2) * b + cubicChi m ^ 2) +
          cubicChi m * (((m : ℝ) - 1) * b + cubicChi m)))
  convert hcombined using 1
  · funext k
    simp only [q, x, b, cubicAllocationIncrementValue]
    ring
  · change
      spineIncrementNumerator m x b g =
        x ^ (m - 1) * g +
          (3 * (((m : ℝ) - 1) * b + cubicChi m) +
            cubicChi m * x ^ (m - 1)) * b +
        (2 * (((m : ℝ) - 2) * b + cubicChi m ^ 2) +
          cubicChi m * (((m : ℝ) - 1) * b + cubicChi m)) * mu
    have hden : (m : ℝ) - 1 ≠ 0 := by
      have hmReal : (2 : ℝ) ≤ m := by exact_mod_cast hm
      linarith
    unfold spineIncrementNumerator
    dsimp only [mu]
    simp only [cubicChi]
    field_simp [hden]
    ring

/-- Expectations of nonnegative functions commute with a concrete `PMF.map`
when the source expectation is finite. -/
theorem pmf_map_mul_hasSum_of_nonneg
    {α β : Type*} (μ : PMF α) (f : α → β) (g : β → ℝ)
    (hg : ∀ b, 0 ≤ g b)
    (hs : Summable (fun a ↦ (μ a).toReal * g (f a))) :
    HasSum (fun b ↦ (μ.map f b).toReal * g b)
      (∑' a, (μ a).toReal * g (f a)) := by
  classical
  let t : α → β → ℝ := fun a b ↦
    (if b = f a then (μ a).toReal else 0) * g b
  have htNonneg (a : α) (b : β) : 0 ≤ t a b := by
    simp only [t]
    split_ifs
    · exact mul_nonneg ENNReal.toReal_nonneg (hg b)
    · simp
  have htRow (a : α) :
      HasSum (t a) ((μ a).toReal * g (f a)) := by
    convert hasSum_ite_eq (f a) ((μ a).toReal * g (f a)) using 1
    funext b
    by_cases hb : b = f a <;> simp [t, hb]
  have ht : Summable (Function.uncurry t) := by
    apply (summable_prod_of_nonneg fun z : α × β ↦ htNonneg z.1 z.2).2
    constructor
    · exact fun a ↦ (htRow a).summable
    · convert hs using 1
      funext a
      exact (htRow a).tsum_eq
  have heq : (∑' b, (μ.map f b).toReal * g b) =
      ∑' a, (μ a).toReal * g (f a) := by
    simp_rw [pmf_map_apply_toReal]
    calc
    (∑' b, (∑' a, if b = f a then (μ a).toReal else 0) * g b) =
        ∑' b, ∑' a, t a b := by
      apply tsum_congr
      intro b
      have hμ : Summable (fun a ↦ (μ a).toReal) :=
        ENNReal.summable_toReal μ.tsum_coe_ne_top
      have hfiber : Summable
          (fun a ↦ if b = f a then (μ a).toReal else 0) := by
        apply hμ.of_nonneg_of_le
        · intro a
          split_ifs <;> positivity
        · intro a
          split_ifs
          · exact le_rfl
          · exact ENNReal.toReal_nonneg
      rw [hfiber.tsum_mul_right]
    _ = ∑' a, ∑' b, t a b := ht.tsum_comm
    _ = ∑' a, (μ a).toReal * g (f a) := by
      apply tsum_congr
      intro a
      exact (htRow a).tsum_eq
  have hcolumns : Summable (fun b ↦ ∑' a, t a b) :=
    ht.prod_symm.prod
  have htarget : Summable (fun b ↦ (μ.map f b).toReal * g b) := by
    apply hcolumns.congr
    intro b
    rw [pmf_map_apply_toReal]
    have hμ : Summable (fun a ↦ (μ a).toReal) :=
      ENNReal.summable_toReal μ.tsum_coe_ne_top
    have hfiber : Summable
        (fun a ↦ if b = f a then (μ a).toReal else 0) := by
      apply hμ.of_nonneg_of_le
      · intro a
        split_ifs <;> positivity
      · intro a
        split_ifs
        · exact le_rfl
        · exact ENNReal.toReal_nonneg
    rw [hfiber.tsum_mul_right]
  convert htarget.hasSum using 1
  exact heq.symm

theorem tsum_pmf_map_mul_of_nonneg
    {α β : Type*} (μ : PMF α) (f : α → β) (g : β → ℝ)
    (hg : ∀ b, 0 ≤ g b)
    (hs : Summable (fun a ↦ (μ a).toReal * g (f a))) :
    (∑' b, (μ.map f b).toReal * g b) =
      ∑' a, (μ a).toReal * g (f a) :=
  (pmf_map_mul_hasSum_of_nonneg μ f g hg hs).tsum_eq

theorem pmf_toReal_hasSum_one {α : Type*} (μ : PMF α) :
    HasSum (fun a ↦ (μ a).toReal) 1 := by
  have h := ENNReal.hasSum_toReal μ.tsum_coe_ne_top
  convert h using 1
  rw [← ENNReal.tsum_toReal_eq (fun a ↦ μ.apply_ne_top a), μ.tsum_coe]
  simp

/-- The reverse finite-expectation direction for a deterministic PMF map. -/
theorem pmf_pullback_mul_hasSum_of_nonneg
    {α β : Type*} (μ : PMF α) (f : α → β) (g : β → ℝ)
    (hg : ∀ b, 0 ≤ g b)
    (htarget : Summable (fun b ↦ (μ.map f b).toReal * g b)) :
    HasSum (fun a ↦ (μ a).toReal * g (f a))
      (∑' b, (μ.map f b).toReal * g b) := by
  classical
  let s : β → α → ℝ := fun b a ↦
    (if b = f a then (μ a).toReal else 0) * g b
  have hsNonneg (b : β) (a : α) : 0 ≤ s b a := by
    simp only [s]
    split_ifs
    · exact mul_nonneg ENNReal.toReal_nonneg (hg b)
    · simp
  have hμ : Summable (fun a ↦ (μ a).toReal) :=
    ENNReal.summable_toReal μ.tsum_coe_ne_top
  have hsRow (b : β) : Summable (s b) := by
    have hfiber : Summable
        (fun a ↦ if b = f a then (μ a).toReal else 0) := by
      apply hμ.of_nonneg_of_le
      · intro a
        split_ifs <;> positivity
      · intro a
        split_ifs
        · exact le_rfl
        · exact ENNReal.toReal_nonneg
    apply (hfiber.mul_right (g b)).congr
    intro a
    rfl
  have hsRowEq (b : β) :
      (∑' a, s b a) = (μ.map f b).toReal * g b := by
    rw [pmf_map_apply_toReal]
    simp only [s]
    have hfiber : Summable
        (fun a ↦ if b = f a then (μ a).toReal else 0) := by
      apply hμ.of_nonneg_of_le
      · intro a
        split_ifs <;> positivity
      · intro a
        split_ifs
        · exact le_rfl
        · exact ENNReal.toReal_nonneg
    rw [hfiber.tsum_mul_right]
  have hsProd : Summable (Function.uncurry s) := by
    apply (summable_prod_of_nonneg fun z : β × α ↦ hsNonneg z.1 z.2).2
    constructor
    · exact hsRow
    · exact htarget.congr (fun b ↦ by simpa using (hsRowEq b).symm)
  have hsource : Summable (fun a ↦ (μ a).toReal * g (f a)) := by
    have hcol := hsProd.prod_symm.prod
    apply hcol.congr
    intro a
    have hsingle : HasSum (fun b ↦ s b a) ((μ a).toReal * g (f a)) := by
      convert hasSum_ite_eq (f a) ((μ a).toReal * g (f a)) using 1
      funext b
      by_cases hb : b = f a <;> simp [s, hb]
    exact hsingle.tsum_eq
  have hforward := pmf_map_mul_hasSum_of_nonneg μ f g hg hsource
  convert hsource.hasSum using 1
  exact hforward.tsum_eq

/-- Nonnegative expectations commute with a concrete `PMF.bind` when the
resulting joint expectation is finite. -/
theorem pmf_bind_mul_hasSum_of_nonneg
    {α β : Type*} (μ : PMF α) (K : α → PMF β) (g : β → ℝ)
    (hg : ∀ b, 0 ≤ g b)
    (hrow : ∀ a, Summable (fun b ↦ (K a b).toReal * g b))
    (hs : Summable (fun a ↦ (μ a).toReal *
      (∑' b, (K a b).toReal * g b))) :
    HasSum (fun b ↦ (μ.bind K b).toReal * g b)
      (∑' a, (μ a).toReal * (∑' b, (K a b).toReal * g b)) := by
  let t : α → β → ℝ := fun a b ↦
    (μ a).toReal * (K a b).toReal * g b
  have htNonneg (a : α) (b : β) : 0 ≤ t a b := by
    exact mul_nonneg
      (mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg) (hg b)
  have htRow (a : α) : Summable (t a) := by
    apply ((hrow a).mul_left ((μ a).toReal)).congr
    intro b
    simp only [t]
    ring
  have htRowEq (a : α) :
      (∑' b, t a b) = (μ a).toReal *
        (∑' b, (K a b).toReal * g b) := by
    simp only [t]
    calc
      (∑' b, (μ a).toReal * (K a b).toReal * g b) =
          ∑' b, (μ a).toReal * ((K a b).toReal * g b) := by
        apply tsum_congr
        intro b
        ring
      _ = (μ a).toReal *
          (∑' b, (K a b).toReal * g b) :=
        (hrow a).tsum_mul_left ((μ a).toReal)
  have ht : Summable (Function.uncurry t) := by
    apply (summable_prod_of_nonneg fun z : α × β ↦ htNonneg z.1 z.2).2
    constructor
    · exact htRow
    · convert hs using 1
      funext a
      exact htRowEq a
  have hcolumn (b : β) :
      (μ.bind K b).toReal * g b = ∑' a, t a b := by
    rw [pmf_bind_apply_toReal]
    have hμ : Summable (fun a ↦ (μ a).toReal) :=
      ENNReal.summable_toReal μ.tsum_coe_ne_top
    have hbase : Summable
        (fun a ↦ (μ a).toReal * (K a b).toReal) := by
      apply hμ.of_nonneg_of_le
      · intro a
        positivity
      · intro a
        have hKle : (K a b).toReal ≤ 1 := by
          rw [← ENNReal.toReal_one]
          exact ENNReal.toReal_mono ENNReal.one_ne_top ((K a).coe_le_one b)
        have hK0 : 0 ≤ (K a b).toReal := ENNReal.toReal_nonneg
        have hμ0 : 0 ≤ (μ a).toReal := ENNReal.toReal_nonneg
        nlinarith [mul_nonneg hμ0 hK0]
    rw [hbase.tsum_mul_right]
  have hcolumns : Summable (fun b ↦ ∑' a, t a b) :=
    ht.prod_symm.prod
  have htarget : Summable (fun b ↦ (μ.bind K b).toReal * g b) := by
    exact hcolumns.congr (fun b ↦ (hcolumn b).symm)
  have heq : (∑' b, (μ.bind K b).toReal * g b) =
      ∑' a, (μ a).toReal * (∑' b, (K a b).toReal * g b) := by
    calc
      (∑' b, (μ.bind K b).toReal * g b) =
          ∑' b, ∑' a, t a b := tsum_congr hcolumn
      _ = ∑' a, ∑' b, t a b := ht.tsum_comm
      _ = ∑' a, (μ a).toReal *
          (∑' b, (K a b).toReal * g b) := by
        apply tsum_congr
        intro a
        exact htRowEq a
  convert htarget.hasSum using 1
  exact heq.symm

/-- The finite conditional expectation of one positive increment from a row of
the total spine kernel. -/
def cubicSpineKernelPositiveIncrement
    (m : ℕ) (p : ProbabilityMass) (hm : 2 ≤ m) (hcrit : Critical m p)
    (k : ℕ) : ℝ :=
  ∑' ell, (cubicSpineKernel m p hm hcrit k ell).toReal *
    positiveNatIncrement k ell

theorem cubicSpineKernelPositiveIncrement_eq_of_carrier_pos
    (m : ℕ) (p : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p) (hthird : TiltSummable m 3 p)
    (k : ℕ) (hk : 0 < cubicCarrier m k) :
    cubicSpineKernelPositiveIncrement m p hm hcrit k =
      cubicAllocationIncrementValue m k (zeroTilt m p)
        (normalizedFactorialTwo m p) / cubicCarrier m k := by
  have hraw := cubicAllocationIncrementMass_hasSum m p hm hcrit hthird k
  have hweighted : HasSum
      (fun y : Fin (m - 1) → ℕ ↦
        (cubicAllocationPMF m p hm hcrit k hk y).toReal *
          positiveNatIncrement k (cubicSpineOutput k y))
      (cubicAllocationIncrementValue m k (zeroTilt m p)
        (normalizedFactorialTwo m p) / cubicCarrier m k) := by
    have hdiv := hraw.div_const (cubicCarrier m k)
    convert hdiv using 1
    funext y
    rw [cubicAllocationPMF_apply_toReal,
      positiveNatIncrement_cubicSpineOutput]
    simp only [cubicAllocationWeight, cubicAllocationIncrementMass]
    ring
  unfold cubicSpineKernelPositiveIncrement
  rw [cubicSpineKernel_eq_allocation m p hm hcrit k hk]
  exact (tsum_pmf_map_mul_of_nonneg
    (cubicAllocationPMF m p hm hcrit k hk) (cubicSpineOutput k)
      (positiveNatIncrement k) (positiveNatIncrement_nonneg k)
      hweighted.summable).trans hweighted.tsum_eq

theorem cubicSpineKernelPositiveIncrement_eq_zero_of_carrier_eq_zero
    (m : ℕ) (p : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p) (k : ℕ) (hk : cubicCarrier m k = 0) :
    cubicSpineKernelPositiveIncrement m p hm hcrit k = 0 := by
  rw [cubicSpineKernelPositiveIncrement,
    cubicSpineKernel_eq_pure_zero_of_carrier_eq_zero m p hm hcrit k hk]
  rw [tsum_eq_single 0]
  · simp [positiveNatIncrement]
  · intro ell hell
    simp [hell]

theorem cubicSpineKernel_positiveIncrement_hasSum
    (m : ℕ) (p : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p) (hthird : TiltSummable m 3 p) (k : ℕ) :
    HasSum
      (fun ell ↦ (cubicSpineKernel m p hm hcrit k ell).toReal *
        positiveNatIncrement k ell)
      (cubicSpineKernelPositiveIncrement m p hm hcrit k) := by
  by_cases hk : 0 < cubicCarrier m k
  · have hraw := cubicAllocationIncrementMass_hasSum m p hm hcrit hthird k
    have hweighted : HasSum
        (fun y : Fin (m - 1) → ℕ ↦
          (cubicAllocationPMF m p hm hcrit k hk y).toReal *
            positiveNatIncrement k (cubicSpineOutput k y))
        (cubicAllocationIncrementValue m k (zeroTilt m p)
          (normalizedFactorialTwo m p) / cubicCarrier m k) := by
      have hdiv := hraw.div_const (cubicCarrier m k)
      convert hdiv using 1
      funext y
      rw [cubicAllocationPMF_apply_toReal,
        positiveNatIncrement_cubicSpineOutput]
      simp only [cubicAllocationWeight, cubicAllocationIncrementMass]
      ring
    rw [cubicSpineKernel_eq_allocation m p hm hcrit k hk]
    have hmap := pmf_map_mul_hasSum_of_nonneg
      (cubicAllocationPMF m p hm hcrit k hk) (cubicSpineOutput k)
        (positiveNatIncrement k) (positiveNatIncrement_nonneg k) hweighted.summable
    convert hmap using 1
    rw [cubicSpineKernelPositiveIncrement_eq_of_carrier_pos
      m p hm hcrit hthird k hk]
    exact hweighted.tsum_eq.symm
  · have hk0 : cubicCarrier m k = 0 :=
      le_antisymm (le_of_not_gt hk) (cubicCarrier_nonneg m k hm)
    rw [cubicSpineKernel_eq_pure_zero_of_carrier_eq_zero m p hm hcrit k hk0,
      cubicSpineKernelPositiveIncrement_eq_zero_of_carrier_eq_zero
        m p hm hcrit k hk0]
    have hz : (fun ell ↦ ((PMF.pure 0 : PMF ℕ) ell).toReal *
        positiveNatIncrement k ell) = 0 := by
      funext ell
      by_cases hell : ell = 0 <;> simp [hell, positiveNatIncrement]
    rw [hz]
    exact hasSum_zero

theorem cubicAllocationIncrementValue_eq_zero_of_carrier_eq_zero
    (m : ℕ) (p : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p) (hthird : TiltSummable m 3 p)
    (k : ℕ) (hk : cubicCarrier m k = 0) :
    cubicAllocationIncrementValue m k (zeroTilt m p)
      (normalizedFactorialTwo m p) = 0 := by
  have hsum := cubicAllocationIncrementMass_hasSum m p hm hcrit hthird k
  have hzero : cubicAllocationIncrementMass m p hm hcrit k = 0 := by
    funext y
    have ha := iidTupleWeight_mul_cubicAllocation_eq_zero_of_carrier_eq_zero
      m p hm hcrit k hk y
    change iidTupleWeight (criticalTiltLaw m p hm hcrit) y *
      cubicAllocation m k y * companionExcess y = (0 : ℝ)
    rw [ha, zero_mul]
  rw [hzero] at hsum
  exact (hasSum_zero.unique hsum).symm

/-- The actual one-step expectation under the cubic-size-biased source and the
total transition kernel. -/
def cubicSpineExpectedPositiveIncrement
    (m : ℕ) (p : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p) (hthird : TiltSummable m 3 p)
    (hJ : 0 < normalizedCubicMoment m p) : ℝ :=
  ∑' k, (cubicSizeBiasedPMF m p hm hcrit hthird hJ k).toReal *
    cubicSpineKernelPositiveIncrement m p hm hcrit k

theorem cubicSizeBiased_mul_kernelPositiveIncrement
    (m : ℕ) (p : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p) (hthird : TiltSummable m 3 p)
    (hJ : 0 < normalizedCubicMoment m p) (k : ℕ) :
    (cubicSizeBiasedPMF m p hm hcrit hthird hJ k).toReal *
        cubicSpineKernelPositiveIncrement m p hm hcrit k =
      criticalTiltLaw m p hm hcrit k *
          cubicAllocationIncrementValue m k (zeroTilt m p)
            (normalizedFactorialTwo m p) /
        normalizedCubicMoment m p := by
  by_cases hk : 0 < cubicCarrier m k
  · rw [cubicSizeBiasedPMF_apply_toReal,
      cubicSpineKernelPositiveIncrement_eq_of_carrier_pos
        m p hm hcrit hthird k hk]
    simp only [criticalTiltLaw_apply]
    let H := cubicCarrier m k
    let q := normalizedTilt m p k
    let v := cubicAllocationIncrementValue m k (zeroTilt m p)
      (normalizedFactorialTwo m p)
    let J := normalizedCubicMoment m p
    change (H * q / J) * (v / H) = q * v / J
    rw [div_eq_mul_inv]
    calc
      H * q * J⁻¹ * (v * H⁻¹) =
          (H * H⁻¹) * (q * v * J⁻¹) := by ring
      _ = q * v * J⁻¹ := by rw [mul_inv_cancel₀ hk.ne', one_mul]
  · have hk0 : cubicCarrier m k = 0 :=
      le_antisymm (le_of_not_gt hk) (cubicCarrier_nonneg m k hm)
    rw [cubicSpineKernelPositiveIncrement_eq_zero_of_carrier_eq_zero
      m p hm hcrit k hk0,
      cubicAllocationIncrementValue_eq_zero_of_carrier_eq_zero
        m p hm hcrit hthird k hk0]
    simp

/-- Exact `eq:incformula` for the concrete total kernel. -/
theorem cubicSpineExpectedPositiveIncrement_eq_ratio
    (m : ℕ) (p : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p) (hthird : TiltSummable m 3 p)
    (hJ : 0 < normalizedCubicMoment m p) :
    cubicSpineExpectedPositiveIncrement m p hm hcrit hthird hJ =
      spineIncrementRatio m (zeroTilt m p)
        (normalizedFactorialTwo m p) (normalizedFactorialThree m p) := by
  have hcarrier := criticalTilt_mul_cubicAllocationIncrementValue_hasSum
    m p hm hcrit hthird
  have hdiv := hcarrier.div_const (normalizedCubicMoment m p)
  unfold cubicSpineExpectedPositiveIncrement
  have hseries :
      (∑' k,
        criticalTiltLaw m p hm hcrit k *
            cubicAllocationIncrementValue m k (zeroTilt m p)
              (normalizedFactorialTwo m p) /
          normalizedCubicMoment m p) =
        spineIncrementNumerator m (zeroTilt m p)
            (normalizedFactorialTwo m p) (normalizedFactorialThree m p) /
          normalizedCubicMoment m p := hdiv.tsum_eq
  calc
    (∑' k, (cubicSizeBiasedPMF m p hm hcrit hthird hJ k).toReal *
        cubicSpineKernelPositiveIncrement m p hm hcrit k) =
        ∑' k,
          criticalTiltLaw m p hm hcrit k *
              cubicAllocationIncrementValue m k (zeroTilt m p)
                (normalizedFactorialTwo m p) /
            normalizedCubicMoment m p := by
      apply tsum_congr
      exact cubicSizeBiased_mul_kernelPositiveIncrement
        m p hm hcrit hthird hJ
    _ = spineIncrementNumerator m (zeroTilt m p)
          (normalizedFactorialTwo m p) (normalizedFactorialThree m p) /
        normalizedCubicMoment m p := hseries
    _ = spineIncrementRatio m (zeroTilt m p)
          (normalizedFactorialTwo m p) (normalizedFactorialThree m p) := by
      rw [normalizedCubicMoment_eq_spineIncrementDenominator
        m p hm hcrit hthird]
      rfl

theorem cubicSpine_expectedPositiveIncrement_hasSum
    (m : ℕ) (p : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p) (hthird : TiltSummable m 3 p)
    (hJ : 0 < normalizedCubicMoment m p) :
    HasSum
      (fun k ↦ (cubicSizeBiasedPMF m p hm hcrit hthird hJ k).toReal *
        cubicSpineKernelPositiveIncrement m p hm hcrit k)
      (cubicSpineExpectedPositiveIncrement m p hm hcrit hthird hJ) := by
  have hcarrier := criticalTilt_mul_cubicAllocationIncrementValue_hasSum
    m p hm hcrit hthird
  have hdiv := hcarrier.div_const (normalizedCubicMoment m p)
  have hactual : HasSum
      (fun k ↦ (cubicSizeBiasedPMF m p hm hcrit hthird hJ k).toReal *
        cubicSpineKernelPositiveIncrement m p hm hcrit k)
      (spineIncrementNumerator m (zeroTilt m p)
          (normalizedFactorialTwo m p) (normalizedFactorialThree m p) /
        normalizedCubicMoment m p) := by
    convert hdiv using 1
    funext k
    exact cubicSizeBiased_mul_kernelPositiveIncrement
      m p hm hcrit hthird hJ k
  convert hactual using 1
  exact (cubicSpineExpectedPositiveIncrement_eq_ratio
    m p hm hcrit hthird hJ).trans (by
      rw [spineIncrementRatio,
        ← normalizedCubicMoment_eq_spineIncrementDenominator
          m p hm hcrit hthird])

theorem cubicSpineExpectedPositiveIncrement_le_four
    (m : ℕ) (p : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p) (hthird : TiltSummable m 3 p)
    (hJ : 0 < normalizedCubicMoment m p) :
    cubicSpineExpectedPositiveIncrement m p hm hcrit hthird hJ ≤ 4 := by
  rw [cubicSpineExpectedPositiveIncrement_eq_ratio m p hm hcrit hthird hJ]
  exact criticalSpineIncrementRatio_le_four m p hm hcrit hthird

/-- Conditional positive-increment expectation of the generation-`n` orbit
kernel at state `k`. -/
def spineKernelPositiveIncrement
    (m : ℕ) (data : ProfileInitialData m) (n k : ℕ) : ℝ :=
  cubicSpineKernelPositiveIncrement m (orbit m data.law n) data.arity
    (orbit_critical m data.law (le_trans (by norm_num) data.arity)
      data.critical n) k

/-- Generation-`n` form of the actual expected positive increment. -/
def spineExpectedPositiveIncrement
    (m : ℕ) (data : ProfileInitialData m) (n : ℕ) : ℝ :=
  cubicSpineExpectedPositiveIncrement m (orbit m data.law n) data.arity
    (orbit_critical m data.law (le_trans (by norm_num) data.arity)
      data.critical n)
    (orbit_tiltSummable_three m data.law
      (le_trans (by norm_num) data.arity) data.critical data.third n)
    (normalizedCubicMoment_profile_orbit_pos m data n)

theorem spineExpectedPositiveIncrement_le_four
    (m : ℕ) (data : ProfileInitialData m) (n : ℕ) :
    spineExpectedPositiveIncrement m data n ≤ 4 := by
  exact cubicSpineExpectedPositiveIncrement_le_four m (orbit m data.law n)
    data.arity
    (orbit_critical m data.law (le_trans (by norm_num) data.arity)
      data.critical n)
    (orbit_tiltSummable_three m data.law
      (le_trans (by norm_num) data.arity) data.critical data.third n)
    (normalizedCubicMoment_profile_orbit_pos m data n)

theorem spine_expectedPositiveIncrement_hasSum
    (m : ℕ) (data : ProfileInitialData m) (n : ℕ) :
    HasSum
      (fun k ↦ (spineMarginalPMF m data n k).toReal *
        spineKernelPositiveIncrement m data n k)
      (spineExpectedPositiveIncrement m data n) := by
  exact cubicSpine_expectedPositiveIncrement_hasSum m (orbit m data.law n)
    data.arity
    (orbit_critical m data.law (le_trans (by norm_num) data.arity)
      data.critical n)
    (orbit_tiltSummable_three m data.law
      (le_trans (by norm_num) data.arity) data.critical data.third n)
    (normalizedCubicMoment_profile_orbit_pos m data n)

theorem spineKernel_positiveIncrement_hasSum
    (m : ℕ) (data : ProfileInitialData m) (n k : ℕ) :
    HasSum
      (fun ell ↦ (spineKernel m data n k ell).toReal *
        positiveNatIncrement k ell)
      (spineKernelPositiveIncrement m data n k) := by
  exact cubicSpineKernel_positiveIncrement_hasSum m (orbit m data.law n)
    data.arity
    (orbit_critical m data.law (le_trans (by norm_num) data.arity)
      data.critical n)
    (orbit_tiltSummable_three m data.law
      (le_trans (by norm_num) data.arity) data.critical data.third n) k

theorem spineMarginalPMF_bind_spineKernel_all
    (m : ℕ) (data : ProfileInitialData m) (n : ℕ) :
    (spineMarginalPMF m data n).bind (spineKernel m data n) =
      spineMarginalPMF m data (n + 1) := by
  cases m with
  | zero =>
      have h := data.arity
      omega
  | succ r =>
      exact spineMarginalPMF_bind_spineKernel r data n

/-- Initial coordinate of a finite path. -/
def finPathInitial {n : ℕ} (u : Fin (n + 1) → ℕ) : ℕ :=
  u 0

/-- Terminal coordinate of a finite path. -/
def finPathTerminal {n : ℕ} (u : Fin (n + 1) → ℕ) : ℕ :=
  u (Fin.last n)

/-- The finite-horizon law generated recursively by the concrete spine
marginal and total transition kernels. -/
def spinePathPMF (m : ℕ) (data : ProfileInitialData m) :
    (n : ℕ) → PMF (Fin (n + 1) → ℕ)
  | 0 => (spineMarginalPMF m data 0).map (fun k _ ↦ k)
  | n + 1 => (spinePathPMF m data n).bind (fun u ↦
      (spineKernel m data n (finPathTerminal u)).map (Fin.snoc u))

theorem spinePathPMF_initial_marginal
    (m : ℕ) (data : ProfileInitialData m) (n : ℕ) :
    (spinePathPMF m data n).map finPathInitial =
      spineMarginalPMF m data 0 := by
  induction n with
  | zero =>
      rw [spinePathPMF, PMF.map_comp]
      have hfun : finPathInitial ∘ (fun k : ℕ ↦ fun _ : Fin 1 ↦ k) = id := by
        funext k
        simp [finPathInitial, Function.comp_def]
      rw [hfun, PMF.map_id]
  | succ n ih =>
      rw [spinePathPMF, PMF.map_bind]
      have hinner (u : Fin (n + 1) → ℕ) :
          ((spineKernel m data n (finPathTerminal u)).map (Fin.snoc u)).map
              finPathInitial =
            PMF.pure (finPathInitial u) := by
        rw [PMF.map_comp]
        have hfun : finPathInitial ∘ Fin.snoc u =
            Function.const ℕ (finPathInitial u) := by
          funext ell
          simpa only [finPathInitial, Function.comp_apply,
            Function.const_apply] using
              (Fin.snoc_castSucc (n := n + 1)
                (α := fun _ : Fin (n + 2) ↦ ℕ) ell u (0 : Fin (n + 1)))
        rw [hfun, PMF.map_const]
      simp_rw [hinner]
      change (spinePathPMF m data n).map finPathInitial = _
      exact ih

theorem spinePathPMF_terminal_marginal
    (m : ℕ) (data : ProfileInitialData m) (n : ℕ) :
    (spinePathPMF m data n).map finPathTerminal =
      spineMarginalPMF m data n := by
  induction n with
  | zero =>
      rw [spinePathPMF, PMF.map_comp]
      have hfun : finPathTerminal ∘ (fun k : ℕ ↦ fun _ : Fin 1 ↦ k) = id := by
        funext k
        simp [finPathTerminal, Function.comp_def]
      rw [hfun, PMF.map_id]
  | succ n ih =>
      rw [spinePathPMF, PMF.map_bind]
      have hinner (u : Fin (n + 1) → ℕ) :
          ((spineKernel m data n (finPathTerminal u)).map (Fin.snoc u)).map
              finPathTerminal =
            spineKernel m data n (finPathTerminal u) := by
        rw [PMF.map_comp]
        have hfun : finPathTerminal ∘ Fin.snoc u = id := by
          funext ell
          simp [finPathTerminal, Function.comp_def]
        rw [hfun, PMF.map_id]
      simp_rw [hinner]
      calc
        (spinePathPMF m data n).bind
            (fun u ↦ spineKernel m data n (finPathTerminal u)) =
            ((spinePathPMF m data n).map finPathTerminal).bind
              (spineKernel m data n) := by
          rw [PMF.bind_map]
          rfl
        _ = (spineMarginalPMF m data n).bind (spineKernel m data n) := by
          rw [ih]
        _ = spineMarginalPMF m data (n + 1) :=
          spineMarginalPMF_bind_spineKernel_all m data n

/-- Sum of positive increments along a finite natural-valued path. -/
def finPathPositiveVariation {n : ℕ} (u : Fin (n + 1) → ℕ) : ℝ :=
  ∑ i : Fin n, positiveNatIncrement (u i.castSucc) (u i.succ)

theorem finPathPositiveVariation_nonneg
    {n : ℕ} (u : Fin (n + 1) → ℕ) :
    0 ≤ finPathPositiveVariation u := by
  exact Finset.sum_nonneg fun i _ ↦ positiveNatIncrement_nonneg _ _

theorem finPathPositiveVariation_snoc
    {n : ℕ} (u : Fin (n + 1) → ℕ) (ell : ℕ) :
    finPathPositiveVariation (Fin.snoc u ell) =
      finPathPositiveVariation u +
        positiveNatIncrement (finPathTerminal u) ell := by
  simp [finPathPositiveVariation, Fin.sum_univ_castSucc,
    finPathTerminal, Fin.succ_last, Fin.succ_castSucc]

theorem spineKernelPositiveIncrement_nonneg
    (m : ℕ) (data : ProfileInitialData m) (n k : ℕ) :
    0 ≤ spineKernelPositiveIncrement m data n k := by
  unfold spineKernelPositiveIncrement cubicSpineKernelPositiveIncrement
  exact tsum_nonneg fun ell ↦ mul_nonneg ENNReal.toReal_nonneg
    (positiveNatIncrement_nonneg k ell)

/-- One conditional path-extension row, bundled with its dependent output
type so later expectation statements do not have to re-infer that type. -/
def spinePathStepPMF
    (m : ℕ) (data : ProfileInitialData m) (n : ℕ)
    (u : Fin (n + 1) → ℕ) : PMF (Fin (n + 2) → ℕ) :=
  (spineKernel m data n (finPathTerminal u)).map
    (fun ell : ℕ ↦ (Fin.snoc u ell : Fin (n + 2) → ℕ))

theorem spinePath_stepVariation_hasSum
    (m : ℕ) (data : ProfileInitialData m) (n : ℕ)
    (u : Fin (n + 1) → ℕ) :
    HasSum
      (fun v : Fin (n + 2) → ℕ ↦
        (spinePathStepPMF m data n u v).toReal *
          @finPathPositiveVariation (n + 1) v)
      (@finPathPositiveVariation n u +
        spineKernelPositiveIncrement m data n (finPathTerminal u)) := by
  unfold spinePathStepPMF
  let K := spineKernel m data n (finPathTerminal u)
  have hmass := (pmf_toReal_hasSum_one K).mul_left
    (@finPathPositiveVariation n u)
  have hinc := spineKernel_positiveIncrement_hasSum
    m data n (finPathTerminal u)
  have hsource : HasSum
      (fun ell ↦ (K ell).toReal *
        @finPathPositiveVariation (n + 1) (Fin.snoc u ell))
      (@finPathPositiveVariation n u +
        spineKernelPositiveIncrement m data n (finPathTerminal u)) := by
    convert hmass.add hinc using 1
    · funext ell
      rw [finPathPositiveVariation_snoc]
      simp only [K]
      ring
    · ring
  have hmap : HasSum
      (fun v : Fin (n + 2) → ℕ ↦
        ((K.map (fun ell : ℕ ↦
          (Fin.snoc u ell : Fin (n + 2) → ℕ))) v).toReal *
            @finPathPositiveVariation (n + 1) v)
      (∑' ell, (K ell).toReal *
        @finPathPositiveVariation (n + 1) (Fin.snoc u ell)) :=
    pmf_map_mul_hasSum_of_nonneg K
      (fun ell : ℕ ↦ (Fin.snoc u ell : Fin (n + 2) → ℕ))
      (fun v : Fin (n + 2) → ℕ ↦ @finPathPositiveVariation (n + 1) v)
      (fun v ↦ @finPathPositiveVariation_nonneg (n + 1) v) hsource.summable
  rw [hsource.tsum_eq] at hmap
  exact hmap

/-- Exact finite-horizon expectation of the accumulated positive variation. -/
theorem spinePath_positiveVariation_hasSum
    (m : ℕ) (data : ProfileInitialData m) (n : ℕ) :
    HasSum
      (fun u : Fin (n + 1) → ℕ ↦
        (spinePathPMF m data n u).toReal * finPathPositiveVariation u)
      (∑ s ∈ Finset.range n, spineExpectedPositiveIncrement m data s) := by
  induction n with
  | zero =>
      have hz : (fun u : Fin 1 → ℕ ↦
          (spinePathPMF m data 0 u).toReal * finPathPositiveVariation u) = 0 := by
        funext u
        simp [finPathPositiveVariation]
      rw [hz]
      exact hasSum_zero
  | succ n ih =>
      let μ := spinePathPMF m data n
      let K : (Fin (n + 1) → ℕ) → PMF (Fin (n + 2) → ℕ) :=
        fun u ↦ spinePathStepPMF m data n u
      let G : ℕ → ℝ := spineKernelPositiveIncrement m data n
      have hG (k : ℕ) : 0 ≤ G k :=
        spineKernelPositiveIncrement_nonneg m data n k
      have htarget : HasSum
          (fun k ↦ ((μ.map finPathTerminal) k).toReal * G k)
          (spineExpectedPositiveIncrement m data n) := by
        dsimp only [μ, G]
        rw [spinePathPMF_terminal_marginal]
        exact spine_expectedPositiveIncrement_hasSum m data n
      have hpullRaw := pmf_pullback_mul_hasSum_of_nonneg
        μ finPathTerminal G hG htarget.summable
      have hpull : HasSum
          (fun u : Fin (n + 1) → ℕ ↦
            (μ u).toReal * G (finPathTerminal u))
          (spineExpectedPositiveIncrement m data n) := by
        rw [htarget.tsum_eq] at hpullRaw
        exact hpullRaw
      have houter : HasSum
          (fun u : Fin (n + 1) → ℕ ↦
            (μ u).toReal *
              (finPathPositiveVariation u + G (finPathTerminal u)))
          ((∑ s ∈ Finset.range n, spineExpectedPositiveIncrement m data s) +
            spineExpectedPositiveIncrement m data n) := by
        have hadd := ih.add hpull
        convert hadd using 1
        funext u
        simp only [μ]
        ring
      have hstep (u : Fin (n + 1) → ℕ) : HasSum
          (fun v : Fin (n + 2) → ℕ ↦
            (K u v).toReal * @finPathPositiveVariation (n + 1) v)
          (finPathPositiveVariation u + G (finPathTerminal u)) := by
        simpa only [K, G] using spinePath_stepVariation_hasSum m data n u
      have hs : Summable
          (fun u : Fin (n + 1) → ℕ ↦
            (μ u).toReal *
              (∑' v : Fin (n + 2) → ℕ,
                (K u v).toReal * @finPathPositiveVariation (n + 1) v)) := by
        apply houter.summable.congr
        intro u
        rw [(hstep u).tsum_eq]
      have hbind := pmf_bind_mul_hasSum_of_nonneg μ K
        (fun v : Fin (n + 2) → ℕ ↦ @finPathPositiveVariation (n + 1) v)
        (fun v ↦ @finPathPositiveVariation_nonneg (n + 1) v)
        (fun u ↦ (hstep u).summable) hs
      have hvalue :
          (∑' u : Fin (n + 1) → ℕ,
            (μ u).toReal *
              (∑' v : Fin (n + 2) → ℕ,
                (K u v).toReal * @finPathPositiveVariation (n + 1) v)) =
          (∑ s ∈ Finset.range n, spineExpectedPositiveIncrement m data s) +
            spineExpectedPositiveIncrement m data n := by
        rw [← houter.tsum_eq]
        apply tsum_congr
        intro u
        rw [(hstep u).tsum_eq]
      rw [hvalue] at hbind
      simpa only [Finset.sum_range_succ, μ, K, spinePathStepPMF,
        spinePathPMF] using hbind

/-- Expected accumulated positive variation under the finite path law. -/
def spinePathExpectedPositiveVariation
    (m : ℕ) (data : ProfileInitialData m) (n : ℕ) : ℝ :=
  ∑' u : Fin (n + 1) → ℕ,
    (spinePathPMF m data n u).toReal * finPathPositiveVariation u

theorem spinePathExpectedPositiveVariation_eq_sum
    (m : ℕ) (data : ProfileInitialData m) (n : ℕ) :
    spinePathExpectedPositiveVariation m data n =
      ∑ s ∈ Finset.range n, spineExpectedPositiveIncrement m data s :=
  (spinePath_positiveVariation_hasSum m data n).tsum_eq

theorem spinePathExpectedPositiveVariation_le_four_mul
    (m : ℕ) (data : ProfileInitialData m) (n : ℕ) :
    spinePathExpectedPositiveVariation m data n ≤ 4 * (n : ℝ) := by
  rw [spinePathExpectedPositiveVariation_eq_sum]
  calc
    (∑ s ∈ Finset.range n, spineExpectedPositiveIncrement m data s) ≤
        ∑ _s ∈ Finset.range n, (4 : ℝ) :=
      Finset.sum_le_sum fun s _ ↦ spineExpectedPositiveIncrement_le_four m data s
    _ = 4 * (n : ℝ) := by simp [mul_comm]

/-- Extend a finite path to a real sequence; values past its horizon are
irrelevant to the pathwise estimate and are set to zero. -/
def finPathToSequence {n : ℕ} (u : Fin (n + 1) → ℕ) (i : ℕ) : ℝ :=
  if hi : i < n + 1 then (u ⟨i, hi⟩ : ℕ) else 0

@[simp]
theorem finPathToSequence_zero
    {n : ℕ} (u : Fin (n + 1) → ℕ) :
    finPathToSequence u 0 = (finPathInitial u : ℝ) := by
  simp [finPathToSequence, finPathInitial]

@[simp]
theorem finPathToSequence_terminal
    {n : ℕ} (u : Fin (n + 1) → ℕ) :
    finPathToSequence u n = (finPathTerminal u : ℝ) := by
  rw [finPathToSequence, dif_pos (Nat.lt_succ_self n)]
  have hind : (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1)) = Fin.last n := by
    ext
    rfl
  rw [hind]
  rfl

theorem positivePathVariation_finPathToSequence
    {n : ℕ} (u : Fin (n + 1) → ℕ) :
    positivePathVariation (finPathToSequence u) n =
      finPathPositiveVariation u := by
  rw [positivePathVariation, finPathPositiveVariation,
    ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i hi
  have hin : (i : ℕ) < n := i.isLt
  simp only [positivePathIncrement, positiveNatIncrement, finPathToSequence,
    dif_pos (show (i : ℕ) < n + 1 by omega),
    dif_pos (show (i : ℕ) + 1 < n + 1 by omega)]
  have hzero : (⟨(i : ℕ), by omega⟩ : Fin (n + 1)) = i.castSucc := by
    ext
    rfl
  have hone : (⟨(i : ℕ) + 1, by omega⟩ : Fin (n + 1)) = i.succ := by
    ext
    rfl
  rw [hzero, hone]

theorem strictTailIndicator_finPath_bound
    {n : ℕ} (u : Fin (n + 1) → ℕ) (R : ℝ) (hR : 0 < R) :
    strictTailIndicator R (finPathTerminal u : ℝ) ≤
      strictTailIndicator (R / 2) (finPathInitial u : ℝ) +
        (2 / R) * finPathPositiveVariation u := by
  simpa only [finPathToSequence_zero, finPathToSequence_terminal,
    positivePathVariation_finPathToSequence] using
      strictTailIndicator_path_bound (finPathToSequence u) n R hR

theorem strictTailIndicator_nonneg (R x : ℝ) :
    0 ≤ strictTailIndicator R x := by
  unfold strictTailIndicator
  split_ifs <;> norm_num

theorem strictTailIndicator_le_one (R x : ℝ) :
    strictTailIndicator R x ≤ 1 := by
  unfold strictTailIndicator
  split_ifs <;> norm_num

theorem pmf_strictTail_summable
    {α : Type*} (μ : PMF α) (X : α → ℝ) (R : ℝ) :
    Summable (fun a ↦ (μ a).toReal * strictTailIndicator R (X a)) := by
  apply (pmf_toReal_hasSum_one μ).summable.of_nonneg_of_le
  · intro a
    exact mul_nonneg ENNReal.toReal_nonneg (strictTailIndicator_nonneg _ _)
  · intro a
    simpa using mul_le_mul_of_nonneg_left
      (strictTailIndicator_le_one R (X a)) ENNReal.toReal_nonneg

/-- The strict tail probability of the generation-`n` cubic-size-biased law. -/
def spineSharpTail
    (m : ℕ) (data : ProfileInitialData m) (n : ℕ) (R : ℝ) : ℝ :=
  ∑' k, (spineMarginalPMF m data n k).toReal *
    strictTailIndicator R (k : ℝ)

theorem spinePath_terminalTail_eq
    (m : ℕ) (data : ProfileInitialData m) (n : ℕ) (R : ℝ) :
    (∑' u : Fin (n + 1) → ℕ,
      (spinePathPMF m data n u).toReal *
        strictTailIndicator R (finPathTerminal u : ℝ)) =
      spineSharpTail m data n R := by
  let g : ℕ → ℝ := fun k ↦ strictTailIndicator R (k : ℝ)
  have hs := pmf_strictTail_summable (spinePathPMF m data n)
    (fun u ↦ (finPathTerminal u : ℝ)) R
  have hmap := tsum_pmf_map_mul_of_nonneg (spinePathPMF m data n)
    finPathTerminal g (fun k ↦ strictTailIndicator_nonneg R (k : ℝ)) hs
  rw [spinePathPMF_terminal_marginal] at hmap
  exact hmap.symm

theorem spinePath_initialTail_eq
    (m : ℕ) (data : ProfileInitialData m) (n : ℕ) (R : ℝ) :
    (∑' u : Fin (n + 1) → ℕ,
      (spinePathPMF m data n u).toReal *
        strictTailIndicator R (finPathInitial u : ℝ)) =
      spineSharpTail m data 0 R := by
  let g : ℕ → ℝ := fun k ↦ strictTailIndicator R (k : ℝ)
  have hs := pmf_strictTail_summable (spinePathPMF m data n)
    (fun u ↦ (finPathInitial u : ℝ)) R
  have hmap := tsum_pmf_map_mul_of_nonneg (spinePathPMF m data n)
    finPathInitial g (fun k ↦ strictTailIndicator_nonneg R (k : ℝ)) hs
  rw [spinePathPMF_initial_marginal] at hmap
  exact hmap.symm

theorem spinePath_tail_le_initial_add
    (m : ℕ) (data : ProfileInitialData m) (n : ℕ) (R : ℝ)
    (hR : 0 < R) :
    (∑' u : Fin (n + 1) → ℕ,
      (spinePathPMF m data n u).toReal *
        strictTailIndicator R (finPathTerminal u : ℝ)) ≤
      (∑' u : Fin (n + 1) → ℕ,
        (spinePathPMF m data n u).toReal *
          strictTailIndicator (R / 2) (finPathInitial u : ℝ)) +
        8 * (n : ℝ) / R := by
  let μ := spinePathPMF m data n
  have hleft := pmf_strictTail_summable μ
    (fun u ↦ (finPathTerminal u : ℝ)) R
  have hinitial := pmf_strictTail_summable μ
    (fun u ↦ (finPathInitial u : ℝ)) (R / 2)
  have hvariation := spinePath_positiveVariation_hasSum m data n
  have hpoint (u : Fin (n + 1) → ℕ) :
      (μ u).toReal * strictTailIndicator R (finPathTerminal u : ℝ) ≤
        (μ u).toReal * strictTailIndicator (R / 2) (finPathInitial u : ℝ) +
          (2 / R) * ((μ u).toReal * finPathPositiveVariation u) := by
    have hμ0 : 0 ≤ (μ u).toReal := ENNReal.toReal_nonneg
    have h := mul_le_mul_of_nonneg_left
      (strictTailIndicator_finPath_bound u R hR) hμ0
    nlinarith
  have hsum :
      (∑' u : Fin (n + 1) → ℕ,
        (μ u).toReal * strictTailIndicator R (finPathTerminal u : ℝ)) ≤
        (∑' u : Fin (n + 1) → ℕ,
          (μ u).toReal * strictTailIndicator (R / 2) (finPathInitial u : ℝ)) +
          (2 / R) * spinePathExpectedPositiveVariation m data n := by
    have hrhs := hinitial.add (hvariation.summable.mul_left (2 / R))
    calc
      (∑' u : Fin (n + 1) → ℕ,
          (μ u).toReal * strictTailIndicator R (finPathTerminal u : ℝ)) ≤
          ∑' u : Fin (n + 1) → ℕ,
            ((μ u).toReal *
              strictTailIndicator (R / 2) (finPathInitial u : ℝ) +
            (2 / R) * ((μ u).toReal * finPathPositiveVariation u)) :=
        hleft.tsum_le_tsum hpoint hrhs
      _ = (∑' u : Fin (n + 1) → ℕ,
          (μ u).toReal * strictTailIndicator (R / 2) (finPathInitial u : ℝ)) +
          (2 / R) * spinePathExpectedPositiveVariation m data n := by
        rw [hinitial.tsum_add (hvariation.summable.mul_left (2 / R)),
          hvariation.summable.tsum_mul_left]
        rfl
  change _ ≤ _
  calc
    (∑' u : Fin (n + 1) → ℕ,
        (μ u).toReal * strictTailIndicator R (finPathTerminal u : ℝ)) ≤
        (∑' u : Fin (n + 1) → ℕ,
          (μ u).toReal * strictTailIndicator (R / 2) (finPathInitial u : ℝ)) +
          (2 / R) * spinePathExpectedPositiveVariation m data n := hsum
    _ ≤ (∑' u : Fin (n + 1) → ℕ,
          (μ u).toReal * strictTailIndicator (R / 2) (finPathInitial u : ℝ)) +
          (2 / R) * (4 * (n : ℝ)) := by
      exact add_le_add_left (mul_le_mul_of_nonneg_left
        (spinePathExpectedPositiveVariation_le_four_mul m data n) (by positivity)) _
    _ = (∑' u : Fin (n + 1) → ℕ,
          (μ u).toReal * strictTailIndicator (R / 2) (finPathInitial u : ℝ)) +
          8 * (n : ℝ) / R := by ring

/-- Actual `eq:sharptail` for the recursively constructed finite coupling. -/
theorem spineSharpTail_le_initial_add
    (m : ℕ) (data : ProfileInitialData m) (n : ℕ) (R : ℝ)
    (hR : 0 < R) :
    spineSharpTail m data n R ≤
      spineSharpTail m data 0 (R / 2) + 8 * (n : ℝ) / R := by
  rw [← spinePath_terminalTail_eq m data n R,
    ← spinePath_initialTail_eq m data n (R / 2)]
  exact spinePath_tail_le_initial_add m data n R hR

end

end DerridaRetaux
