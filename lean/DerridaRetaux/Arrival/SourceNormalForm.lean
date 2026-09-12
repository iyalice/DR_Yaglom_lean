import DerridaRetaux.Arrival.SourceDifference
import Mathlib.Tactic

set_option autoImplicit false

namespace DerridaRetaux

noncomputable section

/-!
# Normal forms for the concrete source expansion

This file proves the semantic part of U22: the count tag attached to an
ordered source-factor choice is also the exponent/order tag of that actual
coefficient term.  We first move `F_s` to its support-zero core, so every
intermediate monomial shift is a natural-number shift.
-/

/-- Positive integer shifts compose without any support hypothesis. -/
theorem shiftByInt_ofNat_comp_ofNat (d e : ℕ) (a : Seq) :
    shiftByInt (d : ℤ) (shiftByInt (e : ℤ) a) =
      shiftByInt ((d + e : ℕ) : ℤ) a := by
  have hseries :
      PowerSeries.mk (shiftByInt (d : ℤ) (shiftByInt (e : ℤ) a)) =
        PowerSeries.mk (shiftByInt ((d + e : ℕ) : ℤ) a) := by
    rw [powerSeries_mk_shiftByInt_ofNat, powerSeries_mk_shiftByInt_ofNat,
      powerSeries_mk_shiftByInt_ofNat, ← mul_assoc, ← pow_add]
  funext n
  simpa using congrArg (fun f ↦ PowerSeries.coeff ℝ n f) hseries

/-- A left shift cancels part of a preceding positive shift. -/
theorem shiftByInt_neg_ofNat_comp_ofNat
    (d e : ℕ) (a : Seq) (hde : d ≤ e) :
    shiftByInt (-(d : ℤ)) (shiftByInt (e : ℤ) a) =
      shiftByInt ((e - d : ℕ) : ℤ) a := by
  have hsupp : CoeffSupportedFrom d (shiftByInt (e : ℤ) a) := by
    intro n hn
    exact shiftByInt_eq_zero_of_lt e n a (hn.trans_le hde)
  have hleft := powerSeries_X_pow_mul_shiftByInt_neg
    d (shiftByInt (e : ℤ) a) hsupp
  have hright :
      PowerSeries.X ^ d *
          PowerSeries.mk (shiftByInt ((e - d : ℕ) : ℤ) a) =
        PowerSeries.mk (shiftByInt (e : ℤ) a) := by
    rw [powerSeries_mk_shiftByInt_ofNat, powerSeries_mk_shiftByInt_ofNat]
    rw [← mul_assoc, ← pow_add, Nat.add_sub_of_le hde]
  have hseries :
      PowerSeries.mk (shiftByInt (-(d : ℤ)) (shiftByInt (e : ℤ) a)) =
        PowerSeries.mk (shiftByInt ((e - d : ℕ) : ℤ) a) := by
    apply PowerSeries.X_pow_mul_cancel
    exact hleft.trans hright.symm
  funext n
  simpa using congrArg (fun f ↦ PowerSeries.coeff ℝ n f) hseries

/-- An arbitrary integer shift can be combined with a preceding natural
shift whenever their total is the stated natural number. -/
theorem shiftByInt_comp_ofNat_eq_ofNat
    (d : ℤ) (e n : ℕ) (a : Seq) (htotal : d + (e : ℤ) = (n : ℤ)) :
    shiftByInt d (shiftByInt (e : ℤ) a) = shiftByInt (n : ℤ) a := by
  cases d with
  | ofNat d =>
      have hcast : ((d + e : ℕ) : ℤ) = (n : ℤ) := by
        simpa only [Int.ofNat_eq_coe, Int.natCast_add] using htotal
      have hn : d + e = n := by exact_mod_cast hcast
      subst n
      exact shiftByInt_ofNat_comp_ofNat d e a
  | negSucc d =>
      have hde : d + 1 ≤ e := by omega
      have hn : e - (d + 1) = n := by omega
      subst n
      simpa only [Int.negSucc_eq] using
        shiftByInt_neg_ofNat_comp_ofNat (d + 1) e a hde

/-- Integer shifts commute with scalar multiplication. -/
theorem shiftByInt_const_mul (d : ℤ) (c : ℝ) (a : Seq) :
    shiftByInt d (fun n : ℕ ↦ c * a n) =
      fun n : ℕ ↦ c * shiftByInt d a n := by
  funext n
  rw [shiftByInt, shiftByInt]
  by_cases h : 0 ≤ (n : ℤ) - d
  · simp [zeroExtend, h]
  · simp [zeroExtend, h]

/-- The support-zero coefficient core `H_s(k)=F_s(k+s)`. -/
def arrivalCoeffCore
    (m : ℕ) (p₀ : ProbabilityMass) (s : ℕ) : Seq :=
  shiftByInt (-(s : ℤ)) (arrivalCoeff m p₀ s)

/-- Restoring the support shift recovers the actual arrival array. -/
theorem shift_arrivalCoeffCore_eq
    (m : ℕ) (p₀ : ProbabilityMass) (s : ℕ) :
    shiftByInt (s : ℤ) (arrivalCoeffCore m p₀ s) =
      arrivalCoeff m p₀ s := by
  have hseries := powerSeries_X_pow_mul_shiftByInt_neg
    s (arrivalCoeff m p₀ s) (arrivalCoeff_supportedFrom m p₀ s)
  have hmk := powerSeries_mk_shiftByInt_ofNat
    s (arrivalCoeffCore m p₀ s)
  rw [arrivalCoeffCore] at hmk
  have hseries' :
      PowerSeries.mk (shiftByInt (s : ℤ) (arrivalCoeffCore m p₀ s)) =
        PowerSeries.mk (arrivalCoeff m p₀ s) := hmk.trans hseries
  funext n
  simpa using congrArg (fun f ↦ PowerSeries.coeff ℝ n f) hseries'

/-- Scalar carried by one concrete factor. -/
def sourceFactorScalar
    (m : ℕ) (p₀ : ProbabilityMass) (s : ℕ) : SourceFactorChoice m → ℝ
  | .inl true => 1
  | .inl false => -arrivalBoundary m p₀ s
  | .inr r => arrivalAlpha m p₀ s (sourceArityValue r)

/-- Convolution order of one factor relative to the core `H_s`. -/
def sourceFactorOrder {m : ℕ} : SourceFactorChoice m → ℕ
  | .inl true => 1
  | .inl false => 0
  | .inr r => sourceArityValue r

/-- Natural monomial shift of one factor relative to the core `H_s`. -/
def sourceFactorCoreShift {m : ℕ} (s : ℕ) : SourceFactorChoice m → ℕ
  | .inl true => s
  | .inl false => s
  | .inr r => s + sourceArityValue r - 1

/-- Each literal factor has the claimed scalar, core shift, and convolution
order.  This is the factor-level semantic bridge missing from the count-only
tag certificate. -/
theorem sourceFactorValue_eq_coreNormalForm
    (m : ℕ) (p₀ : ProbabilityMass) (s : ℕ) (x : SourceFactorChoice m) :
    sourceFactorValue m p₀ s x =
      fun N : ℕ ↦ sourceFactorScalar m p₀ s x *
        shiftByInt ((sourceFactorCoreShift s x : ℕ) : ℤ)
          (convPow (sourceFactorOrder x) (arrivalCoeffCore m p₀ s)) N := by
  cases x with
  | inl b =>
      cases b with
      | true =>
          simp only [sourceFactorValue, sourceFactorScalar, sourceFactorCoreShift,
            sourceFactorOrder, one_mul, convPow_one]
          exact (shift_arrivalCoeffCore_eq m p₀ s).symm
      | false =>
          funext N
          simp only [sourceFactorValue, sourceFactorScalar, sourceFactorCoreShift,
            sourceFactorOrder, convPow_zero, Pi.zero_apply]
          by_cases hNs : N < s
          · rw [shiftByInt_eq_zero_of_lt s N _ hNs]
            simp [hNs.ne]
          · have hsN : s ≤ N := Nat.le_of_not_gt hNs
            rw [shiftByInt_of_le s N _ hsN, diracSeq_apply]
            by_cases hEq : N = s
            · subst N
              simp
            · have hsub : N - s ≠ 0 := by omega
              simp [hEq, hsub]
  | inr r =>
      let q := sourceArityValue r
      have hq : 2 ≤ q := by
        simp [q, sourceArityValue]
      have hfirst :
          sourceOldShift s q + ((q * s : ℕ) : ℤ) =
            ((2 * s + q - 2 : ℕ) : ℤ) := by
        simp only [sourceOldShift]
        rw [show 2 * s + q - 2 = 2 * s + (q - 2) by omega]
        push_cast [hq]
        ring
      have hsecond :
          1 - (s : ℤ) + ((2 * s + q - 2 : ℕ) : ℤ) =
            ((s + q - 1 : ℕ) : ℤ) := by
        omega
      simp only [sourceFactorValue, arrivalFormulaTerm, sourceFactorScalar,
        sourceFactorCoreShift, sourceFactorOrder, q]
      change shiftByInt (1 - (s : ℤ))
          (fun N : ℕ ↦ arrivalAlpha m p₀ s q *
            shiftByInt (sourceOldShift s q)
              (convPow q (arrivalCoeff m p₀ s)) N) = _
      rw [shiftByInt_const_mul]
      rw [← shift_arrivalCoeffCore_eq m p₀ s]
      rw [convPow_shiftByInt_ofNat]
      rw [shiftByInt_comp_ofNat_eq_ofNat
        (sourceOldShift s q) (q * s) (2 * s + q - 2)
        (convPow q (arrivalCoeffCore m p₀ s)) hfirst]
      rw [shiftByInt_comp_ofNat_eq_ofNat
        (1 - (s : ℤ)) (2 * s + q - 2) (s + q - 1)
        (convPow q (arrivalCoeffCore m p₀ s)) hsecond]

/-- Product of the literal scalar factors of an ordered choice. -/
def sourceChoiceScalar
    {m R : ℕ} (p₀ : ProbabilityMass) (s : ℕ)
    (choice : Fin R → SourceFactorChoice m) : ℝ :=
  ∏ i : Fin R, sourceFactorScalar m p₀ s (choice i)

/-- Total core shift of an ordered choice. -/
def sourceChoiceCoreShift
    {m R : ℕ} (s : ℕ) (choice : Fin R → SourceFactorChoice m) : ℕ :=
  ∑ i : Fin R, sourceFactorCoreShift s (choice i)

/-- Total core convolution order of an ordered choice. -/
def sourceChoiceOrder
    {m R : ℕ} (choice : Fin R → SourceFactorChoice m) : ℕ :=
  ∑ i : Fin R, sourceFactorOrder (choice i)

/-- Summing a function over positions is the same as summing it over factor
fibers with their exact multiplicities. -/
theorem sum_sourceFactorMultiplicity_mul
    {m R : ℕ} (choice : Fin R → SourceFactorChoice m)
    (g : SourceFactorChoice m → ℕ) :
    (∑ x : SourceFactorChoice m, sourceFactorMultiplicity choice x * g x) =
      ∑ i : Fin R, g (choice i) := by
  simp only [sourceFactorMultiplicity, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _hi
  simp

/-- The semantic convolution order agrees with `q` in the actual tag. -/
theorem sourceChoiceOrder_eq_tag_q
    {m R : ℕ} (hRm : R ≤ m) (choice : Fin R → SourceFactorChoice m) :
    sourceChoiceOrder choice = (functionExpansionTag hRm choice).q := by
  have hfiber := sum_sourceFactorMultiplicity_mul choice sourceFactorOrder
  unfold sourceChoiceOrder
  rw [← hfiber]
  simp [sourceChoiceOrder, sourceFactorOrder, functionExpansionTag,
    SourceMonomialTag.q, SourceMonomialTag.sourceOrder, Nat.mul_comm]

/-- A single factor shift is `s` plus its source excess. -/
def sourceFactorCoreExcess {m : ℕ} : SourceFactorChoice m → ℕ
  | .inl _b => 0
  | .inr r => sourceArityValue r - 1

theorem sourceFactorCoreShift_eq
    {m : ℕ} (s : ℕ) (x : SourceFactorChoice m) :
    sourceFactorCoreShift s x = s + sourceFactorCoreExcess x := by
  cases x with
  | inl b => cases b <;> simp [sourceFactorCoreShift, sourceFactorCoreExcess]
  | inr r =>
      simp only [sourceFactorCoreShift, sourceFactorCoreExcess]
      have hr : 1 ≤ sourceArityValue r := by simp [sourceArityValue]
      omega

/-- The semantic total excess agrees with `e` in the actual function tag. -/
theorem sum_sourceFactorCoreExcess_eq_tag_e
    {m R : ℕ} (hRm : R ≤ m) (choice : Fin R → SourceFactorChoice m) :
    (∑ i : Fin R, sourceFactorCoreExcess (choice i)) =
      (functionExpansionTag hRm choice).e := by
  have hfiber := sum_sourceFactorMultiplicity_mul choice sourceFactorCoreExcess
  rw [← hfiber]
  simp [sourceFactorCoreExcess, functionExpansionTag, SourceMonomialTag.e,
    SourceMonomialTag.sourceExcess, Nat.mul_comm]

/-- The natural core shift is `R*s+e`. -/
theorem sourceChoiceCoreShift_eq_outer_mul_add_tag_e
    {m R : ℕ} (hRm : R ≤ m) (s : ℕ)
    (choice : Fin R → SourceFactorChoice m) :
    sourceChoiceCoreShift s choice =
      R * s + (functionExpansionTag hRm choice).e := by
  simp only [sourceChoiceCoreShift, sourceFactorCoreShift_eq,
    Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  rw [sum_sourceFactorCoreExcess_eq_tag_e hRm choice]
  simp [Nat.mul_comm]

/-- `PowerSeries.mk` commutes with scalar multiplication of coefficients. -/
theorem powerSeries_mk_const_mul (c : ℝ) (a : Seq) :
    PowerSeries.mk (fun n : ℕ ↦ c * a n) =
      c • PowerSeries.mk a := by
  apply PowerSeries.ext
  intro n
  simp

/-- Power-series normal form of one concrete factor. -/
theorem powerSeries_mk_sourceFactorValue
    (m : ℕ) (p₀ : ProbabilityMass) (s : ℕ) (x : SourceFactorChoice m) :
    PowerSeries.mk (sourceFactorValue m p₀ s x) =
      PowerSeries.C ℝ (sourceFactorScalar m p₀ s x) *
        (PowerSeries.X ^ sourceFactorCoreShift s x *
          PowerSeries.mk (arrivalCoeffCore m p₀ s) ^ sourceFactorOrder x) := by
  rw [sourceFactorValue_eq_coreNormalForm]
  rw [powerSeries_mk_const_mul, PowerSeries.smul_eq_C_mul]
  rw [powerSeries_mk_shiftByInt_ofNat, powerSeries_mk_convPow]

/-- The product underlying one ordered multinomial summand collects exactly
its scalar, total core shift, and total convolution order. -/
theorem prod_powerSeries_sourceFactorValue
    {m R : ℕ} (p₀ : ProbabilityMass) (s : ℕ)
    (choice : Fin R → SourceFactorChoice m) :
    (∏ i : Fin R, PowerSeries.mk (sourceFactorValue m p₀ s (choice i))) =
      PowerSeries.C ℝ (sourceChoiceScalar p₀ s choice) *
        (PowerSeries.X ^ sourceChoiceCoreShift s choice *
          PowerSeries.mk (arrivalCoeffCore m p₀ s) ^ sourceChoiceOrder choice) := by
  simp_rw [powerSeries_mk_sourceFactorValue]
  let c : Fin R → ℝ := fun i ↦ sourceFactorScalar m p₀ s (choice i)
  let d : Fin R → ℕ := fun i ↦ sourceFactorCoreShift s (choice i)
  let q : Fin R → ℕ := fun i ↦ sourceFactorOrder (choice i)
  let H : PowerSeries ℝ := PowerSeries.mk (arrivalCoeffCore m p₀ s)
  have hcollect : ∀ S : Finset (Fin R),
      (∏ i ∈ S, PowerSeries.C ℝ (c i) *
          (PowerSeries.X ^ d i * H ^ q i)) =
        PowerSeries.C ℝ (∏ i ∈ S, c i) *
          (PowerSeries.X ^ (∑ i ∈ S, d i) *
            H ^ (∑ i ∈ S, q i)) := by
    intro S
    induction S using Finset.induction_on with
    | empty => simp
    | @insert i S hi ih =>
        simp only [Finset.mem_insert, Finset.prod_insert, Finset.sum_insert, hi,
          not_false_eq_true, ih, map_mul, pow_add]
        ring
  simpa only [sourceChoiceScalar, sourceChoiceCoreShift, sourceChoiceOrder,
    c, d, q, H] using hcollect Finset.univ

/-- Every ordered product in the actual multinomial expansion has one
support-zero core normal form. -/
theorem fintypeConvPowTerm_eq_coreNormalForm
    {m R : ℕ} (p₀ : ProbabilityMass) (s : ℕ)
    (choice : Fin R → SourceFactorChoice m) :
    fintypeConvPowTerm (sourceFactorValue m p₀ s) choice =
      fun N : ℕ ↦ sourceChoiceScalar p₀ s choice *
        shiftByInt ((sourceChoiceCoreShift s choice : ℕ) : ℤ)
          (convPow (sourceChoiceOrder choice) (arrivalCoeffCore m p₀ s)) N := by
  funext N
  change PowerSeries.coeff ℝ N
      (∏ i : Fin R, PowerSeries.mk (sourceFactorValue m p₀ s (choice i))) = _
  rw [prod_powerSeries_sourceFactorValue]
  have hright :
      PowerSeries.mk
          (fun k : ℕ ↦ sourceChoiceScalar p₀ s choice *
            shiftByInt ((sourceChoiceCoreShift s choice : ℕ) : ℤ)
              (convPow (sourceChoiceOrder choice)
                (arrivalCoeffCore m p₀ s)) k) =
        PowerSeries.C ℝ (sourceChoiceScalar p₀ s choice) *
          (PowerSeries.X ^ sourceChoiceCoreShift s choice *
            PowerSeries.mk (arrivalCoeffCore m p₀ s) ^
              sourceChoiceOrder choice) := by
    rw [powerSeries_mk_const_mul, PowerSeries.smul_eq_C_mul]
    rw [powerSeries_mk_shiftByInt_ofNat, powerSeries_mk_convPow]
  simpa using (congrArg (fun f ↦ PowerSeries.coeff ℝ N f) hright).symm

/-- The tag shift applied to its claimed convolution power is the natural
core monomial of degree `2s+e`. -/
theorem shift_tagSigma_convPow_arrivalCoeff_eq_core
    {m R : ℕ} (p₀ : ProbabilityMass) (hRm : R ≤ m) (s : ℕ)
    (choice : Fin R → SourceFactorChoice m) :
    shiftByInt ((functionExpansionTag hRm choice).sigma s)
        (convPow (functionExpansionTag hRm choice).q
          (arrivalCoeff m p₀ s)) =
      shiftByInt
        ((2 * s + (functionExpansionTag hRm choice).e : ℕ) : ℤ)
        (convPow (functionExpansionTag hRm choice).q
          (arrivalCoeffCore m p₀ s)) := by
  let tag := functionExpansionTag hRm choice
  have htotal :
      tag.sigma s + ((tag.q * s : ℕ) : ℤ) =
        ((2 * s + tag.e : ℕ) : ℤ) := by
    simp only [SourceMonomialTag.sigma]
    push_cast
    ring
  rw [← shift_arrivalCoeffCore_eq m p₀ s]
  rw [convPow_shiftByInt_ofNat]
  exact shiftByInt_comp_ofNat_eq_ofNat
    (tag.sigma s) (tag.q * s) (2 * s + tag.e)
      (convPow tag.q (arrivalCoeffCore m p₀ s)) htotal

/-- The outer shift of a concrete choice also lands at core degree `2s+e`. -/
theorem shift_newShift_fintypeConvPowTerm_eq_core
    {m R : ℕ} (p₀ : ProbabilityMass) (hRm : R ≤ m)
    (s : ℕ) (choice : Fin R → SourceFactorChoice m) :
    shiftByInt (sourceNewShift s R)
        (fintypeConvPowTerm (sourceFactorValue m p₀ s) choice) =
      fun N : ℕ ↦ sourceChoiceScalar p₀ s choice *
        shiftByInt
          ((2 * s + (functionExpansionTag hRm choice).e : ℕ) : ℤ)
          (convPow (functionExpansionTag hRm choice).q
            (arrivalCoeffCore m p₀ s)) N := by
  rw [fintypeConvPowTerm_eq_coreNormalForm]
  rw [shiftByInt_const_mul]
  rw [sourceChoiceOrder_eq_tag_q hRm choice]
  have hshift := sourceChoiceCoreShift_eq_outer_mul_add_tag_e hRm s choice
  have htotal :
      sourceNewShift s R + ((sourceChoiceCoreShift s choice : ℕ) : ℤ) =
        ((2 * s + (functionExpansionTag hRm choice).e : ℕ) : ℤ) := by
    rw [hshift]
    simp only [sourceNewShift]
    push_cast
    ring
  rw [shiftByInt_comp_ofNat_eq_ofNat
    (sourceNewShift s R) (sourceChoiceCoreShift s choice)
      (2 * s + (functionExpansionTag hRm choice).e)
      (convPow (functionExpansionTag hRm choice).q
        (arrivalCoeffCore m p₀ s)) htotal]

/-- The actual expanded function-change term is exactly scalar times the
shifted convolution power named by its concrete tag. -/
theorem sourceFunctionExpandedTerm_eq_tagNormalForm
    {m R : ℕ} (p₀ : ProbabilityMass) (hRm : R ≤ m)
    (s : ℕ) (choice : Fin R → SourceFactorChoice m) :
    sourceFunctionExpandedTerm m p₀ s R choice =
      fun N : ℕ ↦
        (arrivalAlpha m p₀ (s + 1) R * sourceChoiceScalar p₀ s choice) *
          shiftByInt ((functionExpansionTag hRm choice).sigma s)
            (convPow (functionExpansionTag hRm choice).q
              (arrivalCoeff m p₀ s)) N := by
  funext N
  simp only [sourceFunctionExpandedTerm]
  rw [congrFun
    (shift_newShift_fintypeConvPowTerm_eq_core p₀ hRm s choice) N]
  rw [congrFun
    (shift_tagSigma_convPow_arrivalCoeff_eq_core p₀ hRm s choice) N]
  ring

/-- A concrete term is represented by a tag when it is one scalar multiple
of the shifted convolution power specified by that tag. -/
def HasSourceTagNormalForm
    {m : ℕ} (F term : Seq) (s : ℕ) (tag : SourceMonomialTag m) : Prop :=
  ∃ c : ℝ, term = fun N : ℕ ↦
    c * shiftByInt (tag.sigma s) (convPow tag.q F) N

theorem sourceCoefficientChangeTerm_hasTagNormalForm
    {m R : ℕ} (p₀ : ProbabilityMass) (hR : 2 ≤ R) (hRm : R ≤ m)
    (s : ℕ) :
    HasSourceTagNormalForm (arrivalCoeff m p₀ s)
      (sourceCoefficientChangeTerm m p₀ s R) s
      (coefficientChangeTag hRm) := by
  refine ⟨arrivalAlpha m p₀ (s + 1) R - arrivalAlpha m p₀ s R, ?_⟩
  funext N
  simp only [sourceCoefficientChangeTerm, HasSourceTagNormalForm]
  rw [coefficientChangeTag_sigma hR hRm]
  simp [coefficientChangeTag, SourceMonomialTag.q]

theorem sourceShiftNoExcessTerm_hasTagNormalForm
    {m R : ℕ} (p₀ : ProbabilityMass) (hRm : R ≤ m) (s : ℕ) :
    HasSourceTagNormalForm (arrivalCoeff m p₀ s)
      (sourceShiftNoExcessTerm m p₀ s R) s
      (shiftNoExcessTag hRm) := by
  refine ⟨arrivalAlpha m p₀ (s + 1) R, ?_⟩
  funext N
  simp only [sourceShiftNoExcessTerm, HasSourceTagNormalForm]
  rw [shiftNoExcessTag_sigma hRm]
  simp [shiftNoExcessTag, SourceMonomialTag.q]

theorem sourceShiftWithExcessTerm_hasTagNormalForm
    {m R : ℕ} (p₀ : ProbabilityMass) (hR : 2 ≤ R) (hRm : R ≤ m)
    (s : ℕ) :
    HasSourceTagNormalForm (arrivalCoeff m p₀ s)
      (sourceShiftWithExcessTerm m p₀ s R) s
      (shiftWithExcessTag hRm) := by
  refine ⟨-arrivalAlpha m p₀ (s + 1) R, ?_⟩
  funext N
  simp only [sourceShiftWithExcessTerm, HasSourceTagNormalForm]
  rw [shiftWithExcessTag_sigma hR hRm]
  simp [shiftWithExcessTag, SourceMonomialTag.q]

theorem sourceFunctionExpandedTerm_hasTagNormalForm
    {m R : ℕ} (p₀ : ProbabilityMass) (hRm : R ≤ m)
    (s : ℕ) (choice : Fin R → SourceFactorChoice m) :
    HasSourceTagNormalForm (arrivalCoeff m p₀ s)
      (sourceFunctionExpandedTerm m p₀ s R choice) s
      (functionExpansionTag hRm choice) := by
  refine ⟨arrivalAlpha m p₀ (s + 1) R * sourceChoiceScalar p₀ s choice, ?_⟩
  exact sourceFunctionExpandedTerm_eq_tagNormalForm p₀ hRm s choice

/-- Exhaustive semantic certificate for every summand in the concrete source
difference: the degree-two shift pair cancels, while every retained term has
a valid tag and the exact normal form prescribed by that tag. -/
theorem actual_sourceDifference_terms_have_valid_normalForms
    {m R : ℕ} (p₀ : ProbabilityMass) (s : ℕ)
    (hRmem : R ∈ Finset.Icc 2 m) :
    ((coefficientChangeTag (Finset.mem_Icc.mp hRmem).2).Valid ∧
      HasSourceTagNormalForm (arrivalCoeff m p₀ s)
        (sourceCoefficientChangeTerm m p₀ s R) s
        (coefficientChangeTag (Finset.mem_Icc.mp hRmem).2)) ∧
    (R = 2 ∨
      (((shiftNoExcessTag (Finset.mem_Icc.mp hRmem).2).Valid ∧
        HasSourceTagNormalForm (arrivalCoeff m p₀ s)
          (sourceShiftNoExcessTerm m p₀ s R) s
          (shiftNoExcessTag (Finset.mem_Icc.mp hRmem).2)) ∧
       ((shiftWithExcessTag (Finset.mem_Icc.mp hRmem).2).Valid ∧
        HasSourceTagNormalForm (arrivalCoeff m p₀ s)
          (sourceShiftWithExcessTerm m p₀ s R) s
          (shiftWithExcessTag (Finset.mem_Icc.mp hRmem).2)))) ∧
    ∀ choice ∈ nontrivialFunctionChoices m R,
      (functionExpansionTag (Finset.mem_Icc.mp hRmem).2 choice).Valid ∧
        HasSourceTagNormalForm (arrivalCoeff m p₀ s)
          (sourceFunctionExpandedTerm m p₀ s R choice) s
          (functionExpansionTag (Finset.mem_Icc.mp hRmem).2 choice) := by
  have hvalid := actual_sourceDifference_terms_have_valid_tags hRmem
  have hR := (Finset.mem_Icc.mp hRmem).1
  have hRm := (Finset.mem_Icc.mp hRmem).2
  refine ⟨⟨hvalid.1,
    sourceCoefficientChangeTerm_hasTagNormalForm p₀ hR hRm s⟩, ?_, ?_⟩
  · rcases hvalid.2.1 with htwo | hshift
    · exact Or.inl htwo
    · exact Or.inr
        ⟨⟨hshift.1, sourceShiftNoExcessTerm_hasTagNormalForm p₀ hRm s⟩,
          ⟨hshift.2,
            sourceShiftWithExcessTerm_hasTagNormalForm p₀ hR hRm s⟩⟩
  · intro choice hchoice
    exact ⟨hvalid.2.2 choice hchoice,
      sourceFunctionExpandedTerm_hasTagNormalForm p₀ hRm s choice⟩

end

end DerridaRetaux
