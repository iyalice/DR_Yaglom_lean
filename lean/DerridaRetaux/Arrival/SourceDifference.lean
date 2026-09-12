import DerridaRetaux.Arrival.MomentTail
import DerridaRetaux.Arrival.SourceTags
import Mathlib.Algebra.BigOperators.Ring.Finset

set_option autoImplicit false

open scoped BigOperators

namespace DerridaRetaux

noncomputable section

/-!
# Concrete finite expansion of the arrival-source difference

This file connects the finite tag language in `Arrival.SourceTags` to the
actual coefficient arrays in `Arrival.ArrivalRecursion`.  It proves the outer
coefficient/shift/function three-change identity and gives a coefficientwise,
multiplicity-preserving expansion of every function change.  Each non-all-`F`
summand of that concrete expansion receives a mechanically valid
`SourceMonomialTag`.

The further analytic step which rewrites each expanded convolution as a
single shifted `F_s^q` term and sums its cubic tail bound is not asserted here.
-/

/-- The finite indices `0, ..., m-2` are equivalent to the source orders
`2, ..., m` used by `arrivalFormulaSource`. -/
def sourceArityEquivIcc (m : ℕ) :
    SourceArity m ≃ {r : ℕ // r ∈ Finset.Icc 2 m} where
  toFun r := ⟨sourceArityValue r, Finset.mem_Icc.mpr ⟨by
    unfold sourceArityValue
    omega, SourceMonomialTag.sourceArity_le r⟩⟩
  invFun r := ⟨r.1 - 2, by
    have hr := Finset.mem_Icc.mp r.2
    omega⟩
  left_inv r := by
    apply Fin.ext
    change ((r : ℕ) + 2 - 2) = (r : ℕ)
    omega
  right_inv r := by
    apply Subtype.ext
    change (r.1 - 2) + 2 = r.1
    exact Nat.sub_add_cancel (Finset.mem_Icc.mp r.2).1

/-- Reindex a sum over the intrinsic source arities as the manuscript interval
`Finset.Icc 2 m`. -/
theorem sum_sourceArity_eq_Icc
    {M : Type*} [AddCommMonoid M] (m : ℕ) (f : ℕ → M) :
    (∑ r : SourceArity m, f (sourceArityValue r)) =
      ∑ r ∈ Finset.Icc 2 m, f r := by
  calc
    (∑ r : SourceArity m, f (sourceArityValue r)) =
        ∑ r : {r : ℕ // r ∈ Finset.Icc 2 m}, f r :=
      Fintype.sum_equiv (sourceArityEquivIcc m) _ _ (fun _r ↦ rfl)
    _ = ∑ r ∈ Finset.Icc 2 m, f r := by
      simpa only [Finset.attach_eq_univ] using
        (Finset.sum_attach (Finset.Icc 2 m) f)

/-- Integer coefficient shifts distribute over a finite type-indexed sum. -/
theorem shiftByInt_fintype_sum
    {ι : Type*} [Fintype ι] (d : ℤ) (f : ι → Seq) :
    shiftByInt d (fun N : ℕ ↦ ∑ i : ι, f i N) =
      fun N : ℕ ↦ ∑ i : ι, shiftByInt d (f i) N := by
  funext N
  by_cases hindex : 0 ≤ (N : ℤ) - d
  · have hd : d ≤ (N : ℤ) := by omega
    simp [shiftByInt, zeroExtend, hd]
  · have hd : ¬d ≤ (N : ℤ) := by omega
    simp [shiftByInt, zeroExtend, hd]

/-- Integer coefficient shifts distribute over a finite-set sum. -/
theorem shiftByInt_finset_sum
    {ι : Type*} (d : ℤ) (S : Finset ι) (f : ι → Seq) :
    shiftByInt d (fun N : ℕ ↦ ∑ i ∈ S, f i N) =
      fun N : ℕ ↦ ∑ i ∈ S, shiftByInt d (f i) N := by
  funext N
  by_cases hindex : 0 ≤ (N : ℤ) - d
  · have hd : d ≤ (N : ℤ) := by omega
    simp [shiftByInt, zeroExtend, hd]
  · have hd : ¬d ≤ (N : ℤ) := by omega
    simp [shiftByInt, zeroExtend, hd]

/-- Integer coefficient shifts distribute over subtraction. -/
theorem shiftByInt_sub (d : ℤ) (a b : Seq) :
    shiftByInt d (fun N : ℕ ↦ a N - b N) =
      fun N : ℕ ↦ shiftByInt d a N - shiftByInt d b N := by
  funext N
  by_cases hindex : 0 ≤ (N : ℤ) - d
  · have hd : d ≤ (N : ℤ) := by omega
    simp [shiftByInt, zeroExtend, hd]
  · have hd : ¬d ≤ (N : ℤ) := by omega
    simp [shiftByInt, zeroExtend, hd]

/-- One literal order-`r` summand of `arrivalFormulaSource`. -/
def arrivalFormulaTerm
    (m : ℕ) (p₀ : ProbabilityMass) (s r : ℕ) : Seq :=
  fun N : ℕ ↦
    arrivalAlpha m p₀ s r *
      shiftByInt (((r : ℤ) - 2) * (1 - (s : ℤ)))
        (convPow r (arrivalCoeff m p₀ s)) N

/-- The literal source is the finite sum of its order-indexed terms. -/
theorem arrivalFormulaSource_eq_sum_terms
    (m : ℕ) (p₀ : ProbabilityMass) (s : ℕ) :
    arrivalFormulaSource m p₀ s =
      fun N : ℕ ↦ ∑ r ∈ Finset.Icc 2 m, arrivalFormulaTerm m p₀ s r N := by
  rfl

/-- Factor alphabet for the concrete expansion of `F_(s+1)^R`.
`Sum.inl true` is `F_s`, `Sum.inl false` is `-B_s`, and `Sum.inr r`
is the order-`r+2` source factor. -/
abbrev SourceFactorChoice (m : ℕ) := Bool ⊕ SourceArity m

/-- The actual coefficient array represented by one source-factor choice. -/
def sourceFactorValue
    (m : ℕ) (p₀ : ProbabilityMass) (s : ℕ) : SourceFactorChoice m → Seq
  | .inl true => arrivalCoeff m p₀ s
  | .inl false => fun N : ℕ ↦ -(if N = s then arrivalBoundary m p₀ s else 0)
  | .inr r =>
      shiftByInt (1 - (s : ℤ))
        (arrivalFormulaTerm m p₀ s (sourceArityValue r))

/-- The sum of all nonlinear choices is exactly the shifted concrete source. -/
theorem sum_sourceFactor_eq_shift_formulaSource
    (m : ℕ) (p₀ : ProbabilityMass) (s : ℕ) :
    (fun N : ℕ ↦
      ∑ r : SourceArity m, sourceFactorValue m p₀ s (.inr r) N) =
        shiftByInt (1 - (s : ℤ)) (arrivalFormulaSource m p₀ s) := by
  have hterms :
      (fun N : ℕ ↦
        ∑ r : SourceArity m,
          arrivalFormulaTerm m p₀ s (sourceArityValue r) N) =
        arrivalFormulaSource m p₀ s := by
    funext N
    rw [arrivalFormulaSource]
    exact sum_sourceArity_eq_Icc m (fun r ↦ arrivalFormulaTerm m p₀ s r N)
  calc
    (fun N : ℕ ↦
        ∑ r : SourceArity m, sourceFactorValue m p₀ s (.inr r) N) =
        shiftByInt (1 - (s : ℤ))
          (fun N : ℕ ↦
            ∑ r : SourceArity m,
              arrivalFormulaTerm m p₀ s (sourceArityValue r) N) := by
      rw [shiftByInt_fintype_sum]
      rfl
    _ = shiftByInt (1 - (s : ℤ)) (arrivalFormulaSource m p₀ s) := by rw [hterms]

/-- The actual factor alphabet sums coefficientwise to `F_(s+1)`. -/
theorem sum_sourceFactorValue_eq_arrivalCoeff_succ
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m) (hcrit : Critical m p₀)
    (hnotBinaryFixedPoint : ¬(m = 2 ∧ p₀ = diracMass 1)) (s : ℕ) :
    (fun N : ℕ ↦ ∑ x : SourceFactorChoice m, sourceFactorValue m p₀ s x N) =
      arrivalCoeff m p₀ (s + 1) := by
  funext N
  rw [arrivalCoeff_succ_eq_formulaSource m p₀ hm hcrit hnotBinaryFixedPoint]
  rw [Fintype.sum_sum_type, Fintype.sum_bool]
  change arrivalCoeff m p₀ s N - (if N = s then arrivalBoundary m p₀ s else 0) +
      (∑ r : SourceArity m, sourceFactorValue m p₀ s (.inr r) N) = _
  rw [congrFun (sum_sourceFactor_eq_shift_formulaSource m p₀ s) N]

/-- One multiplicity-preserving term in the coefficientwise expansion of a
convolution power of a finite sum. -/
def fintypeConvPowTerm
    {ι : Type*} [Fintype ι] {R : ℕ} (factor : ι → Seq) (choice : Fin R → ι) : Seq :=
  fun N : ℕ ↦
    PowerSeries.coeff ℝ N
      (∏ i : Fin R, PowerSeries.mk (factor (choice i)))

/-- Coefficientwise finite multinomial expansion, including multiplicities.
The index is the full ordered choice function `Fin R → ι`, so no multinomial
coefficient is hidden. -/
theorem convPow_fintype_sum_expansion
    {ι : Type*} [Fintype ι] (R : ℕ) (factor : ι → Seq) :
    convPow R (fun N : ℕ ↦ ∑ x : ι, factor x N) =
      fun N : ℕ ↦ ∑ choice : Fin R → ι, fintypeConvPowTerm factor choice N := by
  have hmk :
      PowerSeries.mk (fun N : ℕ ↦ ∑ x : ι, factor x N) =
        ∑ x : ι, PowerSeries.mk (factor x) := by
    apply PowerSeries.ext
    intro N
    simp
  funext N
  calc
    convPow R (fun k : ℕ ↦ ∑ x : ι, factor x k) N =
        PowerSeries.coeff ℝ N
          (PowerSeries.mk (fun k : ℕ ↦ ∑ x : ι, factor x k) ^ R) := by
      simpa using congrArg (fun p ↦ PowerSeries.coeff ℝ N p)
        (powerSeries_mk_convPow R (fun k : ℕ ↦ ∑ x : ι, factor x k))
    _ = PowerSeries.coeff ℝ N ((∑ x : ι, PowerSeries.mk (factor x)) ^ R) := by
      rw [hmk]
    _ = PowerSeries.coeff ℝ N
        (∑ choice : Fin R → ι, ∏ i : Fin R, PowerSeries.mk (factor (choice i))) := by
      rw [Fintype.sum_pow]
    _ = ∑ choice : Fin R → ι, fintypeConvPowTerm factor choice N := by
      simp [fintypeConvPowTerm]

/-- Number of positions in an ordered expansion choice carrying a fixed
factor. -/
def sourceFactorMultiplicity
    {m R : ℕ} (choice : Fin R → SourceFactorChoice m) (x : SourceFactorChoice m) : ℕ :=
  ∑ i : Fin R, if choice i = x then 1 else 0

theorem sourceFactorMultiplicity_le
    {m R : ℕ} (choice : Fin R → SourceFactorChoice m) (x : SourceFactorChoice m) :
    sourceFactorMultiplicity choice x ≤ R := by
  unfold sourceFactorMultiplicity
  calc
    (∑ i : Fin R, if choice i = x then 1 else 0) ≤ ∑ _i : Fin R, 1 := by
      apply Finset.sum_le_sum
      intro i _hi
      split <;> omega
    _ = R := by simp

/-- Fiber multiplicities over the finite factor alphabet add to the outer
degree. -/
theorem sum_sourceFactorMultiplicity
    {m R : ℕ} (choice : Fin R → SourceFactorChoice m) :
    (∑ x : SourceFactorChoice m, sourceFactorMultiplicity choice x) = R := by
  unfold sourceFactorMultiplicity
  rw [Finset.sum_comm]
  simp

theorem one_le_sourceFactorMultiplicity_of_eq
    {m R : ℕ} (choice : Fin R → SourceFactorChoice m)
    (i : Fin R) (x : SourceFactorChoice m) (hi : choice i = x) :
    1 ≤ sourceFactorMultiplicity choice x := by
  unfold sourceFactorMultiplicity
  have hsingle := Finset.single_le_sum
    (s := Finset.univ)
    (f := fun j : Fin R ↦ if choice j = x then 1 else 0)
    (fun j _hj ↦ Nat.zero_le _) (Finset.mem_univ i)
  simpa [hi] using hsingle

/-- The all-unchanged choice deleted from `(F+G)^R-F^R`. -/
def allUnchangedChoice (m R : ℕ) : Fin R → SourceFactorChoice m :=
  fun _i ↦ .inl true

/-- The concrete count tag attached to an ordered function-expansion choice. -/
def functionExpansionTag
    {m R : ℕ} (hRm : R ≤ m) (choice : Fin R → SourceFactorChoice m) :
    SourceMonomialTag m where
  kind := .functionChange
  outerDegree := ⟨R, Nat.lt_succ_of_le hRm⟩
  nB := ⟨sourceFactorMultiplicity choice (.inl false),
    Nat.lt_succ_of_le ((sourceFactorMultiplicity_le choice (.inl false)).trans hRm)⟩
  nF := ⟨sourceFactorMultiplicity choice (.inl true),
    Nat.lt_succ_of_le ((sourceFactorMultiplicity_le choice (.inl true)).trans hRm)⟩
  nR := fun r ↦ ⟨sourceFactorMultiplicity choice (.inr r),
    Nat.lt_succ_of_le ((sourceFactorMultiplicity_le choice (.inr r)).trans hRm)⟩

/-- Every ordered choice other than all-`F` produces a valid function-change
tag.  Thus validity is proved from the actual finite expansion index, rather
than assumed as an unanalyzed premise. -/
theorem functionExpansionTag_valid
    {m R : ℕ} (hR : 2 ≤ R) (hRm : R ≤ m)
    (choice : Fin R → SourceFactorChoice m)
    (hnontrivial : choice ≠ allUnchangedChoice m R) :
    (functionExpansionTag hRm choice).Valid := by
  have htotal := sum_sourceFactorMultiplicity choice
  rw [Fintype.sum_sum_type, Fintype.sum_bool] at htotal
  change 2 ≤ R ∧
    sourceFactorMultiplicity choice (.inl false) +
        sourceFactorMultiplicity choice (.inl true) +
          (∑ r : SourceArity m, sourceFactorMultiplicity choice (.inr r)) = R ∧
      1 ≤ sourceFactorMultiplicity choice (.inl false) +
        ∑ r : SourceArity m, sourceFactorMultiplicity choice (.inr r)
  refine ⟨hR, ?_, ?_⟩
  · omega
  · by_contra hzero
    have hzero' :
        sourceFactorMultiplicity choice (.inl false) +
          ∑ r : SourceArity m, sourceFactorMultiplicity choice (.inr r) = 0 := by
      omega
    apply hnontrivial
    funext i
    cases hchoice : choice i with
    | inl b =>
        cases b with
        | false =>
            have hone := one_le_sourceFactorMultiplicity_of_eq
              choice i (.inl false) hchoice
            omega
        | true => rfl
    | inr r =>
        have hone := one_le_sourceFactorMultiplicity_of_eq choice i (.inr r) hchoice
        have hle : sourceFactorMultiplicity choice (.inr r) ≤
            ∑ r' : SourceArity m, sourceFactorMultiplicity choice (.inr r') := by
          exact Finset.single_le_sum
            (s := Finset.univ)
            (f := fun r' : SourceArity m ↦ sourceFactorMultiplicity choice (.inr r'))
            (fun r' _hr' ↦ Nat.zero_le _) (Finset.mem_univ r)
        omega

/-- The full ordered expansion of the concrete next-generation convolution
power. -/
theorem arrivalCoeff_succ_convPow_expansion
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m) (hcrit : Critical m p₀)
    (hnotBinaryFixedPoint : ¬(m = 2 ∧ p₀ = diracMass 1)) (s R : ℕ) :
    convPow R (arrivalCoeff m p₀ (s + 1)) =
      fun N : ℕ ↦
        ∑ choice : Fin R → SourceFactorChoice m,
          fintypeConvPowTerm (sourceFactorValue m p₀ s) choice N := by
  rw [← sum_sourceFactorValue_eq_arrivalCoeff_succ
    m p₀ hm hcrit hnotBinaryFixedPoint s]
  exact convPow_fintype_sum_expansion R (sourceFactorValue m p₀ s)

/-- The all-unchanged expansion term is literally `F_s^R`. -/
theorem fintypeConvPowTerm_allUnchanged
    (m : ℕ) (p₀ : ProbabilityMass) (s R : ℕ) :
    fintypeConvPowTerm (sourceFactorValue m p₀ s) (allUnchangedChoice m R) =
      convPow R (arrivalCoeff m p₀ s) := by
  funext N
  change PowerSeries.coeff ℝ N
      (∏ _i : Fin R, PowerSeries.mk (arrivalCoeff m p₀ s)) =
    convPow R (arrivalCoeff m p₀ s) N
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← powerSeries_mk_convPow]
  simp

/-- The finite set of actual function-change summands after deleting the
unique all-`F` choice. -/
def nontrivialFunctionChoices (m R : ℕ) :
    Finset (Fin R → SourceFactorChoice m) :=
  Finset.univ.erase (allUnchangedChoice m R)

/-- Exact coefficientwise function-change expansion.  Multiplicities are
represented by distinct ordered choice functions. -/
theorem arrivalCoeff_functionChange_expansion
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m) (hcrit : Critical m p₀)
    (hnotBinaryFixedPoint : ¬(m = 2 ∧ p₀ = diracMass 1)) (s R N : ℕ) :
    convPow R (arrivalCoeff m p₀ (s + 1)) N -
        convPow R (arrivalCoeff m p₀ s) N =
      ∑ choice ∈ nontrivialFunctionChoices m R,
        fintypeConvPowTerm (sourceFactorValue m p₀ s) choice N := by
  rw [congrFun (arrivalCoeff_succ_convPow_expansion
    m p₀ hm hcrit hnotBinaryFixedPoint s R) N]
  rw [← congrFun (fintypeConvPowTerm_allUnchanged m p₀ s R) N]
  have hsplit := Finset.sum_erase_add
    (s := (Finset.univ : Finset (Fin R → SourceFactorChoice m)))
    (f := fun choice ↦ fintypeConvPowTerm (sourceFactorValue m p₀ s) choice N)
    (Finset.mem_univ (allUnchangedChoice m R))
  change (∑ choice : Fin R → SourceFactorChoice m,
      fintypeConvPowTerm (sourceFactorValue m p₀ s) choice N) -
        fintypeConvPowTerm (sourceFactorValue m p₀ s) (allUnchangedChoice m R) N = _
  rw [← hsplit]
  simp [nontrivialFunctionChoices]

/-- Every summand appearing in the exact function-change expansion carries a
valid source tag. -/
theorem functionChange_summand_has_valid_tag
    {m R : ℕ} (hR : 2 ≤ R) (hRm : R ≤ m)
    {choice : Fin R → SourceFactorChoice m}
    (hchoice : choice ∈ nontrivialFunctionChoices m R) :
    (functionExpansionTag hRm choice).Valid := by
  apply functionExpansionTag_valid hR hRm choice
  intro htrivial
  subst choice
  simp [nontrivialFunctionChoices] at hchoice

/-- The old monomial shift `(R-2)(1-s)`. -/
def sourceOldShift (s R : ℕ) : ℤ :=
  ((R : ℤ) - 2) * (1 - (s : ℤ))

/-- The new monomial shift `(R-2)(1-(s+1))`. -/
def sourceNewShift (s R : ℕ) : ℤ :=
  ((R : ℤ) - 2) * (1 - ((s + 1 : ℕ) : ℤ))

/-- The actual coefficient-change term in `eq:threechanges`. -/
def sourceCoefficientChangeTerm
    (m : ℕ) (p₀ : ProbabilityMass) (s R : ℕ) : Seq :=
  fun N : ℕ ↦
    (arrivalAlpha m p₀ (s + 1) R - arrivalAlpha m p₀ s R) *
      shiftByInt (sourceOldShift s R) (convPow R (arrivalCoeff m p₀ s)) N

/-- The first actual shift-change term, with `e=0`. -/
def sourceShiftNoExcessTerm
    (m : ℕ) (p₀ : ProbabilityMass) (s R : ℕ) : Seq :=
  fun N : ℕ ↦
    arrivalAlpha m p₀ (s + 1) R *
      shiftByInt (sourceNewShift s R) (convPow R (arrivalCoeff m p₀ s)) N

/-- The negative second shift-change term, with `e=R-2`. -/
def sourceShiftWithExcessTerm
    (m : ℕ) (p₀ : ProbabilityMass) (s R : ℕ) : Seq :=
  fun N : ℕ ↦
    -arrivalAlpha m p₀ (s + 1) R *
      shiftByInt (sourceOldShift s R) (convPow R (arrivalCoeff m p₀ s)) N

/-- The actual function-change term before expanding its finite factor choices. -/
def sourceFunctionChangeTerm
    (m : ℕ) (p₀ : ProbabilityMass) (s R : ℕ) : Seq :=
  fun N : ℕ ↦
    arrivalAlpha m p₀ (s + 1) R *
      shiftByInt (sourceNewShift s R)
        (fun k : ℕ ↦
          convPow R (arrivalCoeff m p₀ (s + 1)) k -
            convPow R (arrivalCoeff m p₀ s) k) N

/-- One outer-degree summand of the concrete three-change decomposition. -/
def sourceThreeChangeTerm
    (m : ℕ) (p₀ : ProbabilityMass) (s R : ℕ) : Seq :=
  fun N : ℕ ↦
    sourceCoefficientChangeTerm m p₀ s R N +
      sourceShiftNoExcessTerm m p₀ s R N +
      sourceShiftWithExcessTerm m p₀ s R N +
      sourceFunctionChangeTerm m p₀ s R N

/-- Concrete coefficientwise form of `eq:threechanges`. -/
theorem arrivalFormulaSource_sub_eq_threeChanges
    (m : ℕ) (p₀ : ProbabilityMass) (s N : ℕ) :
    arrivalFormulaSource m p₀ (s + 1) N - arrivalFormulaSource m p₀ s N =
      ∑ R ∈ Finset.Icc 2 m, sourceThreeChangeTerm m p₀ s R N := by
  rw [arrivalFormulaSource, arrivalFormulaSource, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro R _hR
  simp only [sourceThreeChangeTerm, sourceCoefficientChangeTerm,
    sourceShiftNoExcessTerm, sourceShiftWithExcessTerm, sourceFunctionChangeTerm,
    sourceOldShift, sourceNewShift]
  rw [congrFun (shiftByInt_sub
    (((R : ℤ) - 2) * (1 - ((s + 1 : ℕ) : ℤ)))
    (convPow R (arrivalCoeff m p₀ (s + 1)))
    (convPow R (arrivalCoeff m p₀ s))) N]
  ring

/-- At `R=2` the two actual shift terms cancel, as stated in the source. -/
theorem sourceShiftChange_eq_zero_of_degree_two
    (m : ℕ) (p₀ : ProbabilityMass) (s N : ℕ) :
    sourceShiftNoExcessTerm m p₀ s 2 N +
      sourceShiftWithExcessTerm m p₀ s 2 N = 0 := by
  simp [sourceShiftNoExcessTerm, sourceShiftWithExcessTerm,
    sourceNewShift, sourceOldShift]

/-- Tag for an actual coefficient-change summand. -/
def coefficientChangeTag {m R : ℕ} (hRm : R ≤ m) : SourceMonomialTag m where
  kind := .coefficientChange
  outerDegree := ⟨R, Nat.lt_succ_of_le hRm⟩
  nB := ⟨0, by omega⟩
  nF := ⟨0, by omega⟩
  nR := fun _r ↦ ⟨0, by omega⟩

/-- Tag for the actual shift term with `e=0`. -/
def shiftNoExcessTag {m R : ℕ} (hRm : R ≤ m) : SourceMonomialTag m where
  kind := .shiftNoExcess
  outerDegree := ⟨R, Nat.lt_succ_of_le hRm⟩
  nB := ⟨0, by omega⟩
  nF := ⟨0, by omega⟩
  nR := fun _r ↦ ⟨0, by omega⟩

/-- Tag for the actual shift term with `e=R-2`. -/
def shiftWithExcessTag {m R : ℕ} (hRm : R ≤ m) : SourceMonomialTag m where
  kind := .shiftWithExcess
  outerDegree := ⟨R, Nat.lt_succ_of_le hRm⟩
  nB := ⟨0, by omega⟩
  nF := ⟨0, by omega⟩
  nR := fun _r ↦ ⟨0, by omega⟩

theorem coefficientChangeTag_valid
    {m R : ℕ} (hR : 2 ≤ R) (hRm : R ≤ m) :
    (coefficientChangeTag hRm).Valid := by
  simp [coefficientChangeTag, SourceMonomialTag.Valid,
    SourceMonomialTag.canonicalCounts, hR]

theorem shiftNoExcessTag_valid
    {m R : ℕ} (hR : 3 ≤ R) (hRm : R ≤ m) :
    (shiftNoExcessTag hRm).Valid := by
  simp [shiftNoExcessTag, SourceMonomialTag.Valid,
    SourceMonomialTag.canonicalCounts, hR]
  omega

theorem shiftWithExcessTag_valid
    {m R : ℕ} (hR : 3 ≤ R) (hRm : R ≤ m) :
    (shiftWithExcessTag hRm).Valid := by
  simp [shiftWithExcessTag, SourceMonomialTag.Valid,
    SourceMonomialTag.canonicalCounts, hR]
  omega

/-- The coefficient-change tag has exactly the old source shift. -/
theorem coefficientChangeTag_sigma
    {m R : ℕ} (hR : 2 ≤ R) (hRm : R ≤ m) (s : ℕ) :
    (coefficientChangeTag hRm).sigma s = sourceOldShift s R := by
  simp [coefficientChangeTag, SourceMonomialTag.sigma, SourceMonomialTag.e,
    SourceMonomialTag.q, sourceOldShift]
  push_cast [hR]
  ring

/-- The zero-excess shift tag has exactly the new source shift. -/
theorem shiftNoExcessTag_sigma
    {m R : ℕ} (hRm : R ≤ m) (s : ℕ) :
    (shiftNoExcessTag hRm).sigma s = sourceNewShift s R := by
  simp [shiftNoExcessTag, SourceMonomialTag.sigma, SourceMonomialTag.e,
    SourceMonomialTag.q, sourceNewShift]
  ring

/-- The positive-excess shift tag has exactly the old source shift. -/
theorem shiftWithExcessTag_sigma
    {m R : ℕ} (hR : 2 ≤ R) (hRm : R ≤ m) (s : ℕ) :
    (shiftWithExcessTag hRm).sigma s = sourceOldShift s R := by
  simp [shiftWithExcessTag, SourceMonomialTag.sigma, SourceMonomialTag.e,
    SourceMonomialTag.q, sourceOldShift]
  push_cast [hR]
  ring

/-- One actual expanded function-change term after applying the outer shift
and coefficient. -/
def sourceFunctionExpandedTerm
    (m : ℕ) (p₀ : ProbabilityMass) (s R : ℕ)
    (choice : Fin R → SourceFactorChoice m) : Seq :=
  fun N : ℕ ↦
    arrivalAlpha m p₀ (s + 1) R *
      shiftByInt (sourceNewShift s R)
        (fintypeConvPowTerm (sourceFactorValue m p₀ s) choice) N

/-- The actual function-change term is the finite sum of its non-all-`F`
ordered summands. -/
theorem sourceFunctionChangeTerm_eq_expansion
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m) (hcrit : Critical m p₀)
    (hnotBinaryFixedPoint : ¬(m = 2 ∧ p₀ = diracMass 1)) (s R : ℕ) :
    sourceFunctionChangeTerm m p₀ s R =
      fun N : ℕ ↦ ∑ choice ∈ nontrivialFunctionChoices m R,
        sourceFunctionExpandedTerm m p₀ s R choice N := by
  have hexpansion :
      (fun N : ℕ ↦
        convPow R (arrivalCoeff m p₀ (s + 1)) N -
          convPow R (arrivalCoeff m p₀ s) N) =
        fun N : ℕ ↦ ∑ choice ∈ nontrivialFunctionChoices m R,
          fintypeConvPowTerm (sourceFactorValue m p₀ s) choice N := by
    funext N
    exact arrivalCoeff_functionChange_expansion
      m p₀ hm hcrit hnotBinaryFixedPoint s R N
  funext N
  change
    arrivalAlpha m p₀ (s + 1) R *
        shiftByInt (sourceNewShift s R)
          (fun k : ℕ ↦
            convPow R (arrivalCoeff m p₀ (s + 1)) k -
              convPow R (arrivalCoeff m p₀ s) k) N =
      ∑ choice ∈ nontrivialFunctionChoices m R,
        arrivalAlpha m p₀ (s + 1) R *
          shiftByInt (sourceNewShift s R)
            (fintypeConvPowTerm (sourceFactorValue m p₀ s) choice) N
  rw [congrFun (congrArg (shiftByInt (sourceNewShift s R)) hexpansion) N]
  rw [congrFun
    (shiftByInt_finset_sum (sourceNewShift s R)
      (nontrivialFunctionChoices m R)
      (fun choice ↦ fintypeConvPowTerm (sourceFactorValue m p₀ s) choice)) N]
  simp only [Finset.mul_sum]

/-- Fully expanded coefficientwise form of the concrete source difference.
The only nonlinear summands retained are the actual non-all-`F` ordered
choices. -/
theorem arrivalFormulaSource_sub_eq_fullyExpanded
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m) (hcrit : Critical m p₀)
    (hnotBinaryFixedPoint : ¬(m = 2 ∧ p₀ = diracMass 1)) (s N : ℕ) :
    arrivalFormulaSource m p₀ (s + 1) N - arrivalFormulaSource m p₀ s N =
      ∑ R ∈ Finset.Icc 2 m,
        (sourceCoefficientChangeTerm m p₀ s R N +
          sourceShiftNoExcessTerm m p₀ s R N +
          sourceShiftWithExcessTerm m p₀ s R N +
          ∑ choice ∈ nontrivialFunctionChoices m R,
            sourceFunctionExpandedTerm m p₀ s R choice N) := by
  rw [arrivalFormulaSource_sub_eq_threeChanges]
  apply Finset.sum_congr rfl
  intro R _hR
  simp only [sourceThreeChangeTerm]
  rw [congrFun
    (sourceFunctionChangeTerm_eq_expansion
      m p₀ hm hcrit hnotBinaryFixedPoint s R) N]

/-- A single certificate collects the tag coverage of every actual outer
summand: coefficient change, the two nonzero shift terms, and all terms of the
exact function expansion. -/
theorem actual_sourceDifference_terms_have_valid_tags
    {m R : ℕ} (hRmem : R ∈ Finset.Icc 2 m) :
    (coefficientChangeTag (Finset.mem_Icc.mp hRmem).2).Valid ∧
      (R = 2 ∨
        ((shiftNoExcessTag (Finset.mem_Icc.mp hRmem).2).Valid ∧
          (shiftWithExcessTag (Finset.mem_Icc.mp hRmem).2).Valid)) ∧
      ∀ choice ∈ nontrivialFunctionChoices m R,
        (functionExpansionTag (Finset.mem_Icc.mp hRmem).2 choice).Valid := by
  have hR := (Finset.mem_Icc.mp hRmem).1
  have hRm := (Finset.mem_Icc.mp hRmem).2
  refine ⟨coefficientChangeTag_valid hR hRm, ?_, ?_⟩
  · by_cases hReq : R = 2
    · exact Or.inl hReq
    · exact Or.inr ⟨shiftNoExcessTag_valid (by omega) hRm,
        shiftWithExcessTag_valid (by omega) hRm⟩
  · intro choice hchoice
    exact functionChange_summand_has_valid_tag hR hRm hchoice

end

end DerridaRetaux
