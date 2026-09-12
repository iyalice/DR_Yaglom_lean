import Mathlib.Tactic

set_option autoImplicit false

open scoped BigOperators

namespace DerridaRetaux

/-!
# Finite monomial tags for the arrival-source difference

This file formalizes the finite combinatorial layer behind `eq:threechanges`,
`eq:tag`, and the three cases used before `eq:tagbound`.  A raw tag is an
intrinsically finite object.  Its validity predicate is transparent: it is
made only of the factor-count equation, deletion of the all-`F` term, and the
canonical data for coefficient and shift changes.

This module deliberately does not claim that a coefficientwise expansion of
the actual arrival source is exhausted by these tags.  That expansion map,
and the analytic convolution-tail estimate applied to its image, remain
separate obligations.
-/

/-- Indices for source-factor arities `r = 2, ..., m`. -/
abbrev SourceArity (m : ℕ) := Fin (m - 1)

/-- The actual arity represented by a finite source-arity index. -/
def sourceArityValue {m : ℕ} (r : SourceArity m) : ℕ :=
  (r : ℕ) + 2

/-- The four kinds of terms in the three-change decomposition.  The two shift
constructors distinguish the exponents with `e = 0` and `e = R - 2`. -/
inductive SourceChangeKind where
  | functionChange
  | coefficientChange
  | shiftNoExcess
  | shiftWithExcess
  deriving DecidableEq, Fintype

/-- A finite raw monomial tag.  Counts are bounded by `m`; invalid choices are
filtered by `SourceMonomialTag.Valid` below. -/
structure SourceMonomialTag (m : ℕ) where
  kind : SourceChangeKind
  outerDegree : Fin (m + 1)
  nB : Fin (m + 1)
  nF : Fin (m + 1)
  nR : SourceArity m → Fin (m + 1)
  deriving DecidableEq, Fintype

namespace SourceMonomialTag

/-- Number of selected nonlinear source factors. -/
def sourceCount {m : ℕ} (t : SourceMonomialTag m) : ℕ :=
  ∑ r : SourceArity m, (t.nR r : ℕ)

/-- The source excess `e = ∑ (r - 1)n_r` for a function-change monomial. -/
def sourceExcess {m : ℕ} (t : SourceMonomialTag m) : ℕ :=
  ∑ r : SourceArity m, (sourceArityValue r - 1) * (t.nR r : ℕ)

/-- The convolution order contributed by all nonlinear source factors. -/
def sourceOrder {m : ℕ} (t : SourceMonomialTag m) : ℕ :=
  ∑ r : SourceArity m, sourceArityValue r * (t.nR r : ℕ)

/-- Canonical irrelevant counts for a coefficient- or shift-change tag. -/
def canonicalCounts {m : ℕ} (t : SourceMonomialTag m) : Prop :=
  (t.nB : ℕ) = 0 ∧ (t.nF : ℕ) = 0 ∧ ∀ r : SourceArity m, (t.nR r : ℕ) = 0

/-- Transparent legality conditions for the finite tag language.

For a function change, the first equation counts the `R` selected factors and
the second condition says that the deleted all-`F` monomial is absent.  A
nonzero shift change has `R ≥ 3`, because the two shifts coincide at `R = 2`.
-/
def Valid {m : ℕ} (t : SourceMonomialTag m) : Prop :=
  2 ≤ (t.outerDegree : ℕ) ∧
    match t.kind with
    | .functionChange =>
        (t.nB : ℕ) + (t.nF : ℕ) + t.sourceCount = (t.outerDegree : ℕ) ∧
          1 ≤ (t.nB : ℕ) + t.sourceCount
    | .coefficientChange => t.canonicalCounts
    | .shiftNoExcess => 3 ≤ (t.outerDegree : ℕ) ∧ t.canonicalCounts
    | .shiftWithExcess => 3 ≤ (t.outerDegree : ℕ) ∧ t.canonicalCounts

noncomputable instance {m : ℕ} (t : SourceMonomialTag m) : Decidable t.Valid :=
  Classical.propDecidable _

/-- The number `w` of explicit boundary/coefficient-change factors `b_s`. -/
def w {m : ℕ} (t : SourceMonomialTag m) : ℕ :=
  match t.kind with
  | .functionChange => (t.nB : ℕ)
  | .coefficientChange => 1
  | .shiftNoExcess => 0
  | .shiftWithExcess => 0

/-- The exponent correction `e` in `eq:tag`. -/
def e {m : ℕ} (t : SourceMonomialTag m) : ℕ :=
  match t.kind with
  | .functionChange => t.sourceExcess
  | .coefficientChange => (t.outerDegree : ℕ) - 2
  | .shiftNoExcess => 0
  | .shiftWithExcess => (t.outerDegree : ℕ) - 2

/-- The convolution power `q` in `eq:tag`. -/
def q {m : ℕ} (t : SourceMonomialTag m) : ℕ :=
  match t.kind with
  | .functionChange => (t.nF : ℕ) + t.sourceOrder
  | .coefficientChange => (t.outerDegree : ℕ)
  | .shiftNoExcess => (t.outerDegree : ℕ)
  | .shiftWithExcess => (t.outerDegree : ℕ)

/-- The Laurent exponent `σ = e + (2 - q)s`. -/
def sigma {m : ℕ} (t : SourceMonomialTag m) (s : ℕ) : ℤ :=
  (t.e : ℤ) + (2 - (t.q : ℤ)) * (s : ℤ)

/-- The coefficient threshold after removing the monomial shift. -/
def tailThreshold {m : ℕ} (t : SourceMonomialTag m) (N s : ℕ) : ℤ :=
  (N : ℤ) + (s : ℤ) - t.sigma s

/-- The source cutoff `K_m = 2m(m-1)+1`. -/
def sourceDifferenceCutoff (m : ℕ) : ℕ :=
  2 * m * (m - 1) + 1

/-- Valid tags form a finite type, independently of any polynomial-series
representation. -/
abbrev ValidSourceMonomialTag (m : ℕ) := {t : SourceMonomialTag m // t.Valid}

noncomputable instance (m : ℕ) : Fintype (ValidSourceMonomialTag m) := Fintype.ofFinite _

theorem outerDegree_le {m : ℕ} (t : SourceMonomialTag m) :
    (t.outerDegree : ℕ) ≤ m := by
  exact Nat.lt_succ_iff.mp t.outerDegree.isLt

theorem sourceArity_le {m : ℕ} (r : SourceArity m) : sourceArityValue r ≤ m := by
  unfold sourceArityValue
  omega

/-- Splitting every `r` as `(r-1)+1` gives the key order identity. -/
theorem sourceOrder_eq_sourceExcess_add_sourceCount
    {m : ℕ} (t : SourceMonomialTag m) :
    t.sourceOrder = t.sourceExcess + t.sourceCount := by
  unfold sourceOrder sourceExcess sourceCount
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r _hr
  have hr : sourceArityValue r = sourceArityValue r - 1 + 1 := by
    unfold sourceArityValue
    omega
  nth_rewrite 1 [hr]
  rw [Nat.add_mul, one_mul]

/-- Every source factor contributes at least one unit of excess. -/
theorem sourceCount_le_sourceExcess {m : ℕ} (t : SourceMonomialTag m) :
    t.sourceCount ≤ t.sourceExcess := by
  unfold sourceCount sourceExcess
  apply Finset.sum_le_sum
  intro r _hr
  have hr : 1 ≤ sourceArityValue r - 1 := by
    unfold sourceArityValue
    omega
  calc
    (t.nR r : ℕ) = 1 * (t.nR r : ℕ) := by simp
    _ ≤ (sourceArityValue r - 1) * (t.nR r : ℕ) := Nat.mul_le_mul_right _ hr

theorem functionData_of_valid
    {m : ℕ} {t : SourceMonomialTag m} (hvalid : t.Valid)
    (hkind : t.kind = .functionChange) :
    (t.nB : ℕ) + (t.nF : ℕ) + t.sourceCount = (t.outerDegree : ℕ) ∧
      1 ≤ (t.nB : ℕ) + t.sourceCount := by
  simpa [hkind] using hvalid.2

/-- The source formula `q = R - n_B + e` for function-change monomials. -/
theorem q_eq_outerDegree_sub_nB_add_e_of_function
    {m : ℕ} {t : SourceMonomialTag m} (hvalid : t.Valid)
    (hkind : t.kind = .functionChange) :
    t.q = (t.outerDegree : ℕ) - (t.nB : ℕ) + t.e := by
  rcases functionData_of_valid hvalid hkind with ⟨htotal, _hsource⟩
  simp only [q, e, hkind]
  rw [sourceOrder_eq_sourceExcess_add_sourceCount]
  omega

theorem function_sourceExcess_le
    {m : ℕ} {t : SourceMonomialTag m} (hvalid : t.Valid)
    (hkind : t.kind = .functionChange) :
    t.sourceExcess ≤ m * (m - 1) := by
  rcases functionData_of_valid hvalid hkind with ⟨htotal, _hsource⟩
  have hcount : t.sourceCount ≤ (t.outerDegree : ℕ) := by omega
  have hsum : t.sourceExcess ≤ (m - 1) * t.sourceCount := by
    unfold sourceExcess sourceCount
    calc
      (∑ r : SourceArity m, (sourceArityValue r - 1) * (t.nR r : ℕ)) ≤
          ∑ r : SourceArity m, (m - 1) * (t.nR r : ℕ) := by
        apply Finset.sum_le_sum
        intro r _hr
        exact Nat.mul_le_mul_right _ (Nat.sub_le_sub_right (sourceArity_le r) 1)
      _ = (m - 1) * ∑ r : SourceArity m, (t.nR r : ℕ) := by
        rw [Finset.mul_sum]
  calc
    t.sourceExcess ≤ (m - 1) * t.sourceCount := hsum
    _ ≤ (m - 1) * (t.outerDegree : ℕ) := Nat.mul_le_mul_left _ hcount
    _ ≤ (m - 1) * m := Nat.mul_le_mul_left _ (outerDegree_le t)
    _ = m * (m - 1) := Nat.mul_comm _ _

/-- The literal bounds `0 ≤ e ≤ m(m-1)` from `eq:tag`; the lower bound is
intrinsic because `e` is natural-valued. -/
theorem e_le_arity_product {m : ℕ} {t : SourceMonomialTag m} (hvalid : t.Valid) :
    t.e ≤ m * (m - 1) := by
  have hm : 2 ≤ m := hvalid.1.trans (outerDegree_le t)
  have hmProduct : m ≤ m * (m - 1) := by
    simpa only [mul_one] using Nat.mul_le_mul_left m (show 1 ≤ m - 1 by omega)
  cases hkind : t.kind with
  | functionChange =>
      simpa only [e, hkind] using function_sourceExcess_le hvalid hkind
  | coefficientChange =>
      simp only [e, hkind]
      omega
  | shiftNoExcess => simp [e, hkind]
  | shiftWithExcess =>
      simp only [e, hkind]
      omega

/-- The function-change factor count also gives `q+w=R+e`. -/
theorem q_add_w_eq_outerDegree_add_e_of_function
    {m : ℕ} {t : SourceMonomialTag m} (hvalid : t.Valid)
    (hkind : t.kind = .functionChange) :
    t.q + t.w = (t.outerDegree : ℕ) + t.e := by
  rcases functionData_of_valid hvalid hkind with ⟨htotal, _hsource⟩
  have hnB : (t.nB : ℕ) ≤ (t.outerDegree : ℕ) := by omega
  rw [q_eq_outerDegree_sub_nB_add_e_of_function hvalid hkind]
  simp only [w, hkind]
  omega

/-- The literal bound `0 ≤ q ≤ m²` from `eq:tag`. -/
theorem q_le_arity_sq {m : ℕ} {t : SourceMonomialTag m} (hvalid : t.Valid) :
    t.q ≤ m ^ 2 := by
  have hm : 2 ≤ m := hvalid.1.trans (outerDegree_le t)
  have hmSq : m ≤ m ^ 2 := by
    simpa only [pow_two, mul_one] using Nat.mul_le_mul_left m (show 1 ≤ m by omega)
  cases hkind : t.kind with
  | functionChange =>
      have hq := q_eq_outerDegree_sub_nB_add_e_of_function hvalid hkind
      have he := e_le_arity_product hvalid
      have hqBound : t.q ≤ (t.outerDegree : ℕ) + t.e := by omega
      calc
        t.q ≤ (t.outerDegree : ℕ) + t.e := hqBound
        _ ≤ m + m * (m - 1) := Nat.add_le_add (outerDegree_le t) he
        _ = m ^ 2 := by
          have hmDecomp : 1 + (m - 1) = m := by omega
          calc
            m + m * (m - 1) = m * 1 + m * (m - 1) := by simp
            _ = m * (1 + (m - 1)) := (Nat.mul_add m 1 (m - 1)).symm
            _ = m * m := by rw [hmDecomp]
            _ = m ^ 2 := by simp [pow_two]
  | coefficientChange =>
      simpa only [q, hkind] using (outerDegree_le t).trans hmSq
  | shiftNoExcess =>
      simpa only [q, hkind] using (outerDegree_le t).trans hmSq
  | shiftWithExcess =>
      simpa only [q, hkind] using (outerDegree_le t).trans hmSq

/-- If `q=0`, validity forces the unique all-boundary pattern.  In particular,
the monomial has exponent exactly `2s`. -/
theorem q_eq_zero_only_allBoundary
    {m s : ℕ} {t : SourceMonomialTag m} (hvalid : t.Valid) (hq : t.q = 0) :
    t.kind = .functionChange ∧
      (t.nB : ℕ) = (t.outerDegree : ℕ) ∧
      (t.nF : ℕ) = 0 ∧
      (∀ r : SourceArity m, (t.nR r : ℕ) = 0) ∧
      t.w = (t.outerDegree : ℕ) ∧ t.e = 0 ∧ t.sigma s = 2 * (s : ℤ) := by
  have hR : 2 ≤ (t.outerDegree : ℕ) := hvalid.1
  cases hkind : t.kind with
  | coefficientChange =>
      have : (t.outerDegree : ℕ) = 0 := by simpa [q, hkind] using hq
      exfalso
      omega
  | shiftNoExcess =>
      have : (t.outerDegree : ℕ) = 0 := by simpa [q, hkind] using hq
      exfalso
      omega
  | shiftWithExcess =>
      have : (t.outerDegree : ℕ) = 0 := by simpa [q, hkind] using hq
      exfalso
      omega
  | functionChange =>
      have hdata := functionData_of_valid hvalid hkind
      have hqDef : (t.nF : ℕ) + t.sourceOrder = 0 := by
        simpa only [q, hkind] using hq
      have hnF : (t.nF : ℕ) = 0 := by omega
      have horder : t.sourceOrder = 0 := by omega
      have hnR : ∀ r : SourceArity m, (t.nR r : ℕ) = 0 := by
        intro r
        have hterm : sourceArityValue r * (t.nR r : ℕ) ≤ t.sourceOrder := by
          unfold sourceOrder
          exact Finset.single_le_sum
            (s := Finset.univ)
            (f := fun i : SourceArity m ↦ sourceArityValue i * (t.nR i : ℕ))
            (fun i _hi ↦ Nat.zero_le _) (Finset.mem_univ r)
        have hproduct : sourceArityValue r * (t.nR r : ℕ) = 0 := by omega
        rcases Nat.mul_eq_zero.mp hproduct with hr | hnR
        · exfalso
          have : 2 ≤ sourceArityValue r := by
            unfold sourceArityValue
            omega
          omega
        · exact hnR
      have hcount : t.sourceCount = 0 := by simp [sourceCount, hnR]
      have hexcess : t.sourceExcess = 0 := by simp [sourceExcess, hnR]
      have hnB : (t.nB : ℕ) = (t.outerDegree : ℕ) := by omega
      refine ⟨rfl, hnB, hnF, hnR, ?_, ?_, ?_⟩
      · simp [w, hkind, hnB]
      · simp [e, hkind, hexcess]
      · simp [sigma, hq, e, hkind, hexcess]

/-- The all-boundary degree `2s` lies below `N+s` whenever `s<N`. -/
theorem q_eq_zero_degree_below_tail
    {m N s : ℕ} {t : SourceMonomialTag m} (hvalid : t.Valid)
    (hq : t.q = 0) (hsN : s < N) :
    t.sigma s < (N : ℤ) + (s : ℤ) := by
  have hsigma := (q_eq_zero_only_allBoundary (s := s) hvalid hq).2.2.2.2.2.2
  rw [hsigma]
  exact_mod_cast (show 2 * s < N + s by omega)

/-- A valid tag with no `b_s` factor necessarily has convolution order at
least three: either it is a function change containing a source factor, or it
is a nonzero shift change. -/
theorem q_ge_three_of_w_eq_zero
    {m : ℕ} {t : SourceMonomialTag m} (hvalid : t.Valid) (hw : t.w = 0) :
    3 ≤ t.q := by
  cases hkind : t.kind with
  | functionChange =>
      rcases functionData_of_valid hvalid hkind with ⟨_htotal, hsource⟩
      have hnB : (t.nB : ℕ) = 0 := by simpa [w, hkind] using hw
      have hcount : 1 ≤ t.sourceCount := by omega
      have hexcess : 1 ≤ t.e := by
        simp only [e, hkind]
        exact hcount.trans (sourceCount_le_sourceExcess t)
      have hq := q_eq_outerDegree_sub_nB_add_e_of_function hvalid hkind
      rw [hnB, Nat.sub_zero] at hq
      have hR := hvalid.1
      omega
  | coefficientChange => simp [w, hkind] at hw
  | shiftNoExcess =>
      have hshiftData : 3 ≤ (t.outerDegree : ℕ) ∧ t.canonicalCounts := by
        simpa [hkind] using hvalid.2
      have hshift := hshiftData.1
      simpa [q, hkind] using hshift
  | shiftWithExcess =>
      have hshiftData : 3 ≤ (t.outerDegree : ℕ) ∧ t.canonicalCounts := by
        simpa [hkind] using hvalid.2
      have hshift := hshiftData.1
      simpa [q, hkind] using hshift

/-- In the positive-`w` branch, the exact combinatorics give `q+w≥2`. -/
theorem q_add_w_ge_two_of_w_pos
    {m : ℕ} {t : SourceMonomialTag m} (hvalid : t.Valid) (hw : 1 ≤ t.w) :
    2 ≤ t.q + t.w := by
  cases hkind : t.kind with
  | functionChange =>
      rw [q_add_w_eq_outerDegree_add_e_of_function hvalid hkind]
      have hR := hvalid.1
      omega
  | coefficientChange =>
      simp only [q, w, hkind]
      have hR := hvalid.1
      omega
  | shiftNoExcess => simp [w, hkind] at hw
  | shiftWithExcess => simp [w, hkind] at hw

/-- The three source cases are exhaustive and disjoint in the order used by
the manuscript: first `q=0`, then the two `q≥1` branches split by `w`. -/
theorem valid_branch_trichotomy
    {m : ℕ} {t : SourceMonomialTag m} (hvalid : t.Valid) :
    t.q = 0 ∨
      (1 ≤ t.q ∧ t.w = 0 ∧ 3 ≤ t.q) ∨
      (1 ≤ t.q ∧ 1 ≤ t.w ∧ 2 ≤ t.q + t.w) := by
  by_cases hq : t.q = 0
  · exact Or.inl hq
  have hqPos : 1 ≤ t.q := Nat.one_le_iff_ne_zero.mpr hq
  by_cases hw : t.w = 0
  · exact Or.inr (Or.inl ⟨hqPos, hw, q_ge_three_of_w_eq_zero hvalid hw⟩)
  · exact Or.inr (Or.inr
      ⟨hqPos, Nat.one_le_iff_ne_zero.mpr hw,
        q_add_w_ge_two_of_w_pos hvalid (Nat.one_le_iff_ne_zero.mpr hw)⟩)

/-- Algebraic form of `N+s-σ=N+(q-1)s-e`. -/
theorem tailThreshold_eq
    {m : ℕ} (t : SourceMonomialTag m) (N s : ℕ) :
    t.tailThreshold N s =
      (N : ℤ) + ((t.q : ℤ) - 1) * (s : ℤ) - (t.e : ℤ) := by
  simp only [tailThreshold, sigma]
  ring

/-- Under the source cutoff and `q≥1`, the shifted threshold is strictly
larger than `N/2`, encoded without integer division as `N < 2*threshold`. -/
theorem tailThreshold_twice_gt
    {m N s : ℕ} {t : SourceMonomialTag m} (hvalid : t.Valid)
    (hq : 1 ≤ t.q) (hN : s + sourceDifferenceCutoff m < N) :
    (N : ℤ) < 2 * t.tailThreshold N s := by
  have he := e_le_arity_product hvalid
  have htwiceE : 2 * t.e < N := by
    have htwiceELe : 2 * t.e ≤ 2 * (m * (m - 1)) := Nat.mul_le_mul_left 2 he
    simp only [sourceDifferenceCutoff, Nat.mul_assoc] at hN
    omega
  have htwiceEInt : 2 * (t.e : ℤ) < (N : ℤ) := by exact_mod_cast htwiceE
  have hqInt : (1 : ℤ) ≤ (t.q : ℤ) := by exact_mod_cast hq
  have hnonneg : 0 ≤ ((t.q : ℤ) - 1) * (s : ℤ) :=
    mul_nonneg (sub_nonneg.mpr hqInt) (Int.ofNat_nonneg s)
  rw [tailThreshold_eq]
  linarith

/-- In the `w=0` branch, the source power `(s+1)^(3-q)` has nonpositive
integer exponent. -/
theorem sourceExponent_nonpos_of_w_eq_zero
    {m : ℕ} {t : SourceMonomialTag m} (hvalid : t.Valid) (hw : t.w = 0) :
    (3 : ℤ) - (t.q : ℤ) ≤ 0 := by
  have hq := q_ge_three_of_w_eq_zero hvalid hw
  have hqInt : (3 : ℤ) ≤ (t.q : ℤ) := by exact_mod_cast hq
  omega

/-- In the `w≥1` branch, the residual exponent in the source estimate obeys
`4-q-w≤2`, exactly the exponent inequality used after `eq:tagbound`. -/
theorem residualExponent_le_two_of_w_pos
    {m : ℕ} {t : SourceMonomialTag m} (hvalid : t.Valid) (hw : 1 ≤ t.w) :
    (4 : ℤ) - (t.q : ℤ) - (t.w : ℤ) ≤ 2 := by
  have hqw := q_add_w_ge_two_of_w_pos hvalid hw
  have hqwInt : (2 : ℤ) ≤ (t.q : ℤ) + (t.w : ℤ) := by exact_mod_cast hqw
  omega

end SourceMonomialTag

end DerridaRetaux
