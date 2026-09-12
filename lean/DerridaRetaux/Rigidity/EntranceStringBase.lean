import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.ENNReal

set_option autoImplicit false

open Filter MeasureTheory Set Topology

namespace DerridaRetaux

/-!
# Measure-valued strings of entrance type

This file freezes the transparent measure, endpoint, entrance-normalized Volterra,
and singular-characteristic layer used in `DR_Yaglom.tex`, lines 920--946.  In
particular, a string is not assumed to be locally finite on all of `ℝ`: its mass may
diverge as a finite right endpoint is approached from below.
-/

/-- A Stieltjes string represented by its measure and finite right endpoint. -/
structure EntranceString where
  mass : Measure ℝ
  endpoint : ℝ

/-- The cumulative string, kept in `ENNReal` so infinite endpoint mass is representable. -/
def stringCumulative (M : EntranceString) (x : ℝ) : ENNReal :=
  M.mass (Iic x)

/-- First entrance-moment integrability at a point strictly below the endpoint. -/
def HasFirstEntranceMomentAt (M : EntranceString) (b : ℝ) : Prop :=
  IntegrableOn (fun x : ℝ ↦ |x|) (Iic b) M.mass

/-- Second entrance-moment integrability at a point strictly below the endpoint. -/
def HasSecondEntranceMomentAt (M : EntranceString) (b : ℝ) : Prop :=
  IntegrableOn (fun x : ℝ ↦ x ^ 2) (Iic b) M.mass

/--
The transparent entrance-type hypotheses used by the proposed Kotani specialization.

They assert nonzero mass, local finiteness strictly below the endpoint, no mass above
the endpoint, and a nonempty portion of the support on which the first entrance
moment is finite.  No uniqueness or profile conclusion is stored here.
-/
def IsEntranceType (M : EntranceString) : Prop :=
  M.mass ≠ 0 ∧
    (∀ b : ℝ, b < M.endpoint → M.mass (Iic b) < ⊤) ∧
    M.mass (Ioi M.endpoint) = 0 ∧
    ∃ a : ℝ, a < M.endpoint ∧
      0 < M.mass (Iic a) ∧ HasFirstEntranceMomentAt M a

/-- The stronger second-moment condition used by the singular characteristic. -/
def HasSecondEntranceMoment (M : EntranceString) : Prop :=
  ∀ b : ℝ, b < M.endpoint → HasSecondEntranceMomentAt M b

/--
The cumulative mass diverges when the finite right endpoint is approached from below.

This is the transparent `M(0-) = ∞` regime which removes Kotani's right-boundary
nonuniqueness alternative after the endpoint is specialized to zero.
-/
def NoRightBoundaryAmbiguity (M : EntranceString) : Prop :=
  Tendsto (stringCumulative M) (nhdsWithin M.endpoint (Iio M.endpoint)) (𝓝 ⊤)

/-- A specified finite right endpoint together with divergence from its left. -/
def HasRightEnd (M : EntranceString) (l : ℝ) : Prop :=
  M.endpoint = l ∧ NoRightBoundaryAmbiguity M

/--
An entrance-normalized solution of the Volterra equation for a string.

This is the author-approved transparent reading of the canonical solution used in
`DR_Yaglom.tex`, lines 942--946.  For `lambda = -q < 0`, the final equation reads
`phi xi = 1 + q * integral`.  Positivity, monotonicity, uniqueness, and Wronskian
normalization are deliberately theorem obligations rather than fields here.
-/
def IsEntranceNormalizedVolterraSolution
    (M : EntranceString) (lambda : ℝ) (phi : ℝ → ℝ) : Prop :=
  ContinuousOn phi (Iio M.endpoint) ∧
    Tendsto phi atBot (𝓝 1) ∧
    ∀ xi : ℝ, xi < M.endpoint →
      IntegrableOn (fun v : ℝ ↦ (xi - v) * phi v) (Iic xi) M.mass ∧
        phi xi = 1 - lambda * ∫ v in Iic xi, (xi - v) * phi v ∂M.mass

/--
`h` is the singular characteristic produced by the canonical formula in source
equation `eq:characteristic` (`DR_Yaglom.tex`, lines 942--945).

The characteristic is relational: no total selector is introduced before existence
and uniqueness of the normalized Volterra solution are proved internally.
-/
def HasSingularCharacteristic (M : EntranceString) (lambda h : ℝ) : Prop :=
  ∃ phi : ℝ → ℝ,
    IsEntranceNormalizedVolterraSolution M lambda phi ∧
      Tendsto
        (fun xi : ℝ ↦
          xi + phi xi * ∫ v in xi..M.endpoint, ((phi v) ^ 2)⁻¹)
        atBot (𝓝 h)

/-- Translation convention `(M.translate c)(x) = M(x + c)`. -/
noncomputable def EntranceString.translate (M : EntranceString) (c : ℝ) : EntranceString where
  mass := Measure.map (fun x : ℝ ↦ x - c) M.mass
  endpoint := M.endpoint - c

@[simp] theorem stringCumulative_apply (M : EntranceString) (x : ℝ) :
    stringCumulative M x = M.mass (Iic x) :=
  rfl

@[simp] theorem EntranceString.translate_endpoint (M : EntranceString) (c : ℝ) :
    (M.translate c).endpoint = M.endpoint - c :=
  rfl

theorem hasRightEnd_endpoint {M : EntranceString} {l : ℝ} (h : HasRightEnd M l) :
    M.endpoint = l :=
  h.1

theorem hasRightEnd_noRightBoundaryAmbiguity {M : EntranceString} {l : ℝ}
    (h : HasRightEnd M l) : NoRightBoundaryAmbiguity M :=
  h.2

theorem isEntranceType_locallyFiniteBelow {M : EntranceString}
    (h : IsEntranceType M) {b : ℝ} (hb : b < M.endpoint) :
    M.mass (Iic b) < ⊤ :=
  h.2.1 b hb

theorem isEntranceType_noMassAbove {M : EntranceString} (h : IsEntranceType M) :
    M.mass (Ioi M.endpoint) = 0 :=
  h.2.2.1

end DerridaRetaux
