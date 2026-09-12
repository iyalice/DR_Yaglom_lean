import DerridaRetaux.Spine.Coupling
import DerridaRetaux.Spine.ThirdTail

/-!
# Third-moment consequences of the concrete cubic-spine coupling

The earlier tail module was deliberately parameterized by an upstream spine
tail inequality.  The recursively constructed path law now supplies that
premise, so this file closes the core implication without importing any
published input as an axiom.
-/

set_option autoImplicit false

open Filter Topology

namespace DerridaRetaux

noncomputable section

/-- The tail computed from the `PMF` marginal in the concrete coupling is the
same real tail as the `ProbabilityMass` formulation used by `ThirdTail`. -/
theorem spineSharpTail_eq_spineMarginalTail
    (m : ℕ) (data : ProfileInitialData m) (n : ℕ) (R : ℝ) :
    spineSharpTail m data n R = spineMarginalTail m data n R := by
  unfold spineSharpTail spineMarginalTail probabilityMassTail
  apply tsum_congr
  intro k
  rw [spineMarginalPMF_apply_toReal]
  rfl

/-- `eq:thirdtail` with the actual recursively constructed spine coupling.
The published product bound remains an explicit theorem parameter. -/
theorem profileThirdTail_quadratic_of_concreteSpine
    (m : ℕ) (data : ProfileInitialData m)
    (hnonconstant : ¬ IsDirac data.law)
    (hProduct : CDHLSProductFact m data.law data.arity data.critical hnonconstant) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (R : ℝ), 2 ≤ R →
      normalizedTiltThirdTail m (orbit m data.law n) R ≤
        C * ((n + 1 : ℕ) : ℝ) ^ 2 *
          (spineMarginalTail m data 0 (R / 2) + (n : ℝ) / R) := by
  apply profileThirdTail_quadratic_of_spineTail
    m data hnonconstant hProduct
  intro n R hR
  rw [← spineSharpTail_eq_spineMarginalTail,
    ← spineSharpTail_eq_spineMarginalTail]
  exact spineSharpTail_le_initial_add m data n R hR

/-- The two-stage uniform-integrability conclusion `eq:UI`, now discharged
by the concrete coupling.  The lower time-window cutoff is explicit even
though the proved estimate is uniform on the larger window starting at zero. -/
theorem profileThirdTail_uniform_integrability_of_concreteSpine
    (m : ℕ) (data : ProfileInitialData m)
    (hnonconstant : ¬ IsDirac data.law)
    (hProduct : CDHLSProductFact m data.law data.arity data.critical hnonconstant) :
    ∀ (eta T : ℝ), 0 < eta → eta < T →
      ∀ epsilon : ℝ, 0 < epsilon →
        ∀ᶠ A : ℝ in atTop, ∀ᶠ N : ℕ in atTop, ∀ n : ℕ,
          eta * (N : ℝ) ≤ (n : ℝ) →
          (n : ℝ) ≤ T * (N : ℝ) →
          normalizedTiltThirdTail m (orbit m data.law n) (A * (N : ℝ)) /
              (N : ℝ) ^ 2 ≤ epsilon := by
  intro eta T heta hetaT epsilon hepsilon
  have hT : 0 < T := heta.trans hetaT
  have hUI := profileThirdTail_uniform_integrability_of_spineTail
    m data hnonconstant hProduct
      (fun n R hR ↦ by
        rw [← spineSharpTail_eq_spineMarginalTail,
          ← spineSharpTail_eq_spineMarginalTail]
        exact spineSharpTail_le_initial_add m data n R hR)
      T hT epsilon hepsilon
  filter_upwards [hUI] with A hA
  filter_upwards [hA] with N hN
  intro n _hnLower hnUpper
  exact hN n hnUpper

end

end DerridaRetaux
