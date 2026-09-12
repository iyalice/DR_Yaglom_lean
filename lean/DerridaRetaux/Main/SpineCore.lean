import DerridaRetaux.Spine.ConcreteTail

/-!
# Source-facing cubic-spine lemma, axiom-free core

The concrete time-inhomogeneous kernels and finite path laws witness the
Markov-chain construction in `lem:spine`.  All support boundary cases are
handled by the total kernel itself.
-/

set_option autoImplicit false

namespace DerridaRetaux.FixedArity

noncomputable section

/-- Lemma `lem:spine`: concrete one-step marginals, recursively coupled finite
paths, the exact `eq:incformula`, the bound `eq:increment`, and the actual
tail inequality `eq:sharptail`. -/
theorem cubicWeightedChain
    (m : ℕ) (data : ProfileInitialData m) :
    (∀ n : ℕ,
      (spineMarginalPMF m data n).bind (spineKernel m data n) =
        spineMarginalPMF m data (n + 1)) ∧
    (∀ n : ℕ,
      (spinePathPMF m data n).map finPathInitial =
        spineMarginalPMF m data 0) ∧
    (∀ n : ℕ,
      (spinePathPMF m data n).map finPathTerminal =
        spineMarginalPMF m data n) ∧
    (∀ n : ℕ,
      spineExpectedPositiveIncrement m data n =
          spineIncrementRatio m (zeroTilt m (orbit m data.law n))
            (normalizedFactorialTwo m (orbit m data.law n))
            (normalizedFactorialThree m (orbit m data.law n)) ∧
        spineExpectedPositiveIncrement m data n ≤ 4) ∧
    ∀ (n : ℕ) (R : ℝ), 0 < R →
      spineMarginalTail m data n R ≤
        spineMarginalTail m data 0 (R / 2) + 8 * (n : ℝ) / R := by
  refine ⟨spineMarginalPMF_bind_spineKernel_all m data,
    spinePathPMF_initial_marginal m data,
    spinePathPMF_terminal_marginal m data, ?_, ?_⟩
  · intro n
    constructor
    · exact cubicSpineExpectedPositiveIncrement_eq_ratio
        m (orbit m data.law n) data.arity
        (orbit_critical m data.law (le_trans (by norm_num) data.arity)
          data.critical n)
        (orbit_tiltSummable_three m data.law
          (le_trans (by norm_num) data.arity) data.critical data.third n)
        (normalizedCubicMoment_profile_orbit_pos m data n)
    · exact spineExpectedPositiveIncrement_le_four m data n
  · intro n R hR
    rw [← spineSharpTail_eq_spineMarginalTail,
      ← spineSharpTail_eq_spineMarginalTail]
    exact spineSharpTail_le_initial_add m data n R hR

end

end DerridaRetaux.FixedArity
