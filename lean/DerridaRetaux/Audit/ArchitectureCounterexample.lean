import DerridaRetaux.Basic.ProbabilityMass

set_option autoImplicit false

namespace DerridaRetaux.Audit

/-!
# Machine-checked package discrepancy

`LEAN_ARCHITECTURE.md`, lines 78--79, omits the arity hypothesis from its suggested
deterministic-critical-law helper.  This file records the exact counterexample.  It
does not contradict the manuscript theorem, whose public data always includes
`2 ≤ m`; `critical_isDirac_eq_binary` is the corrected internal lemma.
-/

theorem deterministicCriticalClassification_without_arity_is_false :
    ¬ (∀ (m : ℕ) (p : ProbabilityMass),
      Critical m p → IsDirac p → m = 2 ∧ p = diracMass 1) := by
  intro h
  have hbad := h 0 (diracMass 1) critical_zero_diracMass_one (isDirac_diracMass 1)
  omega

end DerridaRetaux.Audit
