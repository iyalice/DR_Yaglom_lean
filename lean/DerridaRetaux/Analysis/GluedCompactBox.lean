import DerridaRetaux.Analysis.GluedExhaustionLimit

set_option autoImplicit false

open Filter Set Topology

namespace DerridaRetaux

noncomputable section

/-- The glued two-variable exhaustion limit is continuous on every compact
box contained in the positive-time, nonnegative-space half-strip. -/
theorem continuousOn_gluedExhaustionLimit_compactBox
    (a : ℕ → ℕ → ℕ → ℝ) (phi : ℕ → ℕ)
    (g : ∀ k, BoundedContinuousFunction (gridExhaustionRectangle k) ℝ)
    (hlim : ∀ k, TendstoUniformly
      (fun n (p : gridExhaustionRectangle k) ↦
        gridBilinearInterp (phi n) (a (phi n))
          (p : ℝ × ℝ).1 (p : ℝ × ℝ).2)
      (fun p ↦ g k p) atTop)
    (eta T R : ℝ) (heta : 0 < eta) (hetaT : eta ≤ T) (hR : 0 ≤ R) :
    ContinuousOn (fun p : ℝ × ℝ ↦ gluedExhaustionLimit g p.1 p.2)
      (Icc eta T ×ˢ Icc (0 : ℝ) R) := by
  let B : ℝ := max T R
  have hB : 0 ≤ B := hR.trans (le_max_right T R)
  obtain ⟨k, hk⟩ := exists_mem_gridExhaustionRectangle heta hB
  obtain ⟨kt, hkt⟩ := exists_nat_ge T
  let K : ℕ := max k kt
  have hkK : k ≤ K := le_max_left k kt
  have hpointK : (eta, B) ∈ gridExhaustionRectangle K :=
    gridExhaustionRectangle_mono hkK hk
  have hcompat : ∀ {r l : ℕ}, ∀ hrl : r ≤ l,
      ∀ p : gridExhaustionRectangle r,
        g r p = g l ⟨(p : ℝ × ℝ),
          gridExhaustionRectangle_mono hrl p.property⟩ := by
    intro r l hrl p
    exact exhaustionLimits_compatible
      (fun N q ↦ gridBilinearInterp N (a N) q.1 q.2)
      phi g hlim hrl p
  apply (continuousOn_gluedExhaustionLimit_rectangle g hcompat K).mono
  intro p hp
  have hTUpper : T ≤ ((K + 1 : ℕ) : ℝ) := by
    have hktK : kt ≤ K := le_max_right k kt
    have : (kt : ℝ) ≤ ((K + 1 : ℕ) : ℝ) := by exact_mod_cast hktK.trans (Nat.le_succ K)
    exact hkt.trans this
  exact ⟨⟨hpointK.1.1.trans hp.1.1, hp.1.2.trans hTUpper⟩,
    hp.2.1, hp.2.2.trans ((le_max_right T R).trans hpointK.2.2)⟩

end

end DerridaRetaux
