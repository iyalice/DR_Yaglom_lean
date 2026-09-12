import Mathlib.Tactic

set_option autoImplicit false

open Filter Set Topology

namespace DerridaRetaux

/-- Continuity on every compact subinterval of `(0,∞)` gives continuity on
the whole positive half-line. -/
theorem continuousOn_Ioi_of_continuousOn_compactIntervals
    (f : ℝ → ℝ)
    (hcompact : ∀ eta T : ℝ, 0 < eta → eta ≤ T →
      ContinuousOn f (Icc eta T)) :
    ContinuousOn f (Ioi (0 : ℝ)) := by
  intro t ht
  have ht0 : 0 < t := ht
  let eta : ℝ := t / 2
  let T : ℝ := t + 1
  have heta : 0 < eta := half_pos ht0
  have hetat : eta < t := by dsimp only [eta]; linarith [ht0]
  have htT : t < T := by dsimp only [T]; linarith
  have htbox : t ∈ Icc eta T := ⟨hetat.le, htT.le⟩
  have heq : Ioi (0 : ℝ) =ᶠ[𝓝 t] Icc eta T := by
    filter_upwards [Ioi_mem_nhds ht,
      Ioi_mem_nhds hetat, Iio_mem_nhds htT] with x hx0 hxeta hxT
    apply propext
    constructor
    · intro _
      exact ⟨hxeta.le, hxT.le⟩
    · intro hx
      exact hx0
  rw [continuousWithinAt_congr_set heq]
  exact (hcompact eta T heta (hetat.le.trans htT.le)).continuousWithinAt htbox

end DerridaRetaux
