import DerridaRetaux.Main.Smoothing

set_option autoImplicit false

namespace DerridaRetaux

/-- Rescale the logarithmic smoothing rate on a compact time interval.
This retains the logarithmic modulus of `eqn:diff grid points`, rather than
relaxing it to the square-root modulus used in the compactness proof. -/
theorem scaled_smoothing_rate_le_log
    (C eta T N L h : ℝ) (hC : 0 ≤ C) (heta : 0 < eta) (_hT : 0 < T)
    (hN : 0 < N) (hL : 0 < L) (hh : 0 < h)
    (hlo : eta * N ≤ L) (hhi : L ≤ T * N) (hhN : h ≤ N) :
    N ^ 2 * (C * h / L ^ 3 * (1 + Real.log (L / h))) ≤
      (C * (1 + |Real.log T|) / eta ^ 3) *
        (h / N * (1 + Real.log (N / h))) := by
  have hlog₀ : 0 ≤ Real.log (N / h) :=
    Real.log_nonneg ((one_le_div hh).mpr hhN)
  have hlogT : Real.log (L / N) ≤ Real.log T :=
    Real.log_le_log (div_pos hL hN) ((div_le_iff₀ hN).mpr hhi)
  have hlogsplit : Real.log (L / h) = Real.log (L / N) + Real.log (N / h) := by
    rw [Real.log_div hL.ne' hh.ne', Real.log_div hL.ne' hN.ne',
      Real.log_div hN.ne' hh.ne']
    ring
  have hlog : 1 + Real.log (L / h) ≤
      (1 + |Real.log T|) * (1 + Real.log (N / h)) := by
    rw [hlogsplit]
    nlinarith [le_abs_self (Real.log T), abs_nonneg (Real.log T)]
  have hratio : N / L ≤ 1 / eta := by
    apply (div_le_div_iff₀ hL heta).mpr
    nlinarith
  have hpow : (N / L) ^ 3 ≤ (1 / eta) ^ 3 :=
    pow_le_pow_left₀ (div_nonneg hN.le hL.le) hratio 3
  calc
    _ = C * (N / L) ^ 3 * (h / N) * (1 + Real.log (L / h)) := by
      field_simp [hN.ne', hL.ne']
      <;> ring
    _ ≤ C * (N / L) ^ 3 * (h / N) *
        ((1 + |Real.log T|) * (1 + Real.log (N / h))) :=
      mul_le_mul_of_nonneg_left hlog (by positivity)
    _ ≤ C * (1 / eta) ^ 3 * (h / N) *
        ((1 + |Real.log T|) * (1 + Real.log (N / h))) := by
      gcongr
    _ = _ := by ring

/-- The logarithmic modulus at one mesh step is exactly `(1 + log N) / N`. -/
theorem log_modulus_inverse (N : ℝ) (_hN : 0 < N) :
    (1 / N) * (1 + Real.log (N / 1)) = (1 + Real.log N) / N := by
  simp only [div_one]
  ring

end DerridaRetaux
