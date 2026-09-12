import DerridaRetaux.Analysis.QuadraticConvolutionLimit

set_option autoImplicit false

open Set

namespace DerridaRetaux

/-- Two half-error bounds combine into the desired convolution error. -/
theorem convolution_triangle_lt
    (A : ℝ) (u : ℝ → ℝ → ℝ) (st x y ε : ℝ)
    (hdiscrete : |A - positiveSelfConvolution (u st) x| < ε / 2)
    (hcontinuous : dist (positiveSelfConvolution (u st) x)
      (positiveSelfConvolution (u st) y) < ε / 2) :
    |A - positiveSelfConvolution (u st) y| < ε := by
  rw [← Real.dist_eq]
  calc
    dist A (positiveSelfConvolution (u st) y) ≤
        dist A (positiveSelfConvolution (u st) x) +
          dist (positiveSelfConvolution (u st) x)
            (positiveSelfConvolution (u st) y) := dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := by
      apply add_lt_add
      · simpa only [Real.dist_eq] using hdiscrete
      · exact hcontinuous
    _ = ε := by ring

end DerridaRetaux
