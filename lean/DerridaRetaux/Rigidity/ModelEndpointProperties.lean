import DerridaRetaux.Rigidity.ModelString
import Mathlib.Analysis.Calculus.Deriv.MeanValue

set_option autoImplicit false

open Set

namespace DerridaRetaux

noncomputable section

/-!
# Qualitative properties of the explicit endpoint solution

These are the positivity and monotonicity clauses used by the model-string
Wronskian argument after source equation `eq:modelstring`.
-/

/-- The explicit decreasing solution is positive on the open negative half-line. -/
theorem modelStringEndpointSolution_pos
    (d p : ℝ) {x : ℝ} (hx : x < 0) :
    0 < modelStringEndpointSolution d p x := by
  exact mul_pos (neg_pos.mpr hx) (Real.exp_pos _)

/-- For positive model scale and Laplace parameter, the displayed derivative is
strictly negative on the open negative half-line. -/
theorem modelStringEndpointSolutionDeriv_neg
    {d p x : ℝ} (hd : 0 < d) (hp : 0 < p) (hx : x < 0) :
    modelStringEndpointSolutionDeriv d p x < 0 := by
  have hnum : 0 < d * p := mul_pos hd hp
  have hden : 2 * x < 0 := mul_neg_of_pos_of_neg (by norm_num) hx
  have hratio : d * p / (2 * x) < 0 := div_neg_of_pos_of_neg hnum hden
  exact mul_neg_of_pos_of_neg (Real.exp_pos _) (by linarith)

/-- The explicit endpoint solution is strictly decreasing on `(-∞,0)`. -/
theorem strictAntiOn_modelStringEndpointSolution
    {d p : ℝ} (hd : 0 < d) (hp : 0 < p) :
    StrictAntiOn (modelStringEndpointSolution d p) (Iio 0) := by
  apply strictAntiOn_of_deriv_neg (convex_Iio 0)
  · exact continuousOn_of_forall_continuousAt fun x hx ↦
      (hasDerivAt_modelStringEndpointSolution d p (ne_of_lt hx)).continuousAt
  · intro x hx
    have hxneg : x < 0 := by simpa using hx
    rw [(hasDerivAt_modelStringEndpointSolution d p (ne_of_lt hxneg)).deriv]
    exact modelStringEndpointSolutionDeriv_neg hd hp hxneg

end

end DerridaRetaux
