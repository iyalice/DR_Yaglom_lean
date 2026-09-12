import DerridaRetaux.Basic.PMFBridge
import Mathlib.Probability.ProbabilityMassFunction.Constructions

set_option autoImplicit false

namespace DerridaRetaux

/-!
# Fixed-arity Derrida--Retaux law recursion

The probability-space semantics of one step is the law of
`(X₁ + ... + X_m - 1)₊`.  Natural-number subtraction already implements the positive
part.  The source-facing orbit remains a `ProbabilityMass`; its conversion to the
mathlib `PMF` recursion is proved exactly below.
-/

noncomputable section

/-- The sum of `r` independent natural-valued variables with common law `μ`. -/
def iidSum : ℕ → PMF ℕ → PMF ℕ
  | 0, _ => pure 0
  | r + 1, μ => do
      let previous ← iidSum r μ
      let next ← μ
      pure (previous + next)

@[simp] theorem iidSum_zero (μ : PMF ℕ) : iidSum 0 μ = pure 0 :=
  rfl

@[simp] theorem iidSum_succ (r : ℕ) (μ : PMF ℕ) :
    iidSum (r + 1) μ =
      (do
        let previous ← iidSum r μ
        let next ← μ
        pure (previous + next)) :=
  rfl

/-- One fixed-arity update on mathlib probability mass functions. -/
def lawStep (m : ℕ) (μ : PMF ℕ) : PMF ℕ :=
  (iidSum m μ).map (fun total ↦ total - 1)

/-- One fixed-arity update on the paper-facing real mass bundle. -/
def drStep (m : ℕ) (p : ProbabilityMass) : ProbabilityMass :=
  ProbabilityMass.ofPMF (lawStep m p.toPMF)

/-- The paper-facing orbit, with generation zero equal to the initial law. -/
def orbit (m : ℕ) (p₀ : ProbabilityMass) : ℕ → ProbabilityMass
  | 0 => p₀
  | n + 1 => drStep m (orbit m p₀ n)

@[simp] theorem drStep_toPMF (m : ℕ) (p : ProbabilityMass) :
    (drStep m p).toPMF = lawStep m p.toPMF := by
  simp [drStep]

@[simp] theorem orbit_zero (m : ℕ) (p₀ : ProbabilityMass) : orbit m p₀ 0 = p₀ :=
  rfl

@[simp] theorem orbit_succ (m n : ℕ) (p₀ : ProbabilityMass) :
    orbit m p₀ (n + 1) = drStep m (orbit m p₀ n) :=
  rfl

@[simp] theorem orbit_toPMF_zero (m : ℕ) (p₀ : ProbabilityMass) :
    (orbit m p₀ 0).toPMF = p₀.toPMF :=
  rfl

theorem orbit_toPMF_succ (m n : ℕ) (p₀ : ProbabilityMass) :
    (orbit m p₀ (n + 1)).toPMF = lawStep m (orbit m p₀ n).toPMF := by
  simp

end

end DerridaRetaux
