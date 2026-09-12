import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.NatAntidiagonal
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Topology.UniformSpace.Ascoli

set_option autoImplicit false

/-!
# Mathlib API smoke test

These checks freeze the foundational API surface used by the DR-Yaglom formalization
against Lean/mathlib v4.19.0. They carry no mathematical assumptions.
-/

#check HasSum
#check Summable
#check Finset.antidiagonal
#check Filter.atTop
#check Filter.Eventually
#check Filter.Tendsto
#check Nat.floor
#check Int.floor
#check MeasureTheory.Measure.withDensity
#check MeasureTheory.Measure.map
#check MeasureTheory.IntegrableOn
#check MeasureTheory.integral_prod
#check MeasureTheory.lintegral_prod
#check intervalIntegral.integral_const
#check IntervalIntegrable
#check HasDerivAt
#check HasDerivWithinAt
#check ContinuousOn
#check Real.rpow
#check PMF.bind
#check PMF.map
#check PMF.seq
#check PMF.toMeasure_map
#check UniformOnFun.ofFun
#check ArzelaAscoli.isCompact_closure_of_isClosedEmbedding
