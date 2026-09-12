import DerridaRetaux.Spine.InfinitePath
import DerridaRetaux.Main.MomentLaplaceRegularity
import DerridaRetaux.Main.ProfileTheorem
import DerridaRetaux.Main.IdentificationFinal
import DerridaRetaux.Main.ContinuumLimit
import DerridaRetaux.Main.MomentLaplaceODE
import DerridaRetaux.Main.Remainder
import DerridaRetaux.Main.ContinuumWeakEquation
import DerridaRetaux.Main.Arrival
import DerridaRetaux.Main.ArrivalBounds
import DerridaRetaux.Main.DiscreteMoment
import DerridaRetaux.Main.Identification
import DerridaRetaux.Main.IdentificationModel
import DerridaRetaux.Main.ContinuumMild
import DerridaRetaux.Main.ContinuumMoments
import DerridaRetaux.Main.ContinuumMomentPassage
import DerridaRetaux.Main.ContinuumMomentBounds
import DerridaRetaux.Main.ContinuumThirdTail
import DerridaRetaux.Main.Sharpness
import DerridaRetaux.Main.Smoothing
import DerridaRetaux.Main.Spine

/-!
# Source-facing wrapper audit

This executable audit prints all fifteen manuscript-facing numbered-result wrappers,
the U46 weak-equation wrapper, and their exact transitive axiom sets.  The exhaustive
ledger-level audit is `AllSourceDecls.lean`.
-/

#print DerridaRetaux.FixedArity.profile
#print axioms DerridaRetaux.FixedArity.profile

#print DerridaRetaux.FixedArity.identifySubsequentialLimit
#print axioms DerridaRetaux.FixedArity.identifySubsequentialLimit

#print DerridaRetaux.FixedArity.subsequentialLimitProperties
#print axioms DerridaRetaux.FixedArity.subsequentialLimitProperties

#print DerridaRetaux.FixedArity.momentLaplaceODE
#print axioms DerridaRetaux.FixedArity.momentLaplaceODE

#print DerridaRetaux.FixedArity.thirdOrderTaylorRemainder
#print axioms DerridaRetaux.FixedArity.thirdOrderTaylorRemainder

#print DerridaRetaux.FixedArity.cubicMoment
#print axioms DerridaRetaux.FixedArity.cubicMoment

#print DerridaRetaux.FixedArity.firstTiltedAtomTail
#print axioms DerridaRetaux.FixedArity.firstTiltedAtomTail

#print DerridaRetaux.FixedArity.arrivalRecursion
#print axioms DerridaRetaux.FixedArity.arrivalRecursion

#print DerridaRetaux.FixedArity.sourceDifference
#print axioms DerridaRetaux.FixedArity.sourceDifference

#print DerridaRetaux.FixedArity.farArrivalBound
#print axioms DerridaRetaux.FixedArity.farArrivalBound

#print DerridaRetaux.FixedArity.pointwiseBound
#print axioms DerridaRetaux.FixedArity.pointwiseBound

#print DerridaRetaux.FixedArity.smoothing
#print axioms DerridaRetaux.FixedArity.smoothing

#print DerridaRetaux.FixedArity.cubicWeightedChain
#print axioms DerridaRetaux.FixedArity.cubicWeightedChain

#print DerridaRetaux.FixedArity.thirdMomentTail
#print axioms DerridaRetaux.FixedArity.thirdMomentTail

#print DerridaRetaux.FixedArity.sharpness_core
#print axioms DerridaRetaux.FixedArity.sharpness_core

#print DerridaRetaux.FixedArity.sharpness
#print axioms DerridaRetaux.FixedArity.sharpness

#print DerridaRetaux.FixedArity.constructedModelCumulative_eq_of_characteristics
#print axioms DerridaRetaux.FixedArity.constructedModelCumulative_eq_of_characteristics
#print axioms DerridaRetaux.FixedArity.constructedModelCumulative_eq_of_constructed_characteristic

#print DerridaRetaux.FixedArity.subsequentialMildEquation
#print axioms DerridaRetaux.FixedArity.subsequentialMildEquation
#print DerridaRetaux.FixedArity.subsequentialMoment_integrable
#print axioms DerridaRetaux.FixedArity.subsequentialMoment_integrable
#print DerridaRetaux.FixedArity.subsequentialMoment_tendsto
#print axioms DerridaRetaux.FixedArity.subsequentialMoment_tendsto
#print DerridaRetaux.FixedArity.subsequentialMoment_bounds
#print axioms DerridaRetaux.FixedArity.subsequentialMoment_bounds
#print DerridaRetaux.FixedArity.subsequentialThirdMomentTail
#print axioms DerridaRetaux.FixedArity.subsequentialThirdMomentTail

#print DerridaRetaux.FixedArity.subsequentialHasWeakEquationOn
#print axioms DerridaRetaux.FixedArity.subsequentialHasWeakEquationOn

#check DerridaRetaux.FixedArity.cubicWeightedInfiniteChain
#print axioms DerridaRetaux.FixedArity.cubicWeightedInfiniteChain

#check DerridaRetaux.FixedArity.momentLaplaceLocalIntegralDerivatives
#print axioms DerridaRetaux.FixedArity.momentLaplaceLocalIntegralDerivatives
