import DerridaRetaux

/-! Current numbered-result components and the retained spectral wrappers.
The exhaustive ledger audit is AllSourceDecls; verify_all compiles the union
with all supplementary custom-axiom audits. -/

-- thm:profile
#check DerridaRetaux.FixedArity.profile
#print axioms DerridaRetaux.FixedArity.profile

-- prop:pgf
#check DerridaRetaux.generatingFunction_drStep
#print axioms DerridaRetaux.generatingFunction_drStep
#check DerridaRetaux.generatingFunction_orbit_succ_cross
#print axioms DerridaRetaux.generatingFunction_orbit_succ_cross
#check DerridaRetaux.orbit_tiltSummable_three
#print axioms DerridaRetaux.orbit_tiltSummable_three
#check DerridaRetaux.orbit_critical
#print axioms DerridaRetaux.orbit_critical
#check DerridaRetaux.normalizedTilt_hasSum
#print axioms DerridaRetaux.normalizedTilt_hasSum
#check DerridaRetaux.normalizedTilt_mean_hasSum
#print axioms DerridaRetaux.normalizedTilt_mean_hasSum
#check DerridaRetaux.normalizedTiltGeneratingFunction_orbit_succ
#print axioms DerridaRetaux.normalizedTiltGeneratingFunction_orbit_succ
#check DerridaRetaux.tiltedPartition_orbit_succ_eq
#print axioms DerridaRetaux.tiltedPartition_orbit_succ_eq

-- prop:coarse
#check DerridaRetaux.orbitExcess_bound_all
#print axioms DerridaRetaux.orbitExcess_bound_all
#check DerridaRetaux.criticalProduct_bound_all_of_CDHLSProductFact
#print axioms DerridaRetaux.criticalProduct_bound_all_of_CDHLSProductFact
#check DerridaRetaux.survival_le_excess_div_of_critical
#print axioms DerridaRetaux.survival_le_excess_div_of_critical
#check DerridaRetaux.positiveTiltMass_orbit_eq
#print axioms DerridaRetaux.positiveTiltMass_orbit_eq
#check DerridaRetaux.orbitPositiveTiltMass_bound_all
#print axioms DerridaRetaux.orbitPositiveTiltMass_bound_all
#check DerridaRetaux.orbitPositiveTiltMass_tendsto_zero
#print axioms DerridaRetaux.orbitPositiveTiltMass_tendsto_zero
#check DerridaRetaux.orbitZeroTilt_inverse_uniform
#print axioms DerridaRetaux.orbitZeroTilt_inverse_uniform

-- lem:cubic
#check DerridaRetaux.FixedArity.cubicMoment
#print axioms DerridaRetaux.FixedArity.cubicMoment

-- lem:tiltedlaw
#check DerridaRetaux.FixedArity.tiltedLawRecursion
#print axioms DerridaRetaux.FixedArity.tiltedLawRecursion

-- lem:transportcoefficients
#check DerridaRetaux.transportCoeff_pos
#print axioms DerridaRetaux.transportCoeff_pos
#check DerridaRetaux.transportCoeff_le_one
#print axioms DerridaRetaux.transportCoeff_le_one
#check DerridaRetaux.orbitTransportDefect_le_of_positiveTiltMass_bound
#print axioms DerridaRetaux.orbitTransportDefect_le_of_positiveTiltMass_bound
#check DerridaRetaux.transportProduct_tendsto_pos
#print axioms DerridaRetaux.transportProduct_tendsto_pos
#check DerridaRetaux.antitone_transportProduct
#print axioms DerridaRetaux.antitone_transportProduct

-- lem:atomtail
#check DerridaRetaux.FixedArity.firstTiltedAtomTail
#print axioms DerridaRetaux.FixedArity.firstTiltedAtomTail

-- lem:weightedmass
#check DerridaRetaux.FixedArity.weightedMass
#print axioms DerridaRetaux.FixedArity.weightedMass

-- prop:smoothing
#check DerridaRetaux.FixedArity.smoothing
#print axioms DerridaRetaux.FixedArity.smoothing

-- prop:identification
#check DerridaRetaux.FixedArity.identifySubsequentialLimit
#print axioms DerridaRetaux.FixedArity.identifySubsequentialLimit

-- prop:pointwise
#check DerridaRetaux.FixedArity.pointwiseBound
#print axioms DerridaRetaux.FixedArity.pointwiseBound

-- prop:far
#check DerridaRetaux.FixedArity.farArrivalBoundUniform
#print axioms DerridaRetaux.FixedArity.farArrivalBoundUniform

-- lem:arrival
#check DerridaRetaux.FixedArity.arrivalRecursion
#print axioms DerridaRetaux.FixedArity.arrivalRecursion

-- lem:Fmoment
#check DerridaRetaux.FixedArity.arrivalMomentTail
#print axioms DerridaRetaux.FixedArity.arrivalMomentTail

-- lem:sourcedifference
#check DerridaRetaux.FixedArity.sourceDifference
#print axioms DerridaRetaux.FixedArity.sourceDifference

-- lem:spine
#check DerridaRetaux.FixedArity.cubicWeightedChain
#print axioms DerridaRetaux.FixedArity.cubicWeightedChain
#check DerridaRetaux.FixedArity.cubicWeightedInfiniteChain
#print axioms DerridaRetaux.FixedArity.cubicWeightedInfiniteChain

-- cor:thirdtail
#check DerridaRetaux.FixedArity.thirdMomentTail
#print axioms DerridaRetaux.FixedArity.thirdMomentTail

-- prop:limit
#check DerridaRetaux.FixedArity.subsequentialLimitProperties
#print axioms DerridaRetaux.FixedArity.subsequentialLimitProperties

-- lem:momentODE
#check DerridaRetaux.FixedArity.momentLaplaceODE
#print axioms DerridaRetaux.FixedArity.momentLaplaceODE
#check DerridaRetaux.FixedArity.momentLaplaceLocalIntegralDerivatives
#print axioms DerridaRetaux.FixedArity.momentLaplaceLocalIntegralDerivatives

-- lem:remainder
#check DerridaRetaux.FixedArity.thirdOrderTaylorRemainder
#print axioms DerridaRetaux.FixedArity.thirdOrderTaylorRemainder

-- thm:sharpness
#check DerridaRetaux.FixedArity.sharpnessSurvival
#print axioms DerridaRetaux.FixedArity.sharpnessSurvival

-- lem:productasymptotic
#check DerridaRetaux.FixedArity.productAsymptoticOfSurvival
#print axioms DerridaRetaux.FixedArity.productAsymptoticOfSurvival

#check DerridaRetaux.FixedArity.constructedModelCumulative_eq_of_characteristics
#print axioms DerridaRetaux.FixedArity.constructedModelCumulative_eq_of_characteristics
#check DerridaRetaux.FixedArity.constructedModelCumulative_eq_of_constructed_characteristic
#print axioms DerridaRetaux.FixedArity.constructedModelCumulative_eq_of_constructed_characteristic
