# Reuse audit

This audit is read-only with respect to both earlier Derrida--Retaux projects.  No old
project is a Lake dependency of this repository, and no old source file was modified.

## Current repository baseline

At the frozen baseline commit `aa546d6`, this repository tracked only `.gitignore`,
`DR_Yaglom.tex`, and `README.md`.  It contained no Lean source to reuse.  Every Lean
file in the present branch was created for this handoff.

## Quarantined terminal results

The two declarations named by the handoff do not occur in `Derrida-Retaux complex`.
They occur only in the separate `Derrida-Retaux simple` project, in
`DR/Terminal/Barrier.lean`:

- `DR.Terminal.proposition47_3`;
- `DR.Terminal.originalOrbitCrossing_eventually_of_fixedTests47_3`.

Both compile under Lean/mathlib v4.19.0 and their live `#print axioms` output contains
only `propext`, `Classical.choice`, and `Quot.sound`.  Nevertheless, they are theorems
about the binary, finite-polynomial type `DR.FiniteLaw`; one assumes a barrier
minorant, and the other assumes the desired test and survival-window limits.  They do
not have an arity parameter and cannot prove the present arbitrary-fixed-arity PMF
statement.  They are therefore architecture references only and are not imported.

The old complex project independently records the same mismatch in
`DR/FixedArity/Regression/LegacyBridge.lean`: there is no proved conversion preserving
the step, orbit means, and free-energy definitions between `DR.FiniteLaw` and its
fixed-arity `PMF Nat` development.

## Safe proof ideas, requiring local porting

The following old modules contain potentially reusable, axiom-free arguments.  Their
ideas may be ported only after restating them over this project's transparent
definitions and recompiling them here:

- `DR/FixedArity/Model.lean` and `Convolution.lean`: iid sums, law step, and orbit;
- `DR/FixedArity/FiniteIdentities.lean`: weighted Abel summation, triangular finite-sum
  exchange, and finite-arity geometric iteration;
- `DR/FixedArity/SourceDifference.lean` and its subdirectory: finite tag/shift
  expansion and a close analogue of the source-difference estimate;
- `DR/FixedArity/Yaglom/TailToLocal.lean` and `PowerBlockTauberian.lean`: generic
  Tauberian sequence lemmas;
- `DR/FixedArity/BKT/BadArrayUniformity.lean`, `Selectors.lean`, and
  `ParameterCovariance.lean`: generic compactness/diagonal and scaling utilities;
- `DR/FixedArity/Critical/NNRealProbabilityCompactness.lean` and
  `NNRealLaplaceCDFConvergence.lean`: tightness, CDF subsequences, and Laplace
  convergence;
- `ResidualProfileFluxAtInfinity.lean` and
  `ResidualProfileRightLimitPointL2.lean`: conditional flux/Wronskian proof patterns.

The last two residual modules were rebuilt successfully during this audit.  Their
statements remain tied to the old `ResidualCompactnessProperties`, `YaglomAdmissible`,
`SturmSolution`, and coefficient definitions; they neither construct the new
`EntranceString` nor close all-off-axis right-square-integrable existence.  Only the
proof patterns are reusable.

## Forbidden imports and assumptions

The new project must not import any of the following:

- broad `import DR`, which pulls the old external interfaces and target layers;
- old `DR.FixedArity.ExternalInterfaces` or `TheoremStatements`;
- old conclusion declarations such as `criticalYaglom`,
  `residualProfile_postRigidity_identification`, or
  `criticalProfile_of_globalSpectralComparison`;
- old conclusion-bearing data bundles such as `ExactGFOrbitData`,
  `ExactExponentialTiltOrbitData`, `SpinalRepresentationData`, or
  `SpinalUniformIntegrabilityData`;
- `Derrida-Retaux simple/DR/Terminal/*` as a fixed-arity proof dependency.

In particular, the old `CDHLSCoarseStatement` is stronger than the new two
upper-only H1 declarations, while its spectral interface is not the proposed Kotani
`EntranceString` specialization.  Importing it would change the stated trust basis.

## Live validation performed in the old checkouts

The audit rebuilt the named terminal module, the basic fixed-arity convolution and
finite-identity modules, the two Tauberian modules, the listed compactness/Laplace
modules, and the two residual rigidity modules.  The sampled declarations reported
only the three standard Lean axioms.  This establishes that those proof ideas are
available for porting; it does not establish any theorem in the present repository.
