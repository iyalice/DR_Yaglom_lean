# Proof obligations

Status: **COMPLETE** (2026-09-12 revision; compilation and axiom audit verified).

No mathematical or formalization obligation remains open in the agreed source scope.

- All 15 numbered results have source-facing compiled declarations.
- All 82 labeled equations have proved declarations or transparent definitions.
- All U01--U62 obligations are marked `proved` and `COMPLETE`.
- The continuum mild equation, compactly supported time-integrated weak equation
  (including the boundary trace), moment/Laplace ODEs, Taylor remainder, constructed
  and model string characteristics, H2 comparison, endpoint de-translation,
  physical-time recovery, Laplace inversion, whole-sequence profile, all profile
  consequences, and sharpness construction are closed.

The exact declaration mapping is in `STATEMENT_LEDGER.csv`, `EQUATION_LEDGER.csv`, and
`UNNUMBERED_LEDGER.csv`; `DerridaRetaux/Audit/AllSourceDecls.lean` checks every mapped
declaration and its transitive axiom set.

The infinite-path and local integral-derivative supplements are included and compiled. No remaining proof obligation was identified in this revision. The four external inputs remain accepted premises, not internally re-proved facts.
