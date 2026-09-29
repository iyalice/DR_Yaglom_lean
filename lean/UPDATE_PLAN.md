# Update to the current manuscript — active work

Authority: root `DR_Yaglom.tex` at main `66722ad`, plus the locally authorized
funding and verification-disclosure edits. Baseline Lean source:
`iyalice/DR_Yaglom_lean` commit `2830c58dee0265b8cc71b0dc16acc944cda316a2`.
The 2026-09-12 frozen TeX and ledgers are preserved under `archive/2026-09-12/`.

Scope: update all manuscript correspondence, prove newly required results,
retain the four published external inputs unchanged, and rerun build and
compiled axiom audits. Do not weaken manuscript statements or mark unproved
items complete. Historical logs certify only their original frozen source.

## Work queue

1. Restore pinned Lean 4.19.0 / mathlib dependencies and obtain a baseline build.
2. Compare every numbered result and labeled equation and audit intervening
   mathematical prose against the baseline source and formal declarations.
3. Formalize the survival-to-excess barrier argument in the new Appendix A,
   reuse the existing log-product theorem, and prove survival sharpness.
4. Fill any further obligations found by the whole-source correspondence audit.
5. Update snapshot, ledgers, reproducible scripts, public imports, and docs.
6. Run full build, source-hole scan, compiled declaration/axiom audits, and
   final semantic correspondence review. Update the manuscript disclosure only
   to the status actually achieved.

## Current status

Complete. The current manuscript snapshot and all ledgers are updated.
The full build, consolidated compiled axiom audit, and source/ledger checks
passed. See `AcceptanceReport.md` and
`validation/2026-09-29/verification-result.json` for exact source hashes and
public theorem dependency sets. The original four external inputs remain
unchanged. The current AI/verification disclosure points to this edition.
