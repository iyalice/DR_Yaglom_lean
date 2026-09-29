# Current edition handoff — verified

The authoritative manuscript is `../DR_Yaglom.tex`; `DR_Yaglom.tex` is its
byte-identical Lean-project snapshot. See `revision-manifest.json` for source
identity and `UPDATE_PLAN.md` for the active work checkpoint.

Run `python3 scripts/verify_all.py` to build and audit the current edition.
A successful result must be present in
`validation/2026-09-29/verification-result.json`. The 12 September records and
reports are historical and cannot substitute for this gate.

The new public sharpness declaration is `FixedArity.sharpnessSurvival`.
`FixedArity.sharpness` retains its older excess-limit conclusion. Consult
`CORRESPONDENCE_REVIEW.md` before interpreting compound ledger mappings.
No new external input is permitted; the frozen `HumanInputs.lean` hash is
checked automatically.

The final current-edition gate passed; the result file records the exact source hashes.
