#!/usr/bin/env python3
"""Check frozen sources, trust declarations, and source-ledger coverage.

This source check supplements, and does not replace, Lean compilation.
"""
from pathlib import Path
import csv
import hashlib
import re

root = Path(__file__).resolve().parent.parent
expected_hashes = {
    "DR_Yaglom.tex":
        "652c080e30cfc8cb37ea9636ae74e4c0b30875e1a69db5ae81008137b5a0b82a",
    "DerridaRetaux/HumanInputs.lean":
        "2f35158a78164c7ffe0e8def2049a5c6c9a747fa3671b38965110677752f465e",
}
for name, expected in expected_hashes.items():
    actual = hashlib.sha256((root / name).read_bytes()).hexdigest()
    assert actual == expected, f"Frozen source changed: {name}: {actual}"
    print(f"SHA256_OK {name} {actual}")

tex = (root / "DR_Yaglom.tex").read_text()
labels = re.findall(r"\\label\{([^}]+)\}", tex)
assert len(tex.splitlines()) == 1127
assert len(labels) == len(set(labels)) == 105
assert sum(label.startswith("eq:") for label in labels) == 82
for name, count in {"theorem": 2, "proposition": 5, "lemma": 7, "corollary": 1}.items():
    assert len(re.findall(r"\\begin\{" + name + r"\}", tex)) == count
print("SOURCE_OK lines=1127 labels=105 equations=82 numbered_results=15")

allowed_axioms = {
    "cdhls_excess_upper", "cdhls_product_upper",
    "kotani_characteristic_eq_implies_translate", "chenShi_stable_product",
}
input_importers = {
    "DerridaRetaux/Main/ContinuumMild.lean", "DerridaRetaux/Main/ContinuumMoments.lean",
    "DerridaRetaux/Main/Identification.lean",
    "DerridaRetaux/Audit/HumanInputs.lean", "DerridaRetaux/Main/Sharpness.lean",
    "DerridaRetaux/Main/DiscreteMoment.lean", "DerridaRetaux/Main/ArrivalBounds.lean",
    "DerridaRetaux/Main/Smoothing.lean", "DerridaRetaux/Main/Spine.lean",
}
files = [root / "DerridaRetaux.lean", *sorted((root / "DerridaRetaux").rglob("*.lean"))]
found_axioms = []
found_importers = []
primitive = re.compile(
    r"^\s*(?:(?:private|protected|noncomputable)\s+)*(axiom|constant|opaque)\s+([\w'.]+)"
)
for file in files:
    name = file.relative_to(root).as_posix()
    for line_number, line in enumerate(file.read_text().splitlines(), 1):
        where = f"{name}:{line_number}"
        assert not re.search(r"\b(?:sorry|sorryAx|admit|unsafe)\b", line), where
        assert not re.search(r"^\s*(?:(?:private|protected|noncomputable)\s+)*extern\s", line), where
        if match := primitive.match(line):
            kind, declaration = match.groups()
            assert name == "DerridaRetaux/HumanInputs.lean", where
            assert kind == "axiom" and declaration in allowed_axioms, where
            found_axioms.append(declaration)
        if match := re.fullmatch(r"\s*import\s+(\S+)\s*", line):
            module = match.group(1)
            assert module.split(".")[0] in {"Mathlib", "Init", "Std", "Batteries", "DerridaRetaux"}, where
            if module.startswith("DerridaRetaux"):
                assert (root / (module.replace(".", "/") + ".lean")).is_file(), where
            assert module != "DerridaRetaux.Audit.HumanInputs", where
            if module == "DerridaRetaux.HumanInputs":
                assert name in input_importers, where
                found_importers.append(name)
assert len(found_axioms) == 4 and set(found_axioms) == allowed_axioms
assert len(found_importers) == 9 and set(found_importers) == input_importers
print(f"TRUST_SCAN_OK lean_files={len(files)} proof_holes=0 unsafe=0 extern=0 custom_axioms=4")

declarations = set()
for name, count, path_column, declaration_column in [
    ("STATEMENT_LEDGER.csv", 15, 4, 5),
    ("EQUATION_LEDGER.csv", 82, 2, 3),
    ("UNNUMBERED_LEDGER.csv", 62, 2, 3),
]:
    with (root / name).open(newline="") as handle:
        rows = list(csv.reader(handle))[1:]
    assert len(rows) == count, name
    for row in rows:
        for path in row[path_column].split(";"):
            assert (root / path.strip()).is_file(), (name, path)
        declarations.update(d.strip() for d in row[declaration_column].split(";") if d.strip())
audit = (root / "DerridaRetaux/Audit/AllSourceDecls.lean").read_text()
checked = set(re.findall(r"^#check (\S+)$", audit, re.MULTILINE))
assert declarations == checked
assert len(checked) == 419
print("LEDGER_COVERAGE_OK statements=15 equations=82 unnumbered=62 declarations=419")
