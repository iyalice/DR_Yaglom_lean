#!/usr/bin/env python3
"""Check frozen sources, trust declarations, and source-ledger coverage.

This source check supplements, and does not replace, Lean compilation.
"""
from pathlib import Path
import csv
import hashlib
import re

root = Path(__file__).resolve().parent.parent
import json
manifest = json.loads((root / "revision-manifest.json").read_text())
expected_hashes = {
    "DR_Yaglom.tex": manifest["manuscript_sha256"],
    "DerridaRetaux/HumanInputs.lean":
        "2f35158a78164c7ffe0e8def2049a5c6c9a747fa3671b38965110677752f465e",
}
assert (root / "DR_Yaglom.tex").read_bytes() == (root.parent / "DR_Yaglom.tex").read_bytes(), \
    "Lean snapshot differs from active manuscript"
for name, expected in expected_hashes.items():
    actual = hashlib.sha256((root / name).read_bytes()).hexdigest()
    assert actual == expected, f"Frozen source changed: {name}: {actual}"
    print(f"SHA256_OK {name} {actual}")

tex = (root / "DR_Yaglom.tex").read_text()
labels = re.findall(r"\\label\{([^}]+)\}", tex)
assert len(tex.splitlines()) == manifest["source_lines"]
assert len(labels) == len(set(labels)) == manifest["labels"]
equation_labels = {label for label in labels if label.startswith(("eq:", "eqn:", "ineq:"))}
assert len(equation_labels) == manifest["equations"]
result_labels = set()
for match in re.finditer(r"\\begin\{(theorem|proposition|lemma|corollary)\}(.*?)\\end\{\1\}", tex, re.S):
    result_labels.add(re.search(r"\\label\{([^}]+)\}", match[2])[1])
assert len(result_labels) == manifest["statements"]
print(f"SOURCE_OK lines={len(tex.splitlines())} labels={len(labels)} "
      f"equations={len(equation_labels)} numbered_results={len(result_labels)}")

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
    ("STATEMENT_LEDGER.csv", manifest["statements"], "lean_file", "lean_name"),
    ("EQUATION_LEDGER.csv", manifest["equations"], "lean_file", "lean_name"),
    ("UNNUMBERED_LEDGER.csv", manifest["unnumbered"], "lean_file", "lean_name"),
]:
    with (root / name).open(newline="") as handle:
        rows = list(csv.DictReader(handle))
    assert len(rows) == count, name
    key = "source_label" if name == "EQUATION_LEDGER.csv" else "source_id"
    assert len({r[key] for r in rows}) == len(rows), name
    if name == "EQUATION_LEDGER.csv":
        assert {r[key] for r in rows} == equation_labels
    if name == "STATEMENT_LEDGER.csv":
        assert {r[key] for r in rows} == result_labels
    for row in rows:
        assert row["status"] in {"PROVED", "DEFINITION", "proved"}, (name, row[key])
        if "progress" in row:
            assert row["progress"] == "COMPLETE", row[key]
        for path in row[path_column].split(";"):
            assert (root / path.strip()).is_file(), (name, path)
        row_decls = {d.strip() for d in row[declaration_column].split(";") if d.strip()}
        assert row_decls, (name, row[key])
        declarations.update(row_decls)
        dependencies = json.loads(row["compiled_declaration_custom_axioms"])
        assert set(dependencies) == row_decls, (name, row[key], "missing compiled audit")
        for deps in dependencies.values():
            assert set(deps) <= {"DerridaRetaux.HumanInputs." + a for a in allowed_axioms}
audit = (root / "DerridaRetaux/Audit/AllSourceDecls.lean").read_text()
checked = set(re.findall(r"^#check (\S+)$", audit, re.MULTILINE))
printed = set(re.findall(r"^#print axioms (\S+)$", audit, re.MULTILINE))
assert declarations == checked == printed
assert len(checked) == manifest["declarations"]
print(f"LEDGER_COVERAGE_OK statements={manifest['statements']} "
      f"equations={manifest['equations']} unnumbered={manifest['unnumbered']} "
      f"declarations={len(checked)}")
