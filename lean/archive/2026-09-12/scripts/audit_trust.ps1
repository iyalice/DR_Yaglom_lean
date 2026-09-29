param(
  [string]$ProjectRoot = (Resolve-Path (Join-Path $PSScriptRoot '..')).Path
)

Set-StrictMode -Version Latest
$ErrorActionPreference = 'Stop'

$leanRoot = Join-Path $ProjectRoot 'DerridaRetaux'
$rootLean = Join-Path $ProjectRoot 'DerridaRetaux.lean'
$humanInputs = Join-Path $leanRoot 'HumanInputs.lean'
$humanInputsAudit = Join-Path $leanRoot 'Audit\HumanInputs.lean'
$sharpnessWrapper = Join-Path $leanRoot 'Main\Sharpness.lean'
$discreteMomentWrapper = Join-Path $leanRoot 'Main\DiscreteMoment.lean'
$arrivalBoundsWrapper = Join-Path $leanRoot 'Main\ArrivalBounds.lean'
$smoothingWrapper = Join-Path $leanRoot 'Main\Smoothing.lean'
$spineWrapper = Join-Path $leanRoot 'Main\Spine.lean'
$continuumMildWrapper = Join-Path $leanRoot 'Main\ContinuumMild.lean'
$continuumMomentsWrapper = Join-Path $leanRoot 'Main\ContinuumMoments.lean'
$identificationWrapper = Join-Path $leanRoot 'Main\Identification.lean'
$expectedHumanInputsHash = '2f35158a78164c7ffe0e8def2049a5c6c9a747fa3671b38965110677752f465e'
$allowedHumanAxioms = [System.Collections.Generic.HashSet[string]]::new(
  [System.StringComparer]::Ordinal)
@(
  'cdhls_excess_upper'
  'cdhls_product_upper'
  'kotani_characteristic_eq_implies_translate'
  'chenShi_stable_product'
) | ForEach-Object { [void]$allowedHumanAxioms.Add($_) }

$leanFiles = @(
  Get-Item -LiteralPath $rootLean
  Get-ChildItem -LiteralPath $leanRoot -Recurse -File -Filter '*.lean' |
    Sort-Object FullName
)
if ($leanFiles.Count -eq 0) {
  throw "No Lean files found under $leanRoot"
}
if (-not (Test-Path -LiteralPath $humanInputs -PathType Leaf)) {
  throw "Missing frozen HumanInputs file: $humanInputs"
}
if (-not (Test-Path -LiteralPath $humanInputsAudit -PathType Leaf)) {
  throw "Missing HumanInputs audit file: $humanInputsAudit"
}

$forbidden = [ordered]@{
  proof_hole = '\b(?:sorry|sorryAx|admit)\b'
  unsafe     = '\bunsafe\b'
  extern     = '^[ \t]*(?:(?:private|protected|noncomputable)[ \t]+)*extern[ \t]+'
}
$primitivePattern =
  '^[ \t]*(?:(?:private|protected|noncomputable)[ \t]+)*(axiom|constant|opaque)[ \t]+' +
  '([A-Za-z0-9_''\.]+)[ \t]*(?=$|[:({\[])'

$failures = [System.Collections.Generic.List[string]]::new()
$foundHumanAxioms = [System.Collections.Generic.List[string]]::new()
$humanInputsAuditImportCount = 0
$sharpnessWrapperImportCount = 0
$discreteMomentWrapperImportCount = 0
$arrivalBoundsWrapperImportCount = 0
$smoothingWrapperImportCount = 0
$spineWrapperImportCount = 0
$continuumMildWrapperImportCount = 0
$continuumMomentsWrapperImportCount = 0
$identificationWrapperImportCount = 0
foreach ($file in $leanFiles) {
  $relative = [IO.Path]::GetRelativePath($ProjectRoot, $file.FullName)
  $isHumanInputs = $file.FullName -eq $humanInputs
  $lines = @(Get-Content -LiteralPath $file.FullName)
  for ($index = 0; $index -lt $lines.Count; $index++) {
    foreach ($entry in $forbidden.GetEnumerator()) {
      if ($lines[$index] -match $entry.Value) {
        $failures.Add("$($entry.Key):${relative}:$($index + 1):$($lines[$index])")
      }
    }

    if ($lines[$index] -match $primitivePattern) {
      $kind = $Matches[1]
      $name = $Matches[2]
      if ($isHumanInputs -and $kind -ceq 'axiom' -and $allowedHumanAxioms.Contains($name)) {
        $foundHumanAxioms.Add($name)
      } else {
        $failures.Add("unapproved_primitive:${relative}:$($index + 1):$kind $name")
      }
    }

    if ($lines[$index] -match '^[ \t]*import[ \t]+([^ \t]+)[ \t]*$') {
      $module = $Matches[1]
      if ($module -notmatch '^(?:Mathlib|Init|Std|Batteries)(?:\.|$)' -and
          $module -notmatch '^DerridaRetaux(?:\.|$)') {
        $failures.Add("foreign_import:${relative}:$($index + 1):$module")
      }
      if ($module -match '^DerridaRetaux(?:\.|$)') {
        $candidate = Join-Path $ProjectRoot (($module -replace '\.', [IO.Path]::DirectorySeparatorChar) + '.lean')
        if (-not (Test-Path -LiteralPath $candidate -PathType Leaf)) {
          $failures.Add("missing_local_import:${relative}:$($index + 1):$module")
        }
      }
      if ($module -ceq 'DerridaRetaux.HumanInputs' -and
          $file.FullName -ne $humanInputsAudit -and
          $file.FullName -ne $sharpnessWrapper -and
          $file.FullName -ne $discreteMomentWrapper -and
          $file.FullName -ne $arrivalBoundsWrapper -and
          $file.FullName -ne $smoothingWrapper -and
          $file.FullName -ne $continuumMildWrapper -and
          $file.FullName -ne $continuumMomentsWrapper -and
          $file.FullName -ne $identificationWrapper -and
          $file.FullName -ne $spineWrapper) {
        $failures.Add("human_inputs_import_outside_audit:${relative}:$($index + 1):$module")
      }
      if ($module -ceq 'DerridaRetaux.HumanInputs' -and $file.FullName -eq $humanInputsAudit) {
        $humanInputsAuditImportCount++
      }
      if ($module -ceq 'DerridaRetaux.HumanInputs' -and $file.FullName -eq $sharpnessWrapper) {
        $sharpnessWrapperImportCount++
      }
      if ($module -ceq 'DerridaRetaux.HumanInputs' -and $file.FullName -eq $discreteMomentWrapper) {
        $discreteMomentWrapperImportCount++
      }
      if ($module -ceq 'DerridaRetaux.HumanInputs' -and $file.FullName -eq $arrivalBoundsWrapper) {
        $arrivalBoundsWrapperImportCount++
      }
      if ($module -ceq 'DerridaRetaux.HumanInputs' -and $file.FullName -eq $smoothingWrapper) {
        $smoothingWrapperImportCount++
      }
      if ($module -ceq 'DerridaRetaux.HumanInputs' -and $file.FullName -eq $spineWrapper) {
        $spineWrapperImportCount++
      }
      if ($module -ceq 'DerridaRetaux.HumanInputs' -and $file.FullName -eq $continuumMildWrapper) {
        $continuumMildWrapperImportCount++
      }
      if ($module -ceq 'DerridaRetaux.HumanInputs' -and $file.FullName -eq $continuumMomentsWrapper) {
        $continuumMomentsWrapperImportCount++
      }
      if ($module -ceq 'DerridaRetaux.HumanInputs' -and $file.FullName -eq $identificationWrapper) {
        $identificationWrapperImportCount++
      }
      if ($module -ceq 'DerridaRetaux.Audit.HumanInputs') {
        $failures.Add("human_inputs_audit_imported:${relative}:$($index + 1):$module")
      }
    }
  }
}

$foundHumanAxiomSet = [System.Collections.Generic.HashSet[string]]::new(
  [System.StringComparer]::Ordinal)
$foundHumanAxioms | ForEach-Object { [void]$foundHumanAxiomSet.Add($_) }
if ($foundHumanAxioms.Count -ne 4 -or
    -not $foundHumanAxiomSet.SetEquals($allowedHumanAxioms)) {
  $failures.Add(
    "human_input_axioms: expected exactly four allowlisted names, found [$($foundHumanAxioms -join ',')]"
  )
}
if ($humanInputsAuditImportCount -ne 1) {
  $failures.Add(
    "human_inputs_audit_import: expected one direct audit import, got $humanInputsAuditImportCount"
  )
}
if ($sharpnessWrapperImportCount -ne 1) {
  $failures.Add(
    "sharpness_wrapper_human_inputs_import: expected one direct wrapper import, got $sharpnessWrapperImportCount"
  )
}
if ($discreteMomentWrapperImportCount -ne 1) {
  $failures.Add(
    "discrete_moment_wrapper_human_inputs_import: expected one direct wrapper import, got $discreteMomentWrapperImportCount"
  )
}
if ($arrivalBoundsWrapperImportCount -ne 1) {
  $failures.Add(
    "arrival_bounds_wrapper_human_inputs_import: expected one direct wrapper import, got $arrivalBoundsWrapperImportCount"
  )
}
if ($smoothingWrapperImportCount -ne 1) {
  $failures.Add(
    "smoothing_wrapper_human_inputs_import: expected one direct wrapper import, got $smoothingWrapperImportCount"
  )
}
if ($spineWrapperImportCount -ne 1) {
  $failures.Add(
    "spine_wrapper_human_inputs_import: expected one direct wrapper import, got $spineWrapperImportCount"
  )
}

if ($continuumMildWrapperImportCount -ne 1) {
  $failures.Add("continuumMildWrapper: expected one direct import")
}

if ($continuumMomentsWrapperImportCount -ne 1) {
  $failures.Add("continuumMomentsWrapper: expected one direct import")
}

if ($identificationWrapperImportCount -ne 1) {
  $failures.Add("identificationWrapper: expected one direct import")
}

$actualHumanInputsHash = (Get-FileHash -Algorithm SHA256 -LiteralPath $humanInputs).Hash.ToLowerInvariant()
if ($actualHumanInputsHash -cne $expectedHumanInputsHash) {
  $failures.Add(
    "human_inputs_hash: expected $expectedHumanInputsHash, got $actualHumanInputsHash"
  )
}

if ($failures.Count -ne 0) {
  $failures | ForEach-Object { Write-Error $_ }
  exit 1
}

Write-Output ((
  'TRUST_SCAN_OK lean_files={0} proof_holes=0 core_primitives=0 human_inputs=4 ' +
  'human_input_names=cdhls_excess_upper,cdhls_product_upper,' +
  'kotani_characteristic_eq_implies_translate,chenShi_stable_product ' +
  'human_inputs_sha256={1} unsafe=0 extern=0 foreign_imports=0 ' +
  'human_inputs_imports=audited_and_allowlisted_wrappers_only'
) -f $leanFiles.Count, $actualHumanInputsHash)
