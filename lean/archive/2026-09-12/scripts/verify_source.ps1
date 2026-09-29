[CmdletBinding()]
param()

$ErrorActionPreference = 'Stop'
$repoRoot = Split-Path -Parent $PSScriptRoot
$texPath = Join-Path $repoRoot 'DR_Yaglom.tex'
$expectedHash = '652c080e30cfc8cb37ea9636ae74e4c0b30875e1a69db5ae81008137b5a0b82a'

if (-not (Test-Path -LiteralPath $texPath -PathType Leaf)) {
    throw "Missing authoritative source: $texPath"
}

$actualHash = (Get-FileHash -LiteralPath $texPath -Algorithm SHA256).Hash.ToLowerInvariant()
if ($actualHash -cne $expectedHash) {
    throw "SHA256 mismatch: expected $expectedHash, got $actualHash"
}

$lines = [System.IO.File]::ReadAllLines($texPath)
if ($lines.Count -ne 1127) {
    throw "Line-count mismatch: expected 1127, got $($lines.Count)"
}

$text = [System.IO.File]::ReadAllText($texPath)
$labels = [regex]::Matches($text, '\\label\{([^}]+)\}') |
    ForEach-Object { $_.Groups[1].Value }
$uniqueLabels = [System.Collections.Generic.HashSet[string]]::new(
    [System.StringComparer]::Ordinal)
foreach ($label in $labels) {
    if (-not $uniqueLabels.Add($label)) {
        throw "Duplicate case-sensitive label: $label"
    }
}

if ($uniqueLabels.Count -ne 105) {
    throw "Label-count mismatch: expected 105, got $($uniqueLabels.Count)"
}

$equationLabels = @($uniqueLabels | Where-Object {
    $_.StartsWith('eq:', [System.StringComparison]::Ordinal)
})
if ($equationLabels.Count -ne 82) {
    throw "Equation-label mismatch: expected 82, got $($equationLabels.Count)"
}

$expectedEnvironments = [ordered]@{
    theorem     = 2
    proposition = 5
    lemma       = 7
    corollary   = 1
}
foreach ($entry in $expectedEnvironments.GetEnumerator()) {
    $pattern = '\\begin\{' + [regex]::Escape($entry.Key) + '\}'
    $count = [regex]::Matches($text, $pattern).Count
    if ($count -ne $entry.Value) {
        throw "Environment-count mismatch for $($entry.Key): expected $($entry.Value), got $count"
    }
}

Write-Output (
    'SOURCE_OK sha256={0} lines={1} labels={2} equations={3} results=15' -f
    $actualHash, $lines.Count, $uniqueLabels.Count, $equationLabels.Count
)
