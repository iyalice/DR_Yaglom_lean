[CmdletBinding()]
param()

$ErrorActionPreference = 'Stop'
$repoRoot = Split-Path -Parent $PSScriptRoot

function New-OrdinalSet {
    return ,([System.Collections.Generic.HashSet[string]]::new(
        [System.StringComparer]::Ordinal))
}

function Assert-UniqueCount {
    param(
        [Parameter(Mandatory)] [object[]] $Rows,
        [Parameter(Mandatory)] [string] $Column,
        [Parameter(Mandatory)] [int] $Expected,
        [Parameter(Mandatory)] [string] $Name
    )
    if ($Rows.Count -ne $Expected) {
        throw "$Name row count: expected $Expected, got $($Rows.Count)"
    }
    $seen = New-OrdinalSet
    foreach ($row in $Rows) {
        $value = [string]$row.$Column
        if (-not $seen.Add($value)) {
            throw "$Name duplicate under ordinal comparison: $value"
        }
    }
}

function Assert-ExactValues {
    param(
        [Parameter(Mandatory)] [object[]] $Rows,
        [Parameter(Mandatory)] [string] $Column,
        [Parameter(Mandatory)] [string[]] $Allowed,
        [Parameter(Mandatory)] [string] $Name
    )
    $allowedSet = New-OrdinalSet
    $Allowed | ForEach-Object { [void]$allowedSet.Add($_) }
    foreach ($row in $Rows) {
        $value = [string]$row.$Column
        if (-not $allowedSet.Contains($value)) {
            throw "$Name has invalid $Column value '$value' at $($row.source_id)$($row.source_label)"
        }
    }
}

function Assert-ExactCounts {
    param(
        [Parameter(Mandatory)] [object[]] $Rows,
        [Parameter(Mandatory)] [string] $Column,
        [Parameter(Mandatory)] [hashtable] $Expected,
        [Parameter(Mandatory)] [string] $Name
    )
    foreach ($entry in $Expected.GetEnumerator()) {
        $actual = @($Rows | Where-Object { [string]$_.$Column -ceq [string]$entry.Key }).Count
        if ($actual -ne [int]$entry.Value) {
            throw "$Name $Column count for '$($entry.Key)': expected $($entry.Value), got $actual"
        }
    }
}

function Assert-LedgerReferences {
    param(
        [Parameter(Mandatory)] [object[]] $Rows,
        [Parameter(Mandatory)] [System.Collections.Generic.HashSet[string]] $DeclarationNames
    )
    foreach ($row in $Rows) {
        foreach ($relativePath in ([string]$row.lean_file -split ';')) {
            $relativePath = $relativePath.Trim()
            if ($relativePath -ne '' -and
                -not (Test-Path -LiteralPath (Join-Path $repoRoot $relativePath) -PathType Leaf)) {
                throw "Ledger path does not exist at $($row.source_id)$($row.source_label): $relativePath"
            }
        }
        foreach ($column in @('lean_name', 'compiled_precursors')) {
            if ($row.PSObject.Properties.Name -contains $column) {
                foreach ($fullName in ([string]$row.$column -split ';')) {
                    $fullName = $fullName.Trim()
                    if ($fullName -ne '') {
                        $terminalName = ($fullName -split '\.')[-1]
                        if (-not $DeclarationNames.Contains($terminalName)) {
                            throw "Ledger declaration does not exist at $($row.source_id)$($row.source_label): $fullName"
                        }
                    }
                }
            }
        }
    }
}

$statements = @(Import-Csv (Join-Path $repoRoot 'STATEMENT_LEDGER.csv'))
$equations = @(Import-Csv (Join-Path $repoRoot 'EQUATION_LEDGER.csv'))
$unnumbered = @(Import-Csv (Join-Path $repoRoot 'UNNUMBERED_LEDGER.csv'))

Assert-UniqueCount $statements 'source_id' 15 'statement ledger'
Assert-UniqueCount $equations 'source_label' 82 'equation ledger'
Assert-UniqueCount $unnumbered 'source_id' 62 'unnumbered ledger'

$expectedStatementIds = New-OrdinalSet
@(
    'thm:profile', 'thm:sharpness', 'lem:cubic', 'lem:atomtail', 'prop:smoothing',
    'prop:identification', 'prop:pointwise', 'lem:arrival', 'lem:sourcedifference',
    'prop:far', 'lem:spine', 'cor:thirdtail', 'prop:limit', 'lem:momentODE',
    'lem:remainder'
) | ForEach-Object { [void]$expectedStatementIds.Add($_) }
$actualStatementIds = New-OrdinalSet
foreach ($row in $statements) {
    [void]$actualStatementIds.Add([string]$row.source_id)
}
if (-not $expectedStatementIds.SetEquals($actualStatementIds)) {
    throw 'Statement ledger IDs do not match the frozen set of 15 numbered results'
}

Assert-ExactValues $statements 'status' @(
    'PROVED', 'PARTIAL', 'UNFORMALIZED_AT_CONDITIONAL_CHECKPOINT'
) 'statement ledger'
Assert-ExactValues $equations 'status' @('PROVED', 'DEFINITION', 'PARTIAL', 'OPEN') `
    'equation ledger'
Assert-ExactValues $unnumbered 'status' @('definition', 'proved', 'external', 'blocked') `
    'unnumbered ledger'
Assert-ExactValues $unnumbered 'progress' @('COMPLETE', 'PARTIAL', 'OPEN') `
    'unnumbered ledger'
Assert-ExactCounts $statements 'status' @{
    'PROVED' = 15
    'PARTIAL' = 0
    'UNFORMALIZED_AT_CONDITIONAL_CHECKPOINT' = 0
} 'statement ledger'
Assert-ExactCounts $equations 'status' @{
    'PROVED' = 73
    'DEFINITION' = 9
    'PARTIAL' = 0
    'OPEN' = 0
} 'equation ledger'
Assert-ExactCounts $unnumbered 'status' @{
    'definition' = 0
    'proved' = 62
    'external' = 0
    'blocked' = 0
} 'unnumbered ledger'
Assert-ExactCounts $unnumbered 'progress' @{
    'COMPLETE' = 62
    'PARTIAL' = 0
    'OPEN' = 0
} 'unnumbered ledger'
if (@($unnumbered | Where-Object status -eq 'external').Count -ne 0) {
    throw 'No U01--U62 obligation is eligible for external status'
}

$tex = [System.IO.File]::ReadAllText((Join-Path $repoRoot 'DR_Yaglom.tex'))
$sourceEquationSet = New-OrdinalSet
foreach ($match in [regex]::Matches($tex, '\\label\{(eq:[^}]+)\}')) {
    [void]$sourceEquationSet.Add($match.Groups[1].Value)
}
$ledgerEquationSet = New-OrdinalSet
foreach ($row in $equations) {
    [void]$ledgerEquationSet.Add([string]$row.source_label)
}

if (-not $sourceEquationSet.SetEquals($ledgerEquationSet)) {
    $missing = @($sourceEquationSet | Where-Object { -not $ledgerEquationSet.Contains($_) })
    $extra = @($ledgerEquationSet | Where-Object { -not $sourceEquationSet.Contains($_) })
    throw "Equation ledger mismatch. Missing=[$($missing -join ',')] Extra=[$($extra -join ',')]"
}

$expectedUnnumbered = New-OrdinalSet
1..62 | ForEach-Object { [void]$expectedUnnumbered.Add(('U{0:d2}' -f $_)) }
$actualUnnumbered = New-OrdinalSet
foreach ($row in $unnumbered) {
    [void]$actualUnnumbered.Add([string]$row.source_id)
}
if (-not $expectedUnnumbered.SetEquals($actualUnnumbered)) {
    throw 'Unnumbered ledger does not contain exactly U01--U62'
}

$declaredTerminalNames = New-OrdinalSet
$leanFiles = @(
    Get-Item -LiteralPath (Join-Path $repoRoot 'DerridaRetaux.lean')
    Get-ChildItem -LiteralPath (Join-Path $repoRoot 'DerridaRetaux') -Recurse -File `
        -Filter '*.lean'
)
foreach ($file in $leanFiles) {
    $source = [IO.File]::ReadAllText($file.FullName)
    $pattern = '(?m)^[ \t]*(?:noncomputable[ \t]+)?' +
        '(?:def|abbrev|structure|class|theorem|lemma)[ \t]+' +
        '([A-Za-z_][A-Za-z0-9_'']*(?:\.[A-Za-z_][A-Za-z0-9_'']*)*)' +
        '(?=[ \t(:{\[\r\n]|$)'
    foreach ($match in [regex]::Matches($source, $pattern)) {
        $terminalName = ($match.Groups[1].Value -split '\.')[-1]
        if ($terminalName -ne '') {
            [void]$declaredTerminalNames.Add($terminalName)
        }
    }
}
Assert-LedgerReferences $statements $declaredTerminalNames
Assert-LedgerReferences $equations $declaredTerminalNames
Assert-LedgerReferences $unnumbered $declaredTerminalNames

$allowedInputs = New-OrdinalSet
@('H1a', 'H1b', 'H2', 'H3') | ForEach-Object { [void]$allowedInputs.Add($_) }
foreach ($row in @($statements) + @($equations) + @($unnumbered)) {
    $fields = @([string]$row.transitive_human_inputs, [string]$row.expected_inputs)
    foreach ($field in $fields) {
        foreach ($match in [regex]::Matches($field, 'H[0-9]+[a-z]?')) {
            if (-not $allowedInputs.Contains($match.Value)) {
                throw "Unapproved external input '$($match.Value)' in a ledger"
            }
        }
    }
}

$statementProved = @($statements | Where-Object status -CEQ 'PROVED').Count
$statementPartial = @($statements | Where-Object status -CEQ 'PARTIAL').Count
$statementUnformalized =
    @($statements | Where-Object status -CEQ 'UNFORMALIZED_AT_CONDITIONAL_CHECKPOINT').Count
$equationProved = @($equations | Where-Object status -CEQ 'PROVED').Count
$equationDefinition = @($equations | Where-Object status -CEQ 'DEFINITION').Count
$equationPartial = @($equations | Where-Object status -CEQ 'PARTIAL').Count
$equationOpen = @($equations | Where-Object status -CEQ 'OPEN').Count
$unnumberedProved = @($unnumbered | Where-Object status -CEQ 'proved').Count
$unnumberedBlocked = @($unnumbered | Where-Object status -CEQ 'blocked').Count
$unnumberedComplete = @($unnumbered | Where-Object progress -CEQ 'COMPLETE').Count
$unnumberedPartial = @($unnumbered | Where-Object progress -CEQ 'PARTIAL').Count
$unnumberedOpen = @($unnumbered | Where-Object progress -CEQ 'OPEN').Count

Write-Output (
    "LEDGERS_OK statements=$($statements.Count) equations=$($equations.Count) " +
    "unnumbered=$($unnumbered.Count) " +
    "statement_statuses=${statementProved}_proved+${statementPartial}_partial+" +
    "${statementUnformalized}_unformalized " +
    "equation_statuses=${equationProved}_proved+${equationDefinition}_definition+" +
    "${equationPartial}_partial+${equationOpen}_open " +
    "unnumbered_statuses=${unnumberedProved}_proved+${unnumberedBlocked}_blocked " +
    "unnumbered_progress=${unnumberedComplete}_complete+${unnumberedPartial}_partial+" +
    "${unnumberedOpen}_open " +
    'ordinal_case_sensitive=true statuses=true paths=true declarations=true inputs=true'
)
