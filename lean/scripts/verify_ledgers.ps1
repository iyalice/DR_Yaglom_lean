$ErrorActionPreference = 'Stop'
& python (Join-Path $PSScriptRoot 'verify_revision.py')
if ($LASTEXITCODE -ne 0) { exit $LASTEXITCODE }
