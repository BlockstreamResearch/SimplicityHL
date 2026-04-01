$ErrorActionPreference = "Stop"

function Invoke-Cargo {
    & cargo run -- @args
    if ($LASTEXITCODE -ne 0) { exit $LASTEXITCODE }
}

$examplesDir = Join-Path $PSScriptRoot "examples"
$simfFiles = Get-ChildItem -Path $examplesDir -Filter "*.simf" | Sort-Object Name

foreach ($simf in $simfFiles) {
    $base = $simf.BaseName
    $argsFile = Join-Path $examplesDir "$base.args"
    $witFiles = Get-ChildItem -Path $examplesDir -Filter "*.wit" |
        Where-Object { $_.Name -like "$base.*" } |
        Sort-Object Name

    $baseArgs = @($simf.FullName, "--deny-warnings")
    if (Test-Path $argsFile) {
        $baseArgs += "-a", $argsFile
    }

    # Run without witness
    Write-Host "`n=== $base (no witness) ===" -ForegroundColor Cyan
    Invoke-Cargo @baseArgs

    # Run once per .wit file
    foreach ($wit in $witFiles) {
        Write-Host "`n=== $base + $($wit.Name) ===" -ForegroundColor Cyan
        $witArgs = $baseArgs + @("-w", $wit.FullName)
        Invoke-Cargo @witArgs
    }
}
