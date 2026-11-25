param(
    [string]$Python = 'python'
)

$ErrorActionPreference = 'Stop'
$videoRoot = $PSScriptRoot
$toolsRoot = Join-Path $videoRoot '.tools'
$runtimeRoot = Join-Path $toolsRoot 'tiny-voca'
$speechRevision = 'd7c5c01f9d6b606c787cda357156ba9389923f57'
$expectedWeightsHash = '8436ad1c9b57c3533c925588a1b3563f906079a89c081ac0bec9f31ad6e28653'
$pythonEnvironment = Join-Path $videoRoot '.venv'
$pythonExecutable = Join-Path $pythonEnvironment 'Scripts/python.exe'

Get-Command node, ffmpeg -ErrorAction Stop | Out-Null
New-Item -ItemType Directory -Force -Path $toolsRoot | Out-Null
if (-not (Test-Path -LiteralPath $pythonExecutable)) {
    & $Python -m venv $pythonEnvironment
    if ($LASTEXITCODE) { throw 'Creating the video Python environment failed.' }
}
& $pythonExecutable -m pip install --disable-pip-version-check -r (Join-Path $videoRoot 'requirements.txt')
if ($LASTEXITCODE) { throw 'Installing Manim failed.' }

if (-not (Test-Path -LiteralPath $runtimeRoot)) {
    git clone --quiet https://github.com/n4ze3m/tiny-voca.git $runtimeRoot
    if ($LASTEXITCODE) { throw 'Downloading tiny-voca failed.' }
}
git -C $runtimeRoot checkout --quiet $speechRevision
if ($LASTEXITCODE) { throw 'Selecting the pinned tiny-voca revision failed.' }

$weightsPath = Join-Path $runtimeRoot 'js/tiny-voca.gguf'
if (-not (Test-Path -LiteralPath $weightsPath)) {
    Invoke-WebRequest -UseBasicParsing -Uri 'https://huggingface.co/n4ze3m/tiny-voca/resolve/main/gguf/tiny-voca-js.gguf' -OutFile $weightsPath
}
$weightsHash = (Get-FileHash -Algorithm SHA256 -LiteralPath $weightsPath).Hash.ToLowerInvariant()
if ($weightsHash -ne $expectedWeightsHash) {
    throw "The tiny-voca model differs from the pinned SHA256: $weightsHash"
}
Write-Output "Manim 0.22.1 and tiny-voca M2 are installed. Model SHA256: $weightsHash"
