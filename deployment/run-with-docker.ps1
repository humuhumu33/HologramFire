# Atlas-12288 Docker Runner Script
# This script runs the Atlas-12288 project using Docker

Write-Host "=== Atlas-12288 Phase 0 - Docker Runner ===" -ForegroundColor Green

# Check if Docker is available
try {
    $dockerVersion = docker --version 2>$null
    if ($LASTEXITCODE -ne 0) {
        throw "Docker not found"
    }
    Write-Host "Docker found: $dockerVersion" -ForegroundColor Green
} catch {
    Write-Host "Docker is not installed or not in PATH." -ForegroundColor Red
    Write-Host "Please install Docker Desktop from: https://docker.com/get-started/" -ForegroundColor Yellow
    exit 1
}

# Pull the Node.js image
Write-Host "`n=== Pulling Node.js 22 Alpine image ===" -ForegroundColor Cyan
docker pull node:22-alpine

# Run the commands in a container
Write-Host "`n=== Running Atlas-12288 commands in Docker container ===" -ForegroundColor Cyan
docker run -it --rm -v "${PWD}:/app" -w /app node:22-alpine sh -c "
    echo '=== Installing dependencies ===' &&
    npm install &&
    echo '=== Stamping blueprint fingerprint ===' &&
    npm run stamp:blueprint &&
    echo '=== Running tests ===' &&
    npm test &&
    echo '=== Validating blueprint ===' &&
    npm run validate atlas-12288/blueprint/blueprint.json
"

Write-Host "`n=== Atlas-12288 Phase 0 Complete ===" -ForegroundColor Green
