#!/usr/bin/env pwsh
# PowerShell wrapper for performance budget checking
# Usage: .\tools\perf-gate.ps1

Write-Host "🚀 Checking performance budgets..." -ForegroundColor Yellow

try {
    python scripts/check_perf_budget.py
    if ($LASTEXITCODE -eq 0) {
        Write-Host "✅ Performance budgets OK!" -ForegroundColor Green
    } else {
        Write-Host "❌ Performance budget violations detected" -ForegroundColor Red
        exit 1
    }
} catch {
    Write-Host "❌ Error: $_" -ForegroundColor Red
    exit 1
}
