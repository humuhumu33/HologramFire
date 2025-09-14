#!/usr/bin/env pwsh
# PowerShell wrapper for generating Hologram reports
# Usage: .\tools\reports.ps1

Write-Host "🔥 Generating Hologram reports..." -ForegroundColor Yellow

try {
    python scripts/aggregate_reports.py
    if ($LASTEXITCODE -eq 0) {
        Write-Host "✅ Reports generated successfully!" -ForegroundColor Green
        Write-Host "📊 Open reports/index.html to view the dashboard" -ForegroundColor Cyan
    } else {
        Write-Host "❌ Report generation failed" -ForegroundColor Red
        exit 1
    }
} catch {
    Write-Host "❌ Error: $_" -ForegroundColor Red
    exit 1
}
