#!/usr/bin/env python3
"""
Slack/Teams Notifier for Hologram Pipeline
Posts p95s + last E2E CID/name using ci_summary.py data.
"""
import json
import os
import sys
import requests
from pathlib import Path
from typing import Dict, Any, Optional

# Import our existing CI summary functionality
from scripts.ci_summary import read_perf_best, read_e2e_highlights

def format_slack_message(perf_data: Dict[str, float], e2e_data: Dict[str, Any], status: str) -> Dict[str, Any]:
    """Format message for Slack."""
    # Determine color based on status
    color_map = {
        "pass": "good",
        "fail": "danger", 
        "running": "warning",
        "unknown": "#808080"
    }
    color = color_map.get(status, "#808080")
    
    # Build performance section
    perf_text = ""
    if perf_data:
        perf_lines = []
        for metric, p95 in sorted(perf_data.items()):
            perf_lines.append(f"• `{metric}`: {p95:.1f}ms")
        perf_text = "\n".join(perf_lines)
    else:
        perf_text = "• No performance data"
    
    # Build E2E section
    e2e_text = ""
    if e2e_data:
        e2e_lines = []
        for event_type, event in sorted(e2e_data.items()):
            cid = event.get("cid", "N/A")[:12] + "..." if event.get("cid") else "N/A"
            name = event.get("name", "N/A")
            e2e_lines.append(f"• **{event_type}**: `{name}` - CID: `{cid}`")
        e2e_text = "\n".join(e2e_lines)
    else:
        e2e_text = "• No E2E events"
    
    # Build message
    message = {
        "attachments": [
            {
                "color": color,
                "title": f"🔥 Hologram Pipeline - {status.upper()}",
                "title_link": f"https://github.com/{os.getenv('GITHUB_REPOSITORY', 'your-org/hologram')}/actions",
                "fields": [
                    {
                        "title": "📊 Performance (Best p95)",
                        "value": perf_text,
                        "short": False
                    },
                    {
                        "title": "🚀 E2E Highlights", 
                        "value": e2e_text,
                        "short": False
                    }
                ],
                "footer": "Hologram Pipeline",
                "ts": int(os.getenv("GITHUB_RUN_ID", "0"))
            }
        ]
    }
    
    return message

def format_teams_message(perf_data: Dict[str, float], e2e_data: Dict[str, Any], status: str) -> Dict[str, Any]:
    """Format message for Microsoft Teams."""
    # Determine color based on status
    color_map = {
        "pass": "00ff00",
        "fail": "ff0000",
        "running": "ffff00", 
        "unknown": "808080"
    }
    color = color_map.get(status, "808080")
    
    # Build performance section
    perf_text = ""
    if perf_data:
        perf_lines = []
        for metric, p95 in sorted(perf_data.items()):
            perf_lines.append(f"• **{metric}**: {p95:.1f}ms")
        perf_text = "<br>".join(perf_lines)
    else:
        perf_text = "• No performance data"
    
    # Build E2E section
    e2e_text = ""
    if e2e_data:
        e2e_lines = []
        for event_type, event in sorted(e2e_data.items()):
            cid = event.get("cid", "N/A")[:12] + "..." if event.get("cid") else "N/A"
            name = event.get("name", "N/A")
            e2e_lines.append(f"• **{event_type}**: `{name}` - CID: `{cid}`")
        e2e_text = "<br>".join(e2e_lines)
    else:
        e2e_text = "• No E2E events"
    
    # Build message
    message = {
        "@type": "MessageCard",
        "@context": "http://schema.org/extensions",
        "themeColor": color,
        "summary": f"Hologram Pipeline - {status.upper()}",
        "sections": [
            {
                "activityTitle": f"🔥 Hologram Pipeline - {status.upper()}",
                "activitySubtitle": f"GitHub Actions Run: {os.getenv('GITHUB_RUN_ID', 'Unknown')}",
                "activityImage": "https://github.com/favicon.ico",
                "facts": [
                    {
                        "name": "📊 Performance (Best p95)",
                        "value": perf_text
                    },
                    {
                        "name": "🚀 E2E Highlights",
                        "value": e2e_text
                    }
                ],
                "markdown": True
            }
        ],
        "potentialAction": [
            {
                "@type": "OpenUri",
                "name": "View in GitHub Actions",
                "targets": [
                    {
                        "os": "default",
                        "uri": f"https://github.com/{os.getenv('GITHUB_REPOSITORY', 'your-org/hologram')}/actions"
                    }
                ]
            }
        ]
    }
    
    return message

def send_slack_message(webhook_url: str, message: Dict[str, Any]) -> bool:
    """Send message to Slack webhook."""
    try:
        response = requests.post(webhook_url, json=message, timeout=10)
        response.raise_for_status()
        return True
    except Exception as e:
        print(f"❌ Failed to send Slack message: {e}")
        return False

def send_teams_message(webhook_url: str, message: Dict[str, Any]) -> bool:
    """Send message to Teams webhook."""
    try:
        response = requests.post(webhook_url, json=message, timeout=10)
        response.raise_for_status()
        return True
    except Exception as e:
        print(f"❌ Failed to send Teams message: {e}")
        return False

def determine_status(perf_data: Dict[str, float], e2e_data: Dict[str, Any]) -> str:
    """Determine overall pipeline status."""
    # Check if we have data
    if not perf_data and not e2e_data:
        return "unknown"
    
    # Check E2E success
    if e2e_data:
        # Look for successful pipeline events
        success_events = {"publish", "install", "use"}
        found_events = set(e2e_data.keys())
        if not success_events.intersection(found_events):
            return "fail"
    
    # Check performance (simplified - in production, check against budgets)
    if perf_data:
        # If we have performance data, assume pass for now
        # In production, you'd check against actual SLO budgets
        pass
    
    return "pass"

def main():
    """Main function."""
    if len(sys.argv) < 2:
        print("Usage: python scripts/slack_notifier.py [slack|teams] [webhook_url]")
        print("Environment variables:")
        print("  SLACK_WEBHOOK_URL - Slack webhook URL")
        print("  TEAMS_WEBHOOK_URL - Teams webhook URL")
        return
    
    platform = sys.argv[1].lower()
    webhook_url = sys.argv[2] if len(sys.argv) > 2 else None
    
    # Get webhook URL from environment if not provided
    if not webhook_url:
        if platform == "slack":
            webhook_url = os.getenv("SLACK_WEBHOOK_URL")
        elif platform == "teams":
            webhook_url = os.getenv("TEAMS_WEBHOOK_URL")
    
    if not webhook_url:
        print(f"❌ No webhook URL provided for {platform}")
        return
    
    # Get performance and E2E data
    perf_data = read_perf_best()
    e2e_data = read_e2e_highlights()
    
    # Determine status
    status = determine_status(perf_data, e2e_data)
    
    # Format and send message
    if platform == "slack":
        message = format_slack_message(perf_data, e2e_data, status)
        success = send_slack_message(webhook_url, message)
    elif platform == "teams":
        message = format_teams_message(perf_data, e2e_data, status)
        success = send_teams_message(webhook_url, message)
    else:
        print(f"❌ Unknown platform: {platform}")
        return
    
    if success:
        print(f"✅ {platform.title()} notification sent successfully")
    else:
        print(f"❌ Failed to send {platform.title()} notification")
        sys.exit(1)

if __name__ == "__main__":
    main()
