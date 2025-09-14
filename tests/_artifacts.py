import json, time
from pathlib import Path

def log_event(suite: str, event: str, payload: dict):
    """
    Log an event to the JSONL audit trail.
    
    Security note: If payload contains sensitive data (headers, tokens, etc.),
    redact them before calling this function:
    
    # Example redaction:
    safe_payload = {k: v for k, v in payload.items() 
                   if k not in ['authorization', 'x-api-key', 'cookie']}
    """
    root = Path("reports/e2e"); root.mkdir(parents=True, exist_ok=True)
    row = {"ts": int(time.time()), "suite": suite, "event": event, **payload}
    with (root / "events.jsonl").open("a", encoding="utf-8") as f:
        f.write(json.dumps(row, separators=(",", ":")) + "\n")
    return row
