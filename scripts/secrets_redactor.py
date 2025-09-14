#!/usr/bin/env python3
"""
Secrets redaction utility for safe logging.
Redacts sensitive patterns from log output.
"""
import re
import sys
from typing import List, Pattern

# Patterns to redact
REDACTION_PATTERNS: List[Pattern] = [
    re.compile(r'Bearer\s+[A-Za-z0-9\-_]+', re.IGNORECASE),
    re.compile(r'api_key=["\']?[A-Za-z0-9\-_]+["\']?', re.IGNORECASE),
    re.compile(r'Set-Cookie:\s*[^;]+', re.IGNORECASE),
    re.compile(r'Authorization:\s*[A-Za-z0-9\-_]+', re.IGNORECASE),
    re.compile(r'token=["\']?[A-Za-z0-9\-_]+["\']?', re.IGNORECASE),
    re.compile(r'password=["\']?[^"\'\s]+["\']?', re.IGNORECASE),
    re.compile(r'secret=["\']?[A-Za-z0-9\-_]+["\']?', re.IGNORECASE),
    re.compile(r'private_key=["\']?[A-Za-z0-9\-_]+["\']?', re.IGNORECASE),
    re.compile(r'access_token=["\']?[A-Za-z0-9\-_]+["\']?', re.IGNORECASE),
    re.compile(r'refresh_token=["\']?[A-Za-z0-9\-_]+["\']?', re.IGNORECASE),
    re.compile(r'session_id=["\']?[A-Za-z0-9\-_]+["\']?', re.IGNORECASE),
    re.compile(r'cookie=["\']?[^"\']+["\']?', re.IGNORECASE),
    re.compile(r'x-api-key=["\']?[A-Za-z0-9\-_]+["\']?', re.IGNORECASE),
    re.compile(r'x-auth-token=["\']?[A-Za-z0-9\-_]+["\']?', re.IGNORECASE),
]

def redact_secrets(text: str) -> str:
    """Redact sensitive information from text."""
    redacted = text
    for pattern in REDACTION_PATTERNS:
        redacted = pattern.sub(lambda m: m.group(0).split()[0] + " [REDACTED]", redacted)
    return redacted

def safe_print(*args, **kwargs):
    """Print with secrets redaction."""
    # Convert all arguments to strings and redact
    safe_args = [redact_secrets(str(arg)) for arg in args]
    print(*safe_args, **kwargs)

def safe_log(message: str, level: str = "INFO"):
    """Log with secrets redaction."""
    safe_print(f"[{level}] {message}")

def check_file_for_secrets(file_path: str) -> bool:
    """Check if file contains secrets."""
    try:
        with open(file_path, 'r', encoding='utf-8') as f:
            content = f.read()
        
        # Check for secrets
        for pattern in REDACTION_PATTERNS:
            if pattern.search(content):
                return True
        
        return False
    except Exception:
        return False

def main():
    """Main function."""
    if len(sys.argv) > 1 and sys.argv[1] == "--pre-commit":
        # Pre-commit mode
        if len(sys.argv) < 3:
            print("❌ No files provided for pre-commit check")
            sys.exit(1)
        
        files_to_check = sys.argv[2:]
        secrets_found = False
        
        for file_path in files_to_check:
            if check_file_for_secrets(file_path):
                print(f"🚨 Secrets detected in {file_path}")
                secrets_found = True
        
        if secrets_found:
            print("❌ Secrets detected in files. Please remove or redact them.")
            sys.exit(1)
        else:
            print("✅ No secrets detected in files")
            sys.exit(0)
    
    else:
        # Test mode
        test_strings = [
            "Bearer eyJhbGciOiJIUzI1NiIsInR5cCI6IkpXVCJ9...",
            "api_key=sk-1234567890abcdef",
            "Set-Cookie: session_id=abc123; path=/",
            "Authorization: Basic dXNlcjpwYXNzd29yZA==",
            "token=ghp_1234567890abcdef",
            'password="secret123"',
            "secret=my_secret_key"
        ]
        
        print("Testing secrets redaction:")
        for test in test_strings:
            print(f"Original: {test}")
            print(f"Redacted: {redact_secrets(test)}")
            print()

if __name__ == "__main__":
    main()