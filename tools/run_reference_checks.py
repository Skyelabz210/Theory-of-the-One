#!/usr/bin/env python3
"""Run the unchanged supplied checker in an isolated temporary directory."""
import hashlib
import json
import platform
import shutil
import subprocess
import sys
import tempfile
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / 'foundations/theory_of_the_one/verify_residue_core.py'
OUT = ROOT / 'evidence/current'

def main():
    OUT.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix='cram-reference-') as temp:
        script = Path(temp) / SOURCE.name
        shutil.copyfile(SOURCE, script)
        result = subprocess.run([sys.executable, str(script)], capture_output=True, text=True)
        (OUT / 'reference-check.log').write_text(result.stdout + result.stderr)
        report = script.with_name('residue_core_verification.json')
        if report.exists():
            shutil.copyfile(report, OUT / report.name)
        receipt = {
            'command': 'python3 tools/run_reference_checks.py',
            'executed_at_utc': datetime.now(timezone.utc).isoformat(),
            'python': platform.python_version(),
            'exit_code': result.returncode,
            'source_sha256': hashlib.sha256(SOURCE.read_bytes()).hexdigest(),
            'scope': 'Supplied mathematical reference checker; not production execution or a Lean build'
        }
        (OUT / 'execution.json').write_text(json.dumps(receipt, indent=2) + '\n')
        print(result.stdout, end='')
        if result.stderr:
            print(result.stderr, file=sys.stderr, end='')
        return result.returncode

if __name__ == '__main__':
    raise SystemExit(main())
