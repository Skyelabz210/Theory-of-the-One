"""Reproduce stale-receipt failure controls in isolated temporary copies."""
from pathlib import Path
import argparse
import hashlib
import json
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[3]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--lean', default='lean')
    args = parser.parse_args()
    lean = shutil.which(args.lean)
    if lean is None:
        raise RuntimeError('Pinned Lean executable not found')
    results = []
    with tempfile.TemporaryDirectory(prefix='reference-failure-control-') as directory:
        temp = Path(directory)
        for folder in ['tools', 'foundations/theory_of_the_one', 'evidence/current']:
            (temp / folder).mkdir(parents=True)
        runner = ROOT / 'tools/run_reference_checks.py'
        shutil.copy2(runner, temp / 'tools/run_reference_checks.py')
        (temp / 'foundations/theory_of_the_one/verify_residue_core.py').write_text(
            'raise RuntimeError("injected checker failure before report")\n')
        stale = temp / 'evidence/current/residue_core_verification.json'
        stale.write_text('{"status":"PASS","from":"previous run"}\n')
        result = subprocess.run([sys.executable, str(temp / 'tools/run_reference_checks.py')],
                                capture_output=True, text=True)
        receipt = json.loads((temp / 'evidence/current/execution.json').read_text())
        assert result.returncode != 0 and receipt['exit_code'] != 0 and not stale.exists()
        assert (temp / 'evidence/current/reference-check.log').is_file()
        results.append({'runner': 'tools/run_reference_checks.py',
                        'runner_sha256': hashlib.sha256(runner.read_bytes()).hexdigest(),
                        'exit_code': result.returncode, 'stale_pass_present': stale.exists(),
                        'failure_receipt_exit_code': receipt['exit_code'], 'status': 'PASS'})
    with tempfile.TemporaryDirectory(prefix='lean-failure-control-') as directory:
        temp = Path(directory)
        formal = ROOT / 'formal/universal'
        for source in formal.iterdir():
            if source.is_file() and (source.suffix in ['.lean', '.py'] or source.name == 'lean-toolchain'):
                shutil.copy2(source, temp / source.name)
        first = temp / 'ExactObservation.lean'
        first.write_text(first.read_text() + '\n#check missing_identifier_for_audit\n')
        stale = temp / 'verification.json'
        stale.write_text('{"status":"PASS","from":"previous run"}\n')
        result = subprocess.run([sys.executable, 'check_proofs.py', '--lean', lean],
                                cwd=temp, capture_output=True, text=True)
        assert result.returncode != 0 and not stale.exists()
        assert 'missing_identifier_for_audit' in (temp / 'verification.log').read_text()
        runner = formal / 'check_proofs.py'
        results.append({'runner': 'formal/universal/check_proofs.py',
                        'runner_sha256': hashlib.sha256(runner.read_bytes()).hexdigest(),
                        'exit_code': result.returncode, 'stale_pass_present': stale.exists(),
                        'new_failure_log_present': True, 'status': 'PASS'})
    report = {'status': 'PASS', 'scope': 'Failure controls; injected source stays in temporary copies',
              'source_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              'controls': results}
    Path(__file__).with_suffix('.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
