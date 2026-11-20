from pathlib import Path
import hashlib
import json
import zipfile

root = Path(__file__).resolve().parent
workspace = root.parent
files = {
    'manuscript/Arbitrary_Moduli_in_CRAM.md': root / 'Arbitrary_Moduli_in_CRAM.md',
    'manuscript/compatible_residue_states.png': root / 'compatible_residue_states.png',
    'central_checks/verify_arbitrary_moduli.py': workspace / 'whitepaper_checks/verify_arbitrary_moduli.py',
    'central_checks/results.json': workspace / 'whitepaper_checks/results.json',
}
for name in [
    'witness_arbitrary_moduli_claims.py',
    'witness_arbitrary_moduli_claims.py.stdout.log',
    'witness_arbitrary_moduli_claims.py.stderr.log',
    'dependent_sister_probe.py',
    'dependent_sister_probe.py.stdout.log',
    'dependent_sister_probe.py.stderr.log',
    'dependent_sister_probe_results.json',
]:
    files['pinned_checks/' + name] = workspace / 'github_arbitrary_verification' / name

manifest = {
    'white_paper': 'Arbitrary Moduli in CRAM',
    'version': '1.0',
    'date': '2026-11-19',
    'repository': 'Skyelabz210/NINE65_v7',
    'revision': '64c1c89b191093dc12cf81b87da5fb1a02c46dc1',
    'source_paths': {
        'pinned_checks/witness_arbitrary_moduli_claims.py': 'scripts/witness_arbitrary_moduli_claims.py',
        'pinned_checks/dependent_sister_probe.py': 'docs/proofs/cram/clarification-evidence-2026-11-17/dependent_sister_probe.py',
    },
    'files': {name: {'bytes': path.stat().st_size, 'sha256': hashlib.sha256(path.read_bytes()).hexdigest()} for name,path in files.items()},
}
readme = '''# Arbitrary Moduli in CRAM reproduction files

Companion to the research white paper prepared for Anthony Diaz, version 1.0,
19 November 2026. The formatted PDF and editable DOCX are separate deliverables.

## Contents

- `manuscript/` contains the full Markdown manuscript with LaTeX equations and its exact compatibility diagram.
- `central_checks/` contains the reproducible 6,246,650-case integer sweep and its recorded result.
- `pinned_checks/` contains exact script copies from the reviewed NINE65 commit, their stdout/stderr receipts, and the dependent-sister result JSON.
- `manifest.json` gives source revision, original repository paths, byte counts, and SHA-256 digests for the supplied files.

## Reproduce the central sweep

Use Python 3.9 or later. The scripts use only the standard library. The recorded
central run used Python 3.12.14 and exact integer arithmetic.

From the extracted archive directory:

```sh
python3 central_checks/verify_arbitrary_moduli.py --output rerun_central_results.json
```

Expected counts are 641,600 arbitrary-anchor quotient queries, 962,400 direct
target projections, and 4,642,650 bounded residue-derived target projections.
The total is 6,246,650 with zero failures. The direct projection suite uses
the oracle Euclidean quotient; the bounded suite derives its temporary quotient
from source residues and a declared interval. The projection checks use the
sufficient quotient modulo b. Minimal quotient precision b/gcd(M,b) is established
by Theorem 2's algebraic proof in the manuscript.

The script's explicit validation remains active under Python optimization.
Runtime paths and Python version fields may differ in a fresh result; compare
the mathematical ranges, counts, and failure fields rather than requiring a
byte-identical rerun receipt.

## Reproduce the pinned supplementary checks

```sh
python3 pinned_checks/witness_arbitrary_moduli_claims.py
python3 pinned_checks/dependent_sister_probe.py --output rerun_dependent_sister_results.json
```

The arbitrary-moduli witness intentionally exhibits failures of older formulas
and verifies corrected formulas. Its exit-zero result is not a statement that
every historical claim passed. Read the named cases in its output.

The dependent-sister probe enumerates all 11,011 pairs for moduli 77 and 143,
finds 1,001 compatible pairs, checks 1,001 common-polynomial updates, and rejects
the deliberately mismatched update. Additional multiplicative-order and root
checks are included in that pinned script.

## Evidence boundaries

These are finite arithmetic checks. They are not a fresh Lean compilation, a
Rust integration run, a performance benchmark, or a cryptographic security
validation. The white paper separately identifies universal mathematical proofs,
maintained formal sources and matching historical receipts, and implementation
source-inspection findings.

The paper's GitHub citations are pinned. Drive references remain source links
subject to the reader's existing access. This archive does not contain copies
of the underlying Drive documents.
'''

out = root / 'Arbitrary_Moduli_in_CRAM_reproduction.zip'
with zipfile.ZipFile(out, 'w', compression=zipfile.ZIP_DEFLATED, compresslevel=9) as archive:
    archive.writestr('README.md', readme)
    archive.writestr('manifest.json', json.dumps(manifest, indent=2) + '\n')
    for name, path in files.items():
        archive.write(path, name)
with zipfile.ZipFile(out) as archive:
    assert archive.testzip() is None
print(json.dumps({'archive': str(out), 'files': len(files)+2, 'bytes': out.stat().st_size}, indent=2))
