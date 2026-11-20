#!/usr/bin/env python3
"""Reproduce the formal coefficient bridge and preserve fresh execution receipts.

Requires the repository's pinned Lean/Lake toolchain and Python 3.11+.
No Mathlib, external Python package, or network access is needed for these checks.
"""

from pathlib import Path
import argparse
import datetime
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
FORMAL = ROOT / "formal" / "universal"
RECEIPTS = ROOT / "evidence" / "current" / "profinite-mock-theta"
MOCK_SMOKE_SUITES = [
    ("third_order", "MockThetaSmoke.lean", "mock-theta-smoke.log"),
    ("fifth_zero", "FifthZeroSmoke.lean", "fifth-zero-smoke.log"),
    ("fifth_one", "FifthOneSmoke.lean", "fifth-one-smoke.log"),
]


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def source_manifest():
    files = sorted(FORMAL.glob("*.lean")) + [
        FORMAL / "check_proofs.py", FORMAL / "lakefile.toml",
        FORMAL / "lake-manifest.json", FORMAL / "lean-toolchain", Path(__file__),
    ]
    return {str(p.relative_to(ROOT)): digest(p) for p in files}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean", default="lean", help="Pinned Lean executable")
    args = parser.parse_args()
    RECEIPTS.mkdir(parents=True, exist_ok=True)
    # A failed attempt must not leave an older success as its current receipt.
    for name in ["execution.json", "verification.json", "verification.log",
                 "proof-audit.log", "lake-build.log", "closure-smoke.log",
                 *(log for _, _, log in MOCK_SMOKE_SUITES)]:
        (RECEIPTS / name).unlink(missing_ok=True)

    receipt = {
        "status": "RUNNING",
        "started_at_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
        "source_base_commit": subprocess.check_output(
            ["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip(),
        "scope": "Formal coefficients, compatible residue tuples, finite transforms, and arithmetic observation criteria",
        "commands": [],
    }
    try:
        executable = shutil.which(args.lean)
        if executable is None:
            raise RuntimeError("Lean executable not found: " + args.lean)
        lean = Path(executable).absolute()
        lake = lean.parent / "lake"
        if not lake.is_file():
            raise RuntimeError("Supply a pinned Lean installation with Lake in the same bin directory")
        env = os.environ.copy()
        env["PATH"] = str(lean.parent) + os.pathsep + env.get("PATH", "")
        receipt["toolchain"] = (FORMAL / "lean-toolchain").read_text().strip()
        receipt["lean_version"] = subprocess.check_output(
            [str(lean), "--version"], cwd=FORMAL, env=env, text=True).strip()
        receipt["lean_executable_sha256"] = digest(lean)
        receipt["lake_executable_sha256"] = digest(lake)
        receipt["python_version"] = sys.version.split()[0]
        before = source_manifest()
        receipt["source_sha256"] = before

        commands = [
            ([sys.executable, "check_proofs.py", "--lean", str(lean)],
             ["python3", "check_proofs.py", "--lean", "lean"], "proof-audit.log"),
            ([str(lake), "build"], ["lake", "build"], "lake-build.log"),
            ([str(lake), "env", "lean", "ClosureSmoke.lean"],
             ["lake", "env", "lean", "ClosureSmoke.lean"], "closure-smoke.log"),
        ]
        for _, module, log in MOCK_SMOKE_SUITES:
            commands.append(([str(lake), "env", "lean", module],
                             ["lake", "env", "lean", module], log))
        for argv, portable, log_name in commands:
            started = time.monotonic()
            with (RECEIPTS / log_name).open("w") as out:
                result = subprocess.run(argv, cwd=FORMAL, env=env,
                                        stdout=out, stderr=subprocess.STDOUT)
            output = (RECEIPTS / log_name).read_text()
            warning_or_error = bool(re.search(r"\b(?:error|warning):", output))
            receipt["commands"].append({
                "portable_reproduction_command": portable,
                "working_directory": "formal/universal",
                "log": log_name,
                "exit_code": result.returncode,
                "compiler_warning_or_error": warning_or_error,
                "seconds": round(time.monotonic() - started, 3),
                "sha256": digest(RECEIPTS / log_name),
            })
            if result.returncode or warning_or_error:
                raise RuntimeError("Check failed; inspect " + log_name)
            if log_name == "proof-audit.log":
                for name in ("verification.json", "verification.log"):
                    shutil.copy2(FORMAL / name, RECEIPTS / name)
            print("PASS:", " ".join(portable), flush=True)

        if before != source_manifest():
            raise RuntimeError("Formal sources changed during verification; rerun on a stable snapshot")
        verification = json.loads((RECEIPTS / "verification.json").read_text())
        receipt["theorem_declarations"] = verification["theorem_declarations"]
        receipt["profinite_mock_theta_declarations"] = verification["profinite_mock_theta_declarations"]
        receipt["axiom_free_declarations"] = verification["axiom_free_declarations"]
        counts = {}
        for suite, _, log in MOCK_SMOKE_SUITES:
            output = (RECEIPTS / log).read_text()
            totals = re.findall(r"^Total: ([1-9]\d*) exact assertions\.?$", output, re.M)
            if len(totals) != 1:
                raise RuntimeError(f"{log} must report one positive assertion total")
            counts[suite] = int(totals[0])
        receipt["mock_theta_smoke_assertions"] = counts["third_order"]
        receipt["mock_theta_assertions_by_suite"] = counts
        receipt["total_mock_theta_smoke_assertions"] = sum(counts.values())
        receipt["status"] = "PASS"
    except Exception as exc:
        receipt["status"] = "FAIL"
        receipt["error"] = str(exc)
        raise
    finally:
        receipt["finished_at_utc"] = datetime.datetime.now(datetime.timezone.utc).isoformat()
        (RECEIPTS / "execution.json").write_text(json.dumps(receipt, indent=2) + "\n")


if __name__ == "__main__":
    main()
