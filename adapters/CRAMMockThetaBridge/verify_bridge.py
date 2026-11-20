"""Fresh Lake build, kernel audit, executable smoke and reproducible verification receipt."""

import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import tomllib


ROOT = Path(__file__).resolve().parent
OUT = ROOT / ".lake" / "verification"
LOCK = ROOT / "lake-manifest.json"


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def run(*args, log=None, cwd=ROOT):
    result = subprocess.run(args, cwd=cwd, text=True, stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT)
    if log:
        (OUT / log).write_text(result.stdout)
    if result.returncode:
        raise SystemExit(f"{' '.join(args)} failed ({result.returncode})\n{result.stdout}")
    return result.stdout.strip()


def packages(path):
    return {p["name"]: p for p in json.loads(path.read_bytes())["packages"]}


def check_sources(locked, direct):
    for name, package in locked.items():
        repo = ROOT / ".lake" / "packages" / name
        if run("git", "rev-parse", "HEAD", cwd=repo) != package["rev"]:
            raise SystemExit(f"{name} is not at its locked Git revision")
        if run("git", "status", "--porcelain", cwd=repo):
            raise SystemExit(f"{name} has modified or untracked sources")
    for dependency in direct:
        name = dependency["name"]
        entry = locked[name]
        if (entry["url"], entry["rev"], entry["subDir"]) != (
                dependency["git"], dependency["rev"], dependency["subDir"]):
            raise SystemExit(f"{name} manifest and lakefile pins differ")
        package = ROOT / ".lake" / "packages" / name / entry["subDir"]
        for child, expected in packages(package / "lake-manifest.json").items():
            actual = locked[child]
            if (actual["rev"], actual["url"]) != (expected["rev"], expected["url"]):
                raise SystemExit(f"{child} differs from {name}'s committed dependency lock")


def main():
    os.environ.pop("LEAN_PATH", None)
    os.environ["MATHLIB_NO_CACHE_ON_UPDATE"] = "1"
    OUT.mkdir(parents=True, exist_ok=True)
    receipt = OUT / "receipt.json"
    receipt.unlink(missing_ok=True)
    locked = packages(LOCK)
    lock_hash = sha256(LOCK)
    direct = tomllib.loads((ROOT / "lakefile.toml").read_text())["require"]
    pin = (ROOT / "lean-toolchain").read_text().strip().split(":v")[1]
    lake = run("lake", "--version")
    lean = run("lake", "env", "lean", "--version").splitlines()[-1]
    if not lean.startswith(f"Lean (version {pin},") or f"(Lean version {pin})" not in lake:
        raise SystemExit(f"Wrong toolchain for {pin}\n{lean}\n{lake}")
    check_sources(locked, direct)
    print("Rebuilding the adapter and both source packages from their locked revisions", flush=True)
    run("lake", "clean", "CRAMMockThetaBridge", *(d["name"] for d in direct))
    run("lake", "--no-cache", "--wfail", "build", "MockThetaAdapter", log="build.log")
    audit = run("lake", "env", "lean", "-DwarningAsError=true", "BridgeAudit.lean", log="audit.log")
    summary = re.findall(r"^PASS bridge audit: (\d+) kernel declarations, (\d+) required declarations$",
                         audit, re.MULTILINE)
    rows = re.findall(r"^AUDIT ([\w.]+) \[([^]]*)\]$", audit, re.MULTILINE)
    if len(summary) != 1 or not rows or len(rows) != len(dict(rows)) or len(rows) != int(summary[0][1]):
        raise SystemExit("Missing or incomplete bridge axiom audit")
    smoke = run("lake", "env", "lean", "-DwarningAsError=true", "BridgeSmoke.lean", log="smoke.log")
    labels = re.findall(r"^PASS (?!bridge smoke:)(.+)$", smoke, re.MULTILINE)
    counts = re.findall(r"^PASS bridge smoke: (\d+) exact assertions$", smoke, re.MULTILINE)
    if len(counts) != 1 or not labels or len(labels) != int(counts[0]) or len(set(labels)) != len(labels):
        raise SystemExit("Missing or incomplete numerical smoke results")
    if sha256(LOCK) != lock_hash:
        raise SystemExit("Lake changed the committed dependency manifest")
    sources = [*ROOT.glob("*.lean"), LOCK, ROOT / "lakefile.toml", ROOT / "lean-toolchain",
               ROOT / "verify_bridge.py", ROOT / "verify_bridge.sh"]
    result = {"status": "PASS", "command": "./verify_bridge.sh", "lean": lean, "lake": lake,
              "source_sha256": {p.name: sha256(p) for p in sorted(sources)},
              "locked_git_revisions": {n: p["rev"] for n, p in sorted(locked.items())},
              "fresh_build_packages": ["CRAMMockThetaBridge", *(d["name"] for d in direct)],
              "kernel_declarations_audited": int(summary[0][0]),
              "required_declaration_axioms": {n: a.split(",") if a else [] for n, a in sorted(rows)},
              "smoke_assertions": len(labels), "smoke_checks": labels}
    receipt.write_text(json.dumps(result, indent=2) + "\n")
    print(audit, smoke, f"Receipt: {receipt.relative_to(ROOT)}", sep="\n")


if __name__ == "__main__":
    main()
