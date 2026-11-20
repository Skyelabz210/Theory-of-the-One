#!/usr/bin/env python3
"""Rebuild the local analytic package against the locked dependencies and audit its checked environment."""

import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import tomllib


ROOT = Path(__file__).resolve().parent
OUT = ROOT / ".lake" / "verification"
CORE = ROOT.parent.parent / "formal" / "universal"


def run(*args, log=None, cwd=ROOT):
    if log:
        path = OUT / log
        with path.open("w") as stream:
            result = subprocess.run(args, cwd=cwd, stdout=stream, stderr=subprocess.STDOUT)
        output = path.read_text()
    else:
        result = subprocess.run(args, cwd=cwd, text=True, stdout=subprocess.PIPE,
                                stderr=subprocess.STDOUT)
        output = result.stdout
    if result.returncode:
        raise SystemExit(f"{' '.join(args)} failed ({result.returncode})\n{output}")
    return output.strip()


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def package_sources():
    files = [*ROOT.glob("*.lean"), ROOT / "lake-manifest.json", ROOT / "lakefile.toml",
             ROOT / "lean-toolchain", Path(__file__).resolve()]
    return {p.name: sha256(p) for p in sorted(files)}


def core_sources(modules):
    """Record the core checkout's actual transitive source inputs to the local analytic modules."""
    pending = [ROOT / f"{name}.lean" for name in modules]
    core = set()
    while pending:
        for module in re.findall(r"^import ([\w.]+)", pending.pop().read_text(), re.MULTILINE):
            source = CORE.joinpath(*module.split(".")).with_suffix(".lean")
            if source.exists() and source not in core:
                core.add(source)
                pending.append(source)
    return {p.name: sha256(p) for p in sorted(core)}


def main():
    os.environ.pop("LEAN_PATH", None)
    os.environ["MATHLIB_NO_CACHE_ON_UPDATE"] = "1"
    OUT.mkdir(parents=True, exist_ok=True)
    receipt = OUT / "receipt.json"
    for prior in (receipt, OUT / "build.log", OUT / "audit.log"):
        prior.unlink(missing_ok=True)
    source_hashes = package_sources()
    config = tomllib.loads((ROOT / "lakefile.toml").read_text())
    modules = config["lean_lib"][0]["roots"]
    core_hashes = core_sources(modules)
    manifest = ROOT / "lake-manifest.json"
    lock_hash = sha256(manifest)
    locked = {p["name"]: p for p in json.loads(manifest.read_bytes())["packages"]}
    mathlib = next(d for d in config["require"] if d["name"] == "mathlib")
    if (mathlib["git"], mathlib["rev"]) != (locked["mathlib"]["url"], locked["mathlib"]["rev"]):
        raise SystemExit("Mathlib manifest and lakefile disagree")
    if (ROOT / locked["k_elimination_universal"]["dir"]).resolve() != CORE:
        raise SystemExit("Manifest points outside the intended core source directory")
    lean = run("lake", "env", "lean", "--version").splitlines()[-1]
    lake = run("lake", "--version")
    version = (ROOT / "lean-toolchain").read_text().strip().split(":v")[1]
    if not lean.startswith(f"Lean (version {version},") or f"(Lean version {version})" not in lake:
        raise SystemExit(f"Wrong toolchain for {version}\n{lean}\n{lake}")
    pins = {}
    for name, dep in locked.items():
        if dep["type"] != "git":
            continue
        repo = ROOT / ".lake" / "packages" / name
        if run("git", "rev-parse", "HEAD", cwd=repo) != dep["rev"] or run("git", "status", "--porcelain", cwd=repo):
            raise SystemExit(f"{name} differs from its locked source")
        pins[name] = dep["rev"]
    upstream = ROOT / ".lake" / "packages" / "mathlib" / "lake-manifest.json"
    for dep in json.loads(upstream.read_bytes())["packages"]:
        actual = locked[dep["name"]]
        if (actual["url"], actual["rev"]) != (dep["url"], dep["rev"]):
            raise SystemExit(f"{dep['name']} differs from Mathlib's committed dependency lock")
    print("Rebuilding the local analytic modules. Progress is in .lake/verification/build.log", flush=True)
    run("lake", "clean", "MockThetaAnalytic")
    run("lake", "--rehash", "--wfail", "build", "MockThetaAnalytic", log="build.log")
    report = run("lake", "env", "lean", "-DwarningAsError=true", "AnalyticAudit.lean", log="audit.log")
    counts = {m: (int(t), int(d)) for m, t, d in re.findall(r"^MODULE (\w+) (\d+) (\d+)$", report, re.M)}
    decls = {m: {} for m in modules}
    for module, name, deps in re.findall(r"^THEOREM (\w+) (\S+) \[([^]]*)\]$", report, re.M):
        decls[module][name] = deps.split(",") if deps else []
    if (set(modules) != counts.keys() or any(len(decls[m]) != counts[m][0] for m in modules)
            or report.splitlines()[-1] != f"PASS analytic audit: {sum(d for t, d in counts.values())} declarations in {len(modules)} modules"):
        raise SystemExit("Missing or incomplete analytic axiom audit")
    if sha256(manifest) != lock_hash:
        raise SystemExit("Lake changed the dependency manifest")
    if package_sources() != source_hashes or core_sources(modules) != core_hashes:
        raise SystemExit("Analytic or local core inputs changed during verification")
    result = {"status": "PASS", "command": "python3 verify_analytic.py", "lean": lean, "lake": lake,
              "source_sha256": source_hashes, "core_source_sha256": core_hashes,
              "locked_git_revisions": dict(sorted(pins.items())),
              "module_kernel_counts": {m: {"theorems": t, "declarations": d} for m, (t, d) in counts.items()},
              "theorem_axioms": {m: dict(sorted(t.items())) for m, t in decls.items()}}
    receipt.write_text(json.dumps(result, indent=2) + "\n")
    print(report)
    print(f"Receipt: {receipt.relative_to(ROOT)}")


if __name__ == "__main__":
    main()
