#!/usr/bin/env python3
"""Replay original normalized-CRT warmup and Q2 without expensive unrelated sections.

The selected AST statements are compiled unchanged from the hash-pinned source.
The original 9,000 Q1 CRT samples are actually executed, preserving every RNG draw
before Q2. No preceding skipped statement consumes that RNG. Q2 then runs
unchanged. This wrapper does not claim to rerun the tropical checks or Q3.
"""
from contextlib import redirect_stdout
from datetime import datetime, timezone
from pathlib import Path
import ast
import hashlib
import importlib.metadata
import io
import json
import platform
import sys

ROOT = Path(__file__).resolve().parent
SOURCE = ROOT / "source_packet" / "carry_questions.py"
ARCHIVE = ROOT / "source_packet" / "carry_questions_output.txt"
EXPECTED_SHA256 = "498cf7bae0be75298a50af24bcf74aa3fa4ad77e2383e9e46e1f0354e756492a"
PIN = "64c1c89b191093dc12cf81b87da5fb1a02c46dc1"


def section_index(nodes, label):
    for index, node in enumerate(nodes):
        if isinstance(node, ast.Expr) and isinstance(node.value, ast.Call):
            if any(isinstance(arg, ast.Constant) and isinstance(arg.value, str)
                   and label in arg.value for arg in node.value.args):
                return index
    raise AssertionError("Missing section: " + label)


def execute(nodes, namespace):
    module = ast.Module(body=nodes, type_ignores=[])
    exec(compile(module, str(SOURCE), "exec"), namespace)


def main():
    for name in ("carry_q2_results.json", "carry_q2_execution.json", "carry_q2_replay.log"):
        (ROOT / name).unlink(missing_ok=True)
    data = SOURCE.read_bytes()
    assert hashlib.sha256(data).hexdigest() == EXPECTED_SHA256, "source drift"
    nodes = ast.parse(data, filename=str(SOURCE)).body
    warmup_start = next(i for i, n in enumerate(nodes)
                        if isinstance(n, ast.FunctionDef) and n.name == "lanes")
    q2_start = section_index(nodes, "=== Q2.")
    q3_start = section_index(nodes, "=== Q3.")
    prefix, omitted = [], []
    for node in nodes[:warmup_start]:
        keep = isinstance(node, (ast.Import, ast.ImportFrom))
        keep |= isinstance(node, ast.ClassDef) and node.name == "Rng"
        keep |= (isinstance(node, ast.Assign)
                 and any(isinstance(t, ast.Name) and t.id == "R" for t in node.targets))
        (prefix if keep else omitted).append(node)
    assert not any(isinstance(n, ast.Name) and n.id == "R"
                   for node in omitted for n in ast.walk(node)), "omitted RNG access"
    assert len([n for n in prefix if isinstance(n, ast.ClassDef)]) == 1
    selected = prefix + nodes[warmup_start:q3_start]
    selected_dump = "\n".join(ast.dump(n, include_attributes=False) for n in selected)
    namespace = {"__name__": "__targeted_packet_replay__"}
    captured = io.StringIO()
    started = datetime.now(timezone.utc).isoformat()
    with redirect_stdout(captured):
        execute(prefix, namespace)
        execute(nodes[warmup_start:q2_start], namespace)
        warmup_cases, warmup_violations = namespace["n"], namespace["bad"]
        state_before_q2 = namespace["R"].s
        assert warmup_cases == 9000 and warmup_violations == 0
        execute(nodes[q2_start:q3_start], namespace)
    output = captured.getvalue()
    (ROOT / "carry_q2_replay.log").write_text(output)
    cases, violations = namespace["n"], namespace["bad"]
    sizes, contained = sorted(namespace["amb_sizes"]), namespace["contains"]
    assert cases == 18000 and violations == 0
    assert sizes == [6, 7, 8] and contained == 18000
    q2_line = next(line for line in output.splitlines()
                   if line.startswith("K = alpha + c (mod A):"))
    archive_line = next(line for line in ARCHIVE.read_text().splitlines()
                       if line.startswith("K = alpha + c (mod A):"))
    assert q2_line == archive_line, "archived aggregate mismatch"
    result = {
        "status": "PASS", "source_repository": "Skyelabz210/NINE65_v7",
        "source_commit": PIN, "source_sha256": EXPECTED_SHA256,
        "q1_normalized_crt_warmup": {
            "cases": warmup_cases, "violations": warmup_violations,
            "seed": 20261117, "rng_state_before_q2": state_before_q2,
            "scope": "Original warmup executed unchanged; preserves Q2 input stream",
        },
        "q2": {
            "cases": cases, "identity_violations": violations,
            "candidate_set_sizes": sizes, "true_K_in_candidates": contained,
            "source_range": "0 <= X < M*A", "rank_contract": "normalized xi_i",
            "identity": "K = alpha + c modulo A",
            "candidate_definition": "{(a+c) mod A : 0 <= a < k}",
            "matches_archived_aggregate": True,
        },
        "excluded_sections": [
            "Q1 Hermite/tropical sweep",
            "Q1 Theorem-5 carry enumeration",
            "Q3 fixed-point truncation experiment",
        ],
        "limitations": [
            "Finite deterministic experiment, not a universal proof or a Lean build.",
            "Candidate cardinalities follow the selected k and anchors larger than k.",
            "Does not recover an unrestricted integer K from a fixed finite observation.",
            "The two other sampled bases are test fixtures, not changes to selected S6.",
        ],
    }
    (ROOT / "carry_q2_results.json").write_text(json.dumps(result, indent=2) + "\n")
    execution = {
        "status": "PASS", "started_at_utc": started,
        "completed_at_utc": datetime.now(timezone.utc).isoformat(),
        "command": "python3 replay_carry_q2.py", "python": platform.python_version(),
        "python_implementation": platform.python_implementation(),
        "dependencies": {name: importlib.metadata.version(name) for name in ("sympy", "mpmath")},
        "source_sha256": EXPECTED_SHA256,
        "replay_wrapper_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "selected_ast_sha256": hashlib.sha256(selected_dump.encode()).hexdigest(),
        "selection": {
            "prefix_node_count": len(prefix),
            "warmup_source_lines": [nodes[warmup_start].lineno, nodes[q2_start - 1].end_lineno],
            "q2_source_lines": [nodes[q2_start].lineno, nodes[q3_start - 1].end_lineno],
            "omitted_prefix_has_no_R_access": True,
            "original_selected_statements_modified": False,
        },
        "result_sha256": hashlib.sha256((ROOT / "carry_q2_results.json").read_bytes()).hexdigest(),
        "log_sha256": hashlib.sha256((ROOT / "carry_q2_replay.log").read_bytes()).hexdigest(),
        "archive_output_sha256": hashlib.sha256(ARCHIVE.read_bytes()).hexdigest(),
    }
    (ROOT / "carry_q2_execution.json").write_text(json.dumps(execution, indent=2) + "\n")
    print(output, end="")


if __name__ == "__main__":
    sys.dont_write_bytecode = True
    main()
