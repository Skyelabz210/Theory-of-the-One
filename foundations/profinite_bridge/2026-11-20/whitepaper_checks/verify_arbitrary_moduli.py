#!/usr/bin/env python3
"""Reproduce the white paper's three finite, exact-integer arithmetic checks.

These checks corroborate identities; they are not a proof-assistant compilation
or a conformance test of any CRAM runtime. X and K are semantic/oracle values.
The bounded-query calculation derives its temporary quotient from residue
observations and a declared interval; it does not read the oracle quotient.

Run with Python 3.9 or later, for example:
    python3 verify_arbitrary_moduli.py --output results.json
"""

from __future__ import annotations

import argparse
import json
import math
import platform
import sys
from pathlib import Path


def require(condition: bool, message: str) -> None:
    """Keep validation active even if Python is invoked with optimization."""
    if not condition:
        raise AssertionError(message)


def recover_quotient_coordinate(
    primary_residue: int,
    auxiliary_residue: int,
    auxiliary_modulus: int,
    common_factor: int,
    quotient_period: int,
    reduced_primary_inverse: int,
) -> int:
    delta = (auxiliary_residue - primary_residue) % auxiliary_modulus
    require(delta % common_factor == 0, "Residue difference is not gcd-compatible")
    if quotient_period == 1:
        return 0
    return (delta // common_factor * reduced_primary_inverse) % quotient_period


def verify_anchor_queries() -> dict:
    cases = 0
    signed_negative_cases = 0
    modulus_one_cases = 0
    trivial_quotient_period_cases = 0
    for primary_modulus in range(1, 41):
        for auxiliary_modulus in range(1, 41):
            common_factor = math.gcd(primary_modulus, auxiliary_modulus)
            quotient_period = auxiliary_modulus // common_factor
            inverse = (
                pow(primary_modulus // common_factor, -1, quotient_period)
                if quotient_period > 1
                else 0
            )
            for source_integer in range(-200, 201):
                primary_residue = source_integer % primary_modulus
                auxiliary_residue = source_integer % auxiliary_modulus
                oracle_quotient = source_integer // primary_modulus
                require(
                    source_integer == primary_residue + primary_modulus * oracle_quotient,
                    "Signed Euclidean decomposition failed",
                )
                require(0 <= primary_residue < primary_modulus, "Remainder out of range")
                recovered = recover_quotient_coordinate(
                    primary_residue,
                    auxiliary_residue,
                    auxiliary_modulus,
                    common_factor,
                    quotient_period,
                    inverse,
                )
                require(
                    recovered == oracle_quotient % quotient_period,
                    "Arbitrary-anchor quotient congruence failed",
                )
                cases += 1
                signed_negative_cases += source_integer < 0
                modulus_one_cases += primary_modulus == 1 or auxiliary_modulus == 1
                trivial_quotient_period_cases += quotient_period == 1
    require(cases == 641_600, "Unexpected anchor-query case count")
    return {
        "name": "arbitrary_anchor_quotient_queries",
        "domain": {"M": [1, 40], "A": [1, 40], "X": [-200, 200]},
        "ranges_are_inclusive": True,
        "cases": cases,
        "failures": 0,
        "negative_X_cases": signed_negative_cases,
        "M_or_A_equals_one_cases": modulus_one_cases,
        "A_over_gcd_equals_one_cases": trivial_quotient_period_cases,
    }


def verify_target_projections() -> dict:
    cases = 0
    signed_negative_cases = 0
    target_one_cases = 0
    for primary_modulus in range(1, 41):
        for source_integer in range(-200, 201):
            primary_residue = source_integer % primary_modulus
            exact_quotient = source_integer // primary_modulus
            for target_modulus in range(1, 61):
                target = (
                    primary_residue % target_modulus
                    + (primary_modulus % target_modulus) * (exact_quotient % target_modulus)
                ) % target_modulus
                require(target == source_integer % target_modulus, "Target projection failed")
                cases += 1
                signed_negative_cases += source_integer < 0
                target_one_cases += target_modulus == 1
    require(cases == 962_400, "Unexpected target-projection case count")
    return {
        "name": "target_projection_from_exact_euclidean_quotient",
        "domain": {"M": [1, 40], "X": [-200, 200], "b": [1, 60]},
        "ranges_are_inclusive": True,
        "cases": cases,
        "failures": 0,
        "negative_X_cases": signed_negative_cases,
        "b_equals_one_cases": target_one_cases,
        "evidence_scope": "Identity check using the oracle Euclidean quotient, not its production.",
    }


def verify_bounded_query_to_target() -> dict:
    cases = 0
    signed_negative_cases = 0
    target_one_cases = 0
    trivial_quotient_period_cases = 0
    source_states = 0
    for primary_modulus in range(1, 31):
        for auxiliary_modulus in range(1, 31):
            common_factor = math.gcd(primary_modulus, auxiliary_modulus)
            quotient_period = auxiliary_modulus // common_factor
            inverse = (
                pow(primary_modulus // common_factor, -1, quotient_period)
                if quotient_period > 1
                else 0
            )
            lower_quotient_bound = -(quotient_period // 2)
            for oracle_quotient in range(lower_quotient_bound, lower_quotient_bound + quotient_period):
                for primary_residue in range(primary_modulus):
                    source_integer = primary_residue + primary_modulus * oracle_quotient
                    auxiliary_residue = source_integer % auxiliary_modulus
                    coordinate = recover_quotient_coordinate(
                        primary_residue,
                        auxiliary_residue,
                        auxiliary_modulus,
                        common_factor,
                        quotient_period,
                        inverse,
                    )
                    # Select the unique quotient representative in the declared interval.
                    derived_quotient = lower_quotient_bound + (
                        coordinate - lower_quotient_bound
                    ) % quotient_period
                    require(derived_quotient == oracle_quotient, "Bounded quotient selection failed")
                    source_states += 1
                    for target_modulus in range(1, 31):
                        target = (
                            primary_residue % target_modulus
                            + (primary_modulus % target_modulus)
                            * (derived_quotient % target_modulus)
                        ) % target_modulus
                        require(
                            target == source_integer % target_modulus,
                            "Bounded residue-derived target projection failed",
                        )
                        cases += 1
                        signed_negative_cases += source_integer < 0
                        target_one_cases += target_modulus == 1
                        trivial_quotient_period_cases += quotient_period == 1
    require(cases == 4_642_650, "Unexpected bounded-query case count")
    return {
        "name": "bounded_residue_query_to_arbitrary_target",
        "domain": {
            "M": [1, 30],
            "A": [1, 30],
            "b": [1, 30],
            "N": "A // gcd(M,A)",
            "K": "-floor(N/2) <= K < -floor(N/2)+N",
            "v_M": "0 <= v_M < M",
        },
        "numeric_ranges_are_inclusive": True,
        "source_states": source_states,
        "cases": cases,
        "failures": 0,
        "negative_X_cases": signed_negative_cases,
        "b_equals_one_cases": target_one_cases,
        "A_over_gcd_equals_one_cases": trivial_quotient_period_cases,
        "evidence_scope": "Temporary quotient derived from residues plus the declared interval.",
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=Path(__file__).with_name("results.json"))
    args = parser.parse_args()
    checks = [
        verify_anchor_queries(),
        verify_target_projections(),
        verify_bounded_query_to_target(),
    ]
    total_cases = sum(check["cases"] for check in checks)
    require(total_cases == 6_246_650, "Unexpected aggregate case count")
    result = {
        "status": "passed",
        "arithmetic": "Python exact integers; no floating-point arithmetic",
        "python_version": platform.python_version(),
        "python_executable": sys.executable,
        "total_central_identity_cases": total_cases,
        "total_failures": 0,
        "checks": checks,
        "scope": "Finite arithmetic corroboration only; not universal proof or runtime conformance.",
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({
        "status": result["status"],
        "counts": [check["cases"] for check in checks],
        "total": total_cases,
        "failures": 0,
        "output": str(args.output.resolve()),
        "python_executable": sys.executable,
    }, indent=2))


if __name__ == "__main__":
    main()
