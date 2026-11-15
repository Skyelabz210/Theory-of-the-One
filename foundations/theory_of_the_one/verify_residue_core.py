#!/usr/bin/env python3
"""Exact finite checks supporting Theory of the One's proved algebraic lemmas.

This is a mathematical reference checker, not a CRAM production implementation.
Semantic integers and explicit representatives are permitted test oracles. These
finite checks supplement the symbolic proofs; they do not replace them, certify
cryptographic security, or verify a particular repository implementation.
All numeric computation uses integers. No floating-point literals or division.
"""

from __future__ import annotations

import ast
import hashlib
import json
from collections import Counter
from itertools import combinations_with_replacement, product
from math import gcd, lcm, prod
from pathlib import Path


COUNTS: Counter[str] = Counter()
FAILURES: list[dict] = []


def check(section: str, condition: bool, context: object = None) -> None:
    COUNTS[section] += 1
    if not condition:
        FAILURES.append({"section": section, "context": context})


def residue_tuple(x: int, basis: tuple[int, ...]) -> tuple[int, ...]:
    return tuple(x % m for m in basis)


def compatible(rs: tuple[int, ...], basis: tuple[int, ...]) -> bool:
    return all((rs[i] - rs[j]) % gcd(basis[i], basis[j]) == 0
               for i in range(len(basis)) for j in range(i))


def anchor_class(M: int, A: int, r: int, s: int) -> tuple[int, int]:
    """Return (K mod H,H), H=A/gcd(M,A); reject incompatible observations."""
    g = gcd(M, A)
    if (s - r) % g:
        raise ValueError("incompatible anchor residues")
    H = A // g
    if H == 1:
        return 0, 1
    return (((s - r) // g) * pow(M // g, -1, H)) % H, H


def corridor_representative(kappa: int, H: int, lo: int, size: int) -> int:
    """The corridor is the set of integers lo <= K < lo+size, 1 <= size <= H."""
    if not (1 <= size <= H):
        raise ValueError("invalid corridor cardinality")
    candidate = lo + (kappa - lo) % H
    if candidate >= lo + size:
        raise ValueError("no representative in corridor")
    return candidate


def carry(r: int, s: int, M: int) -> int:
    return (r + s) // M


def proper_divisors(n: int) -> list[int]:
    return [d for d in range(1, n) if n % d == 0]


def check_unit_orbits() -> None:
    bases = [b for length in (1, 2, 3)
             for b in combinations_with_replacement(range(2, 9), length)]
    for basis in bases:
        L = lcm(*basis)
        image = {residue_tuple(x, basis) for x in range(L)}
        check("unit_orbit_size", len(image) == L, basis)
        check("unit_period", residue_tuple(L, basis) == (0,) * len(basis), basis)
        pairwise = all(gcd(basis[i], basis[j]) == 1
                       for i in range(len(basis)) for j in range(i))
        check("full_product_criterion", (L == prod(basis)) == pairwise, basis)
        for rs in product(*(range(m) for m in basis)):
            check("generalized_crt_compatibility", (rs in image) == compatible(rs, basis),
                  (basis, rs))
    for basis in [(2, 3, 5, 7, 11, 13), (2, 3, 5, 7, 11, 13, 17, 19)]:
        check("safe_basis_capacity", lcm(*basis) == prod(basis), basis)
    check("dependent_capacity_example", lcm(6, 10, 15) == 30, None)


def check_projection_determinacy() -> None:
    for L in range(2, 21):
        for q in range(2, 21):
            fibers: dict[int, set[int]] = {}
            for x in range(lcm(L, q)):
                fibers.setdefault(x % L, set()).add(x % q)
            determined = all(len(values) == 1 for values in fibers.values())
            check("new_view_determinacy", determined == (L % q == 0), (L, q))


def check_anchors() -> None:
    for M in range(2, 20):
        for A in range(2, 20):
            L = lcm(M, A)
            for x in range(-2 * L, 2 * L + 1):
                K, r = divmod(x, M)
                kappa, H = anchor_class(M, A, r, x % A)
                check("anchor_congruence", kappa == K % H, (M, A, x))
                lo = K - H // 2
                recovered = corridor_representative(kappa, H, lo, H)
                check("anchor_bounded_exact_recovery", recovered == K, (M, A, x, lo))
            for r in range(M):
                for s in range(A):
                    allowed = (s - r) % gcd(M, A) == 0
                    try:
                        kappa, H = anchor_class(M, A, r, s)
                    except ValueError:
                        check("anchor_compatibility_admission", not allowed, (M, A, r, s))
                    else:
                        x = r + M * kappa
                        check("anchor_compatibility_admission",
                              allowed and x % M == r and x % A == s, (M, A, r, s))
    for M in range(2, 41):
        A = M + 1
        for x in range(M * A):
            check("adjacent_anchor_subtraction", (x % M - x % A) % A == x // M,
                  (M, x))
    for H in range(1, 17):
        for size in range(1, H + 1):
            for lo in range(-8, 9):
                for kappa in range(H):
                    matches = [K for K in range(lo, lo + size) if K % H == kappa]
                    try:
                        K = corridor_representative(kappa, H, lo, size)
                    except ValueError:
                        check("corridor_unique_or_reject", not matches, (H, size, lo, kappa))
                    else:
                        check("corridor_unique_or_reject", matches == [K], (H, size, lo, kappa))
    check("anchor_alias_boundary", residue_tuple(23, (6, 10)) == residue_tuple(53, (6, 10))
          and 23 // 6 != 53 // 6, None)
    # Coprime residues from different sources can still decode to a plausible value.
    kappa, _ = anchor_class(5, 7, 7 % 5, 12 % 7)
    check("source_binding_negative_control", 7 % 5 + 5 * kappa == 12 != 7, None)


def check_target_residues() -> None:
    for M in range(2, 13):
        for q in range(2, 13):
            h = q // gcd(M, q)
            for K in range(-20, 21):
                for r in range(M):
                    target = (r % q + (M % q) * (K % h)) % q
                    check("minimal_target_k_resolution", target == (r + M * K) % q,
                          (M, q, K, r))
            for H in range(1, 21):
                check("target_period_criterion", (M * H) % q == 0 if H % h == 0
                      else (M * H) % q != 0, (M, q, H))
        for A in range(2, 13):
            H = A // gcd(M, A)
            L = M * H
            for q in range(2, 13):
                h = q // gcd(M, q)
                if H % h:
                    check("target_insufficient_anchor_witness", 0 % L == L % L
                          and 0 % q != L % q, (M, A, q))
                    continue
                for x in range(L):
                    r = x % M
                    kappa, _ = anchor_class(M, A, r, x % A)
                    got = (r % q + (M % q) * (kappa % h)) % q
                    check("anchor_to_target_projection", got == x % q, (M, A, q, x))


def check_carries_and_order() -> None:
    for M in range(2, 21):
        for r, s, t in product(range(M), repeat=3):
            left = carry(r, s, M) + carry((r + s) % M, t, M)
            right = carry(s, t, M) + carry(r, (s + t) % M, M)
            check("carry_cocycle", left == right == (r + s + t) // M, (M, r, s, t))
        for x, y in product(range(-30, 31), repeat=2):
            K, r = divmod(x, M)
            J, s = divmod(y, M)
            check("signed_winding_addition", (x + y) // M == K + J + carry(r, s, M),
                  (M, x, y))
            check("signed_winding_multiplication",
                  (x * y) // M == M * K * J + K * s + J * r + (r * s) // M,
                  (M, x, y))
            check("transient_lexicographic_order", (x < y) == ((K, r) < (J, s)),
                  (M, x, y))
        for x in range(-50, 51):
            K, r = divmod(x, M)
            check("signed_winding_negation", (-x) // M == -K - (1 if r else 0), (M, x))
            check("sign_from_transient_k", (x < 0) == (K < 0), (M, x))
    check("missing_carry_negative_control", (4 + 3) // 5 != 4 // 5 + 3 // 5, None)


def check_division() -> None:
    for d in range(1, 16):
        for m in range(2, 21):
            for x in range(-2 * d * m, 2 * d * m + 1):
                q, rho = divmod(x, d)
                t = x % (d * m)
                check("quotient_coefficient_witness", (t - rho) % d == 0
                      and (t - rho) // d == q % m, (d, m, x))
    for d in range(1, 16):
        for N in range(1, 31):
            H = N // gcd(N, d)
            for m in range(2, 21):
                # Two possible quotients differing by H give identical observed dividends.
                same_observation = (d * H) % N == 0
                same_target = H % m == 0
                fibers: dict[int, set[int]] = {}
                for q in range(lcm(H, m)):
                    fibers.setdefault((d * q) % N, set()).add(q % m)
                empirically_determined = all(len(values) == 1 for values in fibers.values())
                check("quotient_minimal_information", same_observation and
                      empirically_determined == same_target, (d, N, m))
                if not same_target:
                    check("quotient_insufficient_information_witness",
                          0 % N == (d * H) % N and 0 % m != H % m, (d, N, m))
    for p in (2, 3, 5, 7):
        for alpha in range(1, 5):
            m = p ** alpha
            for t in range(4):
                N = p ** (alpha + t)
                for u in range(1, 10):
                    if u % p == 0:
                        continue
                    d = p ** t * u
                    for q in range(-20, 21):
                        for rho in range(min(d, 4)):
                            x = d * q + rho
                            witness = (x - rho) % N
                            got = ((witness // (p ** t)) * pow(u, -1, m)) % m
                            check("valuation_matched_quotient", got == q % m,
                                  (p, alpha, t, u, q, rho))
    check("shared_divisor_negative_control", 0 % 6 == 6 % 6
          and (0 // 2) % 6 != (6 // 2) % 6, None)


def check_typed_operations_and_reversal() -> None:
    for basis in ((2, 3), (4, 6), (6, 10, 15)):
        L = lcm(*basis)
        for x, y in product(range(L), repeat=2):
            rx, ry = residue_tuple(x, basis), residue_tuple(y, basis)
            addition = tuple((a + b) % m for a, b, m in zip(rx, ry, basis))
            multiplication = tuple((a * b) % m for a, b, m in zip(rx, ry, basis))
            check("homogeneous_coherence", compatible(addition, basis)
                  and compatible(multiplication, basis), (basis, x, y))
    check("heterogeneous_coprime_example", residue_tuple(4, (2, 3)) == (0, 1)
          and 4 != 1 + 1 and 4 != 1 * 1, None)
    check("heterogeneous_overlap_negative_control", not compatible((2, 1), (4, 6)), None)
    for m in range(2, 31):
        for d in range(m):
            image = {(d * x) % m for x in range(m)}
            check("multiplication_reversible_iff_unit", (len(image) == m) == (gcd(d, m) == 1),
                  (m, d))
        for r in range(m):
            check("orientation_conjugacy", (-((-r + 1) % m)) % m == (r - 1) % m, (m, r))
    for m in range(2, 11):
        for x, y, z in product(range(m), repeat=3):
            z_out = (z + x * y) % m
            check("input_retaining_reversible_embedding", (z_out - x * y) % m == z,
                  (m, x, y, z))
    for x, y in product(range(2), repeat=2):
        check("syntactic_topology_collision", (x + y) % 2 == (x - y) % 2, (x, y))
    for x in range(2):
        check("syntactic_unary_collision", x * x % 2 == x, x)


def profinite_idempotent_component(n: int) -> int:
    two_power, odd = 1, n
    while odd % 2 == 0:
        two_power *= 2
        odd //= 2
    if odd == 1:
        return 0
    return (two_power * pow(two_power, -1, odd)) % n


def check_refinement_and_euclid() -> None:
    chain = (2, 6, 30, 210, 2310)
    for x in range(-100, 101):
        for small, big in zip(chain, chain[1:]):
            check("integer_refinement_coherence", (x % big) % small == x % small,
                  (x, small, big))
    for n in range(1, 257):
        a = profinite_idempotent_component(n)
        check("profinite_extra_state_idempotence", (a * a) % n == a, n)
        for m in range(1, n + 1):
            if n % m == 0:
                check("profinite_extra_state_coherence", a % m == profinite_idempotent_component(m),
                      (m, n))
    check("profinite_not_integer_witness", profinite_idempotent_component(3) == 1
          and all(profinite_idempotent_component(2 ** k) == 0 for k in range(1, 9)), None)
    check("euclid_perfect_six", proper_divisors(6) == [1, 2, 3]
          and sum(proper_divisors(6)) == 6, None)
    check("euclid_parity_classes_overlap", 12 == 2 * 6 == 3 * 4, None)
    check("euclid_relative_primality", gcd(8, 9) == 1
          and len(proper_divisors(8)) > 1 and len(proper_divisors(9)) > 1, None)


def main() -> int:
    check_unit_orbits()
    check_projection_determinacy()
    check_anchors()
    check_target_residues()
    check_carries_and_order()
    check_division()
    check_typed_operations_and_reversal()
    check_refinement_and_euclid()
    source_path = Path(__file__)
    source = source_path.read_text(encoding="utf-8")
    tree = ast.parse(source)
    float_literals = sum(isinstance(node, ast.Constant) and isinstance(node.value, float)
                         for node in ast.walk(tree))
    true_division_nodes = sum(isinstance(node, ast.Div) for node in ast.walk(tree))
    check("integer_only_static_audit", float_literals == 0 and true_division_nodes == 0, None)
    report = {
        "title": "Theory of the One: exact finite verification",
        "status": "PASS" if not FAILURES else "FAIL",
        "verification_role": "Reference calculations supporting the written proofs",
        "scope_exclusions": ["Not a universal proof by finite enumeration",
                             "Not an execution of production CRAM APIs",
                             "Not a cryptographic or side-channel certification"],
        "assertions_total": sum(COUNTS.values()),
        "assertions_passed": sum(COUNTS.values()) - len(FAILURES),
        "assertions_failed": len(FAILURES),
        "checks_by_section": dict(sorted(COUNTS.items())),
        "static_audit": {"floating_point_literals": float_literals,
                         "true_division_ast_nodes": true_division_nodes},
        "script_sha256": hashlib.sha256(source.encode("utf-8")).hexdigest(),
        "failures": FAILURES,
    }
    output = source_path.with_name("residue_core_verification.json")
    output.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(report, indent=2))
    return 1 if FAILURES else 0


if __name__ == "__main__":
    raise SystemExit(main())
