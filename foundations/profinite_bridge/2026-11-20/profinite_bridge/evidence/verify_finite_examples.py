#!/usr/bin/env python3
"""Exact finite checks for The Profinite Bridge; not universal or Lean proofs."""
from collections import Counter
from fractions import Fraction
from math import gcd, lcm, prod
from pathlib import Path
import hashlib
import json

ROOT = Path(__file__).resolve().parent
checks = 0


def require(condition, label):
    global checks
    checks += 1
    if not condition:
        raise AssertionError(label)


def partitions(n, largest=None):
    if n == 0:
        yield ()
        return
    if largest is None:
        largest = n
    for first in range(min(n, largest), 0, -1):
        for rest in partitions(n - first, first):
            yield (first,) + rest


def prime_factors(n):
    result = []
    d = 2
    while d * d <= n:
        while n % d == 0:
            result.append(d)
            n //= d
        d += 1
    if n > 1:
        result.append(n)
    return result


def multiplicative_order(a, modulus):
    require(gcd(a, modulus) == 1, "order requires a unit")
    value = 1
    for exponent in range(1, modulus + 1):
        value = value * a % modulus
        if value == 1:
            return exponent
    raise AssertionError("unit order not found")


def main():
    ranks, cranks, partition_rows = Counter(), Counter(), []
    for p in partitions(6):
        rank = p[0] - len(p)
        ones = p.count(1)
        crank = p[0] if ones == 0 else sum(part > ones for part in p) - ones
        ranks[rank % 11] += 1
        cranks[crank % 11] += 1
        partition_rows.append({"partition": list(p), "rank": rank, "crank": crank})
    rank_vector = [ranks[r] for r in range(11)]
    crank_vector = [cranks[r] for r in range(11)]
    require(len(partition_rows) == 11, "partition number p(6)")
    require(rank_vector == [1, 2, 1, 1, 0, 1, 1, 0, 1, 1, 2], "rank vector")
    require(crank_vector == [1] * 11, "crank vector")

    basis = [2, 3, 5, 7, 11, 13]
    M = prod(basis)
    Mi = [M // p for p in basis]
    inverse = [pow(a, -1, p) for a, p in zip(Mi, basis)]
    upper = sum((Fraction(p - 1, p) for p in basis), Fraction(0))
    alpha_max = upper.numerator // upper.denominator
    distribution = Counter()
    for x in range(M):
        xi = [(x % p) * u % p for p, u in zip(basis, inverse)]
        total = sum(a * b for a, b in zip(xi, Mi))
        alpha, remainder = divmod(total, M)
        require(remainder == x, "normalized CRT representative")
        require(0 <= alpha <= alpha_max, "normalized rank range")
        distribution[alpha] += 1
    expected = {0: 738, 1: 8862, 2: 15420, 3: 4847, 4: 163}
    require(M == 30030, "S6 product")
    require(alpha_max == 4, "sharp S6 maximum")
    require(dict(distribution) == expected, "S6 rank distribution")

    A = M + 1
    factors = prime_factors(A)
    require(factors == [59, 509], "30031 prime factors")
    require(prod(factors) == A and gcd(M, A) == 1, "outside anchor factorization")
    powers = [pow(M, n, A) for n in range(9)]
    require(powers == [1 if n % 2 == 0 else A - 1 for n in range(9)],
            "finite alternating residue witness")

    star_examples, alias_controls = [], []
    for sign in (1, -1):
        base, coefficient = 6, 1
        anchor = coefficient * base + sign
        inv = (-sign * coefficient) % anchor
        require(base * inv % anchor == 1, "signed star inverse")
        for source in (0, 20):
            main = source % base
            observed = source % anchor
            quotient_readout = ((observed - main) * inv) % anchor
            recovered = main + base * quotient_readout
            require(recovered == source, "star bounded representative")
            require(quotient_readout == source // base, "bounded quotient")
            star_examples.append({
                "M": base, "c": coefficient, "sign": sign, "A": anchor,
                "X": source, "r": main, "s": observed, "inverse": inv,
                "derived_K": quotient_readout, "recovered_X": recovered,
                "admitted_window": [0, base * anchor],
                "window_convention": "left closed, right open",
            })
        shifted = base * anchor
        require((shifted % base, shifted % anchor) == (0, 0), "alias observations")
        require(shifted != 0, "alias sources differ")
        alias_controls.append({
            "M": base, "A": anchor, "sources": [0, shifted],
            "same_readings": [0, 0], "source_at_upper_endpoint_is_not_admitted": True,
        })

    orders = {}
    for modulus, expected_order in ((23, 11), (29, 14), (667, 154)):
        order = multiplicative_order(4, modulus)
        require(order == expected_order, "multiplicative order")
        proper = {d: pow(4, d, modulus) for d in range(1, order) if order % d == 0}
        require(all(v != 1 for v in proper.values()), "proper divisor control")
        orders[str(modulus)] = {
            "base": 4, "order": order, "residue_at_order": pow(4, order, modulus),
            "proper_divisor_power_residues": proper,
        }
    require(667 == 23 * 29 and orders["667"]["order"] == lcm(11, 14),
            "product-modulus order")

    result = {
        "status": "PASS",
        "scope": "Exact finite integer/rational reference checks; not runtime or universal proof",
        "assertions": checks,
        "source_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "partition_n6": {
            "modulus": 11, "partitions": partition_rows,
            "rank_counts": rank_vector, "crank_counts": crank_vector,
        },
        "s6_normalized_rank": {
            "basis": basis, "M": M, "canonical_states": M,
            "Mi": Mi, "inverses": inverse, "alpha_max": alpha_max,
            "max_normalized_sum": [upper.numerator, upper.denominator],
            "rank_counts": {str(k): expected[k] for k in sorted(expected)},
            "meaning": "rank of sum of normalized xi_i*Mi, not external source winding",
        },
        "outside_anchor": {
            "M": M, "A": A, "prime_factors": factors,
            "powers_M_mod_A_for_exponents_0_through_8": powers,
            "scope": "Finite witness; convergence/obstruction theorem is a separate written proof",
        },
        "signed_star_examples": star_examples,
        "alias_controls": alias_controls,
        "multiplicative_orders": orders,
        "limitations": [
            "The n=6 enumeration does not prove the general crank theorem.",
            "Finite rank enumeration does not replace the general bound proof.",
            "Orbit orders do not establish a mock-theta or architectural boundary at 23.",
            "Scalar sources are independent mathematical test oracles, not runtime payloads.",
        ],
    }
    output = ROOT / "finite_examples_results.json"
    output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({"status": result["status"], "assertions": checks,
                      "canonical_states": M, "partitions": len(partition_rows),
                      "multiplicative_orders": {k: v["order"] for k, v in orders.items()}},
                     indent=2))


if __name__ == "__main__":
    main()
