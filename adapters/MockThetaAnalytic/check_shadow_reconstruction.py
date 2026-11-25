#!/usr/bin/env python3
"""Replay the S6 coefficient-to-shadow construction with exact arithmetic."""

import argparse
from fractions import Fraction
from hashlib import sha256
from itertools import permutations
import json
from math import isqrt, lcm
from pathlib import Path


PRIMARY = 30030
PRIME = 5
SECTORS = (0, 2, 6, 7, 8, 10)
CUTOFFS = (0, 1, 16, 64, 256, 1024, 2048)
OUTPUT_DEGREE = 4096
INPUT_DEGREE = (PRIME**2 * OUTPUT_DEGREE + 22) // 24


def mock_coefficients(cutoff, modulus):
    """Evaluate MockTheta's two binomial divisions per factor in a residue ring."""
    result = [0] * (cutoff + 1)
    for n in range(isqrt(cutoff) + 1):
        row = [1] + [0] * (cutoff - n*n)
        for j in range(1, n + 1):
            for _ in range(2):
                for d in range(j, len(row)):
                    row[d] = (row[d] - row[d-j]) % modulus
        for d, value in enumerate(row, n*n):
            result[d] = (result[d] + value) % modulus
    return result


def odd_part_product(cutoff):
    """Independent parity check using distinct odd subsets."""
    degree_mask = (1 << (cutoff + 1)) - 1
    result = 1
    for j in range(1, cutoff + 1, 2):
        result = (result ^ (result << j)) & degree_mask
    return tuple((result >> d) & 1 for d in range(cutoff + 1))


def parity_readings(cutoff, rows, modulus=PRIMARY):
    """Validate a dense sequence of canonical, degree-labeled observations."""
    readings = {}
    for degree, value in rows:
        if not 0 <= degree <= cutoff or degree in readings:
            raise ValueError("degree outside prefix or duplicated")
        if not 0 <= value < modulus:
            raise ValueError("noncanonical residue")
        readings[degree] = value % 2
    if len(readings) != cutoff + 1:
        raise ValueError("incomplete degree prefix")
    if modulus % 2:
        raise ValueError("the frame does not determine parity")
    return tuple(readings[d] for d in range(cutoff + 1))


def reciprocal(bits):
    """Invert a unit series over F₂ using just its observed prefix."""
    if not bits or bits[0] != 1:
        raise ValueError("a parity prefix must have constant coefficient one")
    degree = len(bits) - 1
    reversed_input = sum(bit << (degree-d) for d, bit in enumerate(bits))
    inverse = 1
    for d in range(1, degree + 1):
        product = (reversed_input >> (degree-d)) & inverse
        inverse |= (product.bit_count() % 2) << d
    return tuple((inverse >> d) & 1 for d in range(len(bits)))


def eta_sign(m):
    """Euler sign of the unique signed root congruent to 1 modulo 6."""
    root = m if m % 6 == 1 else -m
    return -1 if ((root-1)//6) % 2 else 1


def recover_eta(bits):
    """Lift reciprocal bits to signed eta coefficients at integral q-exponents."""
    result = {}
    for d, bit in enumerate(reciprocal(bits)):
        if bit == 0:
            continue
        degree = 24*d + 1
        m = isqrt(degree)
        if m*m != degree:
            raise ValueError(f"nonpentagonal reciprocal bit at degree {d}")
        result[degree] = eta_sign(m)
    return result


def first_moment(m):
    return 4*m if m % 4 == 1 else -4*m


def signed_lattice(degree):
    """Independent oracle from the analytic completion's differential shadow."""
    radius = isqrt(degree)
    return {m*m: 4*m for j in range(-radius//6-1, radius//6+2)
            if abs(m := 6*j+1) <= radius}


def partitions(n, cap, distinct=False):
    if n == 0:
        yield ()
    for first in range(min(n, cap), 0, -1):
        for tail in partitions(n-first, first-int(distinct), distinct):
            yield (first, *tail)


def franklin(parts):
    """Pair distinct partitions by moving their smallest row or diagonal."""
    if not parts:
        return parts
    count = len(parts)
    slope = 1
    while slope < count and parts[slope-1] == parts[slope] + 1:
        slope += 1
    smallest = parts[-1]
    if smallest <= slope:
        if smallest == count:
            return parts
        return tuple(part + int(j < smallest) for j, part in enumerate(parts[:-1]))
    if slope == count and smallest == slope + 1:
        return parts
    return (*tuple(part - int(j < slope) for j, part in enumerate(parts)), slope)


def check_franklin(limit):
    fixed = [(0, ())]
    for k in range(1, limit + 1):
        for start in (2*k-1, 2*k):
            parts = tuple(range(start, start-k, -1))
            if sum(parts) <= limit:
                fixed.append((sum(parts), parts))
    seen = []
    count = 0
    for n in range(limit + 1):
        for p in partitions(n, n, distinct=True):
            other = franklin(p)
            assert sum(other) == n and len(set(other)) == len(other)
            assert tuple(sorted(other, reverse=True)) == other and all(v > 0 for v in other)
            assert franklin(other) == p
            if p == other:
                seen.append((n, p))
            else:
                assert (len(p) - len(other)) % 2 == 1
            count += 1
    assert sorted(seen) == sorted(fixed)
    return count


def crank_rows():
    matrix = []
    for size in range(2, 8):
        histogram = [0] * 11
        for parts in partitions(size, size):
            ones = parts.count(1)
            crank = sum(p > ones for p in parts)-ones if ones else parts[0]
            histogram[crank % 11] += 1
        matrix.append(tuple(histogram[r] for r in SECTORS))
    determinant = 0
    for perm in permutations(range(6)):
        term = (-1)**sum(a > b for j, a in enumerate(perm) for b in perm[j+1:])
        for j, k in enumerate(perm):
            term *= matrix[j][k]
        determinant += term
    assert abs(determinant) == 1
    return tuple(matrix), determinant


def matrix_vector(matrix, values):
    return tuple(sum(a*b for a, b in zip(row, values)) for row in matrix)


def legendre(value):
    result = pow(value % PRIME, (PRIME-1)//2, PRIME)
    return -1 if result == PRIME-1 else result


def diamond(row, power):
    # Multiplying an even character by ξ(5) shifts its phase by 5.
    # In negative-square sectors the shift is 5² and χ₁₂(5) contributes −1.
    inverse = pow(PRIME**2, -power, 11)
    return tuple((-1)**power * row[SECTORS.index(r*inverse % 11)] for r in SECTORS)


def packet_row(coefficients, degree):
    value = coefficients.get(degree, 0)
    return tuple(value if -degree % 11 == r else 0 for r in SECTORS)


def hecke_row(coefficients, degree, *, source):
    up = packet_row(coefficients, PRIME**2 * degree)
    mid = diamond(packet_row(coefficients, degree), 1)
    down = (diamond(packet_row(coefficients, degree // PRIME**2), 2)
            if degree % PRIME**2 == 0 else (0,) * 6)
    if source:
        return tuple(PRIME*u + legendre(degree)*m + d for u, m, d in zip(up, mid, down))
    return tuple(u + legendre(-degree)*m + PRIME*d for u, m, d in zip(up, mid, down))


def check_hecke(eta, shadow, maximum_input):
    if maximum_input < PRIME**2 * OUTPUT_DEGREE:
        raise ValueError("insufficient Hecke lookahead")
    matrix, determinant = crank_rows()
    inverse = ((0,0,1,1,-1,0), (1,0,0,0,0,0), (-1,-1,0,0,2,-1),
               (-1,0,0,-1,1,0), (0,1,-1,-1,1,0), (1,0,0,1,-2,1))
    rotation = tuple(SECTORS.index(4*r % 11) for r in SECTORS)
    for j in range(len(SECTORS)):
        unit = tuple(int(i == j) for i in range(len(SECTORS)))
        assert matrix_vector(inverse, matrix_vector(matrix, unit)) == unit
        assert matrix_vector(matrix, matrix_vector(inverse, unit)) == unit
    for n in range(OUTPUT_DEGREE + 1):
        source = hecke_row(eta, n, source=True)
        target = hecke_row(shadow, n, source=False)
        transferred = tuple(first_moment(isqrt(n))*c for c in source)
        original = packet_row(shadow, n)
        expected = tuple(-6*original[j] for j in rotation)
        assert transferred == target == expected
        crank_reading = matrix_vector(matrix, original)
        recovered = matrix_vector(inverse, crank_reading)
        assert recovered == original
        moved_reading = matrix_vector(matrix, tuple(-6*recovered[j] for j in rotation))
        assert matrix_vector(matrix, target) == moved_reading
    full = sum(hecke_row(shadow, 1, source=False))
    padded = sum(hecke_row({1: shadow[1]}, 1, source=False))
    size_three = matrix[1]
    separate = sum(a*c for a,c in zip(size_three, hecke_row(shadow, 1, source=False)))
    fixed_mask = size_three[SECTORS.index(10)] * full
    assert (full, padded, separate, fixed_mask) == (-24, -4, -24, 0)
    return {"degree": OUTPUT_DEGREE, "lookahead_degree": PRIME**2 * OUTPUT_DEGREE,
            "sector_coefficient_pairs": (OUTPUT_DEGREE+1)*6,
            "crank_coefficient_pairs": (OUTPUT_DEGREE+1)*6,
            "crank_matrix_determinant": determinant, "crank_matrix": matrix,
            "degree_one_full_and_zero_padded": [full, padded],
            "degree_one_size_three_separate_and_fixed": [separate, fixed_mask]}


def evaluate(coefficients, radius, phase, max_degree):
    """Evaluate all sectors in Q(i) with one denominator per nome."""
    den = radius.denominator**max_degree
    real = dict.fromkeys(SECTORS, 0)
    imag = dict.fromkeys(SECTORS, 0)
    for d, value in coefficients.items():
        coefficient = value * radius.numerator**d * radius.denominator**(max_degree-d)
        quarter = (phase*d) % 4
        sign = 1 if quarter < 2 else -1
        (real if quarter % 2 == 0 else imag)[-d % 11] += sign*coefficient
    return {r: (Fraction(real[r], den), Fraction(imag[r], den)) for r in SECTORS}


def tail_bound(radius, largest_magnitude):
    first = largest_magnitude+1
    ratio = radius**(2*first)
    return 4 * radius**(first**2) * (first/(1-ratio) + ratio/(1-ratio)**2)


def check_enclosures(rows, shadow):
    count = 0
    reference_degree = 24*(CUTOFFS[-1] + 16) + 1
    reference = {d:c for d,c in shadow.items() if d <= reference_degree}
    for radius, phase in ((Fraction(1,2), 0), (Fraction(1,2), 2),
                          (Fraction(1,2), 1), (Fraction(19,20), 0)):
        reference_values = evaluate(reference, radius, phase, reference_degree)
        reference_error = tail_bound(radius, isqrt(reference_degree))
        for cutoff, polynomial in rows.items():
            degree = 24*cutoff+1
            remaining = tail_bound(radius, isqrt(degree)) - reference_error
            assert remaining >= 0
            values = evaluate(polynomial, radius, phase, degree)
            for r in SECTORS:
                error = sum((a-b)**2 for a,b in zip(values[r], reference_values[r]))
                assert error <= remaining**2
                count += 1
    return count


def require_invalid(call):
    try:
        call()
    except ValueError:
        return
    raise AssertionError("invalid input was accepted")


def check_observations(residues):
    require_invalid(lambda: parity_readings(1, [(0, 1)]))
    require_invalid(lambda: parity_readings(1, [(0, 1), (0, 3)]))
    require_invalid(lambda: parity_readings(0, [(0, PRIMARY)]))
    require_invalid(lambda: parity_readings(1, [(0, 1), (2, 0)]))
    require_invalid(lambda: reciprocal((0,)))
    require_invalid(lambda: recover_eta((1, 0, 0, 1)))
    require_invalid(lambda: parity_readings(1, [(0, 1), (1, 0)], modulus=15015))
    assert 15015 % (PRIMARY//2) == 0 and recover_eta((1, 0)) != recover_eta((1, 1))
    for x in (-90091, -30031, -1, 0, 1, 45046):
        for lift in (-5, 0, 7):
            assert (x + lift*PRIMARY) % PRIMARY % 2 == x % 2
    joint = mock_coefficients(64, lcm(PRIMARY, 121))
    pairs = [(x % PRIMARY, x % 121) for x in joint]
    assert [primary for primary, _ in pairs] == residues[:65]
    assert all(primary % 11 == anchor % 11 for primary, anchor in pairs)
    assert recover_eta(parity_readings(64, ((d, r) for d, (r, _) in enumerate(pairs)))) == (
        recover_eta(parity_readings(64, enumerate(residues[:65]))))
    patterns = ({0,1,2,15,26}, {0,1,5,7,15,22})
    inputs = [reciprocal(tuple(int(d in support) for d in range(32))) for support in patterns]
    totals = [tuple(sum(a[r::11]) for r in range(11)) for a in inputs]
    assert totals[0] == totals[1] and inputs[0] != inputs[1]
    assert recover_eta(inputs[0])[49] == -1 and 49 not in recover_eta(inputs[1])
    return {"signed_lift_checks": 18, "same_source_overlap_checks": 65,
            "aggregate_totals": totals[0], "aggregate_shadow_degree_49": [28,0],
            "invalid_prefix_controls": 7, "odd_frame_coefficients": [0,15015]}


def certify():
    readings = mock_coefficients(INPUT_DEGREE, PRIMARY)
    bits = parity_readings(INPUT_DEGREE, enumerate(readings))
    assert bits == odd_part_product(INPUT_DEGREE)
    eta = recover_eta(bits)
    shadow = signed_lattice(24*INPUT_DEGREE+1)
    assert {d:first_moment(isqrt(d))*v for d,v in eta.items()} == shadow
    require_invalid(lambda: check_hecke(eta, shadow, PRIME**2 * OUTPUT_DEGREE-1))
    witnesses = {}
    for d,value in sorted(shadow.items()):
        witnesses.setdefault(-d % 11, [d,value])
    assert sorted(witnesses) == list(SECTORS)
    assert [witnesses[r] for r in SECTORS] == [[121,-44],[361,76],[49,28],[169,52],[25,-20],[1,4]]
    polynomials = {}
    for cutoff in CUTOFFS:
        prefix = parity_readings(cutoff, reversed(list(enumerate(readings[:cutoff+1]))))
        polynomials[cutoff] = {d:first_moment(isqrt(d))*v for d,v in recover_eta(prefix).items()}
        assert polynomials[cutoff] == {d:v for d,v in shadow.items() if d <= 24*cutoff+1}
    return {"status": "PASS", "checker_sha256": sha256(Path(__file__).read_bytes()).hexdigest(),
            "primary": PRIMARY, "input_degree": INPUT_DEGREE,
            "parity_coefficients_checked": len(bits), "cutoffs": CUTOFFS,
            "first_sector_coefficients": witnesses, "zero_sectors": [1,3,4,5,9],
            "franklin_partitions_checked_through_45": check_franklin(45),
            "interval_checks": check_enclosures(polynomials, shadow),
            "observation_controls": check_observations(readings),
            "hecke": check_hecke(eta, shadow, 24*INPUT_DEGREE+1)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--receipt", type=Path)
    args = parser.parse_args()
    result = json.dumps(certify(), indent=2) + "\n"
    if args.receipt:
        args.receipt.write_text(result)
    print(result, end="")


if __name__ == "__main__":
    main()
