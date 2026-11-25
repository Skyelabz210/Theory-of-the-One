#!/usr/bin/env python3
"""Replay the two-cutoff average of FKTY periods from one S6 prefix."""

import argparse
from fractions import Fraction
from hashlib import sha256
import json
from math import isqrt
from pathlib import Path

import mpmath as mp

from check_shadow_period import (
    CUSP, FULL_SHIFT, INPUT_DEGREE, ORDER34, PRIMARY, ROOT, SECTOR_SHIFT, coordinates,
    cusp_values, e, gaussian_moment, period_integral, real, recovered_modes, require, scalar,
    sector, sign6,
)


CUTOFFS = (852, 1024, 2048, 3456, 3480, INPUT_DEGREE)
PARAMETERS = (ORDER34, CUSP-Fraction(1, 10000), CUSP+Fraction(1, 10000))
RUNS = ((55, 24), (75, 36))


def mode_count(cutoff):
    return isqrt(24*cutoff+1)+1


def cusp_polynomial(coefficients):
    """Remove the common FKTY scale and e(-1/576), then reduce modulo X^12+1."""
    row = [0]*12
    for m, coefficient in coefficients.items():
        require((m*m-1) % 24 == 0 and coefficient % m == 0, "invalid square-index coefficient")
        exponent = (m*m-1)//24
        row[exponent % 12] += (coefficient//m)*(-1)**(exponent//12)
    return row


def terminating_polynomial():
    row = [0]*12
    product = [1]+[0]*11
    for n in range(12):
        for j, coefficient in enumerate(product):
            row[j] += -4*(-1)**(n+1)*coefficient
        advanced = product.copy()
        for j, coefficient in enumerate(product):
            degree = j+n+1
            advanced[degree % 12] += (-1)**(degree//12)*coefficient
        product = advanced
    return row


def exact_controls(modes):
    target = terminating_polynomial()
    require(target == [4,-4,4,-4,0,0,4,0,0,4,4,0], "terminating polynomial changed")
    for cutoff in CUTOFFS:
        upper = mode_count(cutoff)
        lower = upper-FULL_SHIFT
        first = cusp_polynomial({m: c for m, c in modes.items() if m < lower})
        second = cusp_polynomial({m: c for m, c in modes.items() if m < upper})
        require(all(a+b == 2*c for a,b,c in zip(first, second, target)),
                "exact diagonal average failed")
    before = cusp_polynomial({m: c for m, c in modes.items() if m < mode_count(3456)})
    after = cusp_polynomial({m: c for m, c in modes.items() if m < mode_count(3480)})
    require(before == [0]*12 and after == [2]+[0]*11, "raw cutoff oscillation control failed")

    # The long phase block tests the sector formula on the signed lattice.
    # It uses the exact character table over one block.
    rows = []
    for r in range(11):
        row = cusp_polynomial({m: m*sign6(m) for m in range(1, SECTOR_SHIFT)
                               if sign6(m) and sector(m) == r})
        rows.append(row)
    require([sum(col) for col in zip(*rows)] == target, "sector half-blocks failed to add")
    zeros = [r for r, row in enumerate(rows) if not any(row)]
    require(zeros == [1,3,4,5,9], "diagonal zero-sector control failed")
    return {"diagonal_average_cutoffs": CUTOFFS, "order24_polynomial": target,
            "raw_before_polynomial": before, "raw_after_polynomial": after,
            "sector_half_block_polynomials": rows, "zero_sectors": zeros}


def moments(modes, point):
    rate = mp.pi/12
    displacement = real(CUSP-point)
    return {m: coefficient*e(Fraction(-m*m, 576))*gaussian_moment(m, displacement, rate)
            for m, coefficient in modes.items()}


def averaged_rows(terms):
    rows = {}
    for cutoff in CUTOFFS:
        upper = mode_count(cutoff)
        lower = upper-FULL_SHIFT
        early = mp.fsum(atom for m, atom in terms.items() if m < lower)
        whole = mp.fsum(atom for m, atom in terms.items() if m < upper)
        rows[cutoff] = (whole, (early+whole)/2)
    return rows


def check_parameter(modes, point):
    runs = []
    for precision, order in RUNS:
        with mp.workdps(precision):
            rows = averaged_rows(moments(modes, point))
            reference, splice, tail = period_integral(24, point, order)
            runs.append((rows, reference, splice, tail))
    earlier, final = runs
    rows, reference, splice, tail = final
    repeat = max(abs(a-b) for cutoff in CUTOFFS for a, b in zip(earlier[0][cutoff], rows[cutoff]))
    require(max(abs(reference-earlier[1]), splice, tail, repeat) < mp.mpf("1e-25"),
            "period quadrature or numerical repeat failed")
    result = []
    for cutoff, (raw, averaged) in rows.items():
        lower = mode_count(cutoff)-FULL_SHIFT
        entry = {"cutoff": cutoff, "frequency_window": [lower, mode_count(cutoff)],
                 "raw_error": scalar(abs(raw-reference)), "averaged_error": scalar(abs(averaged-reference))}
        if lower >= FULL_SHIFT:
            bound = 8*mp.sqrt(12)*FULL_SHIFT**2/(lower-1)
            require(abs(averaged-reference) <= bound, "averaged period exceeds its proved bound")
            entry["proved_uniform_bound_evaluated"] = scalar(bound)
        result.append(entry)
    if point == ORDER34:
        raw, averaged = rows[INPUT_DEGREE]
        require(abs(averaged-reference) < abs(raw-reference), "order-34 averaging control failed")
    return {"x": str(point), "reference": coordinates(reference), "cutoffs": result}


def run():
    modes = recovered_modes()[INPUT_DEGREE]
    controls = exact_controls(modes)
    with mp.workdps(RUNS[-1][0]):
        diagonal = cusp_values(CUSP)[2]
        for _, averaged in averaged_rows(moments(modes, CUSP)).values():
            require(abs(averaged-diagonal) < mp.mpf("1e-60"), "diagonal integral normalization changed")
        cases = [check_parameter(modes, x) for x in PARAMETERS]
        diagonal_value = coordinates(diagonal)
    sources = (Path(__file__).resolve(), Path(__file__).with_name("check_shadow_period.py").resolve(),
               Path(__file__).with_name("check_shadow_reconstruction.py").resolve(),
               ROOT/"tools/check_quantum_transport34.py")
    return {"status": "PASS", "modulus": PRIMARY, "input_coefficients": INPUT_DEGREE+1,
            "mpmath": mp.__version__, "working_decimal_digits_and_orders": RUNS,
            "source_sha256": {str(p.relative_to(ROOT)): sha256(p.read_bytes()).hexdigest() for p in sources},
            "exact_controls": controls, "diagonal_value": diagonal_value,
            "off_diagonal_comparisons": len(CUTOFFS)*len(PARAMETERS),
            "cases": cases,
            "scope": "Integer polynomial controls, plus numerical quadrature with precision replication."}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--receipt", type=Path)
    args = parser.parse_args()
    result = json.dumps(run(), indent=2) + "\n"
    if args.receipt:
        args.receipt.write_text(result)
    print(result, end="")


if __name__ == "__main__":
    main()
