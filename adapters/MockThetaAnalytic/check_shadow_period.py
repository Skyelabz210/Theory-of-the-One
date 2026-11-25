#!/usr/bin/env python3
"""Replay the S6 reconstruction of the FKTY cusp period with mpmath 1.3.0."""

import argparse
from fractions import Fraction
from hashlib import sha256
import json
from math import isqrt
from pathlib import Path
import sys

import mpmath as mp

from check_shadow_reconstruction import (
    CUTOFFS, INPUT_DEGREE, PRIMARY, SECTORS, first_moment, mock_coefficients,
    parity_readings, recover_eta,
)

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "tools"))
from check_quantum_transport34 import cusp_values, e, period_integral, real, sign6


CUSP = Fraction(-1, 24)
ORDER34 = Fraction(-1, 34)
PARAMETERS = (ORDER34, Fraction(0), Fraction(-1, 20))
DEGREES = (*CUTOFFS, INPUT_DEGREE)
FULL_SHIFT = 144
SECTOR_SHIFT = 1584
RUNS = ((55, 24), (75, 36))


def require(condition, message):
    if not condition:
        raise ArithmeticError(message)


def sector(m):
    return -m*m % 11


def signed_cusp_exponent(m):
    """Encode the sign and the quadratic phase as one exponent modulo 576."""
    s = sign6(m)
    return None if s == 0 else (-m*m + 288*(s < 0)) % 576


def check_shifts():
    period = 2 * SECTOR_SHIFT
    for m in range(period):
        phase = signed_cusp_exponent(m)
        opposite = None if phase is None else (phase + 288) % 576
        for shift in (FULL_SHIFT, SECTOR_SHIFT):
            require(signed_cusp_exponent(m+shift) == opposite, "cusp phase failed to reverse")
        require(sector(m+SECTOR_SHIFT) == sector(m), "sector changed under its pairing shift")
    pair = (sector(1), sector(1+FULL_SHIFT))
    require(pair == (10, 7), "the single-shift sector control failed")
    return {"exact_phase_comparisons": 2*period, "exact_sector_comparisons": period,
            "mode_one_sectors_under_144": pair}


def recovered_modes():
    residues = mock_coefficients(INPUT_DEGREE, PRIMARY)
    bits = parity_readings(INPUT_DEGREE, enumerate(residues))
    observed = {}
    for cutoff in DEGREES:
        eta = recover_eta(bits[:cutoff+1])
        end = isqrt(24*cutoff+1)
        weights = {}
        for degree, sign in eta.items():
            m = isqrt(degree)
            weights[m] = first_moment(m)*sign//2
        reference = {m: 2*m*sign6(m) for m in range(1, end+1) if sign6(m)}
        require(weights == reference, "reconstructed theta normalization or support changed")
        observed[cutoff] = weights
    return observed


def gaussian_moment(m, displacement, rate):
    """Integrate i exp(-rate*m²*t) / sqrt(displacement+i*t) over t>0."""
    decay = rate*m*m
    branch = mp.sqrt(-mp.j*decay)
    return (mp.sqrt(mp.pi)/branch * mp.exp(-mp.j*decay*displacement)
            * mp.erfc(branch*mp.sqrt(displacement)))


def finite_periods(weights, point):
    rate = mp.pi/12
    displacement = real(CUSP-point)
    terms = {}
    for m, coefficient in weights[INPUT_DEGREE].items():
        terms[m] = coefficient * e(Fraction(-m*m, 576)) * gaussian_moment(m, displacement, rate)
    rows = {}
    for cutoff, modes in weights.items():
        full = mp.fsum(terms[m] for m in modes)
        sectors = {r: mp.fsum(terms[m] for m in modes if sector(m) == r) for r in range(11)}
        require(all(sectors[r] == 0 for r in range(11) if r not in SECTORS), "zero sector gained support")
        require(abs(mp.fsum(sectors.values())-full) < mp.mpf("1e-48"), "sector additivity changed")
        rows[cutoff] = full
    worst_moment_error = 0
    for m in (1, 7, 145):
        decay = rate*m*m
        direct = mp.quad(lambda s: mp.j*mp.exp(-s)/(decay*mp.sqrt(displacement+mp.j*s/decay)),
                         [0, 1, 8, 32, mp.inf])
        worst_moment_error = max(worst_moment_error, abs(direct-gaussian_moment(m, displacement, rate)))
    return rows, worst_moment_error


def scalar(value):
    return mp.nstr(value, 16)


def coordinates(value):
    return {"real": scalar(value.real), "imag": scalar(value.imag)}


def phase_exponent(parity, residue, odd_modulus):
    return residue + odd_modulus*((parity-residue) % 2)


def translated_ten(parity, mod5):
    """Evaluate the five nonzero packet bins with lane-translated characters."""
    product = 1
    total = 0
    for degree in range(1, 6):
        exponent = phase_exponent((parity+degree) % 2, (mod5+degree) % 5, 5)
        total += product * e(Fraction(exponent, 10))
        product *= (1 + e(Fraction(degree, 10)))**2
    return -4*total


def check_translated_boundary(period, reference34, canonical, scale34):
    scale10 = mp.sqrt(12j)*e(Fraction(-1, 240))
    bound = Fraction(7680, isqrt(24*INPUT_DEGREE+1))
    rows = []
    for source in (0, PRIMARY, -1):
        parity, mod5, mod17 = source % 2, source % 5, source % 17
        e34 = phase_exponent(parity, mod17, 17)
        e10 = phase_exponent(parity, mod5, 5)
        require((e34, e10) == (source % 34, source % 10), "source phase mismatch")
        endpoint10 = translated_ten(parity, mod5) / e(Fraction(e10, 10))
        estimate = e(Fraction(e34, 34)) * (period + mp.sqrt(mp.mpf(17)/5)*scale10*endpoint10) / scale34
        reference = e(Fraction(source, 34))*reference34
        require(abs(estimate-e(Fraction(source, 34))*canonical) < mp.mpf("1e-48"),
                "packet normalization or translated phase changed")
        error = abs(estimate-reference)
        require(error <= real(bound), "translated endpoint exceeds the Lean bound")
        rows.append({"source": source, "primary": source % PRIMARY, "mod17": mod17,
                     "exponent10": e10, "exponent34": e34, "estimate": coordinates(estimate),
                     "terminating_reference": coordinates(reference), "absolute_error": scalar(error)})
    zero, alias = rows[:2]
    require(zero["primary"] == alias["primary"] and zero["exponent10"] == alias["exponent10"] and
            zero["mod17"] != alias["mod17"] and zero["exponent34"] != alias["exponent34"],
            "primary-only collision control failed")
    return {"degree": INPUT_DEGREE, "exact_truncation_bound": str(bound), "sources": rows}


def check_precision_cutoffs():
    checks = []
    for n in (1, 2, 10, 1000):
        degree = 2457600*n*n
        last_mode = isqrt(24*degree+1)
        require(Fraction(7680, last_mode) <= Fraction(1, n), "insufficient coefficient cutoff")
        checks.append({"reciprocal_precision": n, "degree": degree, "last_mode": last_mode})
    return checks


def check_parameter(weights, point):
    cooked = []
    for precision, order in RUNS:
        with mp.workdps(precision):
            rows, mode_error = finite_periods(weights, point)
            oracle, splice_error, truncation = period_integral(24, point, order)
            cooked.append((rows, mode_error, oracle, splice_error, truncation))
    before, after = cooked
    rows, mode_error, oracle, splice_error, truncation = after
    mode_error = max(before[1], mode_error)
    repeat_error = max(abs(rows[d]-before[0][d]) for d in DEGREES)
    oracle_repeat_error = abs(oracle-before[2])
    require(max(mode_error, repeat_error, oracle_repeat_error, splice_error, truncation) < mp.mpf("1e-27"),
            "period or one-mode quadrature failed to reproduce")
    delta = abs(real(CUSP-point))
    rows_json = []
    for cutoff, value in rows.items():
        error = abs(value-oracle)
        bound = 4*FULL_SHIFT / ((mp.pi/12) * isqrt(24*cutoff+1) * mp.sqrt(delta))
        require(error < bound, "the reconstructed period violates the proved bound")
        rows_json.append({"coefficient_cutoff": cutoff, "last_mode": isqrt(24*cutoff+1),
                          "absolute_error": scalar(error), "proved_bound_evaluated": scalar(bound)})
    result = {"x": str(point), "distance_from_start": str(abs(CUSP-point)), "poisson_period": coordinates(oracle),
              "largest_prefix_period": coordinates(rows[INPUT_DEGREE]), "cutoffs": rows_json}
    if point == ORDER34:
        other = cusp_values(Fraction(-1, 10))[2]
        _, unimodal34, order34, _ = cusp_values(point)
        multiplier = mp.sqrt(mp.mpf(17)/5)
        defect = order34 - multiplier*other
        require(abs(defect-oracle) < mp.mpf("1e-27"), "finite cusp defect disagrees with the Poisson period")
        scale = mp.sqrt(12j)*e(point/24)
        estimate = (rows[INPUT_DEGREE] + multiplier*other)/scale
        require(abs(2*rows[INPUT_DEGREE]-defect) > 1, "missing factor of one half control failed")
        result["order34_checks"] = {
            "finite_cusp_defect": coordinates(defect),
            "poisson_and_finite_defect_agree_to": "1e-27",
            "order34_boundary_estimate": coordinates(estimate),
            "order34_boundary_error": scalar(abs(estimate-order34/scale)),
            "translated_boundary": check_translated_boundary(
                rows[INPUT_DEGREE], -4*unimodal34, estimate, scale),
            "integer_cutoffs": check_precision_cutoffs(),
            "omitting_half_absolute_error": scalar(abs(2*rows[INPUT_DEGREE]-defect)),
        }
    return result


def run():
    weights = recovered_modes()
    controls = check_shifts()
    sources = (Path(__file__).resolve(), Path(__file__).with_name("check_shadow_reconstruction.py").resolve(),
               ROOT / "tools/check_quantum_transport34.py")
    with mp.workdps(RUNS[-1][0]):
        checks = [check_parameter(weights, x) for x in PARAMETERS]
    return {"status": "PASS", "modulus": PRIMARY, "input_coefficients": INPUT_DEGREE+1,
            "mpmath": mp.__version__,
            "working_decimal_digits_and_orders": RUNS,
            "source_sha256": {str(p.relative_to(ROOT)): sha256(p.read_bytes()).hexdigest() for p in sources},
            "shift_checks": controls, "finite_integral_comparisons": len(DEGREES)*len(PARAMETERS),
            "sector_additivity_comparisons": len(DEGREES)*len(PARAMETERS)*len(RUNS),
            "cases": checks,
            "scope": "Numerical quadrature and precision replication. The uniform bound is proved in Lean."}


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
