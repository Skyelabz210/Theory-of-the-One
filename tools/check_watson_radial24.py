#!/usr/bin/env python3
"""Replay the signed order-24 readout and complementary Watson limit.

The exact checks use integer polynomial arithmetic. The disk series checks
use mpmath 1.3.0 with separate truncation estimates and precision replays.
"""

import argparse
from hashlib import sha256
from itertools import chain
import json
from math import gcd, lcm
from pathlib import Path

import mpmath as mp

from check_quantum_radial import crank_product, rank_series, require


PRIMARY = 30030
ORDER = 24
HALF = ORDER // 2
PERIOD = lcm(PRIMARY, ORDER)
GENERATORS = tuple(h for h in range(ORDER) if gcd(h, ORDER) == 1)
DIRECT_RADII = ("0.98", "0.995")
NEAR_RADII = ("0.999", "0.9999", "0.99999", "0.999999")
PRECISIONS = (70, 100)
BLOCKS = 144


def polynomial(size, terms):
    """Reduce sparse terms, including negative degrees, modulo q^size+1."""
    row = [0] * size
    for power, value in terms:
        quotient, residue = divmod(power, size)
        row[residue] += value if quotient % 2 == 0 else -value
    return tuple(row)


def exact_boundary():
    def odd_head(size):
        # Clear each denominator against the full twelve-factor product.
        suffix = polynomial(size, [(0, 1)])
        summands = []
        for n in reversed(range(HALF)):
            power = 2*n+1
            suffix = polynomial(size, ((i, c) for j, c in enumerate(suffix)
                                      for i in (j, j+power)))
            summands.extend((j+n*n, (-1)**n*c) for j, c in enumerate(suffix))
        return suffix, polynomial(size, summands)

    den, numerator = odd_head(HALF)
    order8_den, _ = odd_head(4)
    require(order8_den == (8, 0, 0, 0), "imprimitive root control changed")

    square_product = [(0, 1)]
    u_terms = []
    f_terms = []
    reflected_product = [(0, 1)]
    for j in range(1, HALF+1):
        u_terms.extend((i, c, j) for i, c in square_product)
        f_terms.extend((i, (-1)**j*c) for i, c in reflected_product)
        square_product = list(enumerate(polynomial(HALF,
            ((i+e*j, c*k) for i, c in square_product for e, k in enumerate((1, 2, 1))))))
        reflected_product = list(enumerate(polynomial(HALF,
            ((i, c) for n, c in reflected_product for i in (n, n-j)))))
    u = polynomial(HALF, ((i+d, c) for i, c, d in u_terms))
    require(polynomial(HALF, f_terms) == u, "reflection to the FKTY cusp disagrees")
    # q^8 = q^4-1 at a primitive root, but need not hold at order eight.
    cyclotomic = [(8, 1), (4, -1), (0, 1)]
    require(den == polynomial(HALF, [(0, 2)] + [(i, 2*c) for i, c in cyclotomic]),
            "odd block denominator identity failed")
    require(numerator == polynomial(HALF, [(0, 1), *enumerate(u)] +
                [(i+2, 2*c) for i, c in cyclotomic] + [(i+1, -2*c) for i, c in cyclotomic]),
            "cleared Watson head and finite FOR value disagree")
    return {
        "odd_denominator": den, "cleared_watson_head": numerator,
        "for_boundary_at_positive_root": tuple(-4*c for c in u),
        "order8_odd_denominator_control": order8_den,
    }, u_terms


def exact_readouts(terms, boundary):
    offsets = (-PERIOD-1, -PRIMARY, -24, -1, 0, 1, 23, 24, PRIMARY, PERIOD+1)

    def readout(r, a):
        require((a-r) % 2 == 0, "same-source parity overlap failed")
        k = (3*((a-r)//2)) % 4
        return k, (r % ORDER+6*k) % ORDER

    extremes = (-10**60-1, -10**60, 10**60, 10**60+1)
    for source in chain(range(-PERIOD//2, PERIOD//2), extremes):
        k, r = divmod(source, PRIMARY)
        a = source % 8
        require(readout(r, a) == (k % 4, source % ORDER), "signed winding or exponent disagrees")
        for d in offsets:
            _, exponent = readout((r+d) % PRIMARY, (a+d) % 8)
            require(exponent == (source+d) % ORDER, "translated exponent disagrees")

    packet_sources = (*extremes, -PERIOD-1, -PRIMARY, -1, 0, 1, PRIMARY, 2*PRIMARY, PERIOD+1)
    for source in packet_sources:
        r, a = source % PRIMARY, source % 8
        _, exponent = readout(r, a)
        dephased = polynomial(HALF, ((i+readout((r+d) % PRIMARY, (a+d) % 8)[1]-exponent, -4*c)
                                      for i, c, d in terms))
        require(dephased == boundary, "dephased packet changed the exact FOR polynomial")

    periods = [lcm(PRIMARY, a) for a in range(1, 9)]
    require(all(p % ORDER for p in periods[:-1]) and periods[-1] == PERIOD,
            "least single anchor changed")
    require(2*PRIMARY % 4 == 0 and 2*PRIMARY % ORDER == HALF,
            "mod-four sign-alias control failed")
    return {"least_anchor_modulus": 8, "quotient_resolution": PERIOD//PRIMARY,
            "checked_signed_sources": PERIOD+len(extremes),
            "checked_translations": (PERIOD+len(extremes))*len(offsets),
            "exact_packet_sources": packet_sources, "mod4_alias_sources": [0, 2*PRIMARY]}


def radial_sample(h, radius, precision):
    with mp.workdps(precision):
        z = [mp.expjpi(mp.mpf(2*h*j)/ORDER) for j in range(ORDER)]
        t = mp.mpf(radius)
        term = endpoint_term = mp.mpc(1)
        interior = mp.mpc(0)
        endpoint_norms = 1
        for n in range(1, BLOCKS*HALF):
            odd = 2*n-1
            v = z[odd % ORDER]
            w = t**odd * v
            term *= -w/(1+w)
            interior += term
            if n < HALF:
                endpoint_term *= -v/(1+v)
                endpoint_norms += abs(endpoint_term)
        compensated = -4*interior
        # The omitted blocks are dominated by their endpoint magnitudes.
        tail = 8*endpoint_norms/mp.mpf(2)**BLOCKS
        if radius not in DIRECT_RADII:
            return compensated, tail, None
        f, f_terms, f_tail = rank_series(t, z, HALF)
        b, b_terms, b_tail = crank_product(t, z, HALF)
        return compensated, tail, (f, b, f_terms, b_terms, f_tail+b_tail)


def numerical_boundary(boundary):
    rows = []
    with mp.workdps(max(PRECISIONS)):
        tolerance = mp.mpf("1e-34")
        for h in GENERATORS:
            z = mp.expjpi(mp.mpf(2*h)/ORDER)
            endpoint = mp.polyval(boundary[::-1], z)
            previous_distance = mp.inf
            for radius in (*DIRECT_RADII, *NEAR_RADII):
                low, high = (radial_sample(h, radius, p) for p in PRECISIONS)
                value, tail, direct = high
                replay_error = abs(value-low[0])
                distance = abs(value-endpoint)
                require(max(replay_error, tail) < tolerance, "stable radial precision budget exceeded")
                row = {"generator": h, "radius": radius, "distance_to_boundary": mp.nstr(distance, 18),
                       "stable_tail_bound": mp.nstr(tail, 12), "stable_precision_change": mp.nstr(replay_error, 12)}
                if direct is not None:
                    f, b, f_terms, b_terms, direct_tail = direct
                    residual = abs(f-b-value)
                    precision_change = max(abs(a-c) for a, c in zip(direct[:2], low[2][:2]))
                    wrong_sign = abs(f+b-value)
                    require(max(residual, direct_tail, precision_change) < tolerance, "direct disk identity disagrees")
                    require(wrong_sign > 100*tolerance, "opposite compensation control is inconclusive")
                    row.update(direct_rank_terms=f_terms, direct_crank_factors=b_terms,
                               direct_tail_bound=mp.nstr(direct_tail, 12), direct_residual=mp.nstr(residual, 12),
                               direct_precision_change=mp.nstr(precision_change, 12),
                               opposite_sign_residual=mp.nstr(wrong_sign, 12))
                else:
                    require(distance < previous_distance, "near-boundary samples do not approach the endpoint")
                    previous_distance = distance
                rows.append(row)
            require(previous_distance < mp.mpf("0.01"), "last sample fell outside the endpoint tolerance")
    return rows


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--receipt", type=Path)
    args = parser.parse_args()
    require(mp.__version__ == "1.3.0", "replay requires mpmath==1.3.0")
    exact, terms = exact_boundary()
    boundary = exact["for_boundary_at_positive_root"]
    receipt = {"status": "PASS", "order": ORDER, "primary": PRIMARY, "period": PERIOD,
               "mpmath": mp.__version__, "decimal_precisions": PRECISIONS, "stable_blocks": BLOCKS,
               "source_sha256": {p.name: sha256(p.read_bytes()).hexdigest() for p in
                                  (Path(__file__), Path(__file__).with_name("check_quantum_radial.py"))},
               "exact_polynomials": exact, "signed_readout": exact_readouts(terms, boundary),
               "radial_samples": numerical_boundary(boundary)}
    result = json.dumps(receipt, indent=2) + "\n"
    if args.receipt:
        args.receipt.write_text(result, encoding="utf-8")
    else:
        print(result, end="")


if __name__ == "__main__":
    main()
