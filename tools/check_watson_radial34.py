#!/usr/bin/env python3
"""Check radial cancellation at the positive-angle primitive order-34 root.

Use Python 3 and mpmath==1.3.0. The rank series f, the Euler product b and
the single-denominator series phi(-q) are evaluated separately.
"""

import argparse
import hashlib
import json
from pathlib import Path

import mpmath as mp


RADII = ("0.999", "0.9998", "0.99995", "0.99999")
PRECISIONS = (135, 175)
TOLERANCE = "1e-55"


def require(condition, message):
    if not condition:
        raise ArithmeticError(message)


def digits(x):
    return mp.nstr(x, 36)


def complex_digits(z):
    return {"real": mp.nstr(z.real, 88), "imag": mp.nstr(z.imag, 88)}


def cusp_value(zeta):
    """FOR's finite -4U sum and its independently reduced degree-15 polynomial."""
    square_product = 1
    finite = mp.mpc(0)
    for n in range(17):
        finite -= 4 * zeta**(n+1) * square_product
        square_product *= (1 + zeta**(n+1))**2
    coeff = (-4, 8, -4, 8, -8, 12, -8, 8, -4, 8, -12, 12, -8, 8, -8, 12)
    polynomial = mp.polyval(coeff[::-1], zeta)
    require(abs(finite - polynomial) < mp.mpf(TOLERANCE), "finite endpoint disagreement")
    return finite


def evaluate(radius, precision):
    with mp.workdps(precision):
        t = mp.mpf(radius)
        zeta = mp.expjpi(mp.mpf(1)/17)
        q = t*zeta
        square = q*q
        endpoint = cusp_value(zeta)
        # For n >= N both successive summand norm ratios decrease below one.
        cutoff = int(mp.ceil(mp.log(mp.mpf(1)/4) / mp.log(t)))
        qn, odd = mp.mpc(1), q
        f, f_term = mp.mpc(1), mp.mpc(1)
        phi, phi_term = mp.mpc(1), mp.mpc(1)
        b_prefix = mp.mpc(1)
        for _ in range(cutoff):
            qn *= q
            factor = 1 + qn
            f_term *= odd / factor**2
            phi_term *= -odd / (1 + qn**2)
            f += f_term
            phi += phi_term
            b_prefix *= (1 - qn) / factor**2
            odd *= square

        f_ratio = t**(2*cutoff+1) / (1 - t**(cutoff+1))**2
        phi_ratio = t**(2*cutoff+1) / (1 - t**(2*cutoff+2))
        require(max(f_ratio, phi_ratio) < 1, "series truncation is too early")
        f_error = abs(f_term)*f_ratio/(1-f_ratio)
        phi_error = abs(phi_term)*phi_ratio/(1-phi_ratio)

        # Expand log(1-z)-2log(1+z) for every omitted z=q^j, j>N.
        # Absolute convergence permits summing the geometric series in j.
        v = t**(cutoff+1)
        terms = int(mp.ceil((precision+12)*mp.log(10)/(-mp.log(v))))
        qk, yk, log_tail = mp.mpc(1), mp.mpc(1), mp.mpc(0)
        y = qn*q
        for k in range(1, terms+1):
            qk *= q
            yk *= y
            log_tail += (2*(-1)**k-1)*yk/(k*(1-qk))
        b = b_prefix * mp.exp(log_tail)
        log_error = 3*v**(terms+1) / ((terms+1)*(1-t)*(1-v))
        b_error = abs(b)*mp.expm1(log_error)
        require(max(f_error, phi_error, b_error) < mp.mpf(TOLERANCE),
                "analytic series truncation budgets exceeded")

        compensated = f+b
        residual = abs(compensated-2*phi)
        require(residual < mp.mpf(TOLERANCE), "Watson interior identity disagrees")
        return {
            "f": f, "b": b, "twice_phi": 2*phi, "f_plus_b": compensated,
            "endpoint": endpoint, "endpoint_distance": abs(compensated-endpoint),
            "wrong_sign_distance": abs(f-b-endpoint), "watson_residual": residual,
            "cutoff": cutoff, "log_terms": terms,
            "f_tail": f_error, "b_tail": b_error, "phi_tail": phi_error,
        }


def run():
    require(mp.__version__ == "1.3.0", "reproduction requires mpmath==1.3.0")
    with mp.workdps(max(PRECISIONS)):
        rows = []
        previous_distance = mp.inf
        for radius in RADII:
            low, high = (evaluate(radius, precision) for precision in PRECISIONS)
            changes = {name: abs(high[name]-low[name])
                       for name in ("f", "b", "twice_phi", "f_plus_b")}
            require(max(changes.values()) < mp.mpf(TOLERANCE), "precision replay disagrees")
            require(high["endpoint_distance"] < previous_distance, "radial distances out of order")
            require(high["wrong_sign_distance"] > 10*high["endpoint_distance"],
                    "opposite compensation sign control inconclusive")
            previous_distance = high["endpoint_distance"]
            rows.append({
                "radius": radius, "series_cutoff_and_product_prefix": high["cutoff"],
                "f": complex_digits(high["f"]), "b": complex_digits(high["b"]),
                "twice_phi_at_neg_q": complex_digits(high["twice_phi"]),
                "f_plus_b": complex_digits(high["f_plus_b"]),
                "distance_to_finite_boundary": digits(high["endpoint_distance"]),
                "opposite_sign_distance_to_boundary": digits(high["wrong_sign_distance"]),
                "absolute_precision_changes": {key: digits(v) for key, v in changes.items()},
                "precision_runs": [{
                    "decimal_digits": dps, "log_product_tail_terms": data["log_terms"],
                    "absolute_watson_residual": digits(data["watson_residual"]),
                    "truncation_bounds": {key: digits(data[key]) for key in ("f_tail", "b_tail", "phi_tail")},
                } for dps, data in zip(PRECISIONS, (low, high))],
            })
        require(previous_distance < mp.mpf("0.05"), "final sample is too far from the finite cusp")
        return {
            "source": "Watson, The final problem, p. 63; Folsom–Ono–Rhoades, Theorem 1.1",
            "root": "exp(2*pi*i/34)", "finite_boundary": complex_digits(high["endpoint"]),
            "mpmath": mp.__version__, "absolute_tolerance": TOLERANCE,
            "command": "python3 tools/check_watson_radial34.py --receipt evidence/current/quantum-radial/watson34.json",
            "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            "series_rule": "Sum defining f and phi(-q) through N = ceil(log(1/4)/log(t)). Bound each remaining tail by its final term's norm times rho/(1-rho), with rho the next ratio bounded using |1+q^j| >= 1-t^j.",
            "product_rule": "Multiply the b(q) factors through N. For j>N sum their log by geometric series. After M log terms the absolute log error is at most 3*t^((N+1)*(M+1))/((M+1)*(1-t)*(1-t^(N+1))).",
            "scope": "Finite numerical samples on one radial path. Truncation estimates exclude floating-point error; the two precisions compare those effects independently.",
            "samples": rows,
        }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--receipt", type=Path, help="write the JSON result to this path")
    args = parser.parse_args()
    result = json.dumps(run(), indent=2, ensure_ascii=False) + "\n"
    if args.receipt:
        args.receipt.write_text(result, encoding="utf-8")
    else:
        print(result, end="")


if __name__ == "__main__":
    main()
