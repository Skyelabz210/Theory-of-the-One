#!/usr/bin/env python3
"""Check Zwegers's first completed component at 24τ. Requires mpmath==1.3.0.

Reproduce with python3 tools/check_analytic_shadow.py --receipt result.json.
The three rational fixtures are in the upper half-plane. Computable tail bounds
below concern the exact sums and integrals. Quadrature, arithmetic, and the
centered differences use ordinary multiprecision numerical approximations.

Zwegers, Mock θ-functions and real analytic modular forms, §§3.1–3.6,
especially (3.2), (3.9), (3.23), (3.29), (3.31).
https://doi.org/10.1090/conm/291/04907
"""

import argparse
import hashlib
import json
import math
from pathlib import Path
import sys

import mpmath as mp


# z = 24τ in Zwegers's notation. Use q = exp(2πiτ) at the scaled input.
FIXTURES = ((1, 7, 1, 40), (-2, 11, 1, 16), (2, 9, 1, 8))
MAX_SUMMAND = 8
MAX_DEGREE = 40
MAX_ROOT = 36
QUAD_SEGMENTS = (0, 1, 4, 16, 64, 128, 384)


def sign6(m):
    return {1: 1, 5: -1}.get(m % 6, 0)


def nome(tau):
    return mp.exp(2 * mp.pi * mp.j * tau)


def holomorphic(tau):
    """q^(-1) f(q^24) via the original hypergeometric summands."""
    Q = nome(24 * tau)
    denominator = mp.mpc(1)
    value = mp.mpc(1)
    for n in range(1, MAX_SUMMAND + 1):
        denominator *= (1 + Q**n)**2
        value += Q**(n*n) / denominator
    return value / nome(tau)


def f_coefficients():
    """Independent Taylor prefix by finite convolution of the inverse factors."""
    inverse = [1] + [0] * MAX_DEGREE
    coeffs = inverse.copy()
    for n in range(1, math.isqrt(MAX_DEGREE) + 1):
        inverse = [sum((-1)**k * (k + 1) * inverse[d - n*k]
                       for k in range(d // n + 1))
                   for d in range(MAX_DEGREE + 1)]
        for d in range(n*n, MAX_DEGREE + 1):
            coeffs[d] += inverse[d - n*n]
    return coeffs


def theta(tau):
    """Θ(τ) = −6g₁(24τ) from positive square roots."""
    q = nome(tau)
    return mp.fsum(sign6(m) * m * q**(m*m) for m in range(1, MAX_ROOT + 1))


def correction_erfc(tau):
    """Nonholomorphic part of H₀(24τ) from the incomplete gamma expansion."""
    factor = mp.sqrt(4 * mp.pi * tau.imag)
    q = nome(tau)
    return -2 * mp.fsum(sign6(m) * mp.erfc(m * factor) * q**(-m*m)
                         for m in range(1, MAX_ROOT + 1) if sign6(m))


def correction_integral(tau):
    """−G₀(24τ), integrating the signed bilateral g₁ directly on the vertical ray."""
    scaled = 24 * tau
    start = -scaled.conjugate()
    terms = []
    for n in range(-MAX_ROOT, MAX_ROOT + 1):
        if abs(6*n + 1) <= MAX_ROOT:
            characteristic = n + mp.mpf(1) / 6
            frequency = 3 * mp.pi * characteristic**2
            # g₁(w) = −Σ (n+1/6) exp(i frequency w), w = start + i v.
            terms.append((frequency, -characteristic * mp.exp(mp.j * frequency * start)))

    def integrand(v):
        g1 = mp.fsum(a * mp.exp(-f * v) for f, a in terms)
        return g1 / mp.sqrt(2 * scaled.imag + v)

    # −2i√3 from H=F−G and dz=i dv on the vertical ray.
    return 2 * mp.sqrt(3) * mp.quad(integrand, QUAD_SEGMENTS)


def completed(tau):
    return holomorphic(tau) + correction_erfc(tau)


def xi_difference(tau, h):
    """ξ_{1/2} = 2i √y conjugate(∂/∂barτ), using both real coordinates."""
    dx = (completed(tau + h) - completed(tau - h)) / (2*h)
    dy = (completed(tau + mp.j*h) - completed(tau - mp.j*h)) / (2*h)
    return mp.j * mp.sqrt(tau.imag) * (dx + mp.j * dy).conjugate()


def projected_derivatives(tau):
    """Compare ξ(P_r H) from translation averages to direct square-residue sums."""
    h = mp.mpf("1e-18")
    tolerance = mp.mpf("1e-27")
    j = mp.j
    shifts = [mp.mpf(k) / 11 for k in range(11)]
    offsets = (h, -h, j*h, -j*h)
    # Evaluate the four centered stencils once at each translated input.
    samples = [[completed(tau + shift + offset) for shift in shifts] for offset in offsets]
    q = nome(tau)
    theta_by_degree = [mp.fsum(4 * sign6(m) * m * q**(m*m)
                               for m in range(1, MAX_ROOT + 1) if m*m % 11 == r)
                       for r in range(11)]
    rows = []
    for r in range(11):
        weights = [mp.exp(-2 * mp.pi * j * r * shift) / 11 for shift in shifts]
        plus_x, minus_x, plus_y, minus_y = [
            mp.fsum(w * u for w, u in zip(weights, stencil)) for stencil in samples]
        derivative = ((plus_x - minus_x) + j * (plus_y - minus_y)) / (2*h)
        observed = j * mp.sqrt(tau.imag) * derivative.conjugate()
        expected = theta_by_degree[(-r) % 11]
        error = abs(observed - expected)
        passed = error < tolerance
        row = {"completion_class": r, "shadow_degree_class": (-r) % 11,
               "observed_xi": complex_value(observed), "four_theta_by_degree": complex_value(expected),
               "absolute_discrepancy": fmt(error)}
        if r in (1, 10):
            # Class 1 has vanishing projected shadow; class 10 contains the
            # leading Fourier mode. A commuting rule without −r interchanges them.
            separation = abs(observed - theta_by_degree[r])
            row["same_class_negative_control_separation"] = fmt(separation)
            passed = passed and separation > mp.mpf("1e-3")
        row["status"] = "PASS" if passed else "FAIL"
        rows.append(row)
    return rows


def tail_bounds(tau, h):
    """Exact-arithmetic majorants, evaluated at the worst y on the stencil."""
    low, high = tau.imag - h, tau.imag + h
    rho = mp.exp(-48 * mp.pi * low)
    prefactor = mp.exp(2 * mp.pi * high)
    # For |Q|≤u<1/2, each finite product of |1+Q^j| is ≥1−Σ_{j≥1}u^j.
    denom = (1 - 2*rho) / (1 - rho)
    n = MAX_SUMMAND + 1
    hyper = prefactor * rho**(n*n) / (denom**2 * (1 - rho**(2*n + 1)))

    # On |Q|=1/4, |f|≤1/(1−R)/(1−R/(1−R))². Cauchy's coefficient
    # estimate and a geometric tail bound apply to the Taylor approximation.
    R = mp.mpf(1) / 4
    assert 0 < rho < R
    majorant = (1 - R) / (1 - 2*R)**2
    taylor = prefactor * majorant * (rho / R)**(MAX_DEGREE + 1) / (1 - rho / R)

    # (m+k)²≥m²+(2m+1)k at integers k≥0. For the nonholomorphic tail
    # use erfc(u)≤exp(−u²) at u≥0 and |q^(−m²)|=exp(2πy m²).
    a = 2 * mp.pi * low
    m = MAX_ROOT + 1
    first, ratio = mp.exp(-a*m*m), mp.exp(-a*(2*m + 1))
    unary = first * (m / (1 - ratio) + ratio / (1 - ratio)**2)
    correction = 2 * first / (1 - ratio)

    # Retained modes beyond height V: bound the denominator by √(48y+V)
    # and integrate each exponential e^(−πm²v/12) exactly.
    V = QUAD_SEGMENTS[-1]
    vertical = 4 * mp.sqrt(3) / (mp.pi * mp.sqrt(48 * low + V)) * mp.fsum(
        mp.exp(-(a + mp.pi*V/12) * m*m) / m
        for m in range(1, MAX_ROOT + 1) if sign6(m))
    return {"hypergeometric_tail": hyper, "taylor_tail": taylor,
            "unary_theta_tail": unary, "erfc_series_tail": correction,
            "retained_vertical_modes_after_cutoff": vertical}


def fmt(v):
    return mp.nstr(v, 18)


def complex_value(v):
    return {"real": fmt(v.real), "imag": fmt(v.imag)}


def evaluate(fixture, coeffs):
    xn, xd, yn, yd = fixture
    tau = mp.mpc(mp.mpf(xn) / xd, mp.mpf(yn) / yd)
    h = mp.mpf("1e-18")
    tolerance = mp.mpf("1e-27")
    wrong_margin = mp.mpf("1e-3")
    q = nome(tau)
    polynomial = mp.polyval(list(reversed(coeffs)), q**24) / q
    correction = correction_erfc(tau)
    integral = correction_integral(tau)
    xi = xi_difference(tau, h)
    refined = xi_difference(tau, h / 2)
    expected = 4 * theta(tau)
    bounds = tail_bounds(tau, h)
    # Taking differences divides sample errors by h. Use the smaller width
    # h/2 in the bound. Discretization and floating-point error are tested
    # numerically by step-halving and by comparison to the independent theta.
    bounds["xi_stencil_series_tails"] = 4 * mp.sqrt(tau.imag) / h * (
        bounds["hypergeometric_tail"] + bounds["erfc_series_tail"])
    errors = {
        "holomorphic_vs_taylor": abs(holomorphic(tau) - polynomial),
        "eichler_integral_vs_erfc": abs(integral - correction),
        "xi_vs_4theta": abs(xi - expected),
        "xi_half_step_vs_4theta": abs(refined - expected),
        "xi_step_halving": abs(xi - refined),
    }
    controls = {"reversed_shadow_sign": abs(xi + expected),
                "omitted_xi_dilation_factor": abs(xi - expected / mp.sqrt(24)),
                "theta_at_wrong_argument": abs(xi - 4 * theta(24 * tau))}
    passed = (all(x < tolerance for x in (*bounds.values(), *errors.values()))
              and all(x > wrong_margin for x in controls.values()))
    return {
        "tau": {"real": f"{xn}/{xd}", "imag": f"{yn}/{yd}"},
        "status": "PASS" if passed else "FAIL",
        "completed": complex_value(holomorphic(tau) + correction),
        "xi_half_step": complex_value(refined), "four_theta": complex_value(expected),
        "exact_arithmetic_tail_majorants_numerically_evaluated": {k: fmt(v) for k,v in bounds.items()},
        "absolute_discrepancies": {k: fmt(v) for k,v in errors.items()},
        "negative_control_separations": {k: fmt(v) for k,v in controls.items()},
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--dps", type=int, default=65, help="Decimal working precision (at least 55)")
    parser.add_argument("--receipt", type=Path, help="Write the numerical results as JSON")
    args = parser.parse_args()
    if args.dps < 55:
        parser.error("--dps must be at least 55")
    if mp.__version__ != "1.3.0":
        parser.error("this check uses mpmath==1.3.0")
    mp.mp.dps = args.dps
    coeffs = f_coefficients()
    rows = [evaluate(tau, coeffs) for tau in FIXTURES]
    xn, xd, yn, yd = FIXTURES[0]
    projection = projected_derivatives(mp.mpc(mp.mpf(xn) / xd, mp.mpf(yn) / yd))
    passed = all(row["status"] == "PASS" for row in rows + projection)
    report = {"status": "PASS" if passed else "FAIL",
              "command": ["python3", "tools/check_analytic_shadow.py", "--dps", str(args.dps)]
                         + (["--receipt", str(args.receipt)] if args.receipt else []),
              "source": "https://doi.org/10.1090/conm/291/04907",
              "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              "python": sys.version.split()[0], "mpmath": mp.__version__, "decimal_precision": args.dps,
              "scope": "Pointwise numerical checks with analytic series-tail majorants. "
                       "Differencing, quadrature and rounding are not interval-certified.",
              "max_hypergeometric_index": MAX_SUMMAND, "max_taylor_degree": MAX_DEGREE,
              "max_unary_root_index": MAX_ROOT, "vertical_quadrature_breaks": list(QUAD_SEGMENTS),
              "difference_steps": ["1e-18", "5e-19"], "absolute_tolerance": "1e-27",
              "negative_control_minimum": "1e-3", "points": rows,
              "mod11_projection": {"tau": rows[0]["tau"], "classes": projection}}
    content = json.dumps(report, ensure_ascii=False, indent=2) + "\n"
    if args.receipt:
        args.receipt.parent.mkdir(parents=True, exist_ok=True)
        args.receipt.write_text(content)
    print(content, end="")
    return 0 if passed else 1


if __name__ == "__main__":
    sys.exit(main())
