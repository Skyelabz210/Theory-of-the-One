#!/usr/bin/env python3
"""Check the FKTY weight-1/2 law at x=-1/34, g x=-1/10.

Folsom, Ki, Truong Vu and Yang, J. Number Theory 170 (2017), 315–346,
https://doi.org/10.1016/j.jnt.2016.06.005, (1.2), (1.13), (3.12) and (3.13).
The period is evaluated from its theta coefficients, independently of the
finite cusp sums. Reproduce with Python 3 and mpmath==1.3.0.
"""

import argparse
from fractions import Fraction
import hashlib
import json
from pathlib import Path

import mpmath as mp


X = Fraction(-1, 34)
G = ((1, 0), (24, 1))
PERIOD = 288
MAX_MODE = 110
MAX_HEIGHT = 400
TOLERANCE = "1e-30"


def require(condition, message):
    if not condition:
        raise ArithmeticError(message)


def real(q):
    return mp.mpf(q.numerator) / q.denominator


def e(q):
    return mp.expjpi(2 * real(q))


def scalar(x):
    return mp.nstr(x, 42)


def coordinates(z):
    return {"real": scalar(z.real), "imag": scalar(z.imag)}


def decimal_power_bound(x):
    """A readable upper bound stable under harmless last-place changes."""
    return f"1e{int(mp.ceil(mp.log10(x)))}" if x else "0"


def cusp_values(x):
    """FKTY F(-1;e(x)) (1.2) and FOR U(-1;e(-x)) (1.1) by separate products."""
    k = x.denominator
    require(k % 2 == 0 and (k*x).denominator == 1, "requires a reduced even denominator")
    phases = [e(n*x) for n in range(k)]
    first_zero = k // 2
    require((first_zero*x) % 1 == Fraction(1, 2), "incorrect first zero factor")

    strange = mp.mpc(0)
    product = mp.mpc(1)
    for n in range(first_zero):
        strange += (-1)**(n+1) * product
        product *= 1 + phases[(n+1) % k]

    unimodal = mp.mpc(0)
    square_product = mp.mpc(1)
    for n in range(first_zero):
        q_power = phases[-((n+1) % k)]
        unimodal += q_power * square_product
        square_product *= (1 + q_power)**2

    twist = mp.sqrt(12j) * e(x/24)
    return strange, unimodal, -4*twist*strange, -4*twist*unimodal


def sign6(n):
    """(12/n) (-1)^((n-1)/2) on odd n coprime to 3, and 0 elsewhere."""
    return {1: 1, 5: -1}.get(n % 6, 0)


def theta_coefficients():
    """Direct and Poisson coefficients on the line Re u = -1/24.

    For w(n)=sign6(n)e(-n²/576), w(n+288)=w(n), w(-n)=-w(n).
    Let C[l]=Σ_{r mod 288} w(r)e(lr/288). With a=t/12, Poisson
    summation of x exp(-π a x²) gives

      θ(-1/24+it) = -i/(288² a^(3/2)) Σ_l l C[l] exp(-π l²/(288² a)).

    Pair ±n in each expansion. The coefficients on the two sides are
    computed independently from the same integer character.
    """
    roots = [e(Fraction(j, 576)) for j in range(576)]
    residues = [(r, sign6(r)) for r in range(PERIOD) if sign6(r)]
    direct = []
    dual = []
    for n in range(1, MAX_MODE + 1):
        if sign6(n):
            direct.append((n*n, 2*n*sign6(n) * roots[-n*n % 576]))
        fourier = mp.fsum(s * roots[(2*r*n - r*r) % 576] for r, s in residues)
        dual.append((n*n, 2*n * fourier))
    return direct, dual


def gaussian_sum(coefficients, beta_height):
    q = mp.exp(-beta_height)
    return mp.fdot(((c, q**d) for d, c in coefficients))


def period_integral(denominator, point, order):
    """Integrate above -1/24 along u=-1/24+it, with du=i dt.

    On 0<t<1/24 substitute t=1/(576v) and use direct finite Fourier
    coefficients of the Poisson sum. Both resulting series have Gaussian
    decay in v. The principal square root is approached in the upper
    half-plane throughout the original contour.
    """
    gamma = denominator
    t0 = mp.mpf(1)/gamma
    beta = mp.pi/12
    displacement = real(Fraction(-1, gamma) - point)
    direct, dual = theta_coefficients()
    dual_factor = -mp.j * mp.mpf(12 * gamma**2)**mp.mpf("1.5") / PERIOD**2

    def original(t):
        return gaussian_sum(direct, beta*t)

    def reflected(v):
        return dual_factor * v**mp.mpf("1.5") * gaussian_sum(dual, beta*v)

    overlap = []
    for t in (t0, t0*mp.mpf("0.9"), t0*mp.mpf("1.1")):
        v = 1 / (gamma**2 * t)
        overlap.append(abs(original(t) - reflected(v)))

    def integrand(v):
        small_t = 1 / (gamma**2 * v)
        return mp.j * (original(v)/mp.sqrt(displacement + mp.j*v)
                       + reflected(v)/(gamma**2 * v**2 * mp.sqrt(displacement + mp.j*small_t)))

    # Geometric panels resolve the square-root kernel and the Gaussian decay.
    nodes, weights = mp.gauss_quadrature(order, "legendre")
    panels = []
    lo = t0
    while lo < MAX_HEIGHT:
        hi = min(2*lo, MAX_HEIGHT)
        center, half_width = (hi+lo)/2, (hi-lo)/2
        panels.append(half_width * mp.fsum(w*integrand(center + half_width*x)
                                          for x, w in zip(nodes, weights)))
        lo = hi

    # |C[l]|≤288. Both |u-x|^(-1/2) kernels are at most |displacement|^(-1/2).
    # On the transformed branch the remaining prefactor, including the
    # Jacobian, is at most B/sqrt(v) times the direct series bound.
    B = abs(dual_factor)*PERIOD/gamma**2
    def amplitude(v):
        return 2*(1+B/mp.sqrt(v))/mp.sqrt(abs(displacement))

    # For p=MAX_MODE+1, (p+j)^2≥p²+(2p+1)j in the omitted Gaussian tail.
    p = MAX_MODE+1
    ratio = mp.exp(-beta*t0*(2*p+1))
    mode_tail = (amplitude(t0) * (p/(1-ratio) + ratio/(1-ratio)**2)
                 * mp.exp(-beta*t0*p*p)/(beta*p*p))
    # Bound the height tail using n²≥n and sum n q^n = q/(1-q)^2.
    q = mp.exp(-beta*MAX_HEIGHT)
    height_tail = amplitude(MAX_HEIGHT)*q/(beta*(1-q)**2)
    return mp.fsum(panels), max(overlap), height_tail + mode_tail


def run():
    (a, b), (c, d) = G
    require(a*d-b*c == 1 and all(n % 24 == 0 for n in (a-1, b, c, d-1)),
            "matrix outside Gamma(24)")
    j = c*X + d
    target = (a*X+b)/j
    require(target == Fraction(-1, 10) and j == Fraction(5, 17), "incorrect cusp action")
    # In (3.13), delta=1 implies both Kronecker symbols and epsilon_delta equal 1.
    require(d == 1, "multiplier calculation uses delta=1")
    multiplier = 1

    with mp.workdps(80):
        computed = []
        configurations = ((55, 24), (55, 36), (80, 36))
        for precision, order in configurations:
            with mp.workdps(precision):
                computed.append(period_integral(c, X, order))

        tolerance = mp.mpf(TOLERANCE)
        period = computed[-1][0]
        quadrature_change = abs(computed[0][0]-computed[1][0])
        precision_change = abs(computed[1][0]-period)
        require(max(quadrature_change, precision_change) < tolerance, "period failed replication")
        require(max(row[1] for row in computed) < tolerance, "dual theta mismatch at splice")
        require(max(row[2] for row in computed) < tolerance, "series or height tail too large")

        endpoints = []
        normalized = []
        for x in (X, target):
            strange, unimodal, phi, from_radial = cusp_values(x)
            agreement = abs(phi-from_radial)
            require(agreement < tolerance, "finite F and U normalization mismatch")
            normalized.append(phi)
            endpoints.append({
                "x": str(x), "physical_f_cusp": str(-x),
                "first_vanishing_factor": x.denominator//2,
                "F_minus_one": coordinates(strange), "U_minus_one_inverse_nome": coordinates(unimodal),
                "compensated_f_boundary_minus_4U": coordinates(-4*unimodal),
                "normalized_phi": coordinates(phi), "F_U_normalized_difference_le": decimal_power_bound(agreement),
            })

        slash = 1/(multiplier*mp.sqrt(real(j)))
        defect = normalized[0] - slash*normalized[1]
        error = abs(defect-period)
        wrong_multiplier = abs(normalized[0] + slash*normalized[1] - period)
        wrong_kernel_branch = abs(defect + period)
        require(error < tolerance, "FKTY cusp defect and independent period differ")
        require(min(wrong_multiplier, wrong_kernel_branch) > 1, "branch or multiplier control inconclusive")
        return {
            "source": "Folsom, Ki, Truong Vu and Yang, J. Number Theory 170 (2017), 315–346",
            "doi": "https://doi.org/10.1016/j.jnt.2016.06.005",
            "publication_pdf_sha256": "757d617b031aa6b87610137bf6288909dc20acede472029215de533393163a75",
            "source_equations": ["(1.1)–(1.3)", "Theorem 1.8 (1.13)", "(3.12)–(3.13)"],
            "mpmath": mp.__version__, "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            "command": "python3 tools/check_quantum_transport34.py --receipt evidence/current/quantum-radial/transport34.json",
            "component": {"a": 1, "b": 2, "c": 0, "ell_b": 12, "weight": "1/2"},
            "matrix": G, "cx_plus_d": str(j), "psi_12": multiplier, "slash_factor": scalar(slash),
            "normalization": "phi(x)=-4 sqrt(12i) e(x/24) F(-1;e(x))=sqrt(12i) e(x/24)[-4U(-1;e(-x))]",
            "square_roots": "principal; sqrt(cx+d)>0 and u-x approaches the negative real axis from above",
            "endpoints": endpoints,
            "contour": "u=-1/24+it, 0<t<infinity; integrate theta_1,2,0(u) du/sqrt(u-x)",
            "theta": "sum over n in Z of n sign6(n) e(n^2 u/24); sign6=+1 at 1, -1 at 5 modulo 6, 0 elsewhere",
            "period_method": "direct Gaussian series above t=1/24, period-288 finite Fourier transform and Poisson sum below; geometric panels with Gauss–Legendre quadrature",
            "maximum_mode": MAX_MODE, "splice_height": "1/24",
            "retained_original_heights": [str(Fraction(1, c**2*MAX_HEIGHT)), str(MAX_HEIGHT)],
            "runs": [{"decimal_digits": digits, "quadrature_order": order}
                     for digits, order in configurations],
            "principal_branch_period": coordinates(period), "finite_cusp_defect": coordinates(defect),
            "absolute_defect_minus_period": scalar(error), "acceptance_threshold": TOLERANCE,
            "two_theta_expansions_overlap_max_difference": scalar(max(row[1] for row in computed)),
            "quadrature_order_change": scalar(quadrature_change), "precision_change": scalar(precision_change),
            "series_and_height_truncation_bound": scalar(computed[-1][2]),
            "controls_absolute_residual": {"psi_minus_one": scalar(wrong_multiplier),
                                          "opposite_integral_sqrt": scalar(wrong_kernel_branch)},
            "scope": "Numerical agreement for one group element and one cusp pair. The Gaussian tail estimates exclude roundoff; quadrature is checked by order and precision replication.",
        }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--receipt", "--output", type=Path, help="write the JSON result to this path")
    args = parser.parse_args()
    result = json.dumps(run(), ensure_ascii=False, indent=2) + "\n"
    if args.receipt:
        args.receipt.write_text(result, encoding="utf-8")
    else:
        print(result, end="")


if __name__ == "__main__":
    main()
