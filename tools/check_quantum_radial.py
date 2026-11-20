#!/usr/bin/env python3
"""Evaluate the interior q-series in Folsom–Ono–Rhoades, Thms. 1.1 and 1.2.

Requires mpmath==1.3.0. The input is q=(1-1/d)ζ. No endpoint identity is
used to compute interior R or C. Exact-series tail estimates below exclude
roundoff; two working precisions test the net effect of arithmetic error.
Source (2013), pp. 4–6, equations (1.4)–(1.6): https://doi.org/10.1017/fmp.2013.3
"""

import argparse
import hashlib
import json
from pathlib import Path
import sys

import mpmath as mp


# ζ=e(1/order), w=ζ^w_power, correction phase=ζ^phase_power.
# The last fixture has w=q-cusp, a=h=1, b=k=11, h'=-1.
FIXTURES = (
    (2, 1, 1, (50, 100, 200, 400)),
    (4, 2, 0, (50, 100, 200, 400)),
    (6, 3, 3, (50, 100, 200, 400)),
    (11, 1, 1, (200, 400, 800, 1600)),
)
TOL = '1e-28'


def require(condition, message):
    if not condition:
        raise ArithmeticError(message)


def roots(order):
    return [mp.mpc(mp.cospi(mp.mpf(2*j)/order), mp.sinpi(mp.mpf(2*j)/order))
            for j in range(order)]


def rank_series(t, z, u):
    """Equation (1.4), with |T[n+1]/T[n]| ≤ t^(2n+1)/(1-t^(n+1))²."""
    order = len(z)
    term = total = mp.mpc(1)
    t_n = mp.mpf(1)
    for n in range(1, 100000):
        t_n *= t
        term *= (t_n*t_n/t * z[(2*n-1) % order] /
                 ((1-t_n*z[(n+u) % order]) * (1-t_n*z[(n-u) % order])))
        total += term
        # The majorant decreases with n, so all subsequent ratios are smaller.
        ratio = t_n*t_n*t / (1-t_n*t)**2
        if ratio < 1:
            bound = abs(term) * ratio / (1-ratio)
            if bound < mp.mpf('1e-38'):
                return total, n, bound
    raise ArithmeticError("rank series exceeded its summation budget")


def crank_theta(t, z, u):
    """C=(1-w)P²/J via Euler's pentagonal and Jacobi's triple product.

    P=(q;q)_∞. J=Σ_{j∈ℤ}(-1)^j w^j q^(j(j−1)/2)
    =(1-w)P(wq;q)_∞(q/w;q)_∞. Pair ±j before summing.
    """
    order = len(z)
    target = mp.power(10, -mp.mp.dps+15)
    N = int(mp.ceil(mp.sqrt(2*mp.log(target*(1-t)/2)/mp.log(t))))
    P = mp.mpc(1)
    J = mp.mpc(1)
    for j in range(1, N+1):
        p = j*(3*j-1)//2
        v = j*(j-1)//2
        sign = -1 if j % 2 else 1
        P += sign*(t**p*z[p % order] + t**(p+j)*z[(p+j) % order])
        J += sign*(t**v*z[(v+j*u) % order] + t**(v+j)*z[(v+j-j*u) % order])

    # Each pair has magnitude ≤ 2 t^m. Lower exponents in the omitted
    # pairs grow by at least 3n+1 (Euler) or n (Jacobi), n=N+1.
    n = N+1
    eP = 2*t**(n*(3*n-1)//2)/(1-t**(3*n+1))
    eJ = 2*t**(n*(n-1)//2)/(1-t**n)
    floor = abs(J)-eJ
    require(floor > 0, "Jacobi denominator unresolved")
    C = (1-z[u]) * P**2 / J
    bound = abs(1-z[u])*(eP*(2*abs(P)+eP)/floor + abs(P)**2*eJ/(abs(J)*floor))
    return C, N, bound


def crank_product(t, z, u):
    """Independent direct product (1.5), used at the first radius of each path."""
    order = len(z)
    t_n = mp.mpf(1)
    C = mp.mpc(1)
    for n in range(1, 100000):
        t_n *= t
        C *= ((1-t_n*z[n % order]) /
              ((1-t_n*z[(n+u) % order]) * (1-t_n*z[(n-u) % order])))
        if n % 100 == 0:
            # Each missing log(1-w^s q^j) has size ≤ t^j/(1-t^j).
            log_tail = 3*t_n*t/((1-t)*(1-t_n*t))
            if log_tail < 1:
                bound = abs(C)*mp.expm1(log_tail)
                if bound < mp.mpf('1e-38'):
                    return C, n, bound
    raise ArithmeticError("crank product exceeded its summation budget")


def endpoints(z, u):
    """Direct finite U sum (1.6) and independent reduced algebraic values."""
    order = len(z)
    # At q=ζ the first vanishing factor in U has j≡±u (mod order).
    first_zero = min(u, order-u)
    product = mp.mpc(1)
    U = mp.mpc(0)
    for n in range(first_zero):
        if n:
            product *= (1-z[(u+n) % order])*(1-z[(n-u) % order])
        U += product*z[(n+1) % order]
    finite = -(1-z[u])*(1-z[-u])*U
    if order == 2:
        closed = mp.mpc(4)
    elif order == 4:
        closed = mp.mpc(0, 4)
    elif order == 6:
        closed = mp.mpc(-2, -2*mp.sqrt(3))
    else:
        closed = (1-z[1])**2
    return finite, closed, first_zero


def interior(order, u, phase_power, d, precision):
    with mp.workdps(precision):
        z = roots(order)
        t = 1-mp.mpf(1)/d
        R, rank_terms, rank_bound = rank_series(t, z, u)
        C, theta_pairs, crank_bound = crank_theta(t, z, u)
        phase = z[phase_power]
        return (R, C, R-phase*C, rank_terms, theta_pairs, rank_bound+crank_bound)


def number(x):
    return mp.nstr(x, 22)


def coordinates(x):
    return [number(x.real), number(x.imag)]


def check_path(order, u, phase_power, divisors, precision):
    z = roots(order)
    finite, closed, first_zero = endpoints(z, u)
    require(abs(finite-closed) < mp.mpf(TOL), "finite endpoint discrepancy")
    require((first_zero+u) % order == 0 or (first_zero-u) % order == 0,
            "root substitution should encounter a zero denominator in R")
    # Extract the linear term from the actual crank product near q=0. The
    # single ordinary partition [1] has crank -1 and weight w^(-1).
    tiny = mp.mpf('1e-40')
    C_tiny, _, _ = crank_product(tiny, z, u)
    slope = (C_tiny-1)/(tiny*z[1])
    coefficient = z[u]+z[-u]-1
    linear_error = abs(slope-coefficient)
    singleton_error = abs(slope-z[-u])
    require(linear_error < mp.mpf(TOL) and singleton_error > mp.mpf('0.1'),
            "the exceptional degree-one crank coefficient was not resolved")
    samples = []
    errors = []
    for d in divisors:
        R, C, corrected, nr, nt, bound = interior(order, u, phase_power, d, precision)
        R2, C2, c2, _, _, bound2 = interior(order, u, phase_power, d, precision+30)
        disagreement = max(abs(R-R2), abs(C-C2), abs(corrected-c2))
        require(max(bound, bound2, disagreement) < mp.mpf(TOL),
                f"insufficient precision for order={order}, d={d}")
        distance = abs(corrected-closed)
        errors.append(distance)
        wrong = abs(R+z[phase_power]*C-closed)
        require(wrong > distance, "wrong-sign control did not separate")
        row = {
            't': f'{d-1}/{d}', 'rank_R': coordinates(R), 'crank_C': coordinates(C),
            'regularized': coordinates(corrected), 'distance_to_endpoint': number(distance),
            'wrong_sign_distance': number(wrong), 'rank_last_index': nr,
            'theta_pairs_each_sum': nt, 'absolute_truncation_bound': number(bound),
            'max_absolute_disagreement_at_extra_30_digits': number(disagreement),
        }
        if order == 11:
            unphased = abs(R-C-closed)
            require(unphased > distance, "omitted order-eleven phase failed to separate")
            row['omitted_phase_distance'] = number(unphased)
        if d == divisors[0]:
            direct, n, direct_bound = crank_product(1-mp.mpf(1)/d, z, u)
            delta = abs(C-direct)
            require(max(delta, direct_bound) < mp.mpf(TOL), "independent crank product discrepancy")
            row['direct_crank_product'] = {'last_factor': n, 'absolute_truncation_bound': number(direct_bound),
                                           'distance_to_theta_quotient': number(delta)}
        samples.append(row)
    require(all(later < earlier for earlier, later in zip(errors, errors[1:])),
            f"endpoint distances fail to decrease at order={order}")
    require(errors[-1] < mp.mpf('0.25'), f"final radius too distant at order={order}")
    return {'order': order, 'w_power_of_zeta': u, 'correction_phase_power_of_zeta': phase_power,
            'first_zero_factor_in_R_at_cusp': first_zero,
            'degree_one_crank_control': {'t': '1e-40', 'product_coefficient': coordinates(coefficient),
                                         'slope_error': number(linear_error),
                                         'distance_to_ordinary_singleton_weight': number(singleton_error)},
            'finite_endpoint': coordinates(finite), 'reduced_endpoint': coordinates(closed),
            'endpoint_disagreement': number(abs(finite-closed)), 'samples': samples}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--dps', type=int, default=340, help="working decimal digits (default 340)")
    parser.add_argument('--receipt', type=Path, help="write JSON to this path instead of stdout")
    args = parser.parse_args()
    if args.dps < 100:
        parser.error('--dps must be at least 100')
    with mp.workdps(args.dps+30):
        cases = [check_path(*fixture, args.dps) for fixture in FIXTURES]
    receipt = {
        'status': 'pass', 'source': 'https://doi.org/10.1017/fmp.2013.3',
        'source_pdf': 'https://afolsom.people.amherst.edu/FolsomOnoRhoades-ForumPi.pdf',
        'source_pdf_sha256': '0f3a0105a62adc6341a5a13fb765a0aa93596d8e3da55e423ca3cc05e8b38a4e',
        'source_location': 'Theorems 1.1 and 1.2, equations (1.4)–(1.6), pp. 4–6',
        'command': f'python3 tools/check_quantum_radial.py --dps {args.dps} --receipt evidence/current/quantum-radial/numerical.json',
        'script_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'python': sys.version.split()[0], 'mpmath': mp.__version__,
        'working_decimal_digits': args.dps, 'repeat_decimal_digits': args.dps+30,
        'absolute_arithmetic_agreement_threshold': TOL, 'root': 'zeta=exp(2*pi*i/order)',
        'correction': 'R(w;t*zeta) - phase*C(w;t*zeta)',
        'crank_convention': 'Product (1.5); [q]C(w;q)=w+w^(-1)-1.',
        'scope': 'Interior samples and exact-series tail estimates evaluated in multiprecision; no interval rounding certificate or numerical proof of the limit.',
        'cases': cases,
    }
    result = json.dumps(receipt, indent=2, ensure_ascii=False)+'\n'
    if args.receipt:
        args.receipt.parent.mkdir(parents=True, exist_ok=True)
        args.receipt.write_text(result, encoding='utf-8')
    else:
        print(result, end='')


if __name__ == '__main__':
    main()
