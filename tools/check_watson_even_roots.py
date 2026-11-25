#!/usr/bin/env python3
"""Check the Watson and reflected FKTY identities and measure Watson root multiplicities."""

import argparse
from hashlib import sha256
import json
from math import comb, gcd, isqrt, lcm
from pathlib import Path


MAX_HALF_ORDER = 96


def require(condition, message):
    if not condition:
        raise ArithmeticError(message)


def add_shift(target, row, degree, scale=1):
    """Add a monomial times row to target, reducing with X^k = -1."""
    for i, coefficient in enumerate(row):
        quotient, residue = divmod(i+degree, len(target))
        target[residue] += scale*coefficient if quotient % 2 == 0 else -scale*coefficient


def add_factor(row, degree):
    result = row.copy()
    add_shift(result, row, degree)
    return result


def watson_head(k, degree, first):
    """Clear each term using its suffix of the full denominator, in reverse order."""
    suffix = [1] + [0]*(degree-1)
    cleared = [0]*degree
    for n in reversed(range(k)):
        suffix = add_factor(suffix, 2*n+first)
        add_shift(cleared, suffix, n*n, (-1)**n)
    return suffix, cleared


def finite_values(k, degree):
    forward = [1] + [0]*(degree-1)
    inverse = forward.copy()
    unimodal = [0]*degree
    reflected = [0]*degree
    for n in range(1, k+1):
        add_shift(unimodal, forward, n)
        add_shift(reflected, inverse, 0, (-1)**n)
        forward = add_factor(add_factor(forward, n), n)
        inverse = add_factor(inverse, -n)
    return unimodal, reflected


def scaled_boundary_row(k, unimodal):
    if k % 2:
        return [-2*c for c in unimodal]
    row = unimodal.copy()
    row[0] += 1
    return row


def check_polynomials():
    for k in range(1, MAX_HALF_ORDER+1):
        first = 1 if k % 2 == 0 else 2
        den, numerator = watson_head(k, k, first)
        u, f = finite_values(k, k)
        require(u == f, f"reflected finite values disagree at half-order {k}")
        target = scaled_boundary_row(k, u)
        den[0] -= 1
        cleared = [0]*k
        for j, coefficient in enumerate(den):
            add_shift(cleared, target, j, coefficient)
        require(numerator == cleared, f"cleared Watson identity failed at half-order {k}")
        wrong, _ = watson_head(k, k, 3-first)
        require(not any(wrong), f"opposite parity denominator did not vanish at half-order {k}")

    # Every primitive eighth root also satisfies X^12 = -1.
    den, numerator = watson_head(12, 4, 1)
    u, _ = finite_values(12, 4)
    target = scaled_boundary_row(12, u)
    require(den == [8, 0, 0, 0] and numerator != target, "imprimitive denominator control failed")
    require(numerator == [7*c for c in target], "imprimitive clearance failed")
    return {"half_orders": [1, MAX_HALF_ORDER], "cleared_identities": MAX_HALF_ORDER,
            "reflected_identities": MAX_HALF_ORDER, "wrong_parity_zero_denominators": MAX_HALF_ORDER,
            "order8_in_half_order12": {"denominator": den[0], "multiplier": 7}}


def divide_x_power_plus_one(coefficients, k):
    """Divide ascending integer coefficients by X^k+1 for positive k."""
    work = coefficients.copy()
    # The high slot holds its quotient coefficient after eliminating the leading term.
    for degree in range(len(work)-1, k-1, -1):
        work[degree-k] -= work[degree]
    return work[k:], work[:k]


def coefficient_at_minus_one(coefficients, degree):
    """Extract the coefficient of (X+1)^degree in the Taylor expansion at −1."""
    return sum(comb(i, degree)*c*(-1)**(i-degree)
               for i, c in enumerate(coefficients[degree:], degree))


def linear_remainders(coefficients, prime):
    """Divide by X+1 until the first nonzero remainder modulo prime."""
    remainders = []
    while coefficients:
        coefficients, remainder = divide_x_power_plus_one(coefficients, 1)
        remainders.append(remainder[0] % prime)
        if remainders[-1]:
            return remainders
    raise ArithmeticError(f"zero Watson polynomial modulo {prime}")


def check_unreduced_divisions():
    """Form W-(D-1)B at full degree, then divide by the monic X^k+1 in Z[X]."""
    last = 44
    primes = [p for p in range(3, last+1, 2) if all(p % d for d in range(3, isqrt(p)+1, 2))]
    classification_primes = {5, 7, 11, 13}
    odd_at_minus_one = []
    even_divisions = 0
    prime_multiplicities = []
    for k in range(1, last+1):
        first = 1 if k % 2 == 0 else 2
        # D and W have degree at most k²+(first-1)k, and U has degree k².
        # At this width every forward term fits in its original coefficient slot.
        den_degree = k*k + (first-1)*k
        u_degree = k*k
        width = den_degree + u_degree + 1
        den, difference = watson_head(k, width, first)
        unimodal, _ = finite_values(k, width)
        target = scaled_boundary_row(k, unimodal)
        den[0] -= 1
        for j, coefficient in enumerate(den):
            if coefficient:
                for i in range(u_degree+1):
                    difference[j+i] -= coefficient*target[i]

        quotient, remainder = divide_x_power_plus_one(difference, k)
        require(not any(remainder), f"nonzero integer remainder at k={k}")
        if k == 1:
            quotient_one = quotient
            require(quotient_one == [1, -1, 2], "incorrect unreduced quotient at k=1")
        slope = coefficient_at_minus_one(difference, 1)
        expected_slope = 2*k*(k+1) if k % 2 else 2*k
        require(slope == expected_slope, f"wrong derivative at k={k}")
        if k % 2:
            quotient_value = coefficient_at_minus_one(quotient, 0)
            quotient_slope = coefficient_at_minus_one(quotient, 1)
            quadratic = coefficient_at_minus_one(difference, 2)
            require(quotient_value == 2*(k+1), f"wrong quotient value at k={k}")
            expected_quotient_slope = -5 if k == 1 else -(k**3+k*k+3*k+6)
            expected_quadratic = -5 if k == 1 else -k*(k**3+2*k*k+3*k+5)
            require(quotient_slope == expected_quotient_slope, f"wrong quotient derivative at k={k}")
            require(quadratic == expected_quadratic, f"wrong quadratic coefficient at k={k}")
            odd_at_minus_one.append({"k": k, "quotient": quotient_value, "derivative": slope,
                                     "quotient_derivative": quotient_slope, "quadratic": quadratic})
        else:
            for s in range(1, k+1, 2):
                if k % s == 0:
                    even_quotient, rest = divide_x_power_plus_one(difference, s)
                    require(not any(rest), f"missing odd divisor X^{s}+1 at even k={k}")
                    require(coefficient_at_minus_one(even_quotient, 0) == 2*(k//s),
                            f"wrong quotient value at k={k}, s={s}")
                    even_divisions += 1
        if k == 5:
            char3_remainders = linear_remainders(difference, 3)
            require(len(char3_remainders) > 3, "characteristic 3 did not give a higher multiplicity")

        for p in primes:
            if p not in classification_primes and k % p:
                continue
            if k % 2 and (k+1) % p == 0:
                expected_multiplicity = 2
                expected_remainder = 3
            else:
                prime_power = 1
                while k % (prime_power*p) == 0:
                    prime_power *= p
                expected_multiplicity = prime_power
                expected_remainder = 2*(k//prime_power) if prime_power > 1 else expected_slope
            remainders = linear_remainders(difference, p)
            multiplicity = len(remainders)-1
            require(multiplicity == expected_multiplicity, f"wrong root multiplicity at k={k} modulo {p}")
            require(remainders[-1] == expected_remainder % p, f"wrong final cofactor at k={k} modulo {p}")
            prime_multiplicities.append({"k": k, "prime": p, "multiplicity": multiplicity,
                                         "first_nonzero_remainder": remainders[-1]})
            if k == 11 and p == 11:
                mod11_remainders = remainders[:-1]
    return {"half_orders": [1, last], "zero_remainders": last,
            "even_odd_divisor_checks": even_divisions, "classification_primes": sorted(classification_primes),
            "quotient_at_one_ascending": quotient_one, "k11_linear_remainders_mod11": mod11_remainders,
            "odd_at_minus_one": odd_at_minus_one, "prime_multiplicities": prime_multiplicities,
            "k5_linear_remainders_mod3": char3_remainders}


def check_phase_readings():
    fixtures = (
        (2730, (), 22), (2730, (11,), 22), (30030, (4,), 24),
        (30030, (8,), 24), (30030, (), 10), (30030, (17,), 34),
        (30030, (12, 8, 6), 24),
    )
    windings = (-10**60, -2, -1, 0, 1, 10**60)
    rows = []
    for m, anchors, order in fixtures:
        period = lcm(m, *anchors)
        need = order//gcd(m, order)
        resolution = period//m
        admitted = resolution % need == 0
        for r in (0, 1, m//2, m-1):
            for winding in windings:
                x = r + m*winding
                y = x + period
                for a in (m, *anchors):
                    require(x % a == y % a, "period shifted a lane reading")
                require((x % order == y % order) == admitted, "phase alias disagrees with resolution")
        rows.append({"primary": m, "anchors": anchors, "order": order, "period": period,
                     "required_resolution": need, "available_resolution": resolution,
                     "phase_recovers": admitted, "signed_pairs": 4*len(windings)})
    return rows


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--receipt", type=Path)
    args = parser.parse_args()
    result = json.dumps({"status": "PASS", "script_sha256": sha256(Path(__file__).read_bytes()).hexdigest(),
                         "integer_polynomials": check_polynomials(), "integer_division": check_unreduced_divisions(),
                         "phase_readings": check_phase_readings()},
                        indent=2) + "\n"
    if args.receipt:
        args.receipt.write_text(result, encoding="utf-8")
    else:
        print(result, end="")


if __name__ == "__main__":
    main()
