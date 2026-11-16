"""Independent finite observation-partition checks for the thesis audit.

No repository imports. These checks assess both directions of information
criteria by enumerating complete relevant periods, rather than calling the
manuscript's checker or using its recovery functions as the oracle.
"""
from collections import Counter
from itertools import combinations_with_replacement, product
from math import gcd, lcm, prod
from pathlib import Path
import hashlib
import json

counts = Counter()

def check(category, condition):
    counts[category] += 1
    if not condition:
        raise AssertionError(category)

# T1: compare actual integer images with every raw tuple, including overlap.
for length in range(1, 4):
    for basis in combinations_with_replacement(range(2, 8), length):
        period = lcm(*basis)
        actual = {tuple(x % m for m in basis) for x in range(period)}
        check("T1_image_size", len(actual) == period)
        for row in product(*(range(m) for m in basis)):
            compatible = all((row[i]-row[j]) % gcd(basis[i], basis[j]) == 0
                             for i in range(length) for j in range(length))
            check("T1_compatibility", (row in actual) == compatible)

# T3: enumerate all reading pairs against actual integer images; recover
# quotient classes from actual canonical divisions, including signed inputs.
for main in range(2, 16):
    for anchor in range(2, 16):
        common = gcd(main, anchor)
        h = anchor // common
        actual = {(x % main, x % anchor) for x in range(lcm(main, anchor))}
        for r in range(main):
            for s in range(anchor):
                check("T3_pair_existence", ((r, s) in actual) == ((s-r) % common == 0))
        for x in range(-2*lcm(main, anchor), 2*lcm(main, anchor)+1):
            r, s = x % main, x % anchor
            kappa = (((s-r)//common)*pow(main//common, -1, h)) % h if h > 1 else 0
            check("T3_signed_class", kappa == (x//main) % h)
        # Admissible windows and impossible classes, including H=1 and N=1.
        for start in range(-h-1, h+2):
            for width in range(1, h+1):
                for kappa in range(h):
                    actual_candidates = [k for k in range(start, start+width) if k % h == kappa]
                    candidate = start + ((kappa-start) % h)
                    accepted = candidate < start+width
                    check("T3_interval", actual_candidates == ([candidate] if accepted else []))

# T4 and T8: target constancy is tested on observation partitions across a
# complete period for the joint observation and requested output.
for main in range(1, 16):
    for target in range(1, 16):
        for h in range(1, 16):
            groups = {}
            for k in range(lcm(h, target)):
                groups.setdefault(k % h, set()).add((main*k) % target)
            constant = all(len(values) == 1 for values in groups.values())
            check("T4_partition_iff", constant == (h % (target//gcd(main, target)) == 0))

for divisor in range(1, 13):
    for target in range(1, 13):
        for observation in range(1, 25):
            quotient_period = observation // gcd(observation, divisor)
            # Fixed remainder need not be zero; choose canonical d-1.
            remainder = divisor - 1
            groups = {}
            for quotient in range(lcm(quotient_period, target)):
                seen = (divisor*quotient+remainder) % observation
                groups.setdefault(seen, set()).add(quotient % target)
            constant = all(len(values) == 1 for values in groups.values())
            check("T8_partition_iff", constant == (quotient_period % target == 0))

# Selected numerical examples, checked independently of the narrative.
examples = {
    "S6": prod((2, 3, 5, 7, 11, 13)) == 30030,
    "S8": prod((2, 3, 5, 7, 11, 13, 17, 19)) == 9699690,
    "composite_anchor": 59*509 == 30031,
    "combined_period": 30030*30031 == 901830930,
    "Dresden_lcm": lcm(260, 365) == 18980,
    "Dresden_shared": 65*584 == 104*365 == 146*260 == 37960,
    "Dresden_shadow": 13*584 == 7592 and 7592 % 11 == 2,
    "nonprime_unit": 17**2 == 289 and gcd(289, 30030) == 1,
    "phase_1001": (1001 % 36, 1001 % 37, 1001 // 36, 1001 % 11) == (29, 2, 27, 0),
    "phase_1000": (1000 % 36, 1000 % 37, 1000 // 36) == (28, 1, 27),
    "phase_alias": (2332 % 36, 2332 % 37, 2332 // 36) == (28, 1, 64),
    "shared_factor": ((30 % 16)//2 * pow(3, -1, 8)) % 8 == 5,
    "notes_500": divmod(500, 7) == (71, 3) and tuple(500 % m for m in (7, 11, 13)) == (3, 5, 6),
}
for example, passed in examples.items():
    check("examples", passed)

# T13 finite coherence of the explicitly defined noninteger idempotent.
# Its noninteger status itself is the written all-powers argument, not this test.
family = {}
for modulus in range(1, 161):
    odd = modulus
    power = 1
    while odd % 2 == 0:
        odd //= 2
        power *= 2
    candidates = [a for a in range(modulus) if a % power == 0 and (a-1) % odd == 0]
    check("T13_unique_coordinates", len(candidates) == 1)
    family[modulus] = candidates[0]
    check("T13_idempotent", (family[modulus]**2-family[modulus]) % modulus == 0)
for big in family:
    for small in family:
        if big % small == 0:
            check("T13_refinement", family[big] % small == family[small])

report = {
    "status": "passed",
    "assertions": sum(counts.values()),
    "failures": 0,
    "counts": dict(counts),
    "example_checks": examples,
    "source_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    "scope": "Independent finite partition and boundary checks; not universal proof or production conformance.",
}
Path(__file__).with_suffix(".json").write_text(json.dumps(report, indent=2)+"\n")
print(json.dumps(report, indent=2))
