# Finite evidence for The Profinite Bridge

This package preserves exact finite reference checks and a targeted replay of the
source experiment. These are not universal theorems, Lean compilation, production
CRAM conformance, or proofs of an analytic/profinite correspondence.

## Reproduce

Use Python 3.11 or newer. The first checker uses only the standard library.
The packet replay also needs the versions in requirements.txt.

~~~sh
python3 verify_finite_examples.py
python3 replay_carry_q2.py
~~~

Run those commands from this directory. The recorded execution used Python
3.12.14, SymPy 1.14.0, and mpmath 1.3.0. Optional dependency installation is
python3 -m pip install -r requirements.txt; no dependency installation was
needed for the recorded run.

## New finite checker

verify_finite_examples.py independently enumerates the eleven partitions of six
and their rank/crank distributions modulo eleven. It exhausts all 30,030 canonical
S6 states for the normalized CRT-rank distribution, factors 30,031, checks the
finite alternating-residue witness, checks both star signs for M=6 and X=0,20,
records the excluded upper-endpoint alias controls, and computes the multiplicative
orders of 4 modulo 23, 29, and 667.

The script records its source hash and exact results in
finite_examples_results.json. The files finite_examples_execution.json and
finite_examples.log record this package's execution.

The scalar sources in these checks are independent mathematical test oracles.
They are not proposed persistent machine state. The selected primary remains
S6 = {2,3,5,7,11,13}.

## Pinned packet and faithful targeted replay

The source_packet directory contains byte-preserved copies of the original
carry_questions.py, carry_questions_output.txt, and directory README from
Skyelabz210/NINE65_v7 at commit
64c1c89b191093dc12cf81b87da5fb1a02c46dc1. See
source_packet/source_manifest.json for original paths, URLs, Git blob hashes,
and SHA-256 hashes. Preserve their source attribution; no new license is granted.
The original directory README also names other experiments not included here.
Those experiments are not dependencies of this replay.

The original script imports fractions and math from Python's standard library
and prevprime/nextprime from SymPy. It has no additional local-code dependency.
The dependency versions are recorded rather than vendoring the libraries.

replay_carry_q2.py first checks the pinned source SHA-256. It selects the original
imports, RNG initialization/class, normalized-CRT warmup, and Q2 statements through
Python's AST, without changing those statements. It actually executes the original
9,000-sample normalized-CRT warmup, preserving all RNG advancement before Q2.
An explicit AST check rejects any RNG access in the omitted prefix.

It then executes Q2's 18,000 cases unchanged and compares the output aggregate to
the archived receipt. The files carry_q2_results.json, carry_q2_execution.json, and
carry_q2_replay.log record the result, exact scope, source/wrapper hashes,
dependency versions, RNG state, and selected source ranges.

The expensive Q1 tropical/Hermite sweep, the separate Q1 carry enumeration, and
Q3 truncation experiment are not rerun here. Their output remains visibly archived
in source_packet/carry_questions_output.txt; it is not fresh evidence.

Q2 assumes normalized coefficients, uses authentic source observations in the
test oracle, and samples 0 <= X < M*A. It verifies K = alpha+c modulo A and
membership in {(a+c) mod A : 0 <= a < k}. Its candidate sizes 6,7,8 follow those
chosen lane counts and anchors, not an unavoidable ambiguity theorem. The other
two sampled bases are historical test fixtures, not changes to selected S6.
