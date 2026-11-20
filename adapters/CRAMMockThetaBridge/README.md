# Single-anchor CRAM readout and finite mock theta evaluation

This standalone Lean package combines NINE65's signed quotient readout with
finite residue-packet evaluation for Ramanujan's four original third-order
series, $f$, $\phi$, $\psi$, and $\chi$.

| Lake dependency | Pinned revision | Package directory |
|---|---|---|
| `KElimination` from NINE65_v7 | [64c1c89b191093dc12cf81b87da5fb1a02c46dc1](https://github.com/Skyelabz210/NINE65_v7/tree/64c1c89b191093dc12cf81b87da5fb1a02c46dc1/lean4/CRAMUniversal) | `lean4/CRAMUniversal` |
| `k_elimination_universal` from Theory-of-the-One | [c59b9850f20b9071b7c2ba28b2013cbe55d4d6a4](https://github.com/Skyelabz210/Theory-of-the-One/tree/c59b9850f20b9071b7c2ba28b2013cbe55d4d6a4/formal/universal) | `formal/universal` |

The adapter imports NINE65's
`KElimination.UniversalResearch.IntegerSpecialization` and
`KElimination.UniversalResearch.StarLift` for the readout and target projection.
It imports `CoefficientObservations` and the named `MockTheta` modules from
Theory-of-the-One for the singleton-anchor resolution and weighted packets.
`BridgeArithmetic` places its period and fiber lemmas in `CRAMMockThetaBridge`.
The two package roots also contain overlapping Lean declaration names. The
adapter uses the specific modules above so each declaration has one source
in its import graph. [Import graph](MockThetaAdapter.lean) · [Lake pins](lakefile.toml)

## The readout and its admitted target

Let $M,A,b>0$. The signed integer $X$ supplies authentic readings $r=X\bmod M$
and $s=X\bmod A$. A public inverse $u$ satisfies $uM\equiv1\pmod A$.
NINE65's `KElimination.IntegerSpecialization.query` computes

$$
\kappa=(((s-r)\bmod A)u)\bmod A
      =\lfloor X/M\rfloor\bmod A.
$$

An adjacent anchor has $A=M+1$ and $u=-1$. Its positive quotient reading is
$(r-s)\bmod A$. The reverse subtraction gives the negative quotient class.
For a general unit anchor the public inverse specifies the sign and factor.
This inverse certificate implies $\gcd(M,A)=1$, so the singleton anchor has
quotient resolution $A$. The target $b$ may share factors with $M$ or $A$.
A nonunit anchor requires an exact defect division and a reduced inverse in a
separate readout theorem.

The target $b$ is admitted when $b/\gcd(M,b)\mid A$, equivalently $b\mid MA$.
At such a target the theorem proves

$$
((r\bmod b)+(M\bmod b)(\kappa\bmod b))\bmod b=X\bmod b.
$$

NINE65's `KElimination.IntegerSpecialization.targetLaneProjection` takes
lane residues and the computed quotient class. $X$ appears in the mathematical
authenticity hypotheses. The congruence holds for arbitrarily large positive
or negative quotients.

`BridgeArithmetic` gives the reduced-period equivalence for both natural and
signed multipliers $k$, and its fiber lemma transports equal quotient classes
modulo $A$ to equal targets modulo $b$.

## The finite transform

Let $R$ carry Lean's `Lean.Grind.CommRing` structure, $t,z\in R$, and assume
$z^b=1$. The same target-admission premise permits evaluation at period
$L=MA$. For coefficients $a_d$ and the complete distribution of packet masses

$$
C_{N,L,i}(t)=\sum_{d<N,\;d\equiv i\pmod L} a_d t^d,
$$

the adapter proves

$$
\sum_{i<L} C_{N,L,i}(t)z^i=\sum_{d<N} a_d (tz)^d.
$$

`finite_evaluation_from_nine65_anchor` returns the readout certificate and
this identity for a supplied coefficient sequence. The adjacent wrappers
`mockTheta_from_nine65_adjacent`, `phi_from_nine65_adjacent`,
`psi_from_nine65_adjacent`, and `chi_from_nine65_adjacent` use the four named
coefficient constructors. Their conclusions identify the observed quotient,
its target projection, and the finite evaluation. The finite character uses
the supplied $z$ and the packet distribution comes from the coefficient
sequence. A single pair of source readings determines the admitted target residue.
Here $N$ counts retained coefficient degrees. Infinite boundary evaluation
and runtime source authentication require additional results.
[Adapter declarations](MockThetaAdapter.lean) · [Target arithmetic](BridgeArithmetic.lean)

## Verification

Use the pinned Lean/Lake 4.27.0-rc1 installation, Git and Python 3.11 or
newer. The first run needs network access to fetch the two direct Git
dependencies and their locked transitive dependencies.
From the repository root run

```sh
cd adapters/CRAMMockThetaBridge
./verify_bridge.sh
```

The script checks each checkout against the manifest, cleans the adapter and
both pinned source packages, and rebuilds the imported modules. It writes a
fresh receipt and the build, audit, and smoke logs under `.lake/verification/`.
The saved receipt records the Git revisions, compiler, source hashes, axiom
dependencies, and executed checks. [Verification receipt](verification.json)

The build, kernel audit, and executable fixtures can also be run individually
from the adapter directory.

```sh
lake build MockThetaAdapter
lake env lean BridgeAudit.lean
lake env lean BridgeSmoke.lean
```

The kernel audit checked 23 declarations from the two adapter modules,
including all 14 required public declarations. It follows their transitive
axioms and permits `propext`, `Classical.choice`, and `Quot.sound`.
[Audit](BridgeAudit.lean) · [Dependency lock](lake-manifest.json)

The smoke program passed 24 exact numerical assertions. It also instantiates each named theorem with $M=6$, $A=7$,
$b=14$, and $X=-1$. The readings $(5,6)$ give $\kappa=6$ and target
$13$. Reversing the adjacent subtraction yields target $11$, an incorrect
public inverse gives $3$, and substituting a stale anchor reading gives $7$.
The sources $-1$ and $41$ have the same two readings and residues $4$ and $1$
modulo $5$, demonstrating the information lost at an inadmissible target.

In $\mathbb F_{29}$, $z=4$ has order $14$. With $t=3$, the first five
coefficients of $f,\phi,\psi,\chi$ give independent expected values
$5,26,1,12$ at $tz=12$. The suite also covers a non-adjacent unit anchor,
modulus one, the empty coefficient truncation, and a truncation that wraps
many degrees onto two residue classes. A separate integer example gives
packet sum $6$ and direct value $15$ when the root premise fails.
[Executable fixtures](BridgeSmoke.lean)
