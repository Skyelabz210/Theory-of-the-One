# CRAM packets at primitive even roots

Lean proves that the compensated radial series of Ramanujan’s \(f\) converges to the finite Folsom–Ono–Rhoades packet value at every primitive root of order \(2k\), for every \(k>0\). It also proves the limit for diagonal Taylor packets at every admitted period and identifies their normalized limit with the FKTY value at every rational with even reduced denominator. A single finite transformation supplies the Watson-to-FOR equality uniformly in \(k\). [Radial and packet theorems](../../adapters/MockThetaAnalytic/FOREvenRoot.lean) · [FOR, Theorem 1.1](https://doi.org/10.1017/fmp.2013.3) · [Watson form of the limit](https://afolsom.people.amherst.edu/FOR-ContempMath.pdf)

## The two radial series

Let \(\zeta\) be primitive of order \(2k\), with \(k>0\). Set \(c=1\) for even \(k\) and \(c=2\) for odd \(k\). The selected Watson terms are
\[
T_{c,n}(q)=\frac{(-q)^{n^2}}{\prod_{j=0}^{n-1}(1+q^{2j+c})}.
\]
Since \(\zeta^2\) is primitive of order \(k\) and \(k+c\) is odd, each block of \(k\) successive denominator factors has product 2. The numerator repeats after \(k\) steps. Thus \(T_{c,n+k}(\zeta)=T_{c,n}(\zeta)/2\) and the absolute endpoint sum converges. The inequality \(\sqrt{u}\,|1+v|\le |1+uv|\) for \(0\le u\le1\) and \(|v|=1\) bounds each successive radial ratio by its endpoint ratio. Dominated convergence gives twice the initial block, with its zero-index term removed for \(\psi\). Watson’s two disk identities then give
\[
\lim_{t\uparrow1}\big(f(t\zeta)-(-1)^k b(t\zeta)\big)=
\begin{cases}
-4\psi(-\zeta),& k\text{ even},\\
2\phi(-\zeta),& k\text{ odd}.
\end{cases}
\]
The proof applies to every primitive root of the given order. [Denominator and convergence](../../adapters/MockThetaAnalytic/FORWatsonTerms.lean) · [Watson’s subtraction identity](../../adapters/MockThetaAnalytic/FORPsiRadial.lean) · [Addition identity](../../adapters/MockThetaAnalytic/FOROrder34.lean)

## The finite transformation

Let \(Q\) be primitive of order \(k\), let \(z^k=1\), and take \(b\ne0\). Define \(A_n=\prod_{j<n}(1-bQ^j)\) and \(H_n(z)=\prod_{j=1}^n(z-Q^j)\). Lean proves the following specialization of Lovejoy’s transformation.
\[
\sum_{n<k} A_n z^n = b^{k-1}\sum_{n<k}\frac{A_n H_n(z)}{b^n Q^{n(n+1)}}.
\]
The two expressions satisfy \((1-z)Y(z)+bzY(Qz)=b^k\) on the root orbit. On the monomial side this follows from the recurrence for \(A_n\) and \(A_k=1-b^k\). On the Newton side, shifting \(z\) gives \(H_{n+1}(Qz)=Q^{n+1}(z-1)H_n(z)\). With \(c_n=A_n/(b^nQ^{n(n+1)})\), the relation \(bQ^{2n+2}c_{n+1}=(1-bQ^n)c_n\) makes the terms telescope. The last term vanishes because \((1-z)H_{k-1}(z)=0\) on the orbit. At \(z=1\), the recurrence fixes the value at \(Q\). Successive shifts then give agreement at every power of \(Q\). [Lean transformation proof](../../adapters/MockThetaAnalytic/FORFiniteTransform.lean) · [Lovejoy, equation (2.3)](https://hrj.episciences.org/8930)

For the physical root \(\zeta\), take \(Q=\zeta^2\), \(b=-\zeta^c\), and \(z=-\zeta^{c-1}\), with \(c\) as above. Then \(b=\zeta z\), \(b^k=-1\), and \(z^k=1\). The two products on the right combine the even and odd factors of \((-\zeta;\zeta)_{2n}\). Inverting their powers and pairing the terms of the reflected strange sum gives \(z\sum_{n<k}A_nz^n=-U_k(\zeta)\). Reversing the Watson block and using its full denominator of 2 gives
\[
2\sum_{n<k}T_{c,n}(\zeta)=\begin{cases}
1+U_k(\zeta),&k\text{ even},\\
-2U_k(\zeta),&k\text{ odd}.
\end{cases}
\]
This gives the same radial value \(-4U_k(\zeta)\) in the two compensation formulas. [Uniform boundary identification](../../adapters/MockThetaAnalytic/FORWatsonBoundary.lean)

## Integer certificates

In \(\mathbb Z[X]\), put
\[
\begin{aligned}
D&=\prod_{j<k}(1+X^{2j+c}),\\
W&=\sum_{n<k}(-X)^{n^2}\prod_{j=n}^{k-1}(1+X^{2j+c}),\\
U&=\sum_{n<k}X^{n+1}\prod_{j=1}^{n}(1+X^j)^2 .
\end{aligned}
\]

### Polynomial congruence of 23 November 2026

Write \(B_k=1+U\) for even \(k\) and \(B_k=-2U\) for odd \(k\). Lean proves the universal polynomial congruence
\[
X^k+1\ \mid\ \Delta_k(X),\qquad \Delta_k=W-(D-1)B_k,\qquad k\ge0.
\]
The empty case has \(W=0\) and \(D=1\). For positive \(k\), Lean proves that the executable integer-vector certificate returns true exactly when this divisibility holds. [Polynomial congruence and certificate equivalence](../../adapters/MockThetaAnalytic/FORWatsonCongruence.lean)

Every complex root of \(X^k+1\) has order \(2h\) with \(k=mh\) for odd \(m\). The selected \(c\) agrees for \(h\) and \(k\). Splitting \(D\) at each \(n\) cancels the nonzero prefix in \(T_{c,n}\) and leaves the suffix defining \(W\). The denominator has \(m\) blocks of product 2, so \(D=2^m\), and the geometric sum gives \(W=(D-1)\,2\sum_{n<h}T_{c,n}\). The unimodal sum terminates at \(h\). The primitive-root identity therefore gives \(\Delta_k(q)=0\) at every complex root. For \(k=12\) at a primitive eighth root the audit checks \(8\sum_{n<12}T_{1,n}=7(1+U_4)\). [Block proof](../../adapters/MockThetaAnalytic/FORWatsonQuotient.lean) · [Audit example](../../adapters/MockThetaAnalytic/AnalyticAudit.lean)

Monic division by \(X^k+1\) gives an integer remainder of degree below \(k\). Its complex evaluation vanishes at the \(k\) distinct odd powers of a primitive \(2k\)-th root, forcing every coefficient to vanish. At \(k=1\), the quotient \(2X^2-X+1\) evaluates to 4 at \(-1\), so \(X+1\) has multiplicity one in \(\Delta_1\). [Root criterion](../../adapters/MockThetaAnalytic/FORWatsonCongruence.lean) · [Sharpness check](../../adapters/MockThetaAnalytic/AnalyticAudit.lean)

For any commutative ring \(A\) and \(x\in A\), evaluating the integer quotient gives \(x^k+1\mid\Delta_k(x)\). If \(x^k=-1\), this gives \(W(x)=(D(x)-1)B_k(x)\). In \(\mathbb Z/8\mathbb Z\) at \(k=3\) and \(x=-1\), the denominator is zero and both sides equal 6. In prime characteristic \(p\), the Frobenius identity gives \((X^h+1)^{p^e}\mid\Delta_{hp^e}(X)\), including \((X+1)^{11}\mid\Delta_{11}(X)\) in \(\mathbb F_{11}[X]\). [Ring specialization and prime-power proof](../../adapters/MockThetaAnalytic/FORWatsonCongruence.lean) · [Mod-8 and mod-11 checks](../../adapters/MockThetaAnalytic/AnalyticAudit.lean)

### Odd half-periods

Let \(Q_k=\Delta_k/(X^k+1)\) be the integer polynomial quotient for \(k>0\). For every odd \(k\), Lean proves
\[
\Delta_k'(-1)=2k(k+1),\qquad Q_k(-1)=2(k+1).
\]
Every term of \(U_k-X\) contains \((X+1)^2\). In the odd case this gives \(\Delta_k\) the same value and derivative at \(-1\) as \(G_k=W+2(D-1)X\). For the \(c=2\) products at length \(n\), appending the last denominator factor gives
\[
G_{n+1}=\bigl(G_n+(-X)^{n^2}+2X\bigr)(1+X^{2n+2})-2X,\qquad G_0=0.
\]
Evaluation and differentiation give \(G_n(-1)=0\) and \(G_n'(-1)=2n(n+1)\) by induction. In the integer factorization \(\Delta_k=(X^k+1)Q_k\), differentiation at \(-1\) now gives \(kQ_k(-1)=2k(k+1)\). Cancelling the positive integer \(k\) gives the asserted quotient value. [Quotient and derivative proofs](../../adapters/MockThetaAnalytic/FORWatsonMultiplicity.lean)

In any commutative ring \(R\), monicity allows cancellation of \(X^k+1\). Hence \((X^k+1)(X+1)\mid\Delta_k\) in \(R[X]\) exactly when \(2(k+1)=0\) in \(R\). In particular \(-1\) is a simple root over \(\mathbb Z\) for every odd \(k\). In \(\mathbb F_p\) for an odd prime divisor \(p\) of odd \(k\), write \(k=h p^e\) with \(p\nmid h\). Frobenius gives \(X^k+1=(X^h+1)^{p^e}\). The quotient \((X^h+1)/(X+1)\) takes the value \(h\) at \(-1\), and \(Q_k(-1)=2\) in this field. The cofactor after removing \((X+1)^{p^e}\) thus evaluates to \(2h^{p^e}=2h\ne0\). The exact multiplicity is \(p^e\). [Prime multiplicity theorem](../../adapters/MockThetaAnalytic/FORWatsonMultiplicity.lean)

For odd \(k\ge3\) the next coefficients are
\[
[Y^2]\Delta_k(Y-1)=-k(k^3+2k^2+3k+5),\qquad
Q'_k(-1)=-(k^3+k^2+3k+6).
\]
Writing \(g_n=[Y^2]G_n(Y-1)\), the same recurrence gives
\[
g_{n+1}=2g_n+n^4-2n^3-9n^2-11n-5,\qquad
g_n=6(2^n-1)-n(n^3+2n^2+3n+5).
\]
Only the \(n=1\) and \(n=2\) summands of \(U_k-X\) contribute to its quadratic coefficient. Their contributions are \(1\) and \(-4\). Every later summand contains \((1+X)^2(1+X^3)^2\), so its coefficient is zero. Multiplying by \(2(D-1)\) contributes \(-6(2^k-1)\), leaving the asserted quadratic coefficient. Comparing the second derivatives of \(\Delta_k=(X^k+1)Q_k\) gives the quotient derivative. For \(k\equiv-1\pmod p\) with \(p>3\), the quadratic coefficient is \(3\) and the constant and linear coefficients vanish. Thus the root is double. [Derivative and double-root proofs](../../adapters/MockThetaAnalytic/FORWatsonMultiplicity.lean)

### Even half-periods

For even \(k>0\) and every odd divisor \(s\) of \(k\), Lean proves the additional integer divisibility
\[
X^s+1\mid\Delta_k(X).
\]
At a root \(q^s=-1\), one has \(q^k=1\) and \(q\) has order \(2h\) for some odd \(h\mid s\). The finite Newton identity holds at every complex argument because both sides have degree below \(h\) and agree on the \(h\) distinct powers of \(q^2\). Evaluating it at \(z=-1\) with \(b=-q\) gives
\[
\sum_{n<h}(-1)^n\prod_{j<n}(1+q^{2j+1})=-U_h(q).
\]
The odd denominator progression contains \(1+q^h=0\), which makes \(D(q)=0\) and terminates the alternating sum. Using \(q^k=1\) to reverse the suffixes in \(W(q)\) gives this sum with the constant term removed, so \(W(q)=-1-U_h(q)\). Since \(U_k(q)=U_h(q)\), the cleared difference vanishes. The monic root criterion yields the integer divisor. [Newton interpolation](../../adapters/MockThetaAnalytic/FORFiniteTransform.lean) · [Reversed numerator](../../adapters/MockThetaAnalytic/FORWatsonBoundary.lean) · [Even-period congruence](../../adapters/MockThetaAnalytic/FORWatsonCongruence.lean)

At \(-1\) the last suffix gives \(W'(-1)=2k-1\), and the contribution of the boundary term adds \(1\). Hence \(\Delta'_k(-1)=2k\). Differentiating the factorization by \(X^s+1\) shows that its integer quotient takes the value \(2k/s\). For an odd prime \(p\), choose \(s=p^{v_p(k)}\). After coefficient reduction the divisor becomes \((X+1)^s\) and the quotient value is nonzero, giving multiplicity exactly \(s\). [Even quotient and multiplicity](../../adapters/MockThetaAnalytic/FORWatsonMultiplicity.lean)

### Exact classification in prime characteristic

For every positive \(k\) and every prime \(p>3\), Lean proves
\[
\operatorname{mult}_{-1}(\Delta_k\bmod p)=
\begin{cases}
2,& k\text{ odd and }p\mid k+1,\\
p^{v_p(k)},&\text{otherwise}.
\end{cases}
\]
For prime 11, the double-root class is \(k\equiv21\pmod{22}\). A reading of \(k\bmod22\) selects the simple, double, or \(11\)-divisible case. In the divisible case the exact power of 11 depends on higher residues. For example, \(k=11\) and \(k=121\) have the same class modulo 22 and give multiplicities \(11\) and \(121\), respectively. Their even counterparts \(k=22\) and \(k=242\) give the same two multiplicities. [Classification](../../adapters/MockThetaAnalytic/FORWatsonMultiplicity.lean) · [Lean examples](../../adapters/MockThetaAnalytic/AnalyticAudit.lean)

In the \(k=11\) integer calculation the quotient value is \(24\), and the first nonzero linear remainder modulo 11 is \(2\) at the twelfth division. Modulo 121, \(k=11\) gives a simple root since \(\Delta'_{11}(-1)=264\equiv22\). The root at \(k=21\) is double modulo 11 and simple modulo 121. At \(k=241\) it is double modulo 121. The characteristic-3 control \(k=5\) has multiplicity three in the integer division replay. [Lean examples](../../adapters/MockThetaAnalytic/AnalyticAudit.lean) · [Integer division results](../../evidence/current/quantum-radial/watson-even-roots.json)

## FKTY reflection and the prime-11 test

For any \(q^k=-1\), define \(C(x)=\sum_{n<2k}(-1)^{n+1}\prod_{j=1}^n(x+q^{-j})\). The product at the last index vanishes after applying the shift to \(x=q^{j+1}\) for \(0\le j<k\), yielding
\[
C(q^j)=(1+q^{j+1})^2C(q^{j+1})+q^{j+1}.
\]
The zero factor at \(q^k\) closes the recursion. Its value at \(1\) is both the terminating reflected strange sum and \(U\). At a rational \(x\) of reduced denominator \(2k\), apply the FKTY scale and phase to the FOR value at \(\zeta=e^{-2\pi ix}\). [Lean reflection theorem](../../adapters/MockThetaAnalytic/FKTYReflection.lean) · [FKTY, Theorem 1.2 and §2.2](https://afolsom.people.amherst.edu/FKTY-JNT16.pdf)

A primitive character distinguishes exactly the residue classes modulo its order. In a signed chart with primary \(M\), the same-source anchors recover the phase of order \(2k\) exactly when their quotient resolution is divisible by \(2k/\gcd(M,2k)\). For order 22, omitting the prime 11 from S6 leaves \(M=2730\). The sources \(X\) and \(X+2730\) then alias in the primary reading and differ in phase. A matching mod‑11 reading supplies resolution 11 and restores period \(30030\). At order 44, full S6 with a same-source mod‑4 reading supplies quotient resolution 2 and period \(60060\). The audit instantiates the uniform Taylor theorem at both periods. [Phase criterion and anchor proof](../../adapters/MockThetaAnalytic/FOREvenRoot.lean) · [Order-22 and order-44 examples](../../adapters/MockThetaAnalytic/AnalyticAudit.lean)

## Replay

The independent replay clears the denominator by multiplying its suffixes in reverse order. It performs 44 monic divisions by \(X^k+1\) for \(1\le k\le44\) and 45 additional divisions by \(X^s+1\) for odd divisors \(s\) of even \(k\) in this range. It checks the Taylor coefficients at all 22 odd indices and the first nonzero linear remainder for 200 half-period and prime pairs, including every half-period in this range modulo 11. The replay also checks the Watson and reflection polynomials and the vanishing denominator of the opposite parity through half-order 96, the imprimitive eighth-root control, and 168 signed phase comparisons across seven anchor configurations. The compiled Lean checker returned `true` for the same 96 half-orders and for \(k=1001\). [Replay program](../../tools/check_watson_even_roots.py) · [Exact receipt](../../evidence/current/quantum-radial/watson-even-roots.json)

The 22 November audit covered 1,693 theorem declarations in 65 analytic modules. The first 23 November audit covered 1,713 theorems in 66 modules with the universal polynomial congruence. With the even-period divisor and full multiplicity classification, a clean rebuild with Lean 4.27.0-rc1 audited 1,774 theorems and 2,061 declarations in total across 67 modules. The proof dependencies are confined to `propext`, `Classical.choice`, and `Quot.sound`. The audit also checks a failing substitution in the Newton transformation with \(Q=1\) and \(k=2\), where the two sides evaluate to 0 and 2. The order-24, order-34, and S6 shadow replays reproduced their receipts. [Lean audit and source hashes](../../adapters/MockThetaAnalytic/verification.json)

Run from the repository root with the pinned Lean and Lake.

```sh
python3 tools/check_watson_even_roots.py | diff -u evidence/current/quantum-radial/watson-even-roots.json -
(cd adapters/MockThetaAnalytic && python3 verify_analytic.py)
```

After the build, `lake env lean --stdin` from `adapters/MockThetaAnalytic` displays the universal theorem and runs the executable checks.

```lean
import FORWatsonMultiplicity
open MockThetaAnalytic
#check watson_polynomial_congruence
#check watson_quotient_at_neg_one
#check watson_even_polynomial_congruence
#check watson_rootMultiplicity_at_neg_one
#eval (List.range' 1 96).all watsonBoundaryCertificate
#eval watsonBoundaryCertificate 1001
```
