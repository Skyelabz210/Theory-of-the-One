import MockTheta

/-!
Executed exact-integer checks for the named third-order mock theta series.

The independent oracle forms finite coefficient arrays using the closed-form
factor coefficients (-1)^k * (k+1) at degree j*k, convolves those factors, then
shifts each product by n*n. It never calls divideBinomial, denominatorAction,
inverseSquaredPochhammer, mockSummand, mockCoeff or sumBelow.

The remaining checks compare the actual packet and evaluation APIs with that
oracle and exercise zero truncation, modulus one, negative coefficients,
overlapping composite refinement, and both integer roots of unity. Values of
t outside the analytic unit disc are intentional: these tests concern finite
polynomials only. They do not test analytic convergence or modularity.
-/

namespace KElimination.MockThetaSmoke

open KElimination.ResidueSeries KElimination.MockTheta

def expect (label : String) (ok : Bool) : IO Unit :=
  unless ok do throw (IO.userError label)

/-- Independent coefficient of (1+q^j)^(-2), used only for positive j. -/
def explicitFactor (j d : Nat) : Int :=
  if d % j = 0 then (-1) ^ (d / j) * ((d / j : Nat) + 1 : Int) else 0

/-- Ordinary finite polynomial convolution, truncated to N coefficients. -/
def convolve (N : Nat) (a b : Array Int) : Array Int :=
  ((List.range N).map (fun d =>
    (List.range (d + 1)).foldl
      (fun acc k => acc + a[k]! * b[d - k]!) 0)).toArray

def oracleReciprocal (N n : Nat) : Array Int :=
  let one := ((List.range N).map (fun d => if d = 0 then (1 : Int) else 0)).toArray
  (List.range n).foldl (fun coeff j =>
    let factor := ((List.range N).map (explicitFactor (j + 1))).toArray
    convolve N coeff factor) one

/-- Independent truncated q-hypergeometric product calculation. -/
def oracleCoefficients (N : Nat) : Array Int :=
  (List.range N).foldl (fun acc n =>
    if n * n < N then
      let reciprocal := oracleReciprocal N n
      ((List.range N).map (fun d =>
        acc[d]! + if n * n ≤ d then reciprocal[d - n * n]! else 0)).toArray
    else acc) (Array.replicate N 0)

def oraclePacket (coeff : Array Int) (t : Int) (N M r : Nat) : Int :=
  (List.range N).foldl (fun acc d =>
    acc + if d % M = r then coeff[d]! * t ^ d else 0) 0

def oraclePolynomial (coeff : Array Int) (N : Nat) (q : Int) : Int :=
  (List.range N).foldl (fun acc d => acc + coeff[d]! * q ^ d) 0

def refinementCases : List (Nat × Nat) :=
  [(1, 1), (1, 6), (2, 6), (3, 6), (2, 12), (3, 12), (4, 12),
   (6, 12), (3, 30), (5, 30), (6, 30), (10, 30), (15, 30)]

def run : IO Unit := do
  let oracle := oracleCoefficients 41
  let mut coefficientCount := 0
  for d in List.range 41 do
    expect s!"mock coefficient {d}" ((mockCoeff d : Int) == oracle[d]!)
    coefficientCount := coefficientCount + 1
  expect "first eleven signed coefficients"
    ((oracle.toList.take 11) == [1, 1, -2, 3, -3, 3, -5, 7, -6, 6, -10])

  let mut coefficientPacketCount := 0
  for M in [1, 2, 3, 4, 6, 11, 12, 23, 30] do
    for d in List.range 17 do
      for r in List.range (M + 1) do
        let expected := if d % M = r then oracle[d]! else 0
        expect s!"coefficient packet M={M} r={r} d={d}"
          ((mockPacket M r d : Int) == expected)
        coefficientPacketCount := coefficientPacketCount + 1

  let mut coefficientRefinementCount := 0
  for pair in refinementCases do
    let m := pair.1
    let M := pair.2
    for d in List.range 17 do
      for r in List.range (m + 1) do
        let fine := sumBelow M (fun s =>
          if s % m = r then (mockPacket M s d : Int) else 0)
        expect s!"coefficient refinement {M}->{m} r={r} d={d}"
          (fine == mockPacket m r d)
        coefficientRefinementCount := coefficientRefinementCount + 1

  let mut weightedPacketCount := 0
  for N in [0, 1, 2, 7, 12] do
    for t in [(-2 : Int), -1, 0, 1, 2] do
      for M in [1, 2, 3, 4, 6, 12, 30] do
        for r in List.range (M + 1) do
          expect s!"weighted packet N={N} t={t} M={M} r={r}"
            (mockWeightedPacket t N M r == oraclePacket oracle t N M r)
          weightedPacketCount := weightedPacketCount + 1

  let mut weightedRefinementCount := 0
  for N in [0, 1, 7, 12] do
    for t in [(-1 : Int), 0, 2] do
      for pair in refinementCases do
        let m := pair.1
        let M := pair.2
        for r in List.range (m + 1) do
          let fine := sumBelow M (fun s =>
            if s % m = r then mockWeightedPacket t N M s else 0)
          expect s!"weighted refinement N={N} t={t} {M}->{m} r={r}"
            (fine == mockWeightedPacket t N m r)
          weightedRefinementCount := weightedRefinementCount + 1

  let mut rootCaseCount := 0
  for N in [0, 1, 2, 7, 12, 21] do
    for t in [(-2 : Int), -1, 0, 1, 2] do
      for M in [1, 2, 3, 4, 6, 12, 30] do
        let roots : List Int := if M % 2 = 0 then [-1, 1] else [1]
        for z in roots do
          let observed := sumBelow M (fun r => mockWeightedPacket t N M r * z ^ r)
          let expected := oraclePolynomial oracle N (t * z)
          expect s!"finite root transform N={N} t={t} M={M} z={z}"
            (observed == expected)
          expect s!"finite polynomial N={N} t={t} M={M} z={z}"
            (mockPolynomial N (t * z) == expected)
          rootCaseCount := rootCaseCount + 1

  -- This missing-period control deliberately violates the root premise.
  let invalidRoot := sumBelow 3 (fun r => mockWeightedPacket (1 : Int) 4 3 r * (-1) ^ r)
  expect "an uncertified odd period need not preserve the -1 evaluation"
    (((-1 : Int) ^ 3 != 1) && invalidRoot != mockPolynomial 4 (-1 : Int))

  let assertions := coefficientCount + 1 + coefficientPacketCount +
    coefficientRefinementCount + weightedPacketCount + weightedRefinementCount +
    2 * rootCaseCount + 1
  IO.println s!"PASS: {coefficientCount} independent mock coefficients (degrees 0..40); {coefficientPacketCount} coefficient packets; {coefficientRefinementCount} coefficient refinements; {weightedPacketCount} oracle weighted packets; {weightedRefinementCount} weighted refinements; {rootCaseCount} root cases with two independent-oracle assertions each; 2 sign/premise controls. Total: {assertions} exact assertions."
  IO.println s!"Coefficients 0..40: {oracle.toList}"

end KElimination.MockThetaSmoke

#eval KElimination.MockThetaSmoke.run
