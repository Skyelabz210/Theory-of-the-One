import MockThetaPhi
import MockThetaPsi
import MockThetaChi

/-!
Exact coefficient and finite character checks for Ramanujan's third-order f, φ, ψ, χ.

The integer oracle convolves explicit factor coefficients and shifts each
product by n². Only ψ starts at n=1. Its factor is the geometric series at
odd stride 2*j-1. The χ oracle equates coefficients in (1-x+x²)b=1.
For f and φ it uses the signed geometric factor formulas at strides j and 2*j.
These oracle calculations are independent of the named coefficient definitions.

Each series is checked on the same residue and truncation cases. Three
equalities on p. 63 of Watson's "The Final Problem" compare the actual
Lean series through degree 40.
-/

namespace KElimination.MockThetaSmoke

open KElimination.ResidueSeries KElimination.MockTheta KElimination.MockThetaPhi
open KElimination.MockThetaPsi KElimination.MockThetaChi KElimination.ProfiniteObservations

def expect (label : String) (ok : Bool) : IO Unit :=
  unless ok do throw (IO.userError label)

/-- Independent coefficient of (1+q^j)^(-2), used only for positive j. -/
def fFactor (j d : Nat) : Int :=
  if d % j = 0 then (-1) ^ (d / j) * ((d / j : Nat) + 1 : Int) else 0

/-- Independent coefficient of (1+q^(2*j))^(-1), for positive j. -/
def phiFactor (j d : Nat) : Int :=
  let step := 2 * j
  if d % step = 0 then (-1) ^ (d / step) else 0

/-- Coefficients of 1/(1-q^(2*j-1)) for positive j. -/
def psiFactor (j d : Nat) : Int :=
  if d % (2 * j - 1) = 0 then 1 else 0

/-- Direct trinomial inversion: b₀=b₁=1 and bₖ₊₂=bₖ₊₁-bₖ. -/
def chiFactor (j d : Nat) : Int :=
  if d % j = 0 then
    let pair := (List.range (d / j)).foldl (fun (b : Int × Int) _ =>
      (b.2, b.2 - b.1)) (1, 1)
    pair.1
  else 0

/-- Ordinary finite polynomial convolution, truncated to N coefficients. -/
def convolve (N : Nat) (a b : Array Int) : Array Int :=
  ((List.range N).map (fun d =>
    (List.range (d + 1)).foldl
      (fun acc k => acc + a[k]! * b[d - k]!) 0)).toArray

def oracleReciprocal (factorCoeff : Nat → Nat → Int) (N n : Nat) : Array Int :=
  let one := ((List.range N).map (fun d => if d = 0 then (1 : Int) else 0)).toArray
  (List.range n).foldl (fun coeff j =>
    let factor := ((List.range N).map (factorCoeff (j + 1))).toArray
    convolve N coeff factor) one

/-- Independent truncated q-hypergeometric product calculation. -/
def oracleCoefficients (factorCoeff : Nat → Nat → Int) (N : Nat) (first : Nat := 0) : Array Int :=
  (List.range N).foldl (fun acc n =>
    if first ≤ n ∧ n * n < N then
      let reciprocal := oracleReciprocal factorCoeff N n
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

def checkCylinders (name : String) (oracle : Array Int)
    (cylinder : positivePeriods.Period → Nat → ResiduePoint positivePeriods → Int) : IO Nat := do
  let periods : List positivePeriods.Period := [
    ⟨1, Nat.zero_lt_succ 0⟩, ⟨3, Nat.zero_lt_succ 2⟩, ⟨6, Nat.zero_lt_succ 5⟩]
  let mut count := 0
  for m in periods do
    for source in [(-4 : Int), -3, 0, 2, 3, 8, 9, 15] do
      let point := intPoint positivePeriods source
      for d in List.range 17 do
        let expected := if (d : Int) % m.val = source % m.val then oracle[d]! else 0
        expect s!"{name} cylinder m={m.val} source={source} degree={d}"
          (cylinder m d point == expected)
        count := count + 1
  IO.println s!"PASS {name}: {count} signed-source cylinder assertions"
  return count

/-- A primitive fourth root in F₅, observed at a period supplied by overlapping
anchors. The expected polynomial is computed in Int and reduced at the end. -/
def checkFourthRoot (name : String) (oracle : Array Int)
    (weighted : Fin 5 → Nat → Nat → Nat → Fin 5) : IO Nat := do
  let period := 3 * CoupledAnchors.resolution 3 [4, 6]
  let z : Fin 5 := 2
  expect "coupled period and fourth root" (period == 12 && z ^ 4 == 1 && z ^ 2 != 1)
  let mut count := 1
  for N in [0, 1, 4, 17] do
    let observed := sumBelow period (fun r => weighted (4 : Fin 5) N period r * z ^ r)
    let expected := (oraclePolynomial oracle N 8 % 5).toNat
    expect s!"{name} fourth root N={N}" (observed.val == expected)
    count := count + 1
  IO.println s!"PASS {name}: {count} fourth-root and coupled-period assertions in Fin 5"
  return count

def checkSeries (name : String) (oracle : Array Int) (knownCoefficients : List Int)
    (coeff : Nat → Int) (packet : Nat → Nat → Nat → Int)
    (weighted : {R : Type} → [Lean.Grind.CommRing R] → R → Nat → Nat → Nat → R)
    (polynomial : Nat → Int → Int)
    (cylinder : positivePeriods.Period → Nat → ResiduePoint positivePeriods → Int)
    (negativeControlN : Nat := 4) : IO Nat := do
  let mut coefficientCount := 0
  for d in List.range 41 do
    expect s!"{name} coefficient {d}" (coeff d == oracle[d]!)
    coefficientCount := coefficientCount + 1
  expect s!"{name} signed coefficient prefix"
    (oracle.toList.take knownCoefficients.length == knownCoefficients)

  let mut coefficientPacketCount := 0
  for M in [1, 2, 3, 4, 6, 11, 12, 23, 30] do
    for d in List.range 17 do
      for r in List.range (M + 1) do
        let expected := if d % M = r then oracle[d]! else 0
        expect s!"{name} coefficient packet M={M} r={r} d={d}"
          ((packet M r d : Int) == expected)
        coefficientPacketCount := coefficientPacketCount + 1

  let mut coefficientRefinementCount := 0
  for pair in refinementCases do
    let m := pair.1
    let M := pair.2
    for d in List.range 17 do
      for r in List.range (m + 1) do
        let fine := sumBelow M (fun s =>
          if s % m = r then (packet M s d : Int) else 0)
        expect s!"{name} coefficient refinement {M}->{m} r={r} d={d}"
          (fine == packet m r d)
        coefficientRefinementCount := coefficientRefinementCount + 1

  let mut weightedPacketCount := 0
  for N in [0, 1, 2, 7, 12] do
    for t in [(-2 : Int), -1, 0, 1, 2] do
      for M in [1, 2, 3, 4, 6, 12, 30] do
        for r in List.range (M + 1) do
          expect s!"{name} weighted packet N={N} t={t} M={M} r={r}"
            (weighted t N M r == oraclePacket oracle t N M r)
          weightedPacketCount := weightedPacketCount + 1

  let mut weightedRefinementCount := 0
  for N in [0, 1, 7, 12] do
    for t in [(-1 : Int), 0, 2] do
      for pair in refinementCases do
        let m := pair.1
        let M := pair.2
        for r in List.range (m + 1) do
          let fine := sumBelow M (fun s =>
            if s % m = r then weighted t N M s else 0)
          expect s!"{name} weighted refinement N={N} t={t} {M}->{m} r={r}"
            (fine == weighted t N m r)
          weightedRefinementCount := weightedRefinementCount + 1

  let mut rootCaseCount := 0
  for N in [0, 1, 2, 7, 12, 21] do
    for t in [(-2 : Int), -1, 0, 1, 2] do
      for M in [1, 2, 3, 4, 6, 12, 30] do
        let roots : List Int := if M % 2 = 0 then [-1, 1] else [1]
        for z in roots do
          let observed := sumBelow M (fun r => weighted t N M r * z ^ r)
          let expected := oraclePolynomial oracle N (t * z)
          expect s!"{name} finite root transform N={N} t={t} M={M} z={z}"
            (observed == expected)
          expect s!"{name} finite polynomial N={N} t={t} M={M} z={z}"
            (polynomial N (t * z) == expected)
          rootCaseCount := rootCaseCount + 1

  -- This missing-period control deliberately violates the root premise.
  let invalidRoot := sumBelow 3 (fun r => weighted (1 : Int) negativeControlN 3 r * (-1) ^ r)
  expect s!"{name} uncertified odd period need not preserve the -1 evaluation"
    (((-1 : Int) ^ 3 != 1) && invalidRoot != polynomial negativeControlN (-1 : Int))

  let assertions := coefficientCount + 1 + coefficientPacketCount +
    coefficientRefinementCount + weightedPacketCount + weightedRefinementCount +
    2 * rootCaseCount + 1
  IO.println s!"PASS {name}: {assertions} exact assertions ({coefficientCount} coefficients, {coefficientPacketCount} degree packets, {coefficientRefinementCount} degree refinements, {weightedPacketCount} weighted packets, {weightedRefinementCount} weighted refinements, {rootCaseCount} root cases checked twice, 2 controls)"
  IO.println s!"{name} coefficients 0..40: {oracle.toList}"
  let cylinders ← checkCylinders name oracle cylinder
  let fourthRoots ← checkFourthRoot name oracle weighted
  return assertions + cylinders + fourthRoots

/-- Multiply a truncated polynomial by ∏(1+sign*qʳ), keeping its original
length. Factors beyond its last degree contribute only their constant term. -/
def multiplyEulerFactors (coeffs : Array Int) (sgn : Int) : Array Int :=
  (List.range (coeffs.size - 1)).foldl (fun a j =>
    let r := j + 1
    ((List.range a.size).map (fun d =>
      a[d]! + if r ≤ d then sgn * a[d-r]! else 0)).toArray) coeffs

/-- Coefficient of θ₄(0,q^m) from its sum over signed integer squares, m>0. -/
def theta4Coeff (m d : Nat) : Int :=
  match (List.range (d + 1)).find? (fun k => m * k * k == d) with
  | some 0 => 1
  | some k => 2 * (-1 : Int) ^ k
  | none => 0

def checkWatson (D : Nat) : IO Nat := do
  let degrees := List.range (D + 1)
  let phiDifference := (degrees.map fun d =>
    2 * (-1 : Int) ^ d * phiCoeff d - mockCoeff d).toArray
  let phiProduct := multiplyEulerFactors phiDifference 1
  let chiDifference := (degrees.map fun d =>
    4 * (chiCoeff d : Int) - mockCoeff d).toArray
  let chiProduct := multiplyEulerFactors chiDifference (-1)
  let theta4AtQ3 := (degrees.map (theta4Coeff 3)).toArray
  let theta4AtQ3Squared := convolve (D + 1) theta4AtQ3 theta4AtQ3
  let mut count := 0
  for d in degrees do
    expect s!"Watson f/φ product d={d}" (phiProduct[d]! == theta4Coeff 1 d)
    expect s!"Watson f/φ/ψ relation d={d}"
      (phiDifference[d]! == mockCoeff d + 4 * (-1 : Int) ^ d * psiCoeff d)
    expect s!"Watson f/χ product d={d}" (chiProduct[d]! == 3 * theta4AtQ3Squared[d]!)
    count := count + 3
  IO.println s!"PASS three Watson relations: {count} coefficient assertions (degrees 0..{D} each)"
  return count

def run : IO Unit := do
  let fOracle := oracleCoefficients fFactor 41
  let fCount ← checkSeries "f" fOracle [1, 1, -2, 3, -3, 3, -5, 7, -6, 6, -10]
    mockCoeff mockPacket mockWeightedPacket mockPolynomial mockCylinder
  let phiOracle := oracleCoefficients phiFactor 41
  let phiCount ← checkSeries "φ" phiOracle [1, 1, 0, -1, 1, 1, -1, -1, 0, 2, 0, -2, 1, 1, -1, -2, 1]
    phiCoeff phiPacket phiWeightedPacket phiPolynomial phiCylinder
  let psiOracle := oracleCoefficients psiFactor 41 1
  let psiCount ← checkSeries "ψ" psiOracle [0, 1, 1, 1, 2, 2, 2, 3, 3, 4, 5, 5, 6]
    psiCoeff psiPacket psiWeightedPacket psiPolynomial psiCylinder
  let chiOracle := oracleCoefficients chiFactor 41
  -- The degree-3 χ coefficient vanishes. Degree 10 detects the missing period.
  let chiCount ← checkSeries "χ" chiOracle [1, 1, 1, 0, 0, 0, 1, 1, 0, 0, -1, 0, 1]
    chiCoeff chiPacket chiWeightedPacket chiPolynomial chiCylinder 11
  let watson ← checkWatson 40
  IO.println s!"Total: {fCount + phiCount + psiCount + chiCount + watson} exact assertions."

end KElimination.MockThetaSmoke

#eval KElimination.MockThetaSmoke.run
