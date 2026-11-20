import MockThetaPhi

/-!
Exact coefficient and finite character checks for Ramanujan's third-order f and φ.

The independent integer oracle convolves finite arrays of explicit geometric
factor coefficients and shifts each product by n². For f the factor has
coefficient (-1)^k*(k+1) at j*k. For φ the factor has coefficient (-1)^k at
2*j*k. Neither calculation uses the formal division or coefficient APIs.

The two sets of packet and root checks use the same inputs for comparison.
A separate coefficientwise check of the first relation on p. 63 of Watson's
"The Final Problem" links the two actual Lean coefficient series through degree 40.
-/

namespace KElimination.MockThetaSmoke

open KElimination.ResidueSeries KElimination.MockTheta KElimination.MockThetaPhi
open KElimination.ProfiniteObservations

def expect (label : String) (ok : Bool) : IO Unit :=
  unless ok do throw (IO.userError label)

/-- Independent coefficient of (1+q^j)^(-2), used only for positive j. -/
def fFactor (j d : Nat) : Int :=
  if d % j = 0 then (-1) ^ (d / j) * ((d / j : Nat) + 1 : Int) else 0

/-- Independent coefficient of (1+q^(2*j))^(-1), for positive j. -/
def phiFactor (j d : Nat) : Int :=
  let step := 2 * j
  if d % step = 0 then (-1) ^ (d / step) else 0

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
def oracleCoefficients (factorCoeff : Nat → Nat → Int) (N : Nat) : Array Int :=
  (List.range N).foldl (fun acc n =>
    if n * n < N then
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

def checkSeries (name : String) (oracle : Array Int) (knownCoefficients : List Int)
    (coeff : Nat → Int) (packet : Nat → Nat → Nat → Int)
    (weighted : Int → Nat → Nat → Nat → Int) (polynomial : Nat → Int → Int) :
    IO Nat := do
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
  let invalidRoot := sumBelow 3 (fun r => weighted (1 : Int) 4 3 r * (-1) ^ r)
  expect s!"{name} uncertified odd period need not preserve the -1 evaluation"
    (((-1 : Int) ^ 3 != 1) && invalidRoot != polynomial 4 (-1 : Int))

  let assertions := coefficientCount + 1 + coefficientPacketCount +
    coefficientRefinementCount + weightedPacketCount + weightedRefinementCount +
    2 * rootCaseCount + 1
  IO.println s!"PASS {name}: {assertions} exact assertions ({coefficientCount} coefficients, {coefficientPacketCount} degree packets, {coefficientRefinementCount} degree refinements, {weightedPacketCount} weighted packets, {weightedRefinementCount} weighted refinements, {rootCaseCount} root cases checked twice, 2 controls)"
  IO.println s!"{name} coefficients 0..40: {oracle.toList}"
  return assertions

def checkPhiCylinders (oracle : Array Int) : IO Nat := do
  let periods : List positivePeriods.Period := [
    ⟨1, Nat.zero_lt_succ 0⟩, ⟨3, Nat.zero_lt_succ 2⟩, ⟨6, Nat.zero_lt_succ 5⟩]
  let mut count := 0
  for m in periods do
    for source in [(-4 : Int), -3, 0, 2, 8] do
      let point := intPoint positivePeriods source
      for d in List.range 17 do
        let expected := if (d : Int) % m.val = source % m.val then oracle[d]! else 0
        expect s!"φ cylinder m={m.val} source={source} degree={d}"
          ((phiCylinder m d point : Int) == expected)
        count := count + 1
  IO.println s!"PASS φ: {count} signed-source cylinder assertions"
  return count

/-- A primitive fourth root in F₅, observed at a period supplied by overlapping
anchors. The expected polynomial is computed in Int and reduced at the end. -/
def checkPhiFourthRoot (oracle : Array Int) : IO Nat := do
  let period := 3 * CoupledAnchors.resolution 3 [4, 6]
  let z : Fin 5 := 2
  expect "coupled period and fourth root" (period == 12 && z ^ 4 == 1 && z ^ 2 != 1)
  let mut count := 1
  for N in [0, 1, 4, 17] do
    let observed := sumBelow period (fun r => phiWeightedPacket (4 : Fin 5) N period r * z ^ r)
    let expected := (oraclePolynomial oracle N 8 % 5).toNat
    expect s!"φ fourth root N={N}" (observed.val == expected)
    count := count + 1
  IO.println s!"PASS φ: {count} fourth-root and coupled-period assertions in Fin 5"
  return count

/-- Test Watson's relation after multiplying by ∏(1+qʳ). Through degree D the
factors with r>D contribute only their constant term. -/
def checkWatson (D : Nat) : IO Nat := do
  let degrees := List.range (D + 1)
  let difference := (degrees.map fun d =>
    2 * (-1 : Int) ^ d * phiCoeff d - mockCoeff d).toArray
  let product := (List.range D).foldl (fun a j =>
    let r := j + 1
    (degrees.map (fun d => a[d]! + if r ≤ d then a[d-r]! else 0)).toArray) difference
  let mut count := 0
  for d in degrees do
    let expected : Int := match degrees.find? (fun k => k * k == d) with
      | some 0 => 1
      | some k => 2 * (-1 : Int) ^ k
      | none => 0
    expect s!"Watson f/φ relation d={d}" (product[d]! == expected)
    count := count + 1
  IO.println s!"PASS Watson relation: {count} coefficient assertions (degrees 0..{D})"
  return count

def run : IO Unit := do
  let fOracle := oracleCoefficients fFactor 41
  let fCount ← checkSeries "f" fOracle [1, 1, -2, 3, -3, 3, -5, 7, -6, 6, -10]
    mockCoeff mockPacket mockWeightedPacket mockPolynomial
  let phiOracle := oracleCoefficients phiFactor 41
  let phiCount ← checkSeries "φ" phiOracle [1, 1, 0, -1, 1, 1, -1, -1, 0, 2, 0, -2, 1, 1, -1, -2, 1]
    phiCoeff phiPacket phiWeightedPacket phiPolynomial
  let cylinders ← checkPhiCylinders phiOracle
  let fourthRoots ← checkPhiFourthRoot phiOracle
  let watson ← checkWatson 40
  IO.println s!"Total: {fCount + phiCount + cylinders + fourthRoots + watson} exact assertions."

end KElimination.MockThetaSmoke

#eval KElimination.MockThetaSmoke.run
