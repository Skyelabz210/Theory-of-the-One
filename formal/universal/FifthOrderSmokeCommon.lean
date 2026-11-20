import CoefficientObservations

/-! Independent finite polynomial calculations and executable observation
checks shared by the two groups of fifth-order functions. -/

namespace KElimination.FifthOrderSmokeCommon

open KElimination.ResidueSeries KElimination.ProfiniteObservations

def expect (label : String) (ok : Bool) : IO Unit :=
  unless ok do throw (IO.userError label)

/-- Three ordinary polynomial factors, written using x=qʲ. -/
inductive Factor where
  | onePlus        -- 1+x
  | invOnePlus     -- 1-x+x²-x³+…
  | invOneMinus    -- 1+x+x²+x³+…

def factorCoeff (factor : Factor) (j d : Nat) : Int :=
  match factor with
  | .onePlus => if d = 0 ∨ d = j then 1 else 0
  | .invOnePlus => if d % j = 0 then (-1)^ (d / j) else 0
  | .invOneMinus => if d % j = 0 then 1 else 0

/-- Ordinary truncated multiplication by the explicit factor at stride j>0. -/
def multiplyFactor (a : Array Int) (factor : Factor) (j : Nat) : Array Int :=
  ((List.range a.size).map fun d =>
    (List.range (d + 1)).foldl (fun s k => s + a[d-k]! * factorCoeff factor j k) 0).toArray

/-- Every caller's exponent is at least n. Terms with a shift ≥N cannot
contribute to the N retained degrees. The oracle uses coefficient arrays and
does not use the formal summand, formal division, or formal product code. -/
def oracle (N : Nat) (exponent : Nat → Nat) (steps : Nat → List Nat)
    (factor : Factor) : Array Int := Id.run do
  let mut out := Array.replicate N (0 : Int)
  for n in List.range N do
    let e := exponent n
    if e < N then
      let one := (Array.replicate (N-e) (0 : Int)).set! 0 1
      let product := (steps n).foldl (fun a j => multiplyFactor a factor j) one
      for d in List.range product.size do
        out := out.set! (e+d) (out[e+d]! + product[d]!)
  return out

def consecutive (n : Nat) : List Nat := (List.range n).map (· + 1)
def oddSteps (n : Nat) : List Nat := (List.range n).map (fun k => 2*k + 1)
def triangle (n : Nat) : Nat := n*(n+1)/2

def oracleValue (a : Array Int) (N : Nat) (q : Int) : Int :=
  (List.range N).foldl (fun acc d => acc + a[d]! * q^d) 0

def oracleWeighted (a : Array Int) (N M r : Nat) (t : Int) : Int :=
  (List.range N).foldl (fun acc d => acc + if d % M = r then a[d]! * t^d else 0) 0

/-- Compare all coefficient and observation entry points for one named series.
The source-prefix check independently fixes the shifts and constant term. -/
def checkSeries (name : String) (a : Array Int) (known : List Int)
    (coeff : Nat → Int) (degreePacket : Nat → Nat → Nat → Int)
    (weighted : {R : Type} → [Lean.Grind.CommRing R] → R → Nat → Nat → Nat → R)
    (polynomial : Nat → Int → Int)
    (cylinder : positivePeriods.Period → Nat → ResiduePoint positivePeriods → Int) :
    IO Nat := do
  expect s!"{name} coefficient prefix" (a.toList.take known.length == known)
  let mut count := 1
  for d in List.range a.size do
    expect s!"{name} coefficient {d}" (coeff d == a[d]!)
    count := count + 1
  for M in [1, 3, 6] do
    for d in List.range 13 do
      for r in List.range (M+1) do
        let expected := if d % M = r then a[d]! else 0
        expect s!"{name} packet M={M} r={r} d={d}" (degreePacket M r d == expected)
        count := count + 1
  let period : positivePeriods.Period := ⟨6, Nat.zero_lt_succ 5⟩
  for source in [(-4 : Int), 0, 2, 3, 8] do
    for d in List.range 13 do
      let expected := if (d : Int) % 6 = source % 6 then a[d]! else 0
      expect s!"{name} cylinder source={source} d={d}"
        (cylinder period d (intPoint positivePeriods source) == expected)
      count := count + 1
  for N in [0, 1, 7, 13] do
    for t in [(-2 : Int), 0, 1] do
      for r in List.range 3 do
        let coarse := weighted t N 3 r
        let fine := weighted t N 6 r + weighted t N 6 (r+3)
        expect s!"{name} weighted N={N} t={t} r={r}" (coarse == oracleWeighted a N 3 r t)
        expect s!"{name} refinement 6→3 N={N} t={t} r={r}" (fine == coarse)
        count := count + 2
      for z in [(-1 : Int), 1] do
        let observed := sumBelow 6 (fun r => weighted t N 6 r * z^r)
        let expected := oracleValue a N (t*z)
        expect s!"{name} root N={N} t={t} z={z}" (observed == expected)
        expect s!"{name} polynomial N={N} t={t} z={z}" (polynomial N (t*z) == expected)
        count := count + 2

  -- The same resolution admits b=4 and rejects b=5. The primitive fourth
  -- root 2 in F₅ exercises a character unavailable over the integers.
  let H := CoupledAnchors.resolution 3 [4, 6]
  let L := 3 * H
  let z : Fin 5 := 2
  expect s!"{name} coupled admission" (H == 4 && L == 12 &&
    decide (reducedTargetPeriod 3 4 ∣ H) && !(decide (reducedTargetPeriod 3 5 ∣ H)))
  expect s!"{name} primitive fourth root" (z^4 == 1 && z^2 != 1)
  count := count + 2
  for N in [0, 1, 4, 17] do
    let observed := sumBelow L (fun r => weighted (4 : Fin 5) N L r * z ^ r)
    let expected := (oracleValue a N 8 % 5).toNat
    expect s!"{name} order-four transform N={N}" (observed.val == expected)
    count := count + 1
  IO.println s!"PASS {name}: {count} assertions, coefficients 0..{a.size-1}: {a.toList}"
  return count

end KElimination.FifthOrderSmokeCommon
