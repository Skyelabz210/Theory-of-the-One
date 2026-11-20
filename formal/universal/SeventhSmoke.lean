import MockThetaSeventh
import FifthOrderSmokeCommon

/-! Finite checks of Ramanujan's three seventh-order functions. The coefficient
oracle multiplies geometric polynomials independently of the formal division
recurrence. The first omitted summand is tested both below its support and at
its leading degree. A separate finite check uses Garvan, "New Fifth and
Seventh Order Mock Theta Function Identities", equations (1.6)–(1.8). -/

namespace KElimination.SeventhSmoke

open FifthOrderSmokeCommon MockThetaSeventh
open KElimination.ResidueSeries (sumBelow)

/-- Leading exponents with the first actual summand numbered zero in each case. -/
def sourceShift (family : Family) (n : Nat) : Nat :=
  match family with
  | .f0 => n*n
  | .f1 => (n+1)^2
  | .f2 => n*(n+1)

def coefficients (family : Family) (N : Nat) : Array Int :=
  let strides := fun n =>
    let length := match family with
      | .f0 => n
      | .f1 | .f2 => n+1
    (List.range length).map (fun j => n+1+j)
  oracle N (sourceShift family) strides .invOneMinus

/-- The empty product gives the constant 1 for ℱ₀. The other first summands
are q/(1−q) and 1/(1−q), so their tails affect every positive degree. -/
def checkCutoffs (name : String) (family : Family) (a : Array Int) : IO Nat := do
  let mut count := 0
  for d in List.range a.size do
    let initial : Int := match family with
      | .f0 => if d = 0 then 1 else 0
      | .f1 => if d = 0 then 0 else 1
      | .f2 => 1
    expect s!"{name} initial summand at {d}" ((summand family 0 d : Int) == initial)
    count := count + 1
  for N in List.range 8 do
    let e := sourceShift family N
    for d in List.range a.size do
      if d ≤ e then
        let retained := sumBelow N (fun n => (summand family n d : Int))
        -- At equality precisely the leading 1 of summand N is missing.
        let missing := if d = e then 1 else 0
        expect s!"{name} summand cutoff N={N}, degree={d}, leading shift={e}"
          (a[d]! - retained == missing)
        count := count + 1
  IO.println s!"PASS {name} initial summand and cutoff boundaries: {count} assertions"
  return count

/-- Multiply by (q;q)∞ through degree D. Its factors with stride greater
than D contribute only the constant term to this truncated polynomial. -/
def eulerProduct (a : Nat → Int) (D : Nat) : Array Int :=
  let degrees := List.range (D+1)
  (List.range D).foldl (fun old j =>
    let r := j+1
    (degrees.map (fun d => old[d]! - if r ≤ d then old[d-r]! else 0)).toArray)
    (degrees.map a).toArray

def checkGarvan : IO Nat := do
  let b0 := eulerProduct f0Coeff 108
  let b1 := eulerProduct f1Coeff 101
  let b2 := eulerProduct f2Coeff 97
  let mut count := 0
  for n in List.range 5 do
    expect s!"Garvan (1.6) n={n}" (b0[25*n+8]! == b2[n]!)
    expect s!"Garvan (1.7) n={n}" (b1[25*n+1]! == b0[n]!)
    count := count + 2
    if n > 0 then
      expect s!"Garvan (1.8) n={n}" (b2[25*n-3]! == -b1[n]!)
      count := count + 1
  IO.println s!"PASS Garvan Euler-product identities: {count} assertions (largest degree 108)"
  return count

def run : IO Unit := do
  let cases : List (Family × String × List Int) := [
    (.f0, "ℱ₀", [1, 1, 0, 1, 1, 1, 0, 2, 1, 2, 1, 2, 1]),
    (.f1, "ℱ₁", [0, 1, 1, 1, 2, 1, 2, 2, 2, 3, 3, 2, 4]),
    (.f2, "ℱ₂", [1, 1, 2, 1, 2, 2, 3, 2, 3, 3, 4, 4, 5])]
  let mut count := 0
  for (family, name, known) in cases do
    let a := coefficients family 41
    let common ← checkSeries name a known (coeff family) (degreePacket family)
      (weightedPacket family) (polynomial family) (cylinder family)
    let boundaries ← checkCutoffs name family a
    count := count + common + boundaries
  let products ← checkGarvan
  IO.println s!"Total: {count + products} exact assertions."

end KElimination.SeventhSmoke

#eval KElimination.SeventhSmoke.run
