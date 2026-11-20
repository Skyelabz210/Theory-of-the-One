import FifthOrderSmokeCommon
import MockThetaFifthOne

/-! Exact coefficient and observation checks for the five index-one functions.
Both χ₁ and F₁ start with the geometric series 1/(1-q) at summand index zero.
Their coefficientwise identity includes a one-degree shift. -/

namespace KElimination.FifthOneSmoke

open FifthOrderSmokeCommon FifthOrderSeries MockThetaFifthOne

def coefficients (family : Family) (N : Nat) : Array Int :=
  match family with
  | .f => oracle N (fun n => n*(n+1)) consecutive .invOnePlus
  | .phi => oracle N (fun n => (n+1)^2) oddSteps .onePlus
  | .psi => oracle N triangle consecutive .onePlus
  | .chi => oracle N id (fun n => (List.range (n+1)).map (fun j => n+1+j)) .invOneMinus
  | .bigF => oracle N (fun n => 2*n*(n+1)) (fun n => oddSteps (n+1)) .invOneMinus

def run : IO Unit := do
  let mut count := 0
  let cases : List (Family × String × List Int) := [
    (.f, "f₁", [1, 0, 1, -1, 1, -1, 2, -2, 1, -1, 2, -2]),
    (.phi, "φ₁", [0, 1, 0, 0, 1, 1, 0, 0, 0, 1, 1, 0]),
    (.psi, "ψ₁", [1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 2, 2]),
    (.chi, "χ₁", [1, 2, 2, 3, 3, 4, 4, 6, 5, 7, 8, 9]),
    (.bigF, "F₁", [1, 1, 1, 1, 2, 2, 2, 3, 3, 3, 4, 4])]
  for (family, name, known) in cases do
    let n ← checkSeries name (coefficients family 41) known (coeff family)
      (degreePacket family) (weightedPacket family) (polynomial family) (cylinder family)
    count := count + n
  let mut special := 0
  for d in List.range 41 do
    expect s!"χ₁ summand zero, degree {d}" ((summand .chi 0 d : Int) == 1)
    expect s!"F₁ summand zero, degree {d}" ((summand .bigF 0 d : Int) == 1)
    special := special + 2
  IO.println s!"PASS index-one geometric initial summands: {special} assertions (degrees 0..40 each)"
  let phiOracle := coefficients .phi 42
  expect "φ₁ coefficient 41 for the shifted identity" ((phiCoeff 41 : Int) == phiOracle[41]!)
  let mut relations := 0
  for d in List.range 42 do
    let qChi := if d = 0 then 0 else (chiCoeff (d-1) : Int)
    let qF := if d = 0 then 0 else (bigFCoeff (d-1) : Int)
    expect s!"qχ₁=2qF₁+φ₁(−q), degree {d}" (qChi == 2*qF + (-1 : Int)^d * phiCoeff d)
    relations := relations + 1
  IO.println s!"PASS shifted identity: {relations} assertions (degrees 0..41), plus independent φ₁[41]={phiOracle[41]!}"
  IO.println s!"Total: {count + special + 1 + relations} exact assertions."

end KElimination.FifthOneSmoke

#eval KElimination.FifthOneSmoke.run
