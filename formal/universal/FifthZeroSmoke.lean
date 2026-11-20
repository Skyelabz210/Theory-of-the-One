import FifthOrderSmokeCommon
import MockThetaFifthZero

/-! The five index-zero functions from Ramanujan's last letter, p. 4.
The alternative expansion in braces for χ₀ provides an oracle with different
summands from the formal definition. All cross-function comparisons are finite. -/

namespace KElimination.FifthZeroSmoke

open FifthOrderSmokeCommon FifthOrderSeries MockThetaFifthZero

def coefficients (family : Family) (N : Nat) : Array Int :=
  match family with
  | .f => oracle N (fun n => n*n) consecutive .invOnePlus
  | .phi => oracle N (fun n => n*n) oddSteps .onePlus
  | .psi => oracle N (fun n => triangle (n+1)) consecutive .onePlus
  | .chi =>
    -- The n=0 term is 1. At n≥1 the term is q^(2n-1) / ∏_{j=n}^{2n-1}(1-qʲ).
    oracle N (fun n => 2*n-1) (fun n => (List.range n).map (fun j => n+j)) .invOneMinus
  | .bigF => oracle N (fun n => 2*n*n) oddSteps .invOneMinus

def run : IO Unit := do
  let mut count := 0
  let cases : List (Family × String × List Int) := [
    (.f, "f₀", [1, 1, -1, 1, 0, 0, -1, 1, 0, 1, -2, 1]),
    (.phi, "φ₀", [1, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 0]),
    (.psi, "ψ₀", [0, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1]),
    (.chi, "χ₀", [1, 1, 1, 2, 1, 3, 2, 3, 3, 5, 3, 6]),
    (.bigF, "F₀", [1, 0, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3])]
  for (family, name, known) in cases do
    let n ← checkSeries name (coefficients family 41) known (coeff family)
      (degreePacket family) (weightedPacket family) (polynomial family) (cylinder family)
    count := count + n
  let mut relations := 0
  for d in List.range 41 do
    let sign : Int := (-1)^d
    let f : Int := fCoeff d
    let phi := (phiCoeff d : Int)
    expect s!"φ₀(−q)+χ₀=2F₀, degree {d}" (sign*phi + chiCoeff d == 2 * bigFCoeff d)
    let Fq2 := if d % 2 = 0 then (bigFCoeff (d/2) : Int) else 0
    let phiNegQ2 := if d % 2 = 0 then (-1 : Int)^(d/2) * phiCoeff (d/2) else 0
    let middle := phiNegQ2 + sign * psiCoeff d
    let left := sign*f + 2*Fq2 - (if d = 0 then 2 else 0)
    expect s!"f₀(−q)+2F₀(q²)−2=φ₀(−q²)+ψ₀(−q), degree {d}" (left == middle)
    expect s!"φ₀(−q²)+ψ₀(−q)=2φ₀(−q²)−f₀(q), degree {d}" (middle == 2*phiNegQ2 - f)
    relations := relations + 3
  IO.println s!"PASS index-zero source identities: {relations} assertions (degrees 0..40 each)"
  IO.println s!"Total: {count + relations} exact assertions."

end KElimination.FifthZeroSmoke

#eval KElimination.FifthZeroSmoke.run
