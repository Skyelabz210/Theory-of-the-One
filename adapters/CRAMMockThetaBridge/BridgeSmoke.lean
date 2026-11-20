import MockThetaAdapter

/-! Concrete instantiations of the bridge theorems and independent numerical
checks for the signed readout, transported target, and finite evaluations. -/

namespace CRAMMockThetaBridge.Smoke

open KElimination.ResidueSeries
open KElimination.MockTheta KElimination.MockThetaPhi
open KElimination.MockThetaPsi KElimination.MockThetaChi

abbrev F29 := Fin 29

private def characterSum (packet : F29 → Nat → Nat → Nat → F29) (N : Nat) : F29 :=
  sumBelow 42 (fun i => packet 3 N 42 i * (4 : F29) ^ i)

/- Each example consumes a named adapter theorem at the same signed source.
The period is 6·7 = 42 and the certified target is 14. -/
example (N : Nat) : characterSum mockWeightedPacket N = mockPolynomial N ((3 : F29) * 4) :=
  (mockTheta_from_nine65_adjacent (3 : F29) 4 N 6 14 (-1) 5 6
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).2

example (N : Nat) : characterSum phiWeightedPacket N = phiPolynomial N ((3 : F29) * 4) :=
  (phi_from_nine65_adjacent (3 : F29) 4 N 6 14 (-1) 5 6
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).2

example (N : Nat) : characterSum psiWeightedPacket N = psiPolynomial N ((3 : F29) * 4) :=
  (psi_from_nine65_adjacent (3 : F29) 4 N 6 14 (-1) 5 6
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).2

example (N : Nat) : characterSum chiWeightedPacket N = chiPolynomial N ((3 : F29) * 4) :=
  (chi_from_nine65_adjacent (3 : F29) 4 N 6 14 (-1) 5 6
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).2

example : KElimination.StarLift.positiveAdjacent 5 6 6 = (-1 : Int) / 6 % 7 :=
  (mockTheta_from_nine65_adjacent (3 : F29) 4 5 6 14 (-1) 5 6
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).1.quotient

example : KElimination.IntegerSpecialization.targetLaneProjection (5 % 14) (KElimination.StarLift.positiveAdjacent 5 6 6)
    (6 % 14) 14 = (-1 : Int) % 14 :=
  (mockTheta_from_nine65_adjacent (3 : F29) 4 5 6 14 (-1) 5 6
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).1.target

private def linearCoeff (n : Nat) : Int := (n : Int) + 1

/- A composite target with a non-adjacent unit anchor and inverse 2. -/
example : KElimination.IntegerSpecialization.targetLaneProjection (7 % 20) (KElimination.IntegerSpecialization.query 7 3 5 2)
    (8 % 20) 20 = (-17 : Int) % 20 :=
  (finite_evaluation_from_nine65_anchor linearCoeff (-2) (-1) 3 8 5 20 (-17) 7 3 2
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)).1.target

/- An anchor of modulus one exposes a single quotient class. A target dividing
the primary can still be read; its public inverse equation is 0 = 0 modulo 1. -/
example : KElimination.IntegerSpecialization.targetLaneProjection (5 % 3) (KElimination.IntegerSpecialization.query 5 0 1 0)
    (6 % 3) 3 = (-1 : Int) % 3 :=
  (readout_and_target 6 1 3 (-1) 5 0 0
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).target

private def numericChecks : List (String × Bool) := Id.run do
  let κ := KElimination.IntegerSpecialization.query 5 6 7 (-1)
  let wrongSign := KElimination.StarLift.negativeAdjacent 5 6 6
  let project := fun k => KElimination.IntegerSpecialization.targetLaneProjection 5 k 6 14
  -- The integer coefficient arrays through degree 4 are
  -- f: [1,1,-2,3,-3]; φ: [1,1,0,-1,1]; ψ: [0,1,1,1,2]; χ: [1,1,1,0,0].
  -- Evaluating each at 12 and reducing modulo 29 gives the four constants below.
  return [
    ("signed general-anchor readout", κ == 6),
    ("signed adjacent readout", KElimination.StarLift.positiveAdjacent 5 6 6 == 6),
    ("transported target", project κ == 13),
    ("reversed subtraction class", wrongSign == 1),
    ("reversed subtraction changes target", project wrongSign == 11),
    ("wrong inverse changes target", project (KElimination.IntegerSpecialization.query 5 6 7 2) == 3),
    ("stale anchor changes target", project (KElimination.IntegerSpecialization.query 5 0 7 (-1)) == 7),
    ("aliased primary readings", (-1 : Int) % 6 == 41 % 6),
    ("aliased anchor readings", (-1 : Int) % 7 == 41 % 7),
    ("target 5 fails divisibility", 42 % 5 != 0),
    ("target 5 distinguishes aliased sources", (-1 : Int) % 5 == 4 && (41 : Int) % 5 == 1),
    ("inverse at non-adjacent anchor", KElimination.IntegerSpecialization.query 7 3 5 2 == 2),
    ("non-adjacent target", KElimination.IntegerSpecialization.targetLaneProjection 7 (KElimination.IntegerSpecialization.query 7 3 5 2) 8 20 == 3),
    ("non-adjacent finite transform", sumBelow 40 (fun i =>
      weightedPacket linearCoeff (fun d => (-2 : Int)^d) 3 40 i * (-1 : Int)^i) == 17),
    ("anchor modulus one", KElimination.IntegerSpecialization.query 5 0 1 0 == 0),
    ("target modulus one", KElimination.IntegerSpecialization.targetLaneProjection 0 κ 0 1 == 0),
    ("root has order 14", (4 : F29)^14 == 1 && (4 : F29)^7 != 1 && (4 : F29)^2 != 1),
    ("f degree truncation", characterSum mockWeightedPacket 5 == 5),
    ("phi degree truncation", characterSum phiWeightedPacket 5 == 26),
    ("psi degree truncation", characterSum psiWeightedPacket 5 == 1),
    ("chi degree truncation", characterSum chiWeightedPacket 5 == 12),
    ("empty coefficient truncation", characterSum mockWeightedPacket 0 == 0),
    ("wrapped degree packets", sumBelow 2 (fun i =>
      mockWeightedPacket (2 : Int) 5 2 i * (-1 : Int)^i) == -81),
    ("uncertified root changes evaluation", sumBelow 2 (fun i =>
      weightedPacket (fun _ => (1 : Int)) (fun _ => 1) 4 2 i * (2 : Int)^i) == 6 &&
      (1 + 2 + 2^2 + 2^3 : Int) == 15 && (2 : Int)^2 != 1)]

def run : IO Unit := do
  let mut count := 0
  for (label, ok) in numericChecks do
    unless ok do throw (IO.userError s!"bridge smoke failed: {label}")
    count := count + 1
    IO.println s!"PASS {label}"
  IO.println s!"PASS bridge smoke: {count} exact assertions"

end CRAMMockThetaBridge.Smoke

#eval CRAMMockThetaBridge.Smoke.run
