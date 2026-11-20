import MockThetaShadow
import PartitionCrank11

/-! Exact checks of the Laurent exponents of Q⁻¹f(Q²⁴) and the signed
unary series ∑_{k ≡ 1 (mod 6)} k Q^(k²). The first oracle enumerates integer
partitions and weights each by its Dyson rank parity. The second traverses
the bilateral lattice k=6n+1 directly. All evaluations are finite. -/

namespace KElimination.MockThetaShadowSmoke

open MockThetaShadow PartitionCrank11
open KElimination.ResidueSeries (sumBelow packet weightedPacket)

def expect (label : String) (ok : Bool) : IO Unit :=
  unless ok do throw (IO.userError label)

def rankDifference (n : Nat) : Int :=
  (partitions n).foldl (fun acc p =>
    if rank p % 2 = 0 then acc + 1 else acc - 1) 0

def checkHolomorphic : IO Nat := do
  let a := ((List.range 41).map rankDifference).toArray
  let mut count := 0
  -- Scan every integer exponent from −25 through 982, including all gaps
  -- after the last tested source coefficient, a₄₀ at exponent 959.
  let laurent := (List.range a.size).foldl (fun table n =>
    table.set! (24*n + 24) a[n]!) (Array.replicate 1008 (0 : Int))
  for i in List.range laurent.size do
    let e : Int := (i : Int) - 25
    expect s!"Laurent coefficient {e}" ((holomorphicCoeff e : Int) == laurent[i]!)
    count := count + 1
  for n in List.range a.size do
    expect s!"exponent at degree {n}" (normalizedExponent n == 24*(n : Int)-1)
    count := count + 1

  -- All pairs are certified units in F₁₀₁. Compute the comparison in Int,
  -- evaluating the independently counted f polynomial at Q²⁴, then reduce.
  let units : List (Nat × Nat) := [(1,1),(2,51),(3,34),(7,29),(100,100)]
  for (x, v) in units do
    let u := Fin.ofNat 101 x
    let inv := Fin.ofNat 101 v
    expect s!"unit Q={x}" (u * inv == 1)
    count := count + 1
    for N in [0, 1, 2, 7, 17, 41] do
      let ref := (List.range N).foldl (fun total n =>
        total + a[n]! * (x : Int)^(24*n)) 0
      let expected := ((v : Int) * ref % 101).toNat
      expect s!"normalized truncation N={N} Q={x}" ((normalizedTrunc N u inv).val == expected)
      count := count + 1

  -- With N=7 and Q=2 the pole and the 24-fold dilation are distinguished:
  -- omitting the pole gives 2, and retaining only the pole with argument Q gives 25.
  let normalized := normalizedTrunc 7 (2 : Fin 101) 51
  let ordinary := (List.range 7).foldl (fun total n => total + a[n]! * 2^n) 0
  expect "pole shift and dilation" (normalized.val == 1 && (2*normalized).val == 2 &&
    ((51 * ordinary) % 101 == 25) && normalized.val != 25)
  IO.println s!"PASS Laurent exponents, rank-parity comparison and unit evaluations: {count+1} assertions"
  return count + 1

/-- This window of lattice indices covers every square below 626. The
omitted indices have absolute value at least 8, hence |6n+1|≥47. -/
def lattice : List Int :=
  (List.range 15).map (fun (i : Nat) => 6*((i : Int)-7) + 1)

def square (k : Int) : Nat := (k*k).toNat

def oracleCoeff (d : Nat) : Int :=
  lattice.foldl (fun total k => if square k = d then total+k else total) 0

def oracleBin (N r : Nat) : Int :=
  lattice.foldl (fun total k =>
    if square k < N ∧ square k % 11 = r then total+k else total) 0

def checkShadow : IO Nat := do
  let mut count := 0
  for d in List.range 626 do
    let expected := oracleCoeff d
    expect s!"primitive unary coefficient d={d}" (shadowCoeff d == expected)
    count := count + 1
    for r in List.range 12 do
      let a := packet shadowCoeff 11 r d
      let b := if d % 11 = r then expected else 0
      expect s!"unary packet d={d}, r={r}" (a == b)
      count := count + 1
  for m in List.range 26 do
    let expected := lattice.foldl (fun s k => if k.natAbs = m then s+k else s) 0
    expect s!"primitive signed weight at |k|={m}" (shadowWeight m == expected)
    count := count + 1
  for (d, scaled) in ([(1,4),(25,-20),(49,28),(121,-44),(169,52)] : List (Nat × Int)) do
    expect s!"published ξ coefficient at degree {d}" (4 * shadowCoeff d == scaled)
    count := count + 1
  IO.println s!"PASS signed lattice coefficients, degree packets, weights and ξ scaling: {count} assertions"
  return count

def checkPairings : IO Nat := do
  let z : Fin 23 := 2
  expect "primitive modulo-11 character in F₂₃" (z^11 == 1 && z != 1)
  let mut count := 1
  for N in [0,1,2,25,26,49,50,121,122,289,290,625,626] do
    let bins := ((List.range 11).map (fun r => weightedPacket shadowCoeff (fun _ => 1) N 11 r)).toArray
    for r in List.range 11 do
      expect s!"signed unary packet N={N} r={r}" (bins[r]! == oracleBin N r)
      count := count + 1
    for j in [0,1,2,10] do
      let zj := z^j
      let observed := sumBelow 11 (fun r => Fin.ofNat 23 (bins[r]! % 23).toNat * zj^r)
      let expected := lattice.foldl (fun total k =>
        if square k < N then total + Fin.ofNat 23 (k % 23).toNat * zj^(square k) else total) 0
      expect s!"unary character N={N} j={j}" (observed == expected)
      expect s!"unary truncation N={N} j={j}" (shadowTrunc N zj == expected)
      count := count + 2
  -- k=−5 contributes −5 at exponent 25, hence class 3. Replacing its
  -- signed amplitude by |k| or observing k mod 11 changes this distribution.
  let negativeBin := weightedPacket shadowCoeff (fun _ => 1) 26 11 3
  let wrongClass := ((-5 : Int) % 11).toNat
  expect "signed amplitude and square-exponent class" (negativeBin == -5 && negativeBin != 5 &&
    wrongClass == 6 && weightedPacket shadowCoeff (fun _ => 1) 26 11 wrongClass == 0)
  -- At k=−11 the exponent class is zero. Reducing the coefficient itself
  -- modulo 11 would lose the nonzero packet mass −11.
  expect "degree class zero retains signed mass" (packet shadowCoeff 11 0 121 == -11 &&
    shadowCoeff 121 % 11 == 0)
  IO.println s!"PASS finite unary mass and eleven-fold character pairings: {count+2} assertions"
  return count + 2

def run : IO Unit := do
  let hol ← checkHolomorphic
  let theta ← checkShadow
  let paired ← checkPairings
  IO.println s!"Total: {hol + theta + paired} exact assertions."

end KElimination.MockThetaShadowSmoke

#eval KElimination.MockThetaShadowSmoke.run
