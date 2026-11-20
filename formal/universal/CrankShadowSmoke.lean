import CrankCharacter11
import CrankShadow11

/-! Finite rank, crank, character and shadow-coordinate checks over Int and Fin 23.
The independent crank-count oracle counts part multiplicities by dynamic programming.
Its inputs are sizes and residues; it never lists partitions or calls the crank statistic.
-/

namespace KElimination.CrankShadowSmoke

open PartitionCrank11 CrankShadow11 CrankCharacter11 ProfiniteObservations

def expect (label : String) (ok : Bool) : IO Unit :=
  unless ok do throw (IO.userError label)

/-- Fill the crank bins without enumerating partitions. Parts without ones
are grouped by their exact maximum. With k ones, each further part exceeding
k increases the crank by one, starting from −k. -/
def oracleCrankBins (size : Nat) : Array Nat := Id.run do
  let mut bins := Array.replicate 11 0
  if size = 0 then
    return bins.set! 0 1
  let mut ways := (Array.replicate (size + 1) 0).set! 0 1
  for part in [2:size+1] do
    for d in [part:size+1] do
      ways := ways.set! d (ways[d]! + ways[d-part]!)
    -- Reserve one occurrence of the maximum part; all other parts are ≤ part.
    let r := part % 11
    bins := bins.set! r (bins[r]! + ways[size-part]!)
  for ones in [1:size+1] do
    let rest := size - ones
    let start := (11 - ones % 11) % 11
    let mut table := (Array.replicate ((rest+1)*11) 0).set! start 1
    for part in [2:rest+1] do
      let increment := if ones < part then 1 else 0
      for d in [part:rest+1] do
        for r in [0:11] do
          let i := 11*d + r
          let previous := 11*(d-part) + ((r + 11 - increment) % 11)
          table := table.set! i (table[i]! + table[previous]!)
    for r in [0:11] do
      bins := bins.set! r (bins[r]! + table[rest*11+r]!)
  return bins

def checkRankParity : IO Nat := do
  let mut count := 0
  expect "rank of the empty partition" (rank [] == 0)
  expect "ordinary crank of the single one" (crank [1] == -1)
  count := count + 2
  for size in [0:41] do
    let difference := (partitions size).foldl (fun (acc : Int) p =>
      if rank p % 2 = 0 then acc + 1 else acc - 1) 0
    expect s!"even ranks minus odd ranks at size {size}" (difference == MockTheta.mockCoeff size)
    count := count + 1
  IO.println s!"Rank parity and third-order f: {count} assertions (degrees 0..40)"
  return count

def checkCrankBins : IO Nat := do
  let mut count := 0
  let cases : List (Nat × Nat) := [(6,1), (17,27), (28,338), (39,2835)]
  for (size, expectedPerBin) in cases do
    let oracle := oracleCrankBins size
    let observed := (histogram11 crank size).toArray
    for r in [0:11] do
      expect s!"partition crank count, size={size}, residue={r}" (observed[r]! == oracle[r]!)
      expect s!"explicit crank count, size={size}, residue={r}" (oracle[r]! == expectedPerBin)
      count := count + 2
    IO.println s!"Crank at size {size}: {observed.toList}"
  return count

def checkCharacters : IO Nat := do
  let z : Fin 23 := 2
  let ps := partitions 6
  let ranks := (histogram11 rank 6).toArray
  let cranks := (histogram11 crank 6).toArray
  let expectedRanks := #[1,2,1,1,0,1,1,0,1,1,2]
  let expectedFourier := #[11,8,22,20,2,17,17,2,20,22,8]
  expect "exact rank bins of six" (ranks == expectedRanks)
  expect "2^11 in the field of 23 elements" (z^11 == 1)
  let mut count := 2
  for j in [0:11] do
    let zj := z^j
    if j > 0 then
      expect s!"no smaller positive exponent, j={j}" (zj != 1)
      count := count + 1
    let rankPair := samplePair rank zj ps
    let crankPair := samplePair crank zj ps
    expect s!"direct rank character {j}" (rankPair.val == expectedFourier[j]!)
    expect s!"rank histogram character {j}" (histPair (fun r => ranks[r]!) zj == rankPair)
    let expectedCrank := if j = 0 then 11 else 0
    expect s!"direct crank character {j}" (crankPair.val == expectedCrank)
    expect s!"crank histogram character {j}" (histPair (fun r => cranks[r]!) zj == crankPair)
    count := count + 4
  -- Every partition above has size 6. Giving each term z^6 instead of its
  -- statistic character changes the answer from zero to 14 in this field.
  let sizeCharacter := (Fin.ofNat 23 ps.length) * z^6
  expect "size and crank are different character arguments at size six"
    (sizeCharacter.val == 14 && sizeCharacter != samplePair crank z ps)
  return count + 1

def checkShadowCoordinates : IO Nat := do
  let mut count := 0
  let direct : positivePeriods.Period := ⟨11, Nat.zero_lt_succ 10⟩
  for stat in [(-23 : Int), -11, -1, 0, 1, 11, 23] do
    let expected := (stat % 11).toNat
    expect s!"direct statistic coordinate {stat}"
      ((intPoint positivePeriods stat).residue direct == expected)
    expect s!"S6 statistic projection {stat}"
      ((intPoint selectedPrimaryPowers stat).residue s6Period % 11 == expected)
    count := count + 2
    for before in [(-15 : Int), 0, 22] do
      let after := before + splitPayload * stat
      let result := s8Readout (before % 11) (after % 11)
      expect s!"S8 increment from its paired shadows ({before}, {stat})" (result == stat % 11)
      count := count + 1
  -- The positive inverse is seven. At increment one, inverse one returns
  -- eight, and swapping the authentic predecessor/successor gives ten.
  let chart : Int := (-15) % 11
  let shadow := (-15 + splitPayload) % 11
  let wrongInverse := IntegerSpecialization.query chart shadow 11 1
  expect "wrong public inverse changes the observed increment"
    (wrongInverse != s8Readout chart shadow && (1 * splitPayload) % 11 != 1)
  expect "swapping the two shadow readings reverses the increment"
    (s8Readout shadow chart == 10 && s8Readout chart shadow == 1)
  count := count + 2
  for source in [(-2*splitPayload-1), -1, 0, splitPayload+4] do
    let alias := source + splitPayload * 11
    let qread := s8Readout ((source % splitPayload) % 11) (source % 11)
    expect s!"S8 quotient class at {source}" (qread == (source / splitPayload) % 11)
    expect s!"S8 readout alias at {source}" (source % splitPayload == alias % splitPayload &&
      source % 11 == alias % 11 && alias / splitPayload == source / splitPayload + 11)
    count := count + 2
  return count

/-- Compare the seventh-order crank-weighted transform with the formal
ℱ₂ prefix and a size-by-residue dynamic program, all arithmetic exact. -/
def checkSeventhCharacter : IO Nat := do
  let t : Fin 23 := 3
  let z : Fin 23 := 2
  let coefficients : Array Nat := #[1,1,2,1,2,2,3,2]
  let mut expected := Array.replicate 11 0
  for d in [0:coefficients.size] do
    let bins := oracleCrankBins d
    for r in [0:11] do
      expected := expected.set! r (expected[r]! + coefficients[d]! * 3^d * bins[r]!)
  let weight := fun d => (MockThetaSeventh.f2Coeff d : Fin 23) * t^d
  let mut count := 0
  for r in [0:11] do
    let actual := weightedClass weight coefficients.size r crank
    expect s!"ℱ₂ crank-weighted class {r}" (actual.val == expected[r]! % 23)
    count := count + 1
  let observed := ResidueSeries.sumBelow 11 (fun r => weightedClass weight coefficients.size r crank * z^r)
  let direct := ResidueSeries.sumBelow coefficients.size (fun d => weight d * samplePair crank z (partitions d))
  let observedClass := fun (p : List Nat) =>
    let before := (p.length : Int) - 5
    let after := before + splitPayload * crank p
    (s8Readout (before % 11) (after % 11)).toNat
  let pairedShadows := ResidueSeries.sumBelow coefficients.size (fun d =>
    weight d * classPair observedClass z (partitions d))
  let integerPair := (List.range 11).foldl (fun acc r => acc + expected[r]! * 2^r) 0
  expect "ℱ₂ weighted crank character paired by residue" (observed.val == integerPair % 23)
  expect "ℱ₂ weighted crank character paired by size" (direct.val == integerPair % 23)
  expect "ℱ₂ character from paired S8 shadow readings" (pairedShadows.val == integerPair % 23)
  IO.println s!"ℱ₂ at weight t=3, crank root 2 in Fin 23, degrees 0..7: {observed.val}"
  return count + 3

def run : IO Unit := do
  let parity ← checkRankParity
  let bins ← checkCrankBins
  let fourier ← checkCharacters
  let shadow ← checkShadowCoordinates
  let weighted ← checkSeventhCharacter
  IO.println s!"Rank/crank Fourier: {fourier}; crank histograms: {bins}; S6/S8 coordinates: {shadow}; seventh-order weighted character: {weighted}."
  IO.println s!"Total: {parity + bins + fourier + shadow + weighted} exact assertions."

end KElimination.CrankShadowSmoke

#eval KElimination.CrankShadowSmoke.run
