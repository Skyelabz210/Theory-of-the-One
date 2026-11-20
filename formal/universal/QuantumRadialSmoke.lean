import QuantumRadial
import MockTheta

/-! Exact checks of the finite right-hand side of the radial-limit formula.
Integer polynomial expansion and monic long division compute a representative
at each primitive complex order. Evaluations in F₁₃₂₁ compare those polynomials
with the actual ring-valued construction at every primitive root of each order. -/

namespace KElimination.QuantumRadialSmoke

open QuantumRadial
open ResidueSeries (sumBelow)
open ProfiniteObservations (reducedTargetPeriod)

def expect (label : String) (ok : Bool) : IO Unit :=
  unless ok do throw (IO.userError label)

/-- The ordinary coefficient array of ∏_{j=1}ⁿ(1+Xʲ)². -/
def productPoly (n : Nat) : Array Int :=
  (List.range n).foldl (fun a i =>
    let j := i+1
    ((List.range (a.size + 2*j)).map fun d =>
      a[d]?.getD 0 + (if j ≤ d then 2 * a[d-j]?.getD 0 else 0) +
        (if 2*j ≤ d then a[d-2*j]?.getD 0 else 0)).toArray) #[1]

/-- Integer coefficients before specializing X to any particular root. -/
def endpointPoly (k : Nat) : Array Int := Id.run do
  let mut a := Array.replicate (k*k+1) (0 : Int)
  for n in List.range k do
    let product := productPoly n
    for j in List.range product.size do
      let d := n+1+j
      a := a.set! d (a[d]! - 4 * product[j]!)
  return a

/-- Long division from the highest degree down by a supplied monic Φ. -/
def monicRemainder (a phi : Array Int) : Array Int := Id.run do
  let degree := phi.size-1
  let mut work := a
  for i in List.range (a.size-degree) do
    let e := a.size-1-i
    let lead := work[e]!
    for j in List.range degree do
      let d := e-degree+j
      work := work.set! d (work[d]! - lead * phi[j]!)
  return ((List.range degree).map (fun j => work[j]?.getD 0)).toArray

/-- Horner evaluation after reducing the signed integer coefficients. -/
def evalPoly (a : Array Int) (q : Fin 1321) : Fin 1321 :=
  a.foldr (fun c acc => acc*q + Fin.ofNat 1321 (c % 1321).toNat) 0

structure RootCase where
  order : Nat
  root : Fin 1321
  cyclotomic : Array Int
  expected : Array Int

/-- The listed roots are powers of 13 in F₁₃₂₁. The order checks below
verify each one and also check every conjugate used in the tests. -/
def cases : List RootCase := [
  ⟨2, 1320, #[1,1], #[4]⟩,
  ⟨4, 257, #[1,0,1], #[0,4]⟩,
  ⟨6, 298, #[1,-1,1], #[0,-4]⟩,
  ⟨8, 371, #[1,0,0,0,1], #[4,4,-4,0]⟩,
  ⟨10, 64, #[1,-1,1,-1,1], #[0,4,-4,8]⟩,
  ⟨22, 1078, #[1,-1,1,-1,1,-1,1,-1,1,-1,1], #[-4,0,0,0,4,0,4,4,0,-4]⟩]

def checkOrder (c : RootCase) : IO Nat := do
  let L := c.order
  let k := L/2
  let full := endpointPoly k
  let remainder := monicRemainder full c.cyclotomic
  expect s!"integer cyclotomic reduction L={L}" (remainder == c.expected)
  let H := CoupledAnchors.resolution 6 [L,2]
  let P := 6*H
  expect s!"overlapping anchors admit order {L}"
    (decide (reducedTargetPeriod 6 L ∣ H) && decide (L ∣ P))
  expect s!"half-period loses order {L}" (!(decide (reducedTargetPeriod 1 L ∣ k)))
  let mut count := 3
  let mut roots := 0
  for a in List.range L do
    if Nat.gcd a L = 1 then
      let z := c.root ^ a
      expect s!"primitive L={L} a={a}"
        (z^L == 1 && ((List.range (L-1)).all fun j => z^(j+1) != 1))
      expect s!"negative half power L={L} a={a}" (z^k == -1)
      expect s!"cyclotomic vanishing L={L} a={a}" (evalPoly c.cyclotomic z == 0)
      expect s!"endpoint from full polynomial L={L} a={a}" (boundaryValue k z == evalPoly full z)
      expect s!"endpoint from reduced polynomial L={L} a={a}" (boundaryValue k z == evalPoly remainder z)
      expect s!"first zero product L={L} a={a}" (uProduct z (k-1) != 0 && uProduct z k == 0)
      expect s!"last retained term L={L} a={a}" (uPartial (k-1) z != uPartial k z)
      count := count + 7
      for t in [0,1,2,5] do
        expect s!"terminated tail L={L} a={a} t={t}" (uPartial (k+t) z == uPartial k z)
        count := count + 1
      for n in List.range (k+2) do
        expect s!"product oracle L={L} a={a} n={n}" (uProduct z n == evalPoly (productPoly n) z)
        count := count + 1
      for r in List.range (P+1) do
        let expected := (List.range k).foldl (fun acc n =>
          if (n+1) % P = r then acc + evalPoly (productPoly n) z else acc) 0
        expect s!"{L}→{P} packet a={a} r={r}" (uPacket z k P r == expected)
        count := count + 1
      let pairing := sumBelow P (fun r => uPacket z k P r * z^r)
      expect s!"resolved character endpoint L={L} a={a}" (-4 * pairing == evalPoly remainder z)
      count := count + 1
      roots := roots + 1
  IO.println s!"PASS order {L}: {roots} primitive roots, endpoint mod Φ_{L}={remainder.toList}, {count} assertions"
  return count

def controls : IO Nat := do
  let z := (-1 : Int)
  expect "empty product and empty sum" (uProduct z 0 == 1 && uPartial 0 z == 0)
  expect "first term carries z, negative four multiplies the sum"
    (uPartial 1 z == -1 && boundaryValue 1 z == 4 && 4 * uPartial 1 z == -4)
  expect "shifted packet at order two" (uPacket z 1 2 0 == 0 && uPacket z 1 2 1 == 1)
  expect "folding into period one changes the value"
    (-4 * uPacket z 1 1 0 == -4 && boundaryValue 1 z == 4)
  expect "nonprimitive label admits earlier termination"
    (z^6 == 1 && z^3 == -1 && uProduct z 1 == 0 && boundaryValue 3 z == boundaryValue 1 z)
  expect "fourth-power certificate alone gives no negative half power"
    (z^4 == 1 && z^2 != -1)
  expect "odd primitive root has no zero factor" (let oddRoot : Fin 1321 := 297
    oddRoot^3 == 1 && oddRoot != 1 && uProduct oddRoot 3 != 0 &&
      uPartial 4 oddRoot != uPartial 3 oddRoot)
  expect "finite f polynomial differs from the radial endpoint"
    (MockTheta.mockPolynomial 5 z == -8 && MockTheta.mockPolynomial 5 z != boundaryValue 1 z)
  IO.println "PASS 8 empty, sign, shift, order and f-truncation controls"
  return 8

/-- Theorem 1.2 at b=k=11 and w=q: in F₇₂₇ a primitive 121st root
represents the published compensation phase as well as its 11th power.
The algebraic U endpoint is exact. These tests do not take a radial limit. -/
def checkTwoVariable : IO Nat := do
  let t : Fin 727 := 358
  let root := t^11
  expect "primitive 121st root" (t^121 == 1 && (List.range 120).all (fun j => t^(j+1) != 1))
  expect "specified eleventh root and phase" (root.val == 662 && root^11 == 1 && root != 1)
  let mut count := 2
  for a in [1:11] do
    let w := root^a
    let wi := root^(11-a)
    let hprime := ((List.range 11).find? fun j => (a*j+1) % 11 == 0).get!
    let phaseExponent := -((a : Int)^2) * hprime * 11
    expect s!"inverse and primitive order 11, a={a}" (wi*w == 1 && w^11 == 1 &&
      (List.range 10).all (fun j => w^(j+1) != 1))
    expect s!"Theorem 1.2 compensation, a=h={a}" (t^(phaseExponent % 121).toNat == w)
    expect s!"empty two-variable truncation a={a}" (uTwoPartial 0 w wi w == 0)
    count := count + 3
    for N in [1,2,11,12] do
      expect s!"diagonal U first factor terminates a={a} N={N}" (uTwoPartial N w wi w == w)
      expect s!"diagonal rank/crank RHS a={a} N={N}" (rankCrankRhs N w wi w == (1-w)^2)
      count := count + 2
    -- Away from the diagonal, choose torsion w² and cusp w. The second
    -- inverse-parameter factor now first vanishes for exponent 2.
    let orderTwoValue := w + (1-w^3)*(1-wi)*w^2
    expect s!"off-diagonal U with two nonzero summands a={a}" (uTwoPartial 1 (w*w) (wi*wi) w == w &&
      uTwoPartial 2 (w*w) (wi*wi) w == orderTwoValue && orderTwoValue != w &&
      uTwoPartial 11 (w*w) (wi*wi) w == orderTwoValue)
    -- An odd-order cusp is valid for this diagonal rank/crank formula; the
    -- negative-half-power premise for f holds instead at −w of order 22.
    expect s!"eleventh versus twenty-second root a={a}" (w^11 != -1 &&
      (-w)^11 == -1 && (-w)^22 == 1 && boundaryValue 11 (-w) ==
        rankCrankRhs 11 (-1 : Fin 727) (-1) (-w))
    count := count + 2
  expect "a=h=1 reference RHS" ((rankCrankRhs 11 root (root^10) root).val == 721)
  IO.println s!"PASS genuine eleventh-order rank/crank endpoints and compensation: {count+1} assertions"
  return count+1

def run : IO Unit := do
  let mut total ← controls
  for c in cases do
    let n ← checkOrder c
    total := total+n
  let oddCases ← checkTwoVariable
  IO.println s!"Total: {total + oddCases} exact assertions."

end KElimination.QuantumRadialSmoke

#eval KElimination.QuantumRadialSmoke.run
