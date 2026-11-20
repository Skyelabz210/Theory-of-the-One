import MockTheta
import CoefficientObservations

/-!
Ramanujan's third-order mock theta function

  ψ(q) = ∑_{n ≥ 1} q^(n*n) / ∏_{j=1}^n (1 − q^(2*j−1)).

The index n is Ramanujan's summand index throughout. A term at index zero
contributes zero, so the coefficient of q⁰ also vanishes.
G. N. Watson gives the defining product in "The Final Problem", p. 62.
-/

namespace KElimination.MockThetaPsi

open Lean.Grind
open KElimination.MockTheta KElimination.ResidueSeries
open KElimination.ProfiniteObservations KElimination.CoefficientObservations

universe u

variable {R : Type u} [CommRing R]

/-- Reciprocal of (1−q)(1−q³)⋯(1−q^(2*n−1)). -/
def inverseOddPochhammer : Nat → Series R
  | 0 => oneSeries
  | n + 1 => divideBinomial (2 * n + 1) (by omega) (-1) (inverseOddPochhammer n)

/-- Coefficient action of the finite denominator of the nth summand. -/
def psiDenominatorAction : Nat → Series R → Series R
  | 0, a => a
  | n + 1, a => psiDenominatorAction n (mulBinomial (2 * n + 1) (-1) a)

theorem psiDenominatorAction_inverse (n : Nat) :
    psiDenominatorAction n (inverseOddPochhammer n : Series R) = oneSeries := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simpa only [psiDenominatorAction, inverseOddPochhammer,
      mulBinomial_divideBinomial] using ih

theorem psiDenominatorAction_injective (n : Nat) (a b : Series R)
    (hab : psiDenominatorAction n a = psiDenominatorAction n b) : a = b := by
  induction n generalizing a b with
  | zero => exact hab
  | succ n ih =>
    exact mulBinomial_injective (2 * n + 1) (by omega) (-1) a b (ih _ _ hab)

theorem inverseOddPochhammer_unique (n : Nat) (a : Series R)
    (ha : psiDenominatorAction n a = oneSeries) :
    a = inverseOddPochhammer n :=
  psiDenominatorAction_injective n _ _ (ha.trans (psiDenominatorAction_inverse n).symm)

theorem inverseOddPochhammer_constant (n : Nat) : (inverseOddPochhammer n 0 : R) = 1 := by
  induction n with
  | zero => simp [inverseOddPochhammer, oneSeries]
  | succ n ih =>
    unfold inverseOddPochhammer
    rw [divideBinomial_below _ _ _ _ _ (by omega)]
    exact ih

/-- Degree d of the summand at the original index n. -/
def psiSummand (n d : Nat) : R :=
  if n = 0 then 0 else shift (n * n) (inverseOddPochhammer n) d

theorem psiSummand_support (n d : Nat) (hd : d < n * n) :
    (psiSummand n d : R) = 0 := by
  simp [psiSummand, shift, Nat.not_le_of_lt hd]

/-- The term at positive index n contributes one at the square boundary itself. -/
theorem psiSummand_at_square (n : Nat) (hn : 0 < n) :
    (psiSummand n (n * n) : R) = 1 := by
  simp [psiSummand, Nat.ne_of_gt hn, shift, inverseOddPochhammer_constant]

/-- Coefficient of q^d in the third-order ψ. -/
def psiCoeff (d : Nat) : R :=
  sumBelow (d + 1) (fun n => psiSummand n d)

theorem psiCoeff_zero : (psiCoeff 0 : R) = 0 := by
  simp [psiCoeff, sumBelow, psiSummand, Semiring.add_zero]

theorem psiCoeff_stable (d N : Nat) (hN : d < N * N) :
    sumBelow N (fun n => (psiSummand n d : R)) = psiCoeff d :=
  squareSum_stable psiSummand psiSummand_support d N hN

/-- Polynomial formed from the first N coefficient degrees. -/
def psiPolynomial (N : Nat) (q : R) : R :=
  sumBelow N (fun d => psiCoeff d * q ^ d)

def psiPacket (M r d : Nat) : R := packet psiCoeff M r d

theorem psiPacket_refinement (m M r d : Nat) (hM : 0 < M) (hdiv : m ∣ M) :
    sumBelow M (fun s => if s % m = r then (psiPacket M s d : R) else 0) =
      psiPacket m r d :=
  packet_refinement psiCoeff m M r d hM hdiv

def psiCylinder {F : PeriodFamily} (m : F.Period) (d : Nat) : ResiduePoint F → R :=
  coefficientCylinder psiCoeff m d

theorem psiCylinder_observable {F : PeriodFamily} (m : F.Period) (d : Nat) :
    ExactObservation.FiberConstant (fun x : ResiduePoint F => x.residue m)
      (psiCylinder m d : ResiduePoint F → R) :=
  coefficientCylinder_observable psiCoeff m d

theorem psiCylinder_refinement {F : PeriodFamily} (m n : F.Period)
    (hdiv : m.val ∣ n.val) (d : Nat) (x : ResiduePoint F) :
    sumBelow n.val (fun s => if s % m.val = x.residue n % m.val then
      (psiPacket n.val s d : R) else 0) = psiCylinder m d x :=
  coefficientCylinder_refinement psiCoeff m n hdiv d x

def psiWeightedPacket (t : R) (N M r : Nat) : R :=
  weightedPacket psiCoeff (fun d => t ^ d) N M r

theorem psiWeightedPacket_refinement (t : R) (N m M r : Nat)
    (hM : 0 < M) (hdiv : m ∣ M) :
    sumBelow M (fun s => if s % m = r then psiWeightedPacket t N M s else 0) =
      psiWeightedPacket t N m r :=
  weightedPacket_refinement psiCoeff (fun d => t ^ d) N m M r hM hdiv

theorem psi_finite_root_evaluation (t z : R) (N M : Nat)
    (hM : 0 < M) (hz : z ^ M = 1) :
    sumBelow M (fun r => psiWeightedPacket t N M r * z ^ r) =
      psiPolynomial N (t * z) :=
  finite_root_evaluation psiCoeff t z N M hM hz

/-- An admitted target query supplies a period for evaluating the weighted
ψ packets at any certified b-root. -/
theorem psi_from_coupled_anchors (t z : R) (N M b : Nat)
    (anchors : List Nat) (r : Int) (hM : 0 < M) (hb : 0 < b)
    (hpos : ∀ a ∈ anchors, 0 < a)
    (hquery : ExactObservation.FiberConstant (anchorObservation M anchors r)
      (affineTarget M b r)) (hz : z ^ b = 1) :
    sumBelow (M * CoupledAnchors.resolution M anchors) (fun s =>
      psiWeightedPacket t N (M * CoupledAnchors.resolution M anchors) s * z ^ s) =
      psiPolynomial N (t * z) :=
  finite_root_evaluation_from_coupled_anchors psiCoeff t z N M b anchors r
    hM hb hpos hquery hz

end KElimination.MockThetaPsi

#print axioms KElimination.MockThetaPsi.psiDenominatorAction_inverse
#print axioms KElimination.MockThetaPsi.psiDenominatorAction_injective
#print axioms KElimination.MockThetaPsi.inverseOddPochhammer_unique
#print axioms KElimination.MockThetaPsi.inverseOddPochhammer_constant
#print axioms KElimination.MockThetaPsi.psiSummand_support
#print axioms KElimination.MockThetaPsi.psiSummand_at_square
#print axioms KElimination.MockThetaPsi.psiCoeff_zero
#print axioms KElimination.MockThetaPsi.psiCoeff_stable
#print axioms KElimination.MockThetaPsi.psiPacket_refinement
#print axioms KElimination.MockThetaPsi.psiCylinder_observable
#print axioms KElimination.MockThetaPsi.psiCylinder_refinement
#print axioms KElimination.MockThetaPsi.psiWeightedPacket_refinement
#print axioms KElimination.MockThetaPsi.psi_finite_root_evaluation
#print axioms KElimination.MockThetaPsi.psi_from_coupled_anchors
