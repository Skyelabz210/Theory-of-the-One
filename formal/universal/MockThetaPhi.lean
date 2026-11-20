import MockTheta
import CoefficientObservations

/-!
Ramanujan's third-order mock theta function

  φ(q) = ∑_{n ≥ 0} q^(n*n) / ∏_{j=1}^n (1 + q^(2*j)).

The reciprocal uses one formal binomial division for each positive even
exponent through 2*n. The numerators give a square cutoff at each degree.
G. N. Watson gives this product in "The Final Problem", p. 62.
-/

namespace KElimination.MockThetaPhi

open Lean.Grind
open KElimination.MockTheta KElimination.ResidueSeries
open KElimination.ProfiniteObservations KElimination.CoefficientObservations

universe u

variable {R : Type u} [CommRing R]

/-- Reciprocal coefficients of the finite product ∏_{j=1}^n (1 + q^(2*j)). -/
def inverseEvenPochhammer : Nat → Series R
  | 0 => oneSeries
  | n + 1 => divideBinomial (2 * (n + 1)) (by omega) 1 (inverseEvenPochhammer n)

/-- Coefficient action of the same finite denominator. -/
def phiDenominatorAction : Nat → Series R → Series R
  | 0, a => a
  | n + 1, a => phiDenominatorAction n (mulBinomial (2 * (n + 1)) 1 a)

theorem phiDenominatorAction_inverse (n : Nat) :
    phiDenominatorAction n (inverseEvenPochhammer n : Series R) = oneSeries := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simpa only [phiDenominatorAction, inverseEvenPochhammer,
      mulBinomial_divideBinomial] using ih

theorem phiDenominatorAction_injective (n : Nat) (a b : Series R)
    (hab : phiDenominatorAction n a = phiDenominatorAction n b) : a = b := by
  induction n generalizing a b with
  | zero => exact hab
  | succ n ih =>
    exact mulBinomial_injective (2 * (n + 1)) (by omega) 1 a b (ih _ _ hab)

theorem inverseEvenPochhammer_unique (n : Nat) (a : Series R)
    (ha : phiDenominatorAction n a = oneSeries) :
    a = inverseEvenPochhammer n :=
  phiDenominatorAction_injective n _ _ (ha.trans (phiDenominatorAction_inverse n).symm)

/-- Degree d in the summand with numerator q^(n*n). -/
def phiSummand (n d : Nat) : R :=
  shift (n * n) (inverseEvenPochhammer n) d

theorem phiSummand_support (n d : Nat) (hd : d < n * n) :
    (phiSummand n d : R) = 0 := by
  simp [phiSummand, shift, Nat.not_le_of_lt hd]

/-- Coefficient of q^d in the third-order φ. -/
def phiCoeff (d : Nat) : R :=
  sumBelow (d + 1) (fun n => phiSummand n d)

/-- Summing the first N summands suffices as soon as the first omitted
numerator degree N² exceeds d. -/
theorem phiCoeff_stable (d N : Nat) (hN : d < N * N) :
    sumBelow N (fun n => (phiSummand n d : R)) = phiCoeff d :=
  squareSum_stable phiSummand phiSummand_support d N hN

/-- Polynomial formed from the first N coefficient degrees. -/
def phiPolynomial (N : Nat) (q : R) : R :=
  sumBelow N (fun d => phiCoeff d * q ^ d)

def phiPacket (M r d : Nat) : R := packet phiCoeff M r d

theorem phiPacket_refinement (m M r d : Nat) (hM : 0 < M) (hdiv : m ∣ M) :
    sumBelow M (fun s => if s % m = r then (phiPacket M s d : R) else 0) =
      phiPacket m r d :=
  packet_refinement phiCoeff m M r d hM hdiv

def phiCylinder {F : PeriodFamily} (m : F.Period) (d : Nat) : ResiduePoint F → R :=
  coefficientCylinder phiCoeff m d

theorem phiCylinder_observable {F : PeriodFamily} (m : F.Period) (d : Nat) :
    ExactObservation.FiberConstant (fun x : ResiduePoint F => x.residue m)
      (phiCylinder m d : ResiduePoint F → R) :=
  coefficientCylinder_observable phiCoeff m d

theorem phiCylinder_refinement {F : PeriodFamily} (m n : F.Period)
    (hdiv : m.val ∣ n.val) (d : Nat) (x : ResiduePoint F) :
    sumBelow n.val (fun s => if s % m.val = x.residue n % m.val then
      (phiPacket n.val s d : R) else 0) = phiCylinder m d x :=
  coefficientCylinder_refinement phiCoeff m n hdiv d x

def phiWeightedPacket (t : R) (N M r : Nat) : R :=
  weightedPacket phiCoeff (fun d => t ^ d) N M r

theorem phiWeightedPacket_refinement (t : R) (N m M r : Nat)
    (hM : 0 < M) (hdiv : m ∣ M) :
    sumBelow M (fun s => if s % m = r then phiWeightedPacket t N M s else 0) =
      phiWeightedPacket t N m r :=
  weightedPacket_refinement phiCoeff (fun d => t ^ d) N m M r hM hdiv

theorem phi_finite_root_evaluation (t z : R) (N M : Nat)
    (hM : 0 < M) (hz : z ^ M = 1) :
    sumBelow M (fun r => phiWeightedPacket t N M r * z ^ r) =
      phiPolynomial N (t * z) :=
  finite_root_evaluation phiCoeff t z N M hM hz

/-- An admitted target query supplies a period for evaluating the weighted
φ packets at any certified b-root. -/
theorem phi_from_coupled_anchors (t z : R) (N M b : Nat)
    (anchors : List Nat) (r : Int) (hM : 0 < M) (hb : 0 < b)
    (hpos : ∀ a ∈ anchors, 0 < a)
    (hquery : ExactObservation.FiberConstant (anchorObservation M anchors r)
      (affineTarget M b r)) (hz : z ^ b = 1) :
    sumBelow (M * CoupledAnchors.resolution M anchors) (fun s =>
      phiWeightedPacket t N (M * CoupledAnchors.resolution M anchors) s * z ^ s) =
      phiPolynomial N (t * z) :=
  finite_root_evaluation_from_coupled_anchors phiCoeff t z N M b anchors r
    hM hb hpos hquery hz

end KElimination.MockThetaPhi

#print axioms KElimination.MockThetaPhi.phiDenominatorAction_inverse
#print axioms KElimination.MockThetaPhi.phiDenominatorAction_injective
#print axioms KElimination.MockThetaPhi.inverseEvenPochhammer_unique
#print axioms KElimination.MockThetaPhi.phiSummand_support
#print axioms KElimination.MockThetaPhi.phiCoeff_stable
#print axioms KElimination.MockThetaPhi.phiPacket_refinement
#print axioms KElimination.MockThetaPhi.phiCylinder_observable
#print axioms KElimination.MockThetaPhi.phiCylinder_refinement
#print axioms KElimination.MockThetaPhi.phiWeightedPacket_refinement
#print axioms KElimination.MockThetaPhi.phi_finite_root_evaluation
#print axioms KElimination.MockThetaPhi.phi_from_coupled_anchors
