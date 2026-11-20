import MockTheta

/-!
Ramanujan's third-order mock theta function

  χ(q) = ∑_{n ≥ 0} q^(n*n) / ∏_{j=1}^n (1 - q^j + q^(2*j)).

The coefficient action of the trinomial is explicit. Its product with
1 + q^j gives 1 + q^(3*j), whose triangular inverse is already proved.
G. N. Watson gives the defining product in "The Final Problem", p. 62.
-/

namespace KElimination.MockThetaChi

open Lean.Grind
open KElimination.MockTheta KElimination.ResidueSeries
open KElimination.ProfiniteObservations KElimination.CoefficientObservations

universe u

variable {R : Type u} [CommRing R]

/-- Coefficient action of multiplication by 1 - q^j + q^(2*j). -/
def mulTrinomial (j : Nat) (a : Series R) (d : Nat) : R :=
  a d - shift j a d + shift (2*j) a d

/-- The coefficient form of (1 + x)(1 - x + x²) = 1 + x³ at x = q^j. -/
theorem trinomial_factorization (j : Nat) (a : Series R) :
    mulBinomial j 1 (mulTrinomial j a) = mulBinomial (3*j) 1 a := by
  funext d
  have h2 : j ≤ d - j ↔ 2*j ≤ d := by omega
  have h3 : 2*j ≤ d - j ↔ 3*j ≤ d := by omega
  have step2 : d - j - j = d - 2*j := by omega
  have step3 : d - j - 2*j = d - 3*j := by omega
  simp only [mulBinomial, mulTrinomial, shift, Semiring.one_mul, h2, h3, step2, step3]
  by_cases h : j ≤ d
  · simp only [if_pos h]
    grind
  · have hn2 : ¬ 2*j ≤ d := by omega
    have hn3 : ¬ 3*j ≤ d := by omega
    simp only [if_neg h, if_neg hn2, if_neg hn3]
    grind

/-- Divide a formal series by the trinomial at positive stride j. -/
def divideTrinomial (j : Nat) (hj : 0 < j) (a : Series R) : Series R :=
  divideBinomial (3*j) (by omega) 1 (mulBinomial j 1 a)

theorem mulTrinomial_divideTrinomial (j : Nat) (hj : 0 < j) (a : Series R) :
    mulTrinomial j (divideTrinomial j hj a) = a := by
  apply mulBinomial_injective j hj 1
  rw [trinomial_factorization, divideTrinomial, mulBinomial_divideBinomial]

theorem mulTrinomial_injective (j : Nat) (hj : 0 < j) (a b : Series R)
    (h : mulTrinomial j a = mulTrinomial j b) : a = b := by
  apply mulBinomial_injective (3*j) (by omega) 1
  rw [← trinomial_factorization j a, ← trinomial_factorization j b, h]

/-- Reciprocal coefficients of the finite trinomial denominator. -/
def inverseChiDenominator : Nat → Series R
  | 0 => oneSeries
  | n + 1 => divideTrinomial (n + 1) (by omega) (inverseChiDenominator n)

/-- Coefficient action of the entire denominator of the nth summand. -/
def chiDenominatorAction : Nat → Series R → Series R
  | 0, a => a
  | n + 1, a => chiDenominatorAction n (mulTrinomial (n + 1) a)

theorem chiDenominatorAction_inverse (n : Nat) :
    chiDenominatorAction n (inverseChiDenominator n : Series R) = oneSeries := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simpa only [chiDenominatorAction, inverseChiDenominator,
      mulTrinomial_divideTrinomial] using ih

theorem chiDenominatorAction_injective (n : Nat) (a b : Series R)
    (hab : chiDenominatorAction n a = chiDenominatorAction n b) : a = b := by
  induction n generalizing a b with
  | zero => exact hab
  | succ n ih =>
    exact mulTrinomial_injective (n + 1) (by omega) a b (ih _ _ hab)

theorem inverseChiDenominator_unique (n : Nat) (a : Series R)
    (ha : chiDenominatorAction n a = oneSeries) :
    a = inverseChiDenominator n :=
  chiDenominatorAction_injective n _ _ (ha.trans (chiDenominatorAction_inverse n).symm)

/-- Degree d in the nth summand of χ. -/
def chiSummand (n d : Nat) : R :=
  shift (n*n) (inverseChiDenominator n) d

theorem chiSummand_support (n d : Nat) (hd : d < n*n) :
    (chiSummand n d : R) = 0 := by
  simp [chiSummand, shift, Nat.not_le_of_lt hd]

/-- Coefficient of q^d in Ramanujan's third-order χ. -/
def chiCoeff (d : Nat) : R :=
  sumBelow (d + 1) (fun n => chiSummand n d)

/-- Every omitted summand has numerator degree at least N². -/
theorem chiCoeff_stable (d N : Nat) (hN : d < N*N) :
    sumBelow N (fun n => (chiSummand n d : R)) = chiCoeff d :=
  squareSum_stable chiSummand chiSummand_support d N hN

/-- Polynomial formed from the first N coefficient degrees. -/
def chiPolynomial (N : Nat) (q : R) : R :=
  sumBelow N (fun d => chiCoeff d * q ^ d)

def chiPacket (M r d : Nat) : R := packet chiCoeff M r d

theorem chiPacket_refinement (m M r d : Nat) (hM : 0 < M) (hdiv : m ∣ M) :
    sumBelow M (fun s => if s % m = r then (chiPacket M s d : R) else 0) =
      chiPacket m r d :=
  packet_refinement chiCoeff m M r d hM hdiv

def chiCylinder {F : PeriodFamily} (m : F.Period) (d : Nat) : ResiduePoint F → R :=
  coefficientCylinder chiCoeff m d

theorem chiCylinder_observable {F : PeriodFamily} (m : F.Period) (d : Nat) :
    ExactObservation.FiberConstant (fun x : ResiduePoint F => x.residue m)
      (chiCylinder m d : ResiduePoint F → R) :=
  coefficientCylinder_observable chiCoeff m d

theorem chiCylinder_refinement {F : PeriodFamily} (m n : F.Period)
    (hdiv : m.val ∣ n.val) (d : Nat) (x : ResiduePoint F) :
    sumBelow n.val (fun s => if s % m.val = x.residue n % m.val then
      (chiPacket n.val s d : R) else 0) = chiCylinder m d x :=
  coefficientCylinder_refinement chiCoeff m n hdiv d x

def chiWeightedPacket (t : R) (N M r : Nat) : R :=
  weightedPacket chiCoeff (fun d => t ^ d) N M r

theorem chiWeightedPacket_refinement (t : R) (N m M r : Nat)
    (hM : 0 < M) (hdiv : m ∣ M) :
    sumBelow M (fun s => if s % m = r then chiWeightedPacket t N M s else 0) =
      chiWeightedPacket t N m r :=
  weightedPacket_refinement chiCoeff (fun d => t ^ d) N m M r hM hdiv

theorem chi_finite_root_evaluation (t z : R) (N M : Nat)
    (hM : 0 < M) (hz : z ^ M = 1) :
    sumBelow M (fun r => chiWeightedPacket t N M r * z ^ r) =
      chiPolynomial N (t * z) :=
  finite_root_evaluation chiCoeff t z N M hM hz

/-- An admitted target query supplies a period for evaluating the weighted
χ packets at any certified b-root. -/
theorem chi_from_coupled_anchors (t z : R) (N M b : Nat)
    (anchors : List Nat) (r : Int) (hM : 0 < M) (hb : 0 < b)
    (hpos : ∀ a ∈ anchors, 0 < a)
    (hquery : ExactObservation.FiberConstant (anchorObservation M anchors r)
      (affineTarget M b r)) (hz : z ^ b = 1) :
    sumBelow (M * CoupledAnchors.resolution M anchors) (fun s =>
      chiWeightedPacket t N (M * CoupledAnchors.resolution M anchors) s * z ^ s) =
      chiPolynomial N (t * z) :=
  finite_root_evaluation_from_coupled_anchors chiCoeff t z N M b anchors r
    hM hb hpos hquery hz

end KElimination.MockThetaChi

#print axioms KElimination.MockThetaChi.trinomial_factorization
#print axioms KElimination.MockThetaChi.mulTrinomial_divideTrinomial
#print axioms KElimination.MockThetaChi.mulTrinomial_injective
#print axioms KElimination.MockThetaChi.chiDenominatorAction_inverse
#print axioms KElimination.MockThetaChi.chiDenominatorAction_injective
#print axioms KElimination.MockThetaChi.inverseChiDenominator_unique
#print axioms KElimination.MockThetaChi.chiSummand_support
#print axioms KElimination.MockThetaChi.chiCoeff_stable
#print axioms KElimination.MockThetaChi.chiPacket_refinement
#print axioms KElimination.MockThetaChi.chiCylinder_observable
#print axioms KElimination.MockThetaChi.chiCylinder_refinement
#print axioms KElimination.MockThetaChi.chiWeightedPacket_refinement
#print axioms KElimination.MockThetaChi.chi_finite_root_evaluation
#print axioms KElimination.MockThetaChi.chi_from_coupled_anchors
