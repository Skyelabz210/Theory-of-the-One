import FifthOrderSeries

/-!
The subscript-zero functions in Ramanujan's fifth-order families.
The summands for n ≥ 0 appear in Bin Chen’s “Mock theta functions and
Appell–Lerch sums”, equations (3.22–3.26).

  f₀: q^(n²) / (−q;q)_n
  φ₀: q^(n²) (−q;q²)_n
  ψ₀: q^((n+1)(n+2)/2) (−q;q)_n
  χ₀: q^n / (q^(n+1);q)_n
  F₀: q^(2n²) / (q;q²)_n
-/

namespace KElimination.MockThetaFifthZero

open Lean.Grind KElimination.MockTheta KElimination.FifthOrderSeries
open KElimination.ResidueSeries KElimination.ProfiniteObservations KElimination.CoefficientObservations

universe u
variable {R : Type u} [CommRing R]

/-- The exponent of the leading monomial in summand n. -/
def exponent : Family → Nat → Nat
  | .f, n | .phi, n => n * n
  | .psi, n => triangular (n + 1)
  | .chi, n => n
  | .bigF, n => 2 * (n * n)

theorem exponent_mono (s : Family) (i j : Nat) (h : i ≤ j) :
    exponent s i ≤ exponent s j := by
  cases s with
  | f | phi => exact Nat.mul_le_mul h h
  | psi => exact triangular_mono (Nat.succ_le_succ h)
  | chi => exact h
  | bigF => exact Nat.mul_le_mul_left 2 (Nat.mul_le_mul h h)

theorem le_exponent (s : Family) (n : Nat) : n ≤ exponent s n := by
  cases s with
  | f | phi => exact Nat.le_mul_self n
  | psi => exact Nat.le_trans (Nat.le_succ n) (le_triangular (n + 1))
  | chi => exact Nat.le_refl n
  | bigF =>
    have hs := Nat.le_mul_self n
    change n ≤ 2 * (n * n)
    omega

/-- The unshifted series of finite factors of the nth summand. The two
numerator products act on the constant series one. The remaining entries use
the formal reciprocals of their denominators. -/
def factors : Family → Nat → Series R
  | .f, n    => reciprocalProduct 1 1 n (by decide) 1
  | .phi, n  => mulProduct 1 2 n 1 oneSeries
  | .psi, n  => mulProduct 1 1 n 1 oneSeries
  | .chi, n  => reciprocalProduct (n + 1) 1 n (by omega) (-1)
  | .bigF, n => reciprocalProduct 1 2 n (by decide) (-1)

theorem f_denominator_iff (n : Nat) (a : Series R) :
    mulProduct 1 1 n 1 a = oneSeries ↔ a = factors .f n :=
  mulProduct_eq_one_iff 1 1 n (by decide) 1 a

theorem chi_denominator_iff (n : Nat) (a : Series R) :
    mulProduct (n + 1) 1 n (-1) a = oneSeries ↔ a = factors .chi n :=
  mulProduct_eq_one_iff (n + 1) 1 n (by omega) (-1) a

theorem bigF_denominator_iff (n : Nat) (a : Series R) :
    mulProduct 1 2 n (-1) a = oneSeries ↔ a = factors .bigF n :=
  mulProduct_eq_one_iff 1 2 n (by decide) (-1) a

/-- Degree d of the nth summand of the selected series. -/
def summand (s : Family) (n d : Nat) : R := shift (exponent s n) (factors s n) d

theorem summand_support (s : Family) (n d : Nat) (h : d < exponent s n) :
    (summand s n d : R) = 0 :=
  if_neg (Nat.not_le_of_lt h)

/-- Coefficient of q^d in the selected series. -/
def coeff (s : Family) (d : Nat) : R := shiftedCoeff (exponent s) (factors s) d

abbrev fCoeff (d : Nat) : R := coeff .f d
abbrev phiCoeff (d : Nat) : R := coeff .phi d
abbrev psiCoeff (d : Nat) : R := coeff .psi d
abbrev chiCoeff (d : Nat) : R := coeff .chi d
abbrev bigFCoeff (d : Nat) : R := coeff .bigF d

/-- The first N summands suffice whenever the first omitted shift
lies beyond the requested coefficient degree. -/
theorem coeff_stable (s : Family) (d N : Nat) (h : d < exponent s N) :
    sumBelow N (fun n => (summand s n d : R)) = coeff s d :=
  shiftedCoeff_stable (exponent s) (factors s) (exponent_mono s) (le_exponent s) d N h

/-- Polynomial truncated after the first N coefficient degrees. -/
def polynomial (s : Family) (N : Nat) (q : R) : R :=
  sumBelow N (fun d => coeff s d * q ^ d)

def degreePacket (s : Family) (M r d : Nat) : R :=
  packet (coeff s) M r d

theorem degreePacket_refinement (s : Family) (m M r d : Nat) (hM : 0 < M) (hdiv : m ∣ M) :
    sumBelow M (fun k => if k % m = r then (degreePacket s M k d : R) else 0) =
      degreePacket s m r d :=
  packet_refinement (coeff s) m M r d hM hdiv

def cylinder {F : PeriodFamily} (s : Family) (m : F.Period) (d : Nat) : ResiduePoint F → R :=
  coefficientCylinder (coeff s) m d

theorem cylinder_observable {F : PeriodFamily} (s : Family) (m : F.Period) (d : Nat) :
    ExactObservation.FiberConstant (fun x : ResiduePoint F => x.residue m)
      (cylinder s m d : ResiduePoint F → R) :=
  coefficientCylinder_observable (coeff s) m d

theorem cylinder_refinement {F : PeriodFamily} (s : Family) (m n : F.Period)
    (hdiv : m.val ∣ n.val) (d : Nat) (x : ResiduePoint F) :
    sumBelow n.val (fun k => if k % m.val = x.residue n % m.val then
      (degreePacket s n.val k d : R) else 0) = cylinder s m d x :=
  coefficientCylinder_refinement (coeff s) m n hdiv d x

def weightedPacket (s : Family) (t : R) (N M r : Nat) : R :=
  ResidueSeries.weightedPacket (coeff s) (fun d => t ^ d) N M r

theorem weightedPacket_refinement (s : Family) (t : R) (N m M r : Nat)
    (hM : 0 < M) (hdiv : m ∣ M) :
    sumBelow M (fun k => if k % m = r then weightedPacket s t N M k else 0) =
      weightedPacket s t N m r :=
  ResidueSeries.weightedPacket_refinement (coeff s) (fun d => t ^ d) N m M r hM hdiv

theorem finite_root_evaluation (s : Family) (t z : R) (N M : Nat) (hM : 0 < M) (hz : z ^ M = 1) :
    sumBelow M (fun r => weightedPacket s t N M r * z ^ r) = polynomial s N (t * z) :=
  ResidueSeries.finite_root_evaluation (coeff s) t z N M hM hz

theorem from_coupled_anchors (s : Family) (t z : R) (N M b : Nat)
    (anchors : List Nat) (r : Int) (hM : 0 < M) (hb : 0 < b)
    (hpos : ∀ a ∈ anchors, 0 < a)
    (hquery : ExactObservation.FiberConstant (anchorObservation M anchors r)
      (affineTarget M b r)) (hz : z ^ b = 1) :
    sumBelow (M * CoupledAnchors.resolution M anchors) (fun k =>
      weightedPacket s t N (M * CoupledAnchors.resolution M anchors) k * z ^ k) =
      polynomial s N (t * z) :=
  finite_root_evaluation_from_coupled_anchors (coeff s) t z N M b anchors r hM hb hpos hquery hz

end KElimination.MockThetaFifthZero

#print axioms KElimination.MockThetaFifthZero.exponent_mono
#print axioms KElimination.MockThetaFifthZero.le_exponent
#print axioms KElimination.MockThetaFifthZero.f_denominator_iff
#print axioms KElimination.MockThetaFifthZero.chi_denominator_iff
#print axioms KElimination.MockThetaFifthZero.bigF_denominator_iff
#print axioms KElimination.MockThetaFifthZero.summand_support
#print axioms KElimination.MockThetaFifthZero.coeff_stable
#print axioms KElimination.MockThetaFifthZero.degreePacket_refinement
#print axioms KElimination.MockThetaFifthZero.cylinder_observable
#print axioms KElimination.MockThetaFifthZero.cylinder_refinement
#print axioms KElimination.MockThetaFifthZero.weightedPacket_refinement
#print axioms KElimination.MockThetaFifthZero.finite_root_evaluation
#print axioms KElimination.MockThetaFifthZero.from_coupled_anchors
