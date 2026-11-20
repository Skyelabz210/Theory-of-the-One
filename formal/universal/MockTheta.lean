import CoefficientObservations

/-!
Exact formal coefficients of Ramanujan's third-order mock theta function

  f(q) = sum_{n >= 0} q^(n*n) / product_{j=1}^n (1 + q^j)^2.

Division below means the uniquely determined formal coefficient recurrence
for a polynomial with constant coefficient one. It uses no field division,
floating-point arithmetic, scalar reconstruction, or stored winding.
The coefficientwise construction is separate from analytic convergence.
-/

namespace KElimination.MockTheta

open Lean.Grind
open KElimination.ResidueSeries
open KElimination.ProfiniteObservations
open KElimination.CoefficientObservations

universe u

abbrev Series (R : Type u) := Nat → R

variable {R : Type u} [CommRing R]

/-- Multiplication by the formal monomial q^j. -/
def shift (j : Nat) (a : Series R) (d : Nat) : R :=
  if j ≤ d then a (d - j) else 0

/-- Coefficient action of multiplication by 1 + u*q^j. -/
def mulBinomial (j : Nat) (u : R) (a : Series R) (d : Nat) : R :=
  a d + u * shift j a d

/-- Exact formal division by 1 + u*q^j, where j is positive. -/
def divideBinomial (j : Nat) (hj : 0 < j) (u : R) (a : Series R)
    (d : Nat) : R :=
  if j ≤ d then a d - u * divideBinomial j hj u a (d - j) else a d
termination_by d
decreasing_by omega

theorem divideBinomial_at_or_above (j : Nat) (hj : 0 < j) (u : R)
    (a : Series R) (d : Nat) (hd : j ≤ d) :
    divideBinomial j hj u a d = a d - u * divideBinomial j hj u a (d-j) := by
  rw [divideBinomial, if_pos hd]

theorem divideBinomial_below (j : Nat) (hj : 0 < j) (u : R)
    (a : Series R) (d : Nat) (hd : d < j) :
    divideBinomial j hj u a d = a d := by
  rw [divideBinomial, if_neg (by omega)]

/-- The triangular recurrence really inverts multiplication by the binomial. -/
theorem mulBinomial_divideBinomial (j : Nat) (hj : 0 < j) (u : R)
    (a : Series R) :
    mulBinomial j u (divideBinomial j hj u a) = a := by
  funext d
  by_cases hd : j ≤ d
  · simp only [mulBinomial, shift, if_pos hd]
    rw [divideBinomial_at_or_above j hj u a d hd]
    exact AddCommGroup.sub_add_cancel
  · simp only [mulBinomial, shift, if_neg hd]
    rw [divideBinomial_below j hj u a d (by omega)]
    grind

theorem mulBinomial_injective (j : Nat) (hj : 0 < j) (u : R)
    (a b : Series R) (hab : mulBinomial j u a = mulBinomial j u b) : a = b := by
  funext d
  induction d using Nat.strongRecOn with
  | ind d ih =>
    have hvalue := congrFun hab d
    by_cases hd : j ≤ d
    · have hsmaller := ih (d-j) (by omega)
      simp only [mulBinomial, shift, if_pos hd] at hvalue
      rw [hsmaller] at hvalue
      exact (AddCommGroup.add_left_inj _).mp hvalue
    · simp only [mulBinomial, shift, if_neg hd] at hvalue
      exact (AddCommGroup.add_left_inj _).mp hvalue

theorem divideBinomial_mulBinomial (j : Nat) (hj : 0 < j) (u : R)
    (a : Series R) :
    divideBinomial j hj u (mulBinomial j u a) = a := by
  apply mulBinomial_injective j hj u
  exact mulBinomial_divideBinomial j hj u (mulBinomial j u a)

/-- The constant formal series 1. -/
def oneSeries (d : Nat) : R := if d = 0 then 1 else 0

/-- Coefficients of the reciprocal of (-q;q)_n squared. -/
def inverseSquaredPochhammer : Nat → Series R
  | 0 => oneSeries
  | n+1 => divideBinomial (n+1) (by omega) 1
      (divideBinomial (n+1) (by omega) 1 (inverseSquaredPochhammer n))

/-- Coefficient action of product_{j=1}^n (1+q^j)^2. -/
def denominatorAction : Nat → Series R → Series R
  | 0, a => a
  | n+1, a => denominatorAction n
      (mulBinomial (n+1) 1 (mulBinomial (n+1) 1 a))

theorem denominatorAction_inverse (n : Nat) :
    denominatorAction n (inverseSquaredPochhammer n : Series R) = oneSeries := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [denominatorAction, inverseSquaredPochhammer]
    rw [mulBinomial_divideBinomial, mulBinomial_divideBinomial]
    exact ih

theorem denominatorAction_injective (n : Nat) (a b : Series R)
    (hab : denominatorAction n a = denominatorAction n b) : a = b := by
  induction n generalizing a b with
  | zero => exact hab
  | succ n ih =>
    have htwice := ih _ _ hab
    have honce := mulBinomial_injective (n+1) (by omega) 1 _ _ htwice
    exact mulBinomial_injective (n+1) (by omega) 1 _ _ honce

/-- This uniquely identifies the denominator reciprocal, rather than assuming it. -/
theorem inverseSquaredPochhammer_unique (n : Nat) (a : Series R)
    (ha : denominatorAction n a = oneSeries) :
    a = inverseSquaredPochhammer n := by
  apply denominatorAction_injective n
  rw [ha, denominatorAction_inverse]

/-- Coefficient d of the nth summand q^(n*n)/(-q;q)_n^2. -/
def mockSummand (n d : Nat) : R :=
  shift (n*n) (inverseSquaredPochhammer n) d

theorem mockSummand_support (n d : Nat) (hd : d < n*n) :
    (mockSummand n d : R) = 0 := by
  simp only [mockSummand, shift, if_neg (by omega : ¬ n*n ≤ d)]

theorem mockSummand_zero_of_index_gt (n d : Nat) (hd : d < n) :
    (mockSummand n d : R) = 0 := by
  apply mockSummand_support
  exact Nat.lt_of_lt_of_le hd (Nat.le_mul_self n)

/-- The coefficient of q^d in Ramanujan's third-order f(q). Every omitted
summand vanishes at this degree, as proved by `mockCoeff_stable`. -/
def mockCoeff (d : Nat) : R :=
  sumBelow (d+1) (fun n => mockSummand n d)

/-- The infinite hypergeometric definition is locally finite coefficientwise. -/
theorem mockCoeff_stable (d N : Nat) (hN : d < N) :
    sumBelow N (fun n => (mockSummand n d : R)) = mockCoeff d := by
  apply sumBelow_eq_of_tail_zero (d+1) N _ (by omega)
  intro n hn _
  exact mockSummand_zero_of_index_gt n d (by omega)

/-- The coefficient-normalized truncation; N is the number of retained degrees,
not the number of hypergeometric summands. -/
def mockPolynomial (N : Nat) (q : R) : R :=
  sumBelow N (fun d => mockCoeff d * q ^ d)

/-- Formal series in a residue cylinder, retaining every coefficient degree. -/
def mockPacket (M r d : Nat) : R := packet mockCoeff M r d

theorem mockPacket_reconstruction (M d : Nat) (hM : 0 < M) :
    sumBelow M (fun r => (mockPacket M r d : R)) = mockCoeff d :=
  packet_reconstruction mockCoeff M d hM

theorem mockPacket_refinement (m M r d : Nat) (hM : 0 < M) (hdiv : m ∣ M) :
    sumBelow M (fun s => if s % m = r then (mockPacket M s d : R) else 0) =
      mockPacket m r d := packet_refinement mockCoeff m M r d hM hdiv

/-- Finite weighted coefficient mass in a residue cylinder. -/
def mockWeightedPacket (t : R) (N M r : Nat) : R :=
  weightedPacket mockCoeff (fun d => t ^ d) N M r

theorem mockWeightedPacket_refinement (t : R) (N m M r : Nat)
    (hM : 0 < M) (hdiv : m ∣ M) :
    sumBelow M (fun s => if s % m = r then mockWeightedPacket t N M s else 0) =
      mockWeightedPacket t N m r :=
  weightedPacket_refinement mockCoeff (fun d => t ^ d) N m M r hM hdiv

/-- Finite Fourier evaluation of the actual named mock theta coefficients. -/
theorem mockTheta_finite_root_evaluation (t z : R) (N M : Nat)
    (hM : 0 < M) (hz : z ^ M = 1) :
    sumBelow M (fun r => mockWeightedPacket t N M r * z ^ r) =
      mockPolynomial N (t * z) :=
  finite_root_evaluation mockCoeff t z N M hM hz

/-- Retained period divisibility transports the finite mock theta evaluation. -/
theorem mockTheta_finite_root_evaluation_of_dvd (t z : R) (N b M : Nat)
    (hM : 0 < M) (hdiv : b ∣ M) (hz : z ^ b = 1) :
    sumBelow M (fun r => mockWeightedPacket t N M r * z ^ r) =
      mockPolynomial N (t * z) :=
  finite_root_evaluation_of_dvd mockCoeff t z N b M hM hdiv hz

/-- The degree-d mock coefficient packet as a function on compatible residue
points. It factors through the named finite coordinate. -/
def mockCylinder {F : PeriodFamily} (m : F.Period) (d : Nat) :
    ResiduePoint F → R :=
  coefficientCylinder mockCoeff m d

theorem mockCylinder_on_diagonal {F : PeriodFamily} (m : F.Period)
    (d source : Nat) :
    (mockCylinder m d (natPoint F source) : R) =
      mockPacket m.val (source % m.val) d := rfl

/-- Cylinder functions pull back under refinement; the coefficient masses
themselves push forward by summing all finer residues in the cylinder. -/
theorem mockCylinder_refinement {F : PeriodFamily} (m n : F.Period)
    (hdiv : m.val ∣ n.val) (d : Nat) (x : ResiduePoint F) :
    sumBelow n.val (fun s => if s % m.val = x.residue n % m.val then
      (mockPacket n.val s d : R) else 0) = mockCylinder m d x :=
  coefficientCylinder_refinement mockCoeff m n hdiv d x

theorem mockCylinder_observable {F : PeriodFamily} (m : F.Period) (d : Nat) :
    ExactObservation.FiberConstant (fun x : ResiduePoint F => x.residue m)
      (mockCylinder m d : ResiduePoint F → R) :=
  coefficientCylinder_observable mockCoeff m d

/-- A finite weighted cylinder function on the same compatible point space. -/
def mockWeightedCylinder {F : PeriodFamily} (t : R) (N : Nat) (m : F.Period) :
    ResiduePoint F → R :=
  ofResidueFunction m (mockWeightedPacket t N m.val)

theorem mockWeightedCylinder_refinement {F : PeriodFamily} (t : R) (N : Nat)
    (m n : F.Period) (hdiv : m.val ∣ n.val) (x : ResiduePoint F) :
    sumBelow n.val (fun s => if s % m.val = x.residue n % m.val then
      mockWeightedPacket t N n.val s else 0) = mockWeightedCylinder t N m x := by
  rw [x.coherent m n hdiv]
  exact mockWeightedPacket_refinement t N m.val n.val (x.residue m)
    (F.positive n.val n.property) hdiv

/-- CRAM's reduced target requirement supplies a sufficient retained period
for this named finite mock theta transform. H represents authenticated quotient
resolution; this theorem neither produces that evidence nor stores a winding. -/
theorem mockTheta_from_reduced_winding (t z : R) (N M H b : Nat)
    (hM : 0 < M) (hH : 0 < H) (hb : 0 < b)
    (hresolve : reducedTargetPeriod M b ∣ H) (hz : z ^ b = 1) :
    sumBelow (M*H) (fun r => mockWeightedPacket t N (M*H) r * z ^ r) =
      mockPolynomial N (t*z) :=
  finite_root_evaluation_from_reduced_winding mockCoeff t z N M H b hM hH hb hresolve hz

/-- End-to-end composition with the existing exact-observation contract for
coupled anchors. Dependency/shared factors enter through the proved LCM/GCD
resolution. A universal residue query admits the corresponding finite transform;
no converse is claimed for a particular polynomial or a nonprimitive root. -/
theorem mockTheta_from_coupled_anchors (t z : R) (N M b : Nat)
    (anchors : List Nat) (r : Int) (hM : 0 < M) (hb : 0 < b)
    (hpos : ∀ a ∈ anchors, 0 < a)
    (hquery : ExactObservation.FiberConstant (anchorObservation M anchors r)
      (affineTarget M b r)) (hz : z ^ b = 1) :
    sumBelow (M * CoupledAnchors.resolution M anchors) (fun s =>
      mockWeightedPacket t N (M * CoupledAnchors.resolution M anchors) s * z ^ s) =
      mockPolynomial N (t*z) :=
  finite_root_evaluation_from_coupled_anchors mockCoeff t z N M b anchors r hM hb hpos hquery hz

end KElimination.MockTheta

#print axioms KElimination.MockTheta.divideBinomial_at_or_above
#print axioms KElimination.MockTheta.divideBinomial_below
#print axioms KElimination.MockTheta.mulBinomial_divideBinomial
#print axioms KElimination.MockTheta.mulBinomial_injective
#print axioms KElimination.MockTheta.divideBinomial_mulBinomial
#print axioms KElimination.MockTheta.denominatorAction_inverse
#print axioms KElimination.MockTheta.denominatorAction_injective
#print axioms KElimination.MockTheta.inverseSquaredPochhammer_unique
#print axioms KElimination.MockTheta.mockSummand_support
#print axioms KElimination.MockTheta.mockSummand_zero_of_index_gt
#print axioms KElimination.MockTheta.mockCoeff_stable
#print axioms KElimination.MockTheta.mockPacket_reconstruction
#print axioms KElimination.MockTheta.mockPacket_refinement
#print axioms KElimination.MockTheta.mockWeightedPacket_refinement
#print axioms KElimination.MockTheta.mockTheta_finite_root_evaluation
#print axioms KElimination.MockTheta.mockTheta_finite_root_evaluation_of_dvd
#print axioms KElimination.MockTheta.mockCylinder_on_diagonal
#print axioms KElimination.MockTheta.mockCylinder_refinement
#print axioms KElimination.MockTheta.mockCylinder_observable
#print axioms KElimination.MockTheta.mockWeightedCylinder_refinement
#print axioms KElimination.MockTheta.mockTheta_from_reduced_winding
#print axioms KElimination.MockTheta.mockTheta_from_coupled_anchors
