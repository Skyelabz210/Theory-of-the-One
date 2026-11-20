import MockTheta
import CrankCharacter11

/-! The finite endpoint in Folsom–Ono–Rhoades, “Mock theta functions and
quantum modular forms”, Theorems 1.1–1.2 and equation (1.6). At a primitive
complex root ζ of order 2k the authors identify the radial limit of
f(q) − (−1)^k b(q) with −4U(−1;ζ). Here the finite U-product, its
termination, and the coefficient-packet expression for that value are
proved over a commutative ring under the explicit hypothesis ζ^k = −1.
The two-variable form also gives the rank–crank boundary expression
at the diagonal endpoint w = q, in particular at an eleventh root.
-/

namespace KElimination.QuantumRadial

open Lean.Grind ResidueSeries ProfiniteObservations

universe u
variable {R : Type u} [CommRing R]

/-- (a;q)_n indexed from j=0 to n−1. -/
def pochhammer (a q : R) : Nat → R
  | 0 => 1
  | n+1 => pochhammer a q n * (1 - a * q^n)

/-- The factor (-q;q)_n² in the summand of U(-1;q). -/
def uProduct (q : R) : Nat → R
  | 0 => 1
  | n+1 => uProduct q n * (1 + q^(n+1))^2

theorem uProduct_eq_pochhammer (q : R) (n : Nat) :
    uProduct q n = (pochhammer (-q) q n)^2 := by
  induction n with
  | zero => simp [uProduct, pochhammer, Semiring.one_pow]
  | succ n ih =>
    rw [uProduct, pochhammer, ih, Semiring.pow_succ q n]
    simp only [Semiring.pow_two]
    grind

/-- The finite two-variable polynomial freezes the inner Pochhammer
parameter q and evaluates the outer exponent n+1 at x. -/
def uPolynomial (N : Nat) (q x : R) : R :=
  sumBelow N (fun n => uProduct q n * x^(n+1))

/-- U(-1;q) with only the first N summands retained. -/
def uPartial (N : Nat) (q : R) : R := uPolynomial N q q

/-- The published radial boundary value, with the positive half-order k. -/
def boundaryValue (k : Nat) (z : R) : R := (-4) * uPartial k z

theorem uProduct_zero_of_le (z : R) (k n : Nat) (hk : 0 < k) (hz : z^k = -1)
    (hkn : k ≤ n) : uProduct z n = 0 := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [uProduct]
    by_cases h : k ≤ n
    · rw [ih h, Semiring.zero_mul]
    · have he : n+1 = k := by omega
      rw [he, hz, Semiring.pow_two]
      grind

/-- The zero Pochhammer factor at index k eliminates the entire tail,
even when the outer evaluation variable differs from z. -/
theorem uPolynomial_stable (N k : Nat) (z x : R) (hk : 0 < k)
    (hz : z^k = -1) (hN : k ≤ N) : uPolynomial N z x = uPolynomial k z x := by
  apply sumBelow_eq_of_tail_zero k N _ hN
  intro n hn _
  rw [uProduct_zero_of_le z k n hk hz hn, Semiring.zero_mul]

theorem boundaryValue_stable (N k : Nat) (z : R) (hk : 0 < k)
    (hz : z^k = -1) (hN : k ≤ N) : (-4) * uPartial N z = boundaryValue k z :=
  congrArg (fun y : R => (-4) * y) (uPolynomial_stable N k z z hk hz hN)

theorem twice_half_period (z : R) (k : Nat) (hz : z^k = -1) : z^(2*k) = 1 := by
  rw [show 2*k = k+k by omega, Semiring.pow_add, hz]
  grind

/-- With the Pochhammer parameter fixed, a summand numbered n contributes
to outer degree n+1. Degree zero has coefficient zero. -/
def outerCoeff (q : R) : Nat → R
  | 0 => 0
  | n+1 => uProduct q n

theorem uPolynomial_as_degrees (N : Nat) (q x : R) :
    uPolynomial N q x = sumBelow (N+1) (fun d => outerCoeff q d * x^d) := by
  induction N with
  | zero => simp [uPolynomial, sumBelow, outerCoeff, Semiring.zero_mul, Semiring.add_zero]
  | succ N ih =>
    change uPolynomial N q x + uProduct q N * x^(N+1) =
      sumBelow (N+1) (fun d => outerCoeff q d * x^d) + uProduct q N * x^(N+1)
    rw [ih]

/-- Bin the first N summands by their outer degree modulo L, holding q fixed. -/
def uPacket (q : R) (N L r : Nat) : R :=
  weightedPacket (outerCoeff q) (fun _ => 1) (N+1) L r

theorem uPacket_refinement (q : R) (N m L r : Nat) (hL : 0 < L) (hdiv : m ∣ L) :
    sumBelow L (fun s => if s % m = r then uPacket q N L s else 0) = uPacket q N m r :=
  weightedPacket_refinement (outerCoeff q) (fun _ => 1) N.succ m L r hL hdiv

theorem uPacket_evaluation (q x : R) (N L : Nat) (hL : 0 < L) (hx : x^L = 1) :
    sumBelow L (fun r => uPacket q N L r * x^r) = uPolynomial N q x := by
  rw [uPolynomial_as_degrees]
  simpa only [uPacket, Semiring.one_pow, Semiring.one_mul] using
    finite_root_evaluation (outerCoeff q) (1 : R) x (N+1) L hL hx

/-- Pair the residue packets with the endpoint character at any retained
multiple of 2k. The summand cutoff can be anywhere at or beyond k. -/
theorem boundaryValue_from_packets (N k L : Nat) (z : R) (hk : 0 < k)
    (hz : z^k = -1) (hN : k ≤ N) (hL : 0 < L) (hdiv : 2*k ∣ L) :
    (-4) * sumBelow L (fun r => uPacket z N L r * z^r) = boundaryValue k z := by
  rw [uPacket_evaluation z z N L hL (root_of_dividing_order z (2*k) L hdiv
    (twice_half_period z k hz))]
  exact boundaryValue_stable N k z hk hz hN

/-- A query for target order 2k admitted by coupled anchors supplies the
period of the endpoint packet transform. -/
theorem boundaryValue_from_coupled_anchors (N k M : Nat) (z : R)
    (anchors : List Nat) (r : Int) (hk : 0 < k) (hz : z^k = -1)
    (hN : k ≤ N) (hM : 0 < M) (hpos : ∀ a ∈ anchors, 0 < a)
    (hquery : ExactObservation.FiberConstant (anchorObservation M anchors r)
      (affineTarget M (2*k) r)) :
    (-4) * sumBelow (M * CoupledAnchors.resolution M anchors) (fun s =>
      uPacket z N (M * CoupledAnchors.resolution M anchors) s * z^s) = boundaryValue k z := by
  have htarget : 0 < 2*k := by omega
  have reduced := (combined_target_fiber_constant_iff M (2*k) anchors r htarget hpos).mp hquery
  exact boundaryValue_from_packets N k _ z hk hz hN (Nat.mul_pos hM
    (CoupledAnchors.resolution_pos M anchors hpos))
    (target_divides_source_period M (2*k) _ htarget reduced)

/-- The first example following Theorem 1.1 at ζ = −1. -/
theorem boundaryValue_at_neg_one : boundaryValue 1 (-1 : R) = 4 := by
  simp only [boundaryValue, uPartial, uPolynomial, sumBelow, uProduct]
  grind

/-- The second example in Theorem 1.1 has k = 2 and yields 4ζ for ζ² = −1. -/
theorem boundaryValue_at_fourth_root (z : R) (hz : z^2 = -1) : boundaryValue 2 z = 4*z := by
  simp only [boundaryValue, uPartial, uPolynomial, sumBelow, uProduct]
  have h : z*z = -1 := (Semiring.pow_two z).symm.trans hz
  simp only [Semiring.pow_two]
  grind

/-- First N terms of U(w;q) in equation (1.6). The parameter wi denotes
an explicit inverse of w; the finite polynomial is defined for arbitrary inputs. -/
def uTwoPartial (N : Nat) (w wi q : R) : R :=
  sumBelow N (fun n => pochhammer (w*q) q n * pochhammer (wi*q) q n * q^(n+1))

/-- The algebraic right-hand side of Theorem 1.2 with the first N terms of U. -/
def rankCrankRhs (N : Nat) (w wi q : R) : R :=
  -(1-w) * (1-wi) * uTwoPartial N w wi q

theorem uTwoPartial_at_neg_one (N : Nat) (q : R) :
    uTwoPartial N (-1) (-1) q = uPartial N q := by
  apply sumBelow_congr
  intro n hn
  rw [uProduct_eq_pochhammer, Semiring.pow_two]
  have h : (-1 : R) * q = -q := by grind
  rw [h]

theorem rankCrankRhs_at_neg_one (k : Nat) (q : R) :
    rankCrankRhs k (-1) (-1) q = boundaryValue k q := by
  rw [rankCrankRhs, uTwoPartial_at_neg_one, boundaryValue]
  grind

/-- (1;q)_n has the initial zero factor 1−1 as soon as n is positive. -/
theorem pochhammer_one_succ (q : R) (n : Nat) : pochhammer 1 q (n+1) = 0 := by
  induction n with
  | zero => rw [pochhammer, pochhammer, Semiring.pow_zero]; grind
  | succ n ih => rw [pochhammer, ih, Semiring.zero_mul]

/-- At w=q and wi=w⁻¹, all terms beyond n=0 vanish. -/
theorem uTwoPartial_diagonal (N : Nat) (w wi : R) (hN : 0 < N) (hwi : wi*w = 1) :
    uTwoPartial N w wi w = w := by
  unfold uTwoPartial
  rw [hwi, sumBelow_eq_of_tail_zero 1 N _ hN]
  · simp only [sumBelow, pochhammer]
    grind
  · intro n hn _
    cases n with
    | zero => omega
    | succ n => rw [pochhammer_one_succ, Semiring.mul_zero, Semiring.zero_mul]

/-- On the diagonal the finite endpoint of the rank–crank difference
reduces to (1−w)². The hypothesis wi*w=1 is the inverse required in (1.6). -/
theorem rankCrankRhs_diagonal (N : Nat) (w wi : R) (hN : 0 < N) (hwi : wi*w = 1) :
    rankCrankRhs N w wi w = (1-w)^2 := by
  rw [rankCrankRhs, uTwoPartial_diagonal N w wi hN hwi, Semiring.pow_two]
  grind

/-- For the odd cusp a=h=1, b=k=11 of Theorem 1.2, w^10 supplies w⁻¹.
Primitivity is needed by the analytic application; w^11=1 suffices here. -/
theorem rankCrankRhs_eleventh_root (N : Nat) (w : R) (hN : 0 < N) (hw : w^11 = 1) :
    rankCrankRhs N w (w^10) w = (1-w)^2 :=
  rankCrankRhs_diagonal N w (w^10) hN ((Semiring.pow_succ w 10).symm.trans hw)

/-- Formal finite product through j=J of
(1−q^j)/((1−w q^j)(1−wi q^j)), the Euler product for the analytic crank C. -/
def crankEuler (w wi : R) : Nat → MockTheta.Series R
  | 0 => MockTheta.oneSeries
  | n+1 => MockTheta.divideBinomial (n+1) (by omega) (-w)
      (MockTheta.divideBinomial (n+1) (by omega) (-wi)
        (MockTheta.mulBinomial (n+1) (-1) (crankEuler w wi n)))

/-- Once the j=1 Euler factor is included, the q coefficient stabilizes at
w + wi − 1, where the inverse parameter for the actual crank is wi = w⁻¹. -/
theorem crankEuler_degree_one (w wi : R) (J : Nat) (hJ : 0 < J) :
    crankEuler w wi J 1 = w + wi - 1 := by
  induction J with
  | zero => omega
  | succ n ih =>
    cases n with
    | zero =>
      simp [crankEuler, MockTheta.divideBinomial, MockTheta.mulBinomial, MockTheta.shift,
        MockTheta.oneSeries]
      grind
    | succ n =>
      rw [crankEuler, MockTheta.divideBinomial_below _ _ _ _ _ (by omega),
        MockTheta.divideBinomial_below _ _ _ _ _ (by omega)]
      simp only [MockTheta.mulBinomial, MockTheta.shift, if_neg (show ¬ n+1+1 ≤ 1 by omega),
        Semiring.mul_zero, Semiring.add_zero]
      exact ih (by omega)

/-- The ordinary singleton partition's crank −1 gives class 10. In the
order-eleven evaluation, its actual character value differs from the analytic
Euler coefficient by w−1. The polynomial identity also holds for arbitrary w. -/
theorem crankEuler_minus_ordinary_degree_one (w : R) (J : Nat) (hJ : 0 < J) :
    crankEuler w (w^10) J 1 -
      CrankCharacter11.samplePair PartitionCrank11.crank w (PartitionCrank11.partitions 1) =
      w - 1 := by
  rw [crankEuler_degree_one w (w^10) J hJ]
  have hp : PartitionCrank11.partitions 1 = [[1]] := by decide +kernel
  rw [hp]
  change w + w^10 - 1 - (0 + w^10) = w - 1
  grind

end KElimination.QuantumRadial

#print axioms KElimination.QuantumRadial.uProduct_eq_pochhammer
#print axioms KElimination.QuantumRadial.uProduct_zero_of_le
#print axioms KElimination.QuantumRadial.uPolynomial_stable
#print axioms KElimination.QuantumRadial.boundaryValue_stable
#print axioms KElimination.QuantumRadial.twice_half_period
#print axioms KElimination.QuantumRadial.uPolynomial_as_degrees
#print axioms KElimination.QuantumRadial.uPacket_refinement
#print axioms KElimination.QuantumRadial.uPacket_evaluation
#print axioms KElimination.QuantumRadial.boundaryValue_from_packets
#print axioms KElimination.QuantumRadial.boundaryValue_from_coupled_anchors
#print axioms KElimination.QuantumRadial.boundaryValue_at_neg_one
#print axioms KElimination.QuantumRadial.boundaryValue_at_fourth_root
#print axioms KElimination.QuantumRadial.uTwoPartial_at_neg_one
#print axioms KElimination.QuantumRadial.rankCrankRhs_at_neg_one
#print axioms KElimination.QuantumRadial.pochhammer_one_succ
#print axioms KElimination.QuantumRadial.uTwoPartial_diagonal
#print axioms KElimination.QuantumRadial.rankCrankRhs_diagonal
#print axioms KElimination.QuantumRadial.rankCrankRhs_eleventh_root
#print axioms KElimination.QuantumRadial.crankEuler_degree_one
#print axioms KElimination.QuantumRadial.crankEuler_minus_ordinary_degree_one
