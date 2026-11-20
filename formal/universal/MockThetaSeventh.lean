import FifthOrderSeries

/-!
The three seventh-order mock theta functions in Ramanujan's last letter.
Bin Chen, “Mock theta functions and Appell–Lerch sums”, (3.46)–(3.48).
In each product the factors are (1 − q^j). Using indices n ≥ 0 throughout:

  ℱ₀: q^(n²)       / ∏_{j=n+1}^{2n}   (1 − q^j)
  ℱ₁: q^((n+1)²)   / ∏_{j=n+1}^{2n+1} (1 − q^j)
  ℱ₂: q^(n(n+1))   / ∏_{j=n+1}^{2n+1} (1 − q^j).

The ℱ₁ index n corresponds to index n+1 in the sum beginning at one.
-/

namespace KElimination.MockThetaSeventh

open Lean.Grind KElimination.MockTheta
open KElimination.FifthOrderSeries (mulProduct reciprocalProduct mulProduct_eq_one_iff
  shiftedCoeff shiftedCoeff_stable)
open KElimination.ResidueSeries KElimination.ProfiniteObservations KElimination.CoefficientObservations

inductive Family where
  | f0 | f1 | f2
  deriving Repr, DecidableEq

universe u
variable {R : Type u} [CommRing R]

def exponent : Family → Nat → Nat
  | .f0, n => n * n
  | .f1, n => (n + 1) * (n + 1)
  | .f2, n => n * (n + 1)

theorem exponent_mono (s : Family) (i j : Nat) (h : i ≤ j) : exponent s i ≤ exponent s j := by
  cases s with
  | f0 => exact Nat.mul_le_mul h h
  | f1 => exact Nat.mul_le_mul (Nat.succ_le_succ h) (Nat.succ_le_succ h)
  | f2 => exact Nat.mul_le_mul h (Nat.succ_le_succ h)

theorem le_exponent (s : Family) (n : Nat) : n ≤ exponent s n := by
  cases s with
  | f0 => exact Nat.le_mul_self n
  | f1 => exact Nat.le_trans (Nat.le_succ n) (Nat.le_mul_self (n + 1))
  | f2 => simp [exponent, Nat.mul_succ]

/-- Number of consecutive factors starting at degree n+1. -/
def factorCount : Family → Nat → Nat
  | .f0, n => n
  | .f1, n | .f2, n => n + 1

def factors (s : Family) (n : Nat) : Series R :=
  reciprocalProduct (n + 1) 1 (factorCount s n) (by omega) (-1)

theorem denominator_iff (s : Family) (n : Nat) (a : Series R) :
    mulProduct (n + 1) 1 (factorCount s n) (-1) a = oneSeries ↔ a = factors s n :=
  mulProduct_eq_one_iff (n + 1) 1 (factorCount s n) (by omega) (-1) a

theorem factors_constant (s : Family) (n : Nat) : (factors s n 0 : R) = 1 := by
  unfold factors
  induction factorCount s n with
  | zero => simp [reciprocalProduct, oneSeries]
  | succ k ih =>
    unfold reciprocalProduct
    rw [divideBinomial_below _ _ _ _ _ (by omega)]
    exact ih

def summand (s : Family) (n d : Nat) : R := shift (exponent s n) (factors s n) d

theorem summand_support (s : Family) (n d : Nat) (h : d < exponent s n) :
    (summand s n d : R) = 0 :=
  if_neg (Nat.not_le_of_lt h)

theorem summand_at_leading_degree (s : Family) (n : Nat) :
    (summand s n (exponent s n) : R) = 1 := by
  simp [summand, shift, factors_constant]

/-- The reindexed ℱ₁ term and the ℱ₂ term share their denominator. The extra
numerator power in ℱ₁ shifts the coefficient at d to d+n+1. -/
theorem f1_summand_eq_f2_shift (n d : Nat) :
    (summand .f1 n (d + (n + 1)) : R) = summand .f2 n d := by
  simp only [summand, shift, exponent, Nat.succ_mul, Nat.add_le_add_iff_right, Nat.add_sub_add_right]
  rfl

theorem f0_summand_at_index_zero (d : Nat) : (summand .f0 0 d : R) = oneSeries d := by
  simp [summand, shift, exponent, factors, factorCount, reciprocalProduct]

theorem f2_summand_at_index_zero (d : Nat) : (summand .f2 0 d : R) = 1 := by
  have h : (fun _ : Nat => (1 : R)) = factors .f2 0 := by
    apply (denominator_iff .f2 0 _).mp
    funext k
    cases k <;> simp [factorCount, mulProduct, mulBinomial, oneSeries, shift] <;> grind
  simpa [summand, exponent, shift] using (congrFun h d).symm

/-- The reindexed first term of ℱ₁ is q/(1−q). -/
theorem f1_summand_at_index_zero (d : Nat) :
    (summand .f1 0 d : R) = (if d = 0 then 0 else 1) := by
  cases d with
  | zero => exact summand_support .f1 0 0 (by decide)
  | succ d =>
    rw [f1_summand_eq_f2_shift 0 d, f2_summand_at_index_zero]
    simp

def coeff (s : Family) (d : Nat) : R := shiftedCoeff (exponent s) (factors s) d

abbrev f0Coeff (d : Nat) : R := coeff .f0 d
abbrev f1Coeff (d : Nat) : R := coeff .f1 d
abbrev f2Coeff (d : Nat) : R := coeff .f2 d

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

end KElimination.MockThetaSeventh

#print axioms KElimination.MockThetaSeventh.exponent_mono
#print axioms KElimination.MockThetaSeventh.le_exponent
#print axioms KElimination.MockThetaSeventh.denominator_iff
#print axioms KElimination.MockThetaSeventh.factors_constant
#print axioms KElimination.MockThetaSeventh.summand_support
#print axioms KElimination.MockThetaSeventh.summand_at_leading_degree
#print axioms KElimination.MockThetaSeventh.f1_summand_eq_f2_shift
#print axioms KElimination.MockThetaSeventh.f0_summand_at_index_zero
#print axioms KElimination.MockThetaSeventh.f2_summand_at_index_zero
#print axioms KElimination.MockThetaSeventh.f1_summand_at_index_zero
#print axioms KElimination.MockThetaSeventh.coeff_stable
#print axioms KElimination.MockThetaSeventh.degreePacket_refinement
#print axioms KElimination.MockThetaSeventh.cylinder_observable
#print axioms KElimination.MockThetaSeventh.cylinder_refinement
#print axioms KElimination.MockThetaSeventh.weightedPacket_refinement
#print axioms KElimination.MockThetaSeventh.finite_root_evaluation
#print axioms KElimination.MockThetaSeventh.from_coupled_anchors
