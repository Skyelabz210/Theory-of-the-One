import MockTheta

/-! Finite products and coefficient cutoffs used by both fifth-order groups. -/

namespace KElimination.FifthOrderSeries

open Lean.Grind KElimination.MockTheta KElimination.ResidueSeries

inductive Family where
  | f | phi | psi | chi | bigF
  deriving Repr, DecidableEq

universe u
variable {R : Type u} [CommRing R]

/-- Coefficient action of the product of (1 + u*q^(start + i*step))
over indices 0 ≤ i < length. The empty product acts as the identity. -/
def mulProduct (start step : Nat) : Nat → R → Series R → Series R
  | 0, _, a => a
  | k + 1, u, a => mulProduct start step k u (mulBinomial (start + step*k) u a)

/-- Reciprocal of the same finite product, whose factors all have positive stride. -/
def reciprocalProduct (start step : Nat) : Nat → (0 < start) → R → Series R
  | 0, _, _ => oneSeries
  | k + 1, hstart, u => divideBinomial (start + step*k) (by omega) u
      (reciprocalProduct start step k hstart u)

theorem mulProduct_reciprocalProduct (start step length : Nat) (hstart : 0 < start) (u : R) :
    mulProduct start step length u (reciprocalProduct start step length hstart u) = oneSeries := by
  induction length with
  | zero => rfl
  | succ k ih =>
    simpa only [mulProduct, reciprocalProduct, mulBinomial_divideBinomial] using ih

theorem mulProduct_injective (start step length : Nat) (hstart : 0 < start)
    (u : R) (a b : Series R) (hab : mulProduct start step length u a = mulProduct start step length u b) :
    a = b := by
  induction length generalizing a b with
  | zero => exact hab
  | succ k ih =>
    exact mulBinomial_injective (start + step*k) (by omega) u a b (ih _ _ hab)

theorem reciprocalProduct_unique (start step length : Nat) (hstart : 0 < start)
    (u : R) (a : Series R) (ha : mulProduct start step length u a = oneSeries) :
    a = reciprocalProduct start step length hstart u :=
  mulProduct_injective start step length hstart u _ _
    (ha.trans (mulProduct_reciprocalProduct start step length hstart u).symm)

theorem mulProduct_eq_one_iff (start step length : Nat) (hstart : 0 < start)
    (u : R) (a : Series R) :
    mulProduct start step length u a = oneSeries ↔ a = reciprocalProduct start step length hstart u := by
  constructor
  · exact reciprocalProduct_unique start step length hstart u a
  · rintro rfl
    exact mulProduct_reciprocalProduct start step length hstart u

def triangular (n : Nat) : Nat := n * (n + 1) / 2

theorem triangular_mono {i j : Nat} (h : i ≤ j) : triangular i ≤ triangular j :=
  Nat.div_le_div_right (Nat.mul_le_mul h (Nat.succ_le_succ h))

theorem le_triangular (n : Nat) : n ≤ triangular n := by
  cases n with
  | zero => decide
  | succ n =>
    have h := Nat.mul_le_mul_left (n + 1) (show 2 ≤ n + 1 + 1 by omega)
    unfold triangular
    omega

/-- The degree-d coefficient of the sum of the shifted factor series. -/
def shiftedCoeff (e : Nat → Nat) (factors : Nat → Series R) (d : Nat) : R :=
  sumBelow (d + 1) (fun n => shift (e n) (factors n) d)

/-- If shifts are nondecreasing and dominate the summand index, the shift at
the first omitted index bounds every omitted contribution. -/
theorem shiftedCoeff_stable (e : Nat → Nat) (factors : Nat → Series R)
    (hmono : ∀ i j, i ≤ j → e i ≤ e j) (hbound : ∀ n, n ≤ e n)
    (d N : Nat) (hN : d < e N) :
    sumBelow N (fun n => shift (e n) (factors n) d) = shiftedCoeff e factors d := by
  unfold shiftedCoeff
  rcases Nat.le_total N (d + 1) with h | h
  · symm
    apply sumBelow_eq_of_tail_zero _ _ _ h
    intro n hn _
    exact if_neg (Nat.not_le_of_lt (Nat.lt_of_lt_of_le hN (hmono N n hn)))
  · apply sumBelow_eq_of_tail_zero _ _ _ h
    intro n hn _
    exact if_neg (Nat.not_le_of_lt (Nat.lt_of_lt_of_le (by omega : d < n) (hbound n)))

end KElimination.FifthOrderSeries

#print axioms KElimination.FifthOrderSeries.mulProduct_reciprocalProduct
#print axioms KElimination.FifthOrderSeries.mulProduct_injective
#print axioms KElimination.FifthOrderSeries.reciprocalProduct_unique
#print axioms KElimination.FifthOrderSeries.mulProduct_eq_one_iff
#print axioms KElimination.FifthOrderSeries.triangular_mono
#print axioms KElimination.FifthOrderSeries.le_triangular
#print axioms KElimination.FifthOrderSeries.shiftedCoeff_stable
