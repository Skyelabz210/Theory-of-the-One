import ShadowReadings
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Field.ZMod
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Ring

/-! Coefficientwise derivation of the reciprocal Euler product from Ramanujan's f.
The marked odd product counts a selected part by one power of the marker.
Moving every selected odd part up by two gives the staircase recurrence. -/

namespace MockThetaAnalytic.ShadowParity

noncomputable section

open KElimination.MockTheta
open KElimination.ResidueSeries
open Finset PowerSeries
open scoped PowerSeries BigOperators

abbrev F := ZMod 2
abbrev Series := PowerSeries F
local notation "X" => (PowerSeries.X : Series)

private theorem neg_series (p : Series) : -p = p := by
  ext d
  simp

private theorem square_binomial (j : ℕ) : (1+X^j)^2 = 1+X^(2*j) := by
  have hz : X^j + X^j = 0 := by
    calc
      X^j + X^j = -(X^j) + X^j := congrArg (· + X^j) (neg_series _).symm
      _ = 0 := neg_add_cancel _
  calc
    _ = (1+X^(2*j)) + (X^j + X^j) := by rw [pow_mul, pow_two]; ring
    _ = _ := by rw [hz, add_zero]

private def dividedRow (n : ℕ) : Series :=
  PowerSeries.mk (inverseSquaredPochhammer n)

private def shiftedRow (n : ℕ) : Series := X^(n*n) * dividedRow n

private theorem mk_mulBinomial (j : ℕ) (a : ℕ → F) :
    PowerSeries.mk (mulBinomial j 1 a) = (1+X^j) * PowerSeries.mk a := by
  ext d
  simp [mulBinomial, shift, add_mul, coeff_X_pow_mul']

private theorem dividedRow_succ (n : ℕ) :
    (1+X^(2*(n+1))) * dividedRow (n+1) = dividedRow n := by
  rw [← square_binomial, pow_two, mul_assoc]
  unfold dividedRow
  rw [← mk_mulBinomial]
  simp only [inverseSquaredPochhammer, mulBinomial_divideBinomial]
  rw [← mk_mulBinomial, mulBinomial_divideBinomial]

private theorem shiftedRow_zero : shiftedRow 0 = 1 := by
  ext d
  simp [shiftedRow, dividedRow, inverseSquaredPochhammer, oneSeries, coeff_one]

private theorem shiftedRow_succ (n : ℕ) :
    shiftedRow (n+1) = X^(2*(n+1)) * shiftedRow (n+1) + X^(2*n+1) * shiftedRow n := by
  have he : (n+1)*(n+1) = (2*n+1)+n*n := by ring
  have hx : shiftedRow (n+1) + X^(2*(n+1)) * shiftedRow (n+1) =
      X^(2*n+1) * shiftedRow n := by
    calc
      _ = X^((n+1)*(n+1)) * ((1+X^(2*(n+1))) * dividedRow (n+1)) := by
        unfold shiftedRow
        ring
      _ = X^((n+1)*(n+1)) * dividedRow n := by rw [dividedRow_succ]
      _ = _ := by rw [shiftedRow, ← mul_assoc, ← pow_add, he]
  calc
    _ = X^(2*n+1) * shiftedRow n - X^(2*(n+1)) * shiftedRow (n+1) := eq_sub_of_add_eq hx
    _ = _ := by rw [sub_eq_add_neg, neg_series, add_comm]

private def oddPolynomial (n : ℕ) : Polynomial Series :=
  ∏ j ∈ range n, (1 + Polynomial.C (X^(2*j+1)) * Polynomial.X)

private theorem oddPolynomial_succ (n : ℕ) :
    oddPolynomial (n+1) = (1 + Polynomial.C X * Polynomial.X) *
      (oddPolynomial n).comp (Polynomial.C (X^2) * Polynomial.X) := by
  unfold oddPolynomial
  rw [prod_range_succ', mul_comm]
  simp only [Nat.mul_zero, zero_add, pow_one, Polynomial.prod_comp, Polynomial.add_comp,
    Polynomial.one_comp, Polynomial.mul_comp, Polynomial.C_comp, Polynomial.X_comp]
  congr 1
  apply prod_congr rfl
  intro j _
  rw [show 2*(j+1)+1 = (2*j+1)+2 by omega, pow_add, Polynomial.C_mul, mul_assoc]

private theorem oddPolynomial_constant (n : ℕ) : (oddPolynomial n).coeff 0 = 1 := by
  induction n with
  | zero => simp [oddPolynomial]
  | succ n ih =>
    rw [oddPolynomial_succ]
    simp only [add_mul, one_mul, Polynomial.coeff_add, mul_assoc, Polynomial.coeff_C_mul,
      Polynomial.coeff_X_mul_zero, mul_zero, add_zero, Polynomial.comp_C_mul_X_coeff,
      pow_zero, mul_one, ih]

private theorem oddPolynomial_next (n k : ℕ) :
    (oddPolynomial (n+1)).coeff (k+1) =
      X^(2*(k+1)) * (oddPolynomial n).coeff (k+1) + X^(2*k+1) * (oddPolynomial n).coeff k := by
  rw [oddPolynomial_succ]
  simp only [add_mul, one_mul, Polynomial.coeff_add, mul_assoc, Polynomial.coeff_C_mul,
    Polynomial.coeff_X_mul, Polynomial.comp_C_mul_X_coeff, ← pow_mul]
  rw [pow_succ' X (2*k)]
  ring

private theorem oddPolynomial_eq_row (n d k : ℕ) (hd : d < n) :
    coeff d ((oddPolynomial n).coeff k) = coeff d (shiftedRow k) := by
  induction n generalizing d k with
  | zero => omega
  | succ n ih =>
    cases k with
    | zero => rw [oddPolynomial_constant, shiftedRow_zero]
    | succ k =>
      rw [oddPolynomial_next, shiftedRow_succ]
      simp only [map_add, coeff_X_pow_mul']
      split_ifs <;> (try congr 1) <;> (try apply ih) <;> omega

private theorem oddPolynomial_natDegree_le (n : ℕ) : (oddPolynomial n).natDegree ≤ n := by
  induction n with
  | zero => simp [oddPolynomial]
  | succ n ih =>
    rw [oddPolynomial, prod_range_succ, ← oddPolynomial]
    refine (Polynomial.natDegree_mul_le.trans (add_le_add ih ?_))
    exact (Polynomial.natDegree_add_le _ _).trans
      (max_le (by simp) (by simpa only [pow_one] using
        Polynomial.natDegree_C_mul_X_pow_le (X^(2*n+1)) 1))

private def oddProduct (n : ℕ) : Series := ∏ j ∈ range n, (1+X^(2*j+1))

private theorem eval_oddPolynomial (n : ℕ) : (oddPolynomial n).eval 1 = oddProduct n := by
  simp [oddPolynomial, oddProduct, Polynomial.eval_prod]

private theorem coeff_shiftedRow (n d : ℕ) : coeff d (shiftedRow n) = (mockSummand n d : F) := by
  rw [shiftedRow, coeff_X_pow_mul']
  simp [dividedRow, mockSummand, shift]

private theorem sumBelow_range (a : ℕ → F) (n : ℕ) :
    sumBelow n a = ∑ j ∈ range n, a j := by
  induction n with
  | zero => simp [sumBelow]
  | succ n ih => simp [sumBelow, sum_range_succ, ih]

theorem coeff_oddProduct (d n : ℕ) (hd : d < n) :
    coeff d (oddProduct n) = (mockCoeff d : F) := by
  rw [← eval_oddPolynomial, Polynomial.eval_eq_sum_range]
  simp only [one_pow, mul_one, map_sum]
  -- Extend to n+1 using the polynomial degree bound.
  have hext : ∑ k ∈ range ((oddPolynomial n).natDegree+1), coeff d ((oddPolynomial n).coeff k) =
      ∑ k ∈ range (n+1), coeff d ((oddPolynomial n).coeff k) := by
    apply Finset.sum_subset (range_mono (Nat.succ_le_succ (oddPolynomial_natDegree_le n)))
    intro k _ hk
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by simpa using hk), map_zero]
  rw [hext]
  simp_rw [oddPolynomial_eq_row n d _ hd, coeff_shiftedRow]
  rw [← sumBelow_range, mockCoeff_stable d (n+1) (by omega)]

def eulerProduct (n : ℕ) : Series := ∏ j ∈ range n, (1+X^(j+1))

private theorem euler_succ (n : ℕ) : eulerProduct (n+1) = eulerProduct n * (1+X^(n+1)) :=
  prod_range_succ _ _

private theorem odd_succ (n : ℕ) : oddProduct (n+1) = oddProduct n * (1+X^(2*n+1)) :=
  prod_range_succ _ _

private theorem euler_constant (n : ℕ) : constantCoeff (eulerProduct n) = 1 := by
  simp [eulerProduct, map_prod, map_pow]

private theorem euler_double (n : ℕ) :
    eulerProduct (2*n) = oddProduct n * eulerProduct n ^ 2 := by
  induction n with
  | zero => simp [eulerProduct, oddProduct]
  | succ n ih =>
    rw [show 2*(n+1)=2*n+1+1 by omega, euler_succ (2*n+1), euler_succ (2*n),
      ih, odd_succ, euler_succ n, mul_pow, square_binomial,
      show 2*n+1+1=2*(n+1) by omega]
    ring

private theorem euler_grow {n N d : ℕ} (h : d ≤ n) (hn : n ≤ N) :
    coeff d (eulerProduct N) = coeff d (eulerProduct n) := by
  rw [← Nat.add_sub_of_le hn, eulerProduct, prod_range_add, ← eulerProduct]
  simp_rw [← sub_neg_eq_add, neg_series (X ^ _)]
  apply coeff_mul_prod_one_sub_of_lt_order
  intro i _
  rw [order_X_pow]
  exact_mod_cast (show d < n+i+1 by omega)

private def AgreesThrough (d : ℕ) (p q : Series) : Prop :=
  ∀ i ≤ d, coeff i p = coeff i q

private theorem agrees_mul_left {d : ℕ} {p q : Series} (f : Series) (h : AgreesThrough d p q) :
    AgreesThrough d (f*p) (f*q) := by
  intro i hi
  simp only [coeff_mul]
  apply sum_congr rfl
  intro ij hij
  have he := Finset.mem_antidiagonal.mp hij
  rw [h ij.2 (by omega)]

private theorem euler_times_odd (d n : ℕ) (hd : d ≤ n) :
    AgreesThrough d (oddProduct n * eulerProduct n) 1 := by
  have h : AgreesThrough d (eulerProduct (2*n)) (eulerProduct n) :=
    fun i hi => euler_grow (hi.trans hd) (by omega)
  rw [euler_double] at h
  have h' := agrees_mul_left (eulerProduct n)⁻¹ h
  have unit : (eulerProduct n)⁻¹ * eulerProduct n = 1 :=
    PowerSeries.inv_mul_cancel _ (by simp [euler_constant])
  have hm : (eulerProduct n)⁻¹ * (oddProduct n * eulerProduct n ^ 2) =
      oddProduct n * eulerProduct n := by
    calc
      _ = (oddProduct n * eulerProduct n) * ((eulerProduct n)⁻¹ * eulerProduct n) := by ring
      _ = _ := by rw [unit, mul_one]
  rw [hm, unit] at h'
  exact h'

private def mockPowerSeries : Series := PowerSeries.mk (fun d => mockCoeff d)

theorem coeff_euler_mul_mock (d n : ℕ) (hd : d < n) :
    coeff d (mockPowerSeries * eulerProduct n) = coeff d (1 : Series) := by
  have h : AgreesThrough d (oddProduct n) mockPowerSeries :=
    fun i hi => by simpa [mockPowerSeries] using coeff_oddProduct i n (hi.trans_lt hd)
  have hm := agrees_mul_left (eulerProduct n) h d le_rfl
  rw [mul_comm (eulerProduct n), mul_comm (eulerProduct n)] at hm
  exact hm.symm.trans (euler_times_odd d n hd.le d le_rfl)

private theorem cast_divide (j : ℕ) (hj : 0 < j) (a : ℕ → ℤ) (d : ℕ) :
    ((divideBinomial j hj 1 a d : ℤ) : F) = divideBinomial j hj 1 (fun i => (a i : F)) d := by
  induction d using Nat.strong_induction_on with
  | h d ih =>
    by_cases hd : j ≤ d
    · rw [divideBinomial_at_or_above j hj 1 a d hd,
        divideBinomial_at_or_above j hj 1 (fun i => (a i : F)) d hd,
        one_mul, one_mul, Int.cast_sub, ih _ (by omega)]
    · rw [divideBinomial_below j hj 1 a d (by omega),
        divideBinomial_below j hj 1 (fun i => (a i : F)) d (by omega)]

private theorem cast_row (n d : ℕ) :
    ((inverseSquaredPochhammer n d : ℤ) : F) = inverseSquaredPochhammer n d := by
  induction n generalizing d with
  | zero => simp only [inverseSquaredPochhammer, oneSeries]; split <;> simp
  | succ n ih =>
    simp only [inverseSquaredPochhammer, cast_divide, ih]

private theorem cast_summand (n d : ℕ) : ((mockSummand n d : ℤ) : F) = mockSummand n d := by
  unfold mockSummand shift
  split <;> simp [cast_row]

theorem signed_coeff_parity (d : ℕ) : ((mockCoeff d : ℤ) : F) = (mockCoeff d : F) := by
  unfold mockCoeff
  generalize d+1 = N
  induction N with
  | zero => simp [sumBelow]
  | succ N ih => simp only [sumBelow, Int.cast_add, ih, cast_summand]

theorem reciprocal_euler (d n : ℕ) (hd : d < n) :
    ShadowReadings.reciprocalBit (fun i => ((mockCoeff i : ℤ) : F)) d =
      coeff d (eulerProduct n) := by
  induction d using Nat.strong_induction_on with
  | h d ih =>
    cases d with
    | zero => simp [ShadowReadings.reciprocalBit_zero, coeff_zero_eq_constantCoeff, euler_constant]
    | succ d =>
      rw [ShadowReadings.reciprocalBit_succ]
      have hmul := coeff_euler_mul_mock (d+1) n hd
      rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun i j => coeff i mockPowerSeries * coeff j (eulerProduct n)),
        Finset.sum_range_succ'] at hmul
      have h0 : (mockCoeff 0 : F) = 1 := by decide
      simp only [mockPowerSeries, coeff_mk, h0, Nat.sub_zero, one_mul, coeff_one,
        Nat.succ_ne_zero, if_false] at hmul
      have hsum := congrArg (fun x : F => x - coeff (d+1) (eulerProduct n)) hmul
      simp only [add_sub_cancel_right, zero_sub, ZMod.neg_eq_self_mod_two] at hsum
      rw [← hsum]
      apply sum_congr rfl
      intro i hi
      have hi := mem_range.mp hi
      rw [signed_coeff_parity, ih _ (by omega) (by omega)]
      simp only [Nat.add_sub_add_right]

end
end MockThetaAnalytic.ShadowParity
