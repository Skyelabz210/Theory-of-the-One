import FORWatsonCongruence
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Data.Nat.Factorization.Basic

/-! The first two derivatives at −1 of the Watson congruence and the
resulting root multiplicities after coefficient reduction. -/

noncomputable section
namespace MockThetaAnalytic

open Finset Polynomial KElimination.QuantumRadial KElimination.ResidueSeries

variable {R : Type*} [CommRing R]

private theorem second_derivative_mul_at_neg_one (P Q : R[X]) :
    (P*Q).derivative.derivative.eval (-1) =
      P.derivative.derivative.eval (-1)*Q.eval (-1) +
      2*P.derivative.eval (-1)*Q.derivative.eval (-1) +
      P.eval (-1)*Q.derivative.derivative.eval (-1) := by
  simp only [derivative_mul, derivative_add, eval_add, eval_mul]
  ring

private theorem second_derivative_neg_X_pow_at_neg_one (m : ℕ) :
    ((-X : R[X])^m).derivative.derivative.eval (-1) = (m:R)*(m-1) := by
  cases m with
  | zero => simp
  | succ n =>
    simp [derivative_pow, derivative_mul]

private theorem watsonClearedNumerator_succ (x : R) (c n : ℕ) :
    watsonClearedNumerator x c (n+1) =
      (watsonClearedNumerator x c n + (-x)^(n^2)) * (1+x^(2*n+c)) := by
  simp only [watsonClearedNumerator, sum_range_succ, Nat.Ico_succ_singleton, prod_singleton]
  rw [add_mul, sum_mul]
  congr 1
  apply sum_congr rfl
  intro j hj
  rw [prod_Ico_succ_top (mem_range.mp hj).le, mul_assoc]

-- Replacing U by X preserves its value and derivative at −1. This
-- expression also has a recurrence at every length of the c=2 progression.
private def oddLinearDifference (R : Type*) [CommRing R] (n : ℕ) : R[X] :=
  watsonClearedNumerator X 2 n + 2*(watsonDen X 2 n-1)*X

private theorem oddLinearDifference_succ (n : ℕ) :
    oddLinearDifference R (n+1) =
      (oddLinearDifference R n + (-X)^(n^2) + 2*X)*(1+X^(2*n+2)) - 2*X := by
  simp only [oddLinearDifference, watsonClearedNumerator_succ, watsonDen, prod_range_succ]
  ring

private theorem oddLinearDifference_at_neg_one (n : ℕ) :
    (oddLinearDifference R n).eval (-1) = 0 ∧
      (oddLinearDifference R n).derivative.eval (-1) = 2*(n:R)*(n+1) ∧
      (oddLinearDifference R n).derivative.derivative.eval (-1) =
        12*((2:R)^n-1) - 2*(n:R)*((n:R)^3+2*(n:R)^2+3*n+5) := by
  induction n with
  | zero => simp [oddLinearDifference, watsonClearedNumerator, watsonDen]
  | succ n ih =>
    have he : Even (2*n+2) := ⟨n+1, by omega⟩
    have ho : Odd (2*n+2-1) := ⟨n, by omega⟩
    have hf : (1+X^(2*n+2) : R[X]).eval (-1) = 2 := by norm_num [he.neg_one_pow]
    have hf' : (1+X^(2*n+2) : R[X]).derivative.eval (-1) = -(2*(n:R)+2) := by
      rw [derivative_add, derivative_one, zero_add, derivative_X_pow, eval_mul, eval_C,
        eval_pow, eval_X, ho.neg_one_pow]
      push_cast
      ring
    have hn' : ((-X : R[X])^(n^2)).derivative.eval (-1) = -(n:R)^2 := by
      simp [derivative_pow]
    have hn'' : ((-X : R[X])^(n^2)).derivative.derivative.eval (-1) =
        (n:R)^2*((n:R)^2-1) := by
      rw [second_derivative_neg_X_pow_at_neg_one, Nat.cast_pow]
    have hf'' : (1+X^(2*n+2) : R[X]).derivative.derivative.eval (-1) =
        (2*(n:R)+2)*(2*(n:R)+1) := by
      rw [derivative_add, derivative_one, zero_add, ← he.neg_pow (X : R[X]),
        second_derivative_neg_X_pow_at_neg_one]
      push_cast
      ring
    refine ⟨?_, ?_, ?_⟩
    · rw [oddLinearDifference_succ, eval_sub, eval_mul, hf]
      simp [ih.1]
      ring
    · rw [oddLinearDifference_succ, derivative_sub, derivative_mul, eval_sub, eval_add,
        eval_mul, hf, eval_mul, hf']
      simp [ih.1, ih.2.1, hn']
      ring
    · rw [oddLinearDifference_succ, derivative_sub, derivative_sub, eval_sub,
        second_derivative_mul_at_neg_one, hf, hf', hf'']
      simp only [derivative_add, eval_add, ih.1, ih.2.1, ih.2.2, hn', hn'',
        eval_pow, eval_neg, eval_X, neg_neg, one_pow]
      simp [pow_succ (2:R) n]
      ring

private theorem uPartial_at_neg_one_first_order {k : ℕ} (hk : 0 < k) :
    (uPartial k (X : R[X])).eval (-1) = -1 ∧
      (uPartial k (X : R[X])).derivative.eval (-1) = 1 := by
  have hp (n : ℕ) : (uProduct (X : R[X]) (n+1)).eval (-1) = 0 ∧
      (uProduct (X : R[X]) (n+1)).derivative.eval (-1) = 0 := by
    induction n with
    | zero => simp [uProduct, derivative_pow]
    | succ n ih =>
      rw [uProduct]
      simp [ih.1, ih.2]
  cases k with
  | zero => omega
  | succ n =>
    induction n with
    | zero => simp [uPartial, uPolynomial, sumBelow, uProduct]
    | succ n ih =>
      have h := ih (Nat.succ_pos n)
      change (uPartial (n+1) X + uProduct X (n+1)*X^(n+2) : R[X]).eval (-1) = -1 ∧
        (uPartial (n+1) X + uProduct X (n+1)*X^(n+2) : R[X]).derivative.eval (-1) = 1
      simp [h.1, h.2, (hp n).1, (hp n).2]

private theorem watson_odd_difference_eq {k : ℕ} (hk : Odd k) :
    watsonCongruenceDifference k (X : R[X]) = oddLinearDifference R k +
      2*(watsonDen X 2 k-1)*(uPartial k X-X) := by
  simp only [watsonCongruenceDifference, if_neg (Nat.not_even_iff_odd.mpr hk), oddLinearDifference]
  ring

/-- For odd k the formal derivative of the unreduced difference at −1 is 2k(k+1). -/
theorem watson_derivative_at_neg_one {k : ℕ} (hk : Odd k) :
    (watsonCongruenceDifference k (X : R[X])).derivative.eval (-1) = 2*(k:R)*(k+1) := by
  have hu := uPartial_at_neg_one_first_order (R := R) hk.pos
  rw [watson_odd_difference_eq hk]
  simp [hu.1, hu.2, (oddLinearDifference_at_neg_one (R := R) k).2.1]

/-- At even positive k, only the last term of the cleared numerator
and the linear term of the unimodal polynomial contribute to the slope. -/
theorem watson_derivative_at_neg_one_of_even {k : ℕ} (hk : 0 < k) (he : Even k) :
    (watsonCongruenceDifference k (X : R[X])).derivative.eval (-1) = 2*(k:R) := by
  have hF (n : ℕ) : (1+X^(2*n+1) : R[X]).eval (-1) = 0 := by
    have hOdd : Odd (2*n+1) := ⟨n, rfl⟩
    simp [hOdd.neg_one_pow]
  obtain ⟨n, rfl⟩ : ∃ n, k = n+2 := by
    obtain ⟨m, hm⟩ := he
    exact ⟨k-2, by omega⟩
  have hD : (watsonDen (X : R[X]) 1 (n+2)).eval (-1) = 0 := by
    rw [watsonDen, prod_range_succ, eval_mul, hF (n+1), mul_zero]
  have hW : (watsonClearedNumerator (X : R[X]) 1 (n+1)).eval (-1) = 0 := by
    rw [watsonClearedNumerator_succ, eval_mul, hF n, mul_zero]
  have hW' : (watsonClearedNumerator (X : R[X]) 1 (n+2)).derivative.eval (-1) =
      2*(n:R)+3 := by
    rw [show n+2=n+1+1 by rfl, watsonClearedNumerator_succ, derivative_mul]
    simp [hW, hF (n+1)]
    ring
  have hU := uPartial_at_neg_one_first_order (R := R) hk
  rw [watsonCongruenceDifference, if_pos he, if_pos he, derivative_sub, eval_sub, hW']
  simp [hD, hU.1, hU.2]
  ring

private theorem uPartial_second_derivative_at_neg_one {k : ℕ} (hk : 3 ≤ k) :
    (uPartial k (X : R[X])).derivative.derivative.eval (-1) = -6 := by
  have hp (n : ℕ) : (uProduct (X : R[X]) (n+3)).eval (-1) = 0 ∧
      (uProduct (X : R[X]) (n+3)).derivative.eval (-1) = 0 ∧
      (uProduct (X : R[X]) (n+3)).derivative.derivative.eval (-1) = 0 := by
    induction n with
    | zero => norm_num [uProduct, derivative_pow]
    | succ n ih =>
      rw [show n.succ+3=n+3+1 by omega, uProduct]
      simp [ih.1, ih.2.1, ih.2.2]
  obtain ⟨n, rfl⟩ : ∃ n, k = n+3 := ⟨k-3, by omega⟩
  induction n with
  | zero => norm_num [uPartial, uPolynomial, sumBelow, uProduct, derivative_pow]
  | succ n ih =>
    change ((uPartial (n+3) X + uProduct X (n+3)*X^(n+4)) : R[X]).derivative.derivative.eval (-1) = -6
    simp [ih (by omega), (hp n).1, (hp n).2.1, (hp n).2.2]

/-- For odd k ≥ 3 the second formal derivative at −1, in any coefficient ring. -/
theorem watson_second_derivative_at_neg_one {k : ℕ} (hk : Odd k) (hk3 : 3 ≤ k) :
    (watsonCongruenceDifference k (X : R[X])).derivative.derivative.eval (-1) =
      -2*(k:R)*((k:R)^3+2*(k:R)^2+3*k+5) := by
  have hD : (watsonDen (X : R[X]) 2 k).eval (-1) = (2:R)^k := by
    simp only [watsonDen, eval_prod, eval_add, eval_one, eval_pow, eval_X]
    calc
      _ = ∏ _ ∈ range k, (2:R) := by
        apply prod_congr rfl
        intro j _
        have he : Even (2*j+2) := ⟨j+1, by omega⟩
        rw [he.neg_one_pow, one_add_one_eq_two]
      _ = _ := by simp
  have hu := uPartial_at_neg_one_first_order (R := R) hk.pos
  rw [watson_odd_difference_eq hk, derivative_add, derivative_add, eval_add, second_derivative_mul_at_neg_one]
  simp [hu.1, hu.2, uPartial_second_derivative_at_neg_one (R := R) hk3, hD,
    (oddLinearDifference_at_neg_one (R := R) k).2.2]
  ring

/-- The integer quotient from monic division by Xᵏ+1 at positive half-periods. -/
def watsonQuotient (k : ℕ) : ℤ[X] :=
  watsonCongruenceDifference k X /ₘ (X^k+1)

theorem watson_quotient_spec {k : ℕ} (hk : 0 < k) :
    watsonCongruenceDifference k (X : ℤ[X]) = (X^k+1)*watsonQuotient k := by
  have hm : (X^k+1 : ℤ[X]).Monic := by simpa using monic_X_pow_add_C (1:ℤ) hk.ne'
  have h := modByMonic_add_div (watsonCongruenceDifference k X) hm
  rw [(modByMonic_eq_zero_iff_dvd hm).mpr (watson_polynomial_congruence k), zero_add] at h
  exact h.symm

private theorem derivative_half_period_at_neg_one {k : ℕ} (hk : Odd k) :
    (X^k+1 : R[X]).derivative.eval (-1) = (k:R) := by
  have he : Even (k-1) := by obtain ⟨j,rfl⟩ := hk; exact ⟨j, by omega⟩
  simp [derivative_X_pow, he.neg_one_pow]

/-- For a positive even h and odd s, the cofactor of Xˢ+1 in the Watson
difference at half-period hs has integer value 2h at −1. -/
theorem watson_even_quotient_at_neg_one {h s : ℕ} (hh : 0 < h) (he : Even h) (hs : Odd s) :
    ∃ Q : ℤ[X], watsonCongruenceDifference (h*s) X = (X^s+1)*Q ∧ Q.eval (-1) = 2*(h:ℤ) := by
  have hk := Nat.mul_pos hh hs.pos
  have hkEven := he.mul_right s
  obtain ⟨Q, hQ⟩ := watson_even_polynomial_congruence hk hkEven hs (dvd_mul_left s h)
  have hderiv := watson_derivative_at_neg_one_of_even (R := ℤ) hk hkEven
  rw [hQ, derivative_mul, eval_add, eval_mul, derivative_half_period_at_neg_one hs] at hderiv
  simp only [eval_mul, eval_add, eval_pow, eval_X, hs.neg_one_pow, eval_one,
    neg_add_cancel, zero_mul, add_zero, Nat.cast_mul] at hderiv
  refine ⟨Q,hQ,?_⟩
  have hs0 : (s:ℤ) ≠ 0 := by exact_mod_cast hs.pos.ne'
  apply mul_left_cancel₀ hs0
  linear_combination hderiv

/-- The cofactor has the exact integer value 2(k+1) at −1 for every odd k. -/
theorem watson_quotient_at_neg_one {k : ℕ} (hk : Odd k) :
    (watsonQuotient k).eval (-1) = 2*((k:ℤ)+1) := by
  have h := watson_derivative_at_neg_one (R := ℤ) hk
  rw [watson_quotient_spec hk.pos, derivative_mul, eval_add, eval_mul, derivative_half_period_at_neg_one hk] at h
  simp only [eval_mul, eval_add, eval_pow, eval_X, hk.neg_one_pow, eval_one, add_zero,
    neg_add_cancel, zero_mul] at h
  have hk0 : (k:ℤ) ≠ 0 := by exact_mod_cast hk.pos.ne'
  apply mul_left_cancel₀ hk0
  linear_combination h

/-- The integer quotient's linear Taylor coefficient for odd k ≥ 3. -/
theorem watson_quotient_derivative_at_neg_one {k : ℕ} (hk : Odd k) (hk3 : 3 ≤ k) :
    (watsonQuotient k).derivative.eval (-1) = -((k:ℤ)^3+(k:ℤ)^2+3*(k:ℤ)+6) := by
  have hA : (X^k+1 : ℤ[X]).derivative.derivative.eval (-1) = -(k:ℤ)*((k:ℤ)-1) := by
    have h := second_derivative_neg_X_pow_at_neg_one (R := ℤ) k
    rw [hk.neg_pow, derivative_neg, derivative_neg, eval_neg] at h
    simp only [derivative_add, derivative_one, add_zero]
    linear_combination -h
  have h := watson_second_derivative_at_neg_one (R := ℤ) hk hk3
  rw [watson_quotient_spec hk.pos, second_derivative_mul_at_neg_one, hA,
    derivative_half_period_at_neg_one hk, watson_quotient_at_neg_one hk] at h
  simp only [eval_add, eval_pow, eval_X, hk.neg_one_pow, eval_one, neg_add_cancel, zero_mul, add_zero] at h
  have hk0 : (2*(k:ℤ)) ≠ 0 := mul_ne_zero (by decide) (by exact_mod_cast hk.pos.ne')
  apply mul_left_cancel₀ hk0
  linear_combination h

private theorem map_watson_quotient_spec {k : ℕ} (hk : 0 < k) :
    watsonCongruenceDifference k (X : R[X]) = (X^k+1)*(watsonQuotient k).map (Int.castRingHom R) := by
  let f := mapRingHom (Int.castRingHom R)
  have h := congrArg f (watson_quotient_spec hk)
  rw [map_watsonCongruenceDifference, map_mul, map_add, map_pow, map_one] at h
  simpa [f] using h

private theorem map_watson_quotient_eval {k : ℕ} (hk : Odd k) :
    ((watsonQuotient k).map (Int.castRingHom R)).eval (-1) = 2*((k:R)+1) := by
  let f := Int.castRingHom R
  calc
    _ = ((watsonQuotient k).map f).eval (f (-1)) := by simp [f]
    _ = f ((watsonQuotient k).eval (-1)) := eval_map_apply ..
    _ = _ := by rw [watson_quotient_at_neg_one hk]; simp [f]

/-- After removing the universal divisor, the remaining polynomial is
divisible by X+1 precisely when 2(k+1) vanishes in the coefficient ring. -/
theorem watson_extra_linear_factor_iff {k : ℕ} (hk : Odd k) :
    (X^k+1)*(X+1 : R[X]) ∣ watsonCongruenceDifference k X ↔ 2*((k:R)+1) = 0 := by
  have hm : (X^k+1 : R[X]).Monic := by simpa using monic_X_pow_add_C (1:R) hk.pos.ne'
  rw [map_watson_quotient_spec hk.pos, hm.isRegular.1.dvd_cancel_left,
    show (X+1 : R[X]) = X-C (-1) by simp, dvd_iff_isRoot, IsRoot.def, map_watson_quotient_eval hk]

private theorem watson_isRoot_neg_one_of_odd {k : ℕ} (hk : Odd k) :
    (watsonCongruenceDifference k (X : R[X])).IsRoot (-1) := by
  change (watsonCongruenceDifference k (X : R[X])).eval (-1) = 0
  rw [map_watson_quotient_spec hk.pos]
  simp [hk.neg_one_pow]

/-- A nonzero first derivative gives a simple root, also over residue rings
with zero divisors. -/
theorem watson_rootMultiplicity_one_of_nonzero_slope {k : ℕ} (hk : Odd k)
    (hs : 2*(k:R)*(k+1) ≠ 0) :
    (watsonCongruenceDifference k (X : R[X])).rootMultiplicity (-1) = 1 := by
  let P := watsonCongruenceDifference k (X : R[X])
  have hd : P.derivative.eval (-1) ≠ 0 := by
    change (watsonCongruenceDifference k (X : R[X])).derivative.eval (-1) ≠ 0
    rwa [watson_derivative_at_neg_one hk]
  have hn : P ≠ 0 := fun h => hd (by simp [h])
  have hpos := (rootMultiplicity_pos hn).mpr (watson_isRoot_neg_one_of_odd hk)
  have hle : ¬ 1 < P.rootMultiplicity (-1) :=
    fun h => hd ((one_lt_rootMultiplicity_iff_isRoot hn).mp h).2
  change P.rootMultiplicity (-1) = 1
  omega

/-- When k reduces to −1 and 6 is nonzero, the Watson root at −1 is double. -/
theorem watson_rootMultiplicity_two_of_cast_eq_neg_one {k : ℕ} (hk : Odd k) (hk3 : 3 ≤ k)
    (hcast : (k:R) = -1) (h6 : (6:R) ≠ 0) :
    (watsonCongruenceDifference k (X : R[X])).rootMultiplicity (-1) = 2 := by
  let P := watsonCongruenceDifference k (X : R[X])
  have hd : P.derivative.derivative.eval (-1) = 6 := by
    change (watsonCongruenceDifference k (X : R[X])).derivative.derivative.eval (-1) = 6
    rw [watson_second_derivative_at_neg_one hk hk3, hcast]
    norm_num
  have hn : P ≠ 0 := fun h => h6 (by simpa [h] using hd.symm)
  have hroot' : P.derivative.IsRoot (-1) := by
    change (watsonCongruenceDifference k (X : R[X])).derivative.eval (-1) = 0
    rw [watson_derivative_at_neg_one hk, hcast, neg_add_cancel, mul_zero]
  have hle := (one_lt_rootMultiplicity_iff_isRoot hn).mpr ⟨watson_isRoot_neg_one_of_odd hk, hroot'⟩
  have hgt : ¬ 2 < P.rootMultiplicity (-1) := by
    intro h
    have hz := isRoot_iterate_derivative_of_lt_rootMultiplicity h
    change P.derivative.derivative.eval (-1) = 0 at hz
    exact h6 (hd.symm.trans hz)
  change P.rootMultiplicity (-1) = 2
  omega

private theorem odd_half_period_cofactor {h : ℕ} (hh : Odd h) :
    ∃ T : R[X], X^h+1 = (X+1)*T ∧ T.eval (-1) = (h:R) := by
  have hdvd : (X-C (-1) : R[X]) ∣ X^h+1 :=
    dvd_iff_isRoot.mpr (by simp [IsRoot.def, hh.neg_one_pow])
  obtain ⟨T,hT⟩ := hdvd
  have hfactor : (X^h+1 : R[X]) = (X+1)*T := by simpa using hT
  refine ⟨T,hfactor,?_⟩
  have hd := congrArg (fun P : R[X] => P.derivative.eval (-1)) hfactor
  change (X^h+1 : R[X]).derivative.eval (-1) = _ at hd
  rw [derivative_half_period_at_neg_one hh] at hd
  simpa using hd.symm

/-- In the odd prime field of characteristic p, if k = h pᵉ with e > 0,
h odd and p ∤ h, the root −1 of the Watson difference has multiplicity pᵉ. -/
theorem watson_rootMultiplicity_odd_prime (p h e : ℕ) [Fact p.Prime]
    (hp : Odd p) (hh : Odd h) (he : 0 < e) (hc : ¬ p ∣ h) :
    (watsonCongruenceDifference (h*p^e) (X : (ZMod p)[X])).rootMultiplicity (-1) = p^e := by
  have hk : Odd (h*p^e) := hh.mul hp.pow
  obtain ⟨T,hT,hTval⟩ := odd_half_period_cofactor (R := ZMod p) hh
  let Q := (watsonQuotient (h*p^e)).map (Int.castRingHom (ZMod p))
  have hQ : Q.eval (-1) = 2 := by
    rw [show Q.eval (-1) = 2*((↑(h*p^e) : ZMod p)+1) from map_watson_quotient_eval hk,
      Nat.cast_mul, Nat.cast_pow, ZMod.natCast_self, zero_pow he.ne', mul_zero, zero_add, mul_one]
  have hh0 : (h : ZMod p) ≠ 0 := (CharP.cast_eq_zero_iff (ZMod p) p h).not.mpr hc
  have hp2 : 2 < p := by
    have hle := (Fact.out : p.Prime).two_le
    obtain ⟨j,hj⟩ := hp
    omega
  have h2 : (2 : ZMod p) ≠ 0 :=
    (CharP.cast_eq_zero_iff (ZMod p) p 2).not.mpr (Nat.not_dvd_of_pos_of_lt (by decide) hp2)
  let cofactor := T^(p^e)*Q
  have hv : cofactor.eval (-1) ≠ 0 := by
    change (T^(p^e)*Q).eval (-1) ≠ 0
    rw [eval_mul, eval_pow, hTval, hQ]
    exact mul_ne_zero (pow_ne_zero _ hh0) h2
  have hf : watsonCongruenceDifference (h*p^e) (X : (ZMod p)[X]) =
      cofactor*(X-C (-1))^(p^e) := by
    rw [map_watson_quotient_spec hk.pos, show (X^(h*p^e)+1 : (ZMod p)[X]) = (X^h+1)^(p^e) by
      rw [add_pow_char_pow, one_pow, ← pow_mul], hT, mul_pow]
    simp only [cofactor, Q, map_neg, map_one, sub_neg_eq_add]
    ac_rfl
  have hn : cofactor ≠ 0 := fun hz => hv (by simp [hz])
  rw [hf, rootMultiplicity_mul_X_sub_C_pow hn, rootMultiplicity_eq_zero hv, zero_add]

private theorem half_period_factorization {p k : ℕ} (hp : p.Prime) (hk : 0 < k) :
    ∃ e h : ℕ, ¬p ∣ h ∧ k = p^e*h ∧ k.factorization p = e := by
  obtain ⟨e,h,hnd,heq⟩ := Nat.exists_eq_pow_mul_and_not_dvd hk.ne' p hp.ne_one
  have hh : h ≠ 0 := fun hz => hk.ne' (by simp [heq, hz])
  refine ⟨e,h,hnd,heq,?_⟩
  rw [heq, Nat.factorization_mul (pow_ne_zero _ hp.ne_zero) hh,
    hp.factorization_pow, Finsupp.add_apply, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd hnd, add_zero]

/-- For odd k and p > 3, the root at −1 is double if p divides k+1.
Otherwise its multiplicity is the largest power of p dividing k. -/
theorem watson_rootMultiplicity_at_neg_one_of_odd {p k : ℕ} [Fact p.Prime] (hp : 3 < p) (hk : Odd k) :
    (watsonCongruenceDifference k (X : (ZMod p)[X])).rootMultiplicity (-1) =
      if p ∣ k+1 then 2 else p^(k.factorization p) := by
  have hp' : p.Prime := Fact.out
  have h2 : ¬p ∣ 2 := Nat.not_dvd_of_pos_of_lt (by decide) (by omega)
  have h3 : ¬p ∣ 3 := Nat.not_dvd_of_pos_of_lt (by decide) hp
  by_cases hsucc : p ∣ k+1
  · rw [if_pos hsucc]
    have hk3 : 3 ≤ k := by
      by_contra! hsmall
      obtain ⟨n,hn⟩ := hk
      have he : k = 1 := by omega
      exact h2 (by simpa [he] using hsucc)
    have hz := (CharP.cast_eq_zero_iff (ZMod p) p (k+1)).2 hsucc
    have hcast : (k : ZMod p) = -1 := eq_neg_of_add_eq_zero_left (by exact_mod_cast hz)
    have h6 : (6 : ZMod p) ≠ 0 := (CharP.cast_eq_zero_iff (ZMod p) p 6).not.mpr <| by
      rw [show 6 = 2*3 by decide, hp'.dvd_mul]
      exact not_or.mpr ⟨h2,h3⟩
    exact watson_rootMultiplicity_two_of_cast_eq_neg_one hk hk3 hcast h6
  rw [if_neg hsucc]
  by_cases hd : p ∣ k
  · obtain ⟨e,h,hnd,heq,hval⟩ := half_period_factorization hp' hk.pos
    have hh := (Nat.odd_mul.mp (heq ▸ hk)).2
    have he : 0 < e := hval ▸ hp'.factorization_pos_of_dvd hk.pos.ne' hd
    rw [hval, heq, mul_comm (p^e) h]
    exact watson_rootMultiplicity_odd_prime p h e (hp'.odd_of_ne_two (by omega)) hh he hnd
  rw [Nat.factorization_eq_zero_of_not_dvd hd, pow_zero]
  apply watson_rootMultiplicity_one_of_nonzero_slope hk
  have hk0 := (CharP.cast_eq_zero_iff (ZMod p) p k).not.mpr hd
  have hs0 : (k:ZMod p)+1 ≠ 0 := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (CharP.cast_eq_zero_iff (ZMod p) p (k+1)).not.mpr hsucc
  exact mul_ne_zero (mul_ne_zero ((CharP.cast_eq_zero_iff (ZMod p) p 2).not.mpr h2) hk0) hs0

/-- At an even positive half-period the exact multiplicity at −1 in odd
prime characteristic is the largest power of that prime dividing k. -/
theorem watson_rootMultiplicity_at_neg_one_of_even {p k : ℕ} [Fact p.Prime] (hp : Odd p)
    (hk : 0 < k) (he : Even k) :
    (watsonCongruenceDifference k (X : (ZMod p)[X])).rootMultiplicity (-1) = p^(k.factorization p) := by
  have hp' : p.Prime := Fact.out
  obtain ⟨e,h,hnd,heq,hval⟩ := half_period_factorization hp' hk
  have hh : 0 < h := Nat.pos_of_ne_zero (fun hz => hk.ne' (by simp [heq, hz]))
  have hhEven : Even h := (Nat.even_mul.mp (heq ▸ he)).resolve_left (Nat.not_even_iff_odd.mpr hp.pow)
  obtain ⟨Q,hQ,hQval⟩ := watson_even_quotient_at_neg_one hh hhEven (hs := hp.pow (n := e))
  let f := Int.castRingHom (ZMod p)
  have hmap := congrArg (mapRingHom f) hQ
  rw [map_watsonCongruenceDifference, map_mul, map_add, map_pow, map_one] at hmap
  have hpow : (X^(p^e)+1 : (ZMod p)[X]) = (X-C (-1))^(p^e) := by
    rw [show (X-C (-1) : (ZMod p)[X]) = X+1 by simp, add_pow_char_pow, one_pow]
  have hfact : watsonCongruenceDifference k (X : (ZMod p)[X]) =
      Q.map f * (X-C (-1))^(p^e) := by
    rw [heq, mul_comm (p^e) h]
    simpa only [coe_mapRingHom, map_X, hpow, mul_comm] using hmap
  have hQeval : (Q.map f).eval (-1) = 2*(h:ZMod p) := calc
    _ = (Q.map f).eval (f (-1)) := by simp [f]
    _ = f (Q.eval (-1)) := eval_map_apply ..
    _ = _ := by rw [hQval]; simp [f]
  have hp2 : 2 < p := by
    have hle := hp'.two_le
    obtain ⟨j,hj⟩ := hp
    omega
  have hnonzero : (Q.map f).eval (-1) ≠ 0 := by
    rw [hQeval]
    exact mul_ne_zero ((CharP.cast_eq_zero_iff (ZMod p) p 2).not.mpr
      (Nat.not_dvd_of_pos_of_lt (by decide) hp2)) ((CharP.cast_eq_zero_iff (ZMod p) p h).not.mpr hnd)
  rw [hfact, rootMultiplicity_mul_X_sub_C_pow (fun hz => hnonzero (by simp [hz])),
    rootMultiplicity_eq_zero hnonzero, zero_add, hval]

/-- The exact root multiplicity at −1 of the Watson difference for every
positive half-period and every prime p > 3. -/
theorem watson_rootMultiplicity_at_neg_one {p k : ℕ} [Fact p.Prime] (hp : 3 < p) (hk : 0 < k) :
    (watsonCongruenceDifference k (X : (ZMod p)[X])).rootMultiplicity (-1) =
      if Odd k ∧ p ∣ k+1 then 2 else p^(k.factorization p) := by
  rcases Nat.even_or_odd k with he | ho
  · rw [if_neg (fun h => (Nat.not_even_iff_odd.mpr h.1) he)]
    have hprime : p.Prime := Fact.out
    exact watson_rootMultiplicity_at_neg_one_of_even (hprime.odd_of_ne_two (by omega)) hk he
  simpa only [ho, true_and] using watson_rootMultiplicity_at_neg_one_of_odd hp ho

end MockThetaAnalytic
