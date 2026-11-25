import FORWatsonQuotient
import Mathlib.Algebra.CharP.Lemmas

/-! The Watson congruence as divisibility of unreduced integer polynomials.
Its denominator-cleared expression specializes to every commutative ring. -/

noncomputable section
namespace MockThetaAnalytic

open Finset Polynomial KElimination.QuantumRadial KElimination.ResidueSeries

variable {R S : Type*} [CommRing R] [CommRing S]

/-- Multiply each Watson numerator by the suffix of the denominator starting at n. -/
def watsonClearedNumerator (x : R) (c k : ℕ) : R :=
  ∑ n ∈ range k, (-x)^(n^2) * ∏ j ∈ Ico n k, (1+x^(2*j+c))

/-- Substituting X in ℤ[X] gives the unreduced polynomial W − (D−1)B. -/
def watsonCongruenceDifference (k : ℕ) (x : R) : R :=
  let c := if Even k then 1 else 2
  watsonClearedNumerator x c k - (watsonDen x c k - 1) *
    (if Even k then 1 + uPartial k x else -2 * uPartial k x)

private theorem map_uPartial (f : R →+* S) (k : ℕ) (x : R) :
    f (uPartial k x) = uPartial k (f x) := by
  have hp (n : ℕ) : f (uProduct x n) = uProduct (f x) n := by
    induction n with
    | zero => simp [uProduct]
    | succ n ih => simp [uProduct, ih]
  induction k with
  | zero => simp [uPartial, uPolynomial, sumBelow]
  | succ k ih =>
    change f (uPartial k x + uProduct x k * x^(k+1)) =
      uPartial k (f x) + uProduct (f x) k * (f x)^(k+1)
    rw [map_add, map_mul, map_pow, ih, hp]

/-- The cleared expression commutes with substitution and coefficient reduction. -/
theorem map_watsonCongruenceDifference (f : R →+* S) (k : ℕ) (x : R) :
    f (watsonCongruenceDifference k x) = watsonCongruenceDifference k (f x) := by
  have htwo : f 2 = 2 := _root_.map_ofNat f 2
  by_cases he : Even k <;>
    simp [watsonCongruenceDifference, watsonClearedNumerator, watsonDen, he, map_uPartial, htwo]

private theorem eval₂_watsonCongruenceDifference (k : ℕ) (x : R) :
    (watsonCongruenceDifference k (X : ℤ[X])).eval₂ (Int.castRingHom R) x =
      watsonCongruenceDifference k x := by
  simpa only [coe_eval₂RingHom, eval₂_X] using
    map_watsonCongruenceDifference (eval₂RingHom (Int.castRingHom R) x) k X

private theorem watsonCongruenceDifference_eq_cleared {k : ℕ} {q : ℂ} (hq : q^k = -1) :
    watsonCongruenceDifference k q = watsonClearedDifference k q := by
  let c := if Even k then 1 else 2
  have hc : Odd (k+c) := by
    by_cases he : Even k
    · simp [c, he]
    · simpa [c, he] using (Nat.not_even_iff_odd.mp he).add_even (by decide : Even 2)
  suffices hW : watsonClearedNumerator q c k =
      watsonDen q c k * ∑ n ∈ range k, watsonTerm c q n by
    exact congrArg (fun w => w - (watsonDen q c k - 1) *
      (if Even k then 1 + uPartial k q else -2 * uPartial k q)) hW
  rw [watsonClearedNumerator, mul_sum]
  apply sum_congr rfl
  intro n hn
  have hprefix : watsonDen q c n ≠ 0 :=
    prod_ne_zero_iff.mpr fun j _ => watson_factor_ne_zero_of_half_power hq hc j
  have hsplit : watsonDen q c k =
      watsonDen q c n * ∏ j ∈ Ico n k, (1+q^(2*j+c)) :=
    (prod_range_mul_prod_Ico _ (mem_range.mp hn).le).symm
  change _ = watsonDen q c k * ((-q)^(n^2) / watsonDen q c n)
  rw [hsplit]
  field_simp [hprefix]

/-- Monic division over ℤ and the k distinct complex roots of Xᵏ+1
detect divisibility of any integer polynomial for k > 0. -/
theorem X_pow_add_one_dvd_iff_complex_roots {k : ℕ} (hk : 0 < k) (P : ℤ[X]) :
    (X^k + 1 : ℤ[X]) ∣ P ↔ ∀ q : ℂ, q^k = -1 → P.eval₂ (Int.castRingHom ℂ) q = 0 := by
  let g : ℤ[X] := X^k + 1
  let f := Int.castRingHom ℂ
  have hm : g.Monic := by simpa [g] using monic_X_pow_add_C (1:ℤ) hk.ne'
  have hg : g ≠ 1 := by simp [g]
  have hdeg : g.natDegree = k := by simpa [g] using natDegree_X_pow_add_C (n := k) (r := (1:ℤ))
  have hroot (q : ℂ) (hq : q^k = -1) : g.eval₂ f q = 0 := by simp [g, eval₂_pow, hq]
  constructor
  · intro hdvd q hq
    exact eval₂_eq_zero_of_dvd_of_eval₂_eq_zero f q hdvd (hroot q hq)
  · intro h
    apply (modByMonic_eq_zero_iff_dvd hm).mp
    apply Polynomial.map_injective f Int.cast_injective
    rw [Polynomial.map_zero]
    apply polynomial_eq_zero_of_half_power_roots (k := k)
    · calc
        _ ≤ (P %ₘ g).natDegree := natDegree_map_le
        _ < g.natDegree := natDegree_modByMonic_lt P hm hg
        _ = k := hdeg
    · intro q hq
      rw [← eval₂_eq_eval_map, eval₂_modByMonic_eq_self_of_root hm (hroot q hq)]
      exact h q hq

/-- The vector certificate tests divisibility of the unreduced integer polynomial. -/
theorem watsonBoundaryCertificate_iff_polynomial_dvd {k : ℕ} (hk : 0 < k) :
    watsonBoundaryCertificate k = true ↔ (X^k + 1 : ℤ[X]) ∣ watsonCongruenceDifference k X := by
  rw [watsonBoundaryCertificate_iff_cleared_zero hk, X_pow_add_one_dvd_iff_complex_roots hk]
  exact forall_congr' fun q => forall_congr' fun hq => by
    rw [eval₂_watsonCongruenceDifference, watsonCongruenceDifference_eq_cleared hq]

/-- Universal integer polynomial congruence, including the empty sum at k = 0. -/
theorem watson_polynomial_congruence (k : ℕ) :
    (X^k + 1 : ℤ[X]) ∣ watsonCongruenceDifference k X := by
  cases k with
  | zero => simp [watsonCongruenceDifference, watsonClearedNumerator, watsonDen]
  | succ k =>
    exact (watsonBoundaryCertificate_iff_polynomial_dvd (Nat.succ_pos k)).mp
      (watsonBoundaryCertificate_all (Nat.succ_pos k))

private theorem watson_even_difference_eq_zero {q : ℂ} {k s : ℕ}
    (hk : 0 < k) (he : Even k) (hs : Odd s) (hsd : s ∣ k) (hq : q^s = -1) :
    watsonCongruenceDifference k q = 0 := by
  obtain ⟨h, m, hh0, _, hm, hprim⟩ := even_root_order_of_half_power hq
  have hh : Odd h := (Nat.odd_mul.mp (hm ▸ hs)).2
  have hhq := primitive_even_half_power hh0 hprim
  have hhk : h ≤ k := Nat.le_of_dvd hk ((Dvd.intro m (by rw [hm, mul_comm])).trans hsd)
  have hqk : q^k = 1 := by
    obtain ⟨a, ha⟩ := hsd
    have hea := (Nat.even_mul.mp (ha ▸ he)).resolve_left (Nat.not_even_iff_odd.mpr hs)
    rw [ha, pow_mul, hq, hea.neg_one_pow]
  have hD (n : ℕ) (hn : h ≤ n) : watsonDen q 1 n = 0 := by
    obtain ⟨j, hj⟩ := hh
    apply prod_eq_zero (i := j) (mem_range.mpr (by omega : j < n))
    rw [← hj, hhq, add_neg_cancel]
  let a (n : ℕ) := (-1:ℂ)^n * watsonDen q 1 n
  have ha0 : a 0 = 1 := by simp [a, watsonDen]
  have hak : a k = 0 := by simp [a, hD k hhk]
  have hshift : (∑ n ∈ range k, a (n+1)) = (∑ n ∈ range k, a n)+a k-a 0 := by
    linear_combination sum_range_succ a k - sum_range_succ' a k
  have hsum : (∑ n ∈ range k, a n) = (∑ n ∈ range h, a n) := by
    symm
    apply sum_subset (range_mono hhk)
    intro j _ hj
    simp [a, hD j (by simpa only [mem_range, not_lt] using hj)]
  have hprog := watson_odd_progression_at_odd_half_period hh hprim
  change (∑ n ∈ range h, a n) = _ at hprog
  have hW : watsonClearedNumerator q 1 k = -uPartial h q - 1 := by
    rw [watsonClearedNumerator, watson_even_reversed_numerator hk he hqk]
    change (∑ n ∈ range k, a (n+1)) = _
    rw [hshift, hak, ha0, add_zero, hsum, hprog]
  have hU : uPartial k q = uPartial h q := uPolynomial_stable k h q q hh0 hhq hhk
  simp only [watsonCongruenceDifference, if_pos he, hD k hhk, hU, hW]
  ring

/-- At even k every odd divisor s of k supplies an additional integer
polynomial divisor Xˢ+1 of the cleared Watson difference. -/
theorem watson_even_polynomial_congruence {k s : ℕ} (hk : 0 < k) (he : Even k)
    (hs : Odd s) (hd : s ∣ k) : (X^s+1 : ℤ[X]) ∣ watsonCongruenceDifference k X := by
  rw [X_pow_add_one_dvd_iff_complex_roots hs.pos]
  intro q hq
  rw [eval₂_watsonCongruenceDifference]
  exact watson_even_difference_eq_zero hk he hs hd hq

/-- Substitution into any commutative ring preserves the full divisor. -/
theorem watson_congruence (k : ℕ) (x : R) : x^k + 1 ∣ watsonCongruenceDifference k x := by
  simpa only [eval₂_add, eval₂_pow, eval₂_X, eval₂_one, eval₂_watsonCongruenceDifference]
    using eval₂_dvd (Int.castRingHom R) x (watson_polynomial_congruence k)

/-- The denominator-cleared Watson equality at a half-period in any commutative ring. -/
theorem watson_cleared_eq_of_half_power {k : ℕ} {x : R} (hx : x^k = -1) :
    let c := if Even k then 1 else 2
    watsonClearedNumerator x c k = (watsonDen x c k - 1) *
      (if Even k then 1 + uPartial k x else -2 * uPartial k x) := by
  have h := watson_congruence k x
  rw [hx, neg_add_cancel, zero_dvd_iff] at h
  exact sub_eq_zero.mp h

/-- In characteristic p the divisor retains its pᵉ-fold factor. -/
theorem watson_congruence_prime_power (p : ℕ) [Fact p.Prime] [CharP R p]
    (h e : ℕ) (x : R) : (x^h + 1)^(p^e) ∣ watsonCongruenceDifference (h*p^e) x := by
  rw [add_pow_char_pow, one_pow, ← pow_mul]
  exact watson_congruence _ _

end MockThetaAnalytic
