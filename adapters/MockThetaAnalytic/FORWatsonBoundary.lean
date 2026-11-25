import FORFiniteTransform
import FKTYReflection

/-! Uniform identification of the two finite Watson values with the FOR
unimodal polynomial. The Newton transform groups the even and odd factors,
and the reflected strange sum pairs two successive terms at a time. -/

noncomputable section
namespace MockThetaAnalytic

open Finset KElimination.QuantumRadial KElimination.ResidueSeries

private def progressionPrefix (q : ℂ) (c n : ℕ) : ℂ :=
  ∏ j ∈ range n, (1+q^(2*j+c))

private theorem progression_pochhammer (q : ℂ) (c n : ℕ) :
    progressionPrefix q c n = pochhammer (-q^c) (q^2) n := by
  rw [progressionPrefix, pochhammer_eq_prod]
  apply prod_congr rfl
  intro j _
  rw [pow_add q (2*j) c, pow_mul q 2 j]
  ring

private theorem pochhammer_neg_succ (q : ℂ) (n : ℕ) :
    pochhammer (-q) q (n+1) = pochhammer (-q) q n*(1+q^(n+1)) := by
  rw [pochhammer, pow_succ' q n, neg_mul, sub_neg_eq_add]

private theorem pochhammer_neg_pair (q : ℂ) (n : ℕ) :
    pochhammer (-q) q (2*(n+1)) = pochhammer (-q) q (2*n)*(1+q^(2*n+1))*(1+q^(2*n+2)) := by
  rw [show 2*(n+1) = (2*n+1)+1 by omega, pochhammer_neg_succ, pochhammer_neg_succ]

private theorem inv_factor {q : ℂ} (hq : q ≠ 0) (j : ℕ) :
    q^j*(1+(q⁻¹)^j) = 1+q^j := by
  rw [mul_add, mul_one, inv_pow, mul_inv_cancel₀ (pow_ne_zero _ hq), add_comm]

private theorem pochhammer_inv_pair {q : ℂ} (hq : q ≠ 0) (n : ℕ) :
    pochhammer (-q) q (2*n) = q^(n*(2*n+1))*pochhammer (-q⁻¹) q⁻¹ (2*n) := by
  induction n with
  | zero => simp [pochhammer]
  | succ n ih =>
    rw [pochhammer_neg_pair, pochhammer_neg_pair, ih, ← inv_factor hq (2*n+1), ← inv_factor hq (2*n+2),
      show (n+1)*(2*(n+1)+1)=n*(2*n+1)+(2*n+1)+(2*n+2) by ring, pow_add, pow_add]
    ring

private theorem even_odd_factors (q : ℂ) {c : ℕ} (hc : c = 1 ∨ c = 2) (n : ℕ) :
    (1-(-q^c)*(q^2)^n)*((-q^(c-1))-(q^2)^(n+1)) =
      (-q^(c-1))*((1+q^(2*n+1))*(1+q^(2*n+2))) := by
  have h₁ : q^(2*n+1) = (q^2)^n*q := by rw [pow_succ, pow_mul]
  have h₂ : q^(2*n+2) = (q^2)^n*q^2 := by rw [pow_add, pow_mul]
  rcases hc with rfl | rfl <;>
    simp only [h₁, h₂, pow_succ (q^2), Nat.reduceSub, pow_zero, pow_one] <;> ring

private theorem grouped_newton_factors (q : ℂ) {c : ℕ} (hc : c = 1 ∨ c = 2) (n : ℕ) :
    pochhammer (-q^c) (q^2) n*(∏ j ∈ range n, ((-q^(c-1))-(q^2)^(j+1))) =
      (-q^(c-1))^n*pochhammer (-q) q (2*n) := by
  induction n with
  | zero => simp [pochhammer]
  | succ n ih =>
    rw [pochhammer, prod_range_succ, pochhammer_neg_pair, pow_succ (-q^(c-1)) n]
    calc
      _ = (pochhammer (-q^c) (q^2) n*(∏ j ∈ range n, ((-q^(c-1))-(q^2)^(j+1))))*
          ((1-(-q^c)*(q^2)^n)*((-q^(c-1))-(q^2)^(n+1))) := by ac_rfl
      _ = _ := by rw [ih, even_odd_factors q hc]; ring

private theorem strange_even_pairs (v : ℂ) (n : ℕ) :
    fNegPartial (2*n) v = ∑ j ∈ range n, v^(2*j+1)*pochhammer (-v) v (2*j) := by
  induction n with
  | zero => simp [fNegPartial, sumBelow]
  | succ n ih =>
    have h₁ : (-1:ℂ)^(2*n+1) = -1 := by rw [pow_add, pow_mul]; norm_num
    have h₂ : (-1:ℂ)^(2*n+1+1) = 1 := by rw [pow_succ, h₁]; norm_num
    have hs : fNegPartial (2*(n+1)) v = fNegPartial (2*n) v +
        (-1:ℂ)^(2*n+1)*pochhammer (-v) v (2*n) +
        (-1:ℂ)^(2*n+1+1)*pochhammer (-v) v (2*n+1) := by
      rw [show 2*(n+1)=2*n+1+1 by omega]
      rfl
    rw [hs, h₁, h₂, pochhammer_neg_succ, sum_range_succ, ih]
    ring

private theorem strange_even_pairs_eq_u {q : ℂ} {k : ℕ} (hk : 0 < k) (hq : q^k = -1) :
    (∑ n ∈ range k, (q⁻¹)^(2*n+1)*pochhammer (-q⁻¹) q⁻¹ (2*n)) = uPartial k q := by
  rw [← strange_even_pairs]
  have hi : (q⁻¹)^k = -1 := by rw [inv_pow, hq]; norm_num
  have htr : fNegPartial (2*k) q⁻¹ = fNegPartial k q⁻¹ := by
    unfold fNegPartial
    apply sumBelow_eq_of_tail_zero _ _ _ (by omega)
    intro n hn _
    have h := uProduct_zero_of_le q⁻¹ k n hk hi hn
    rw [uProduct_eq_pochhammer] at h
    rw [eq_zero_of_pow_eq_zero h, mul_zero]
  rw [htr, fNegPartial_reflection hk hq]

private theorem progression_value {q : ℂ} {k c : ℕ} (hk : 0 < k)
    (hq : IsPrimitiveRoot q (2*k)) (hc : c = 1 ∨ c = 2) :
    (-q^(c-1))*(∑ n ∈ range k, progressionPrefix q c n*(-q^(c-1))^n) =
      (-1:ℂ)^(k+c)*uPartial k q := by
  let b : ℂ := -q^c
  let z : ℂ := -q^(c-1)
  let Q := q^2
  have hq0 := hq.ne_zero (by omega)
  have hb0 : b ≠ 0 := neg_ne_zero.mpr (pow_ne_zero c hq0)
  have hQ0 : Q ≠ 0 := pow_ne_zero 2 hq0
  have hQ : IsPrimitiveRoot Q k := by
    simpa [Q] using hq.pow_of_dvd (by decide : 2 ≠ 0) (dvd_mul_right 2 k)
  have hqk := primitive_even_half_power hk hq
  have hbz : b = q*z := by
    rcases hc with rfl | rfl <;> simp [b,z,pow_two]
  have hbk : b^k = (-1:ℂ)^(k+c) := by
    change (-q^c)^k = _
    rw [neg_pow, pow_right_comm q, hqk, ← pow_add]
  have hs : z*b^(k-1) = (-1:ℂ)^(k+c)*q⁻¹ := by
    apply mul_right_cancel₀ hq0
    calc
      _ = b^(k-1)*b := by rw [hbz]; ring
      _ = b^k := by rw [← pow_succ, Nat.sub_add_cancel hk]
      _ = _ := by rw [hbk, mul_assoc, inv_mul_cancel₀ hq0, mul_one]
  have ht (n : ℕ) :
      (pochhammer b Q n/(b^n*Q^(n*(n+1))))*(∏ j ∈ range n, (z-Q^(j+1))) =
        (q⁻¹)^(2*n)*pochhammer (-q⁻¹) q⁻¹ (2*n) := by
    rw [div_mul_eq_mul_div]
    have hgroup : pochhammer b Q n*(∏ j ∈ range n, (z-Q^(j+1))) =
        z^n*pochhammer (-q) q (2*n) := grouped_newton_factors q hc n
    rw [hgroup, pochhammer_inv_pair hq0]
    apply (div_eq_iff (mul_ne_zero (pow_ne_zero _ hb0) (pow_ne_zero _ hQ0))).2
    have hex : q^n * q^(2*(n*(n+1))) = q^(n*(2*n+1))*q^(2*n) := by
      rw [← pow_add, ← pow_add]
      congr 1
      ring
    symm
    calc
      _ = ((q⁻¹)^(2*n)*q^(2*n))*(z^n*(q^(n*(2*n+1))*pochhammer (-q⁻¹) q⁻¹ (2*n))) := by
        rw [hbz, mul_pow, show Q^(n*(n+1))=q^(2*(n*(n+1))) from (pow_mul q 2 _).symm]
        linear_combination (q⁻¹)^(2*n)*pochhammer (-q⁻¹) q⁻¹ (2*n)*z^n*hex
      _ = _ := by rw [← mul_pow, inv_mul_cancel₀ hq0, one_pow, one_mul]
  simp_rw [progression_pochhammer]
  change z*(∑ n ∈ range k, pochhammer b Q n*z^n) = _
  rw [finite_root_transform_at hk hQ hb0 z, ← mul_assoc, hs, mul_assoc]
  simp_rw [ht]
  rw [mul_sum, ← strange_even_pairs_eq_u hk hqk]
  congr 1
  apply sum_congr rfl
  intro n _
  rw [pow_succ' q⁻¹ (2*n), mul_assoc]

private theorem reversed_watson_tail {q : ℂ} {k c m : ℕ} (hq0 : q ≠ 0)
    (hq2 : q^(2*k) = 1) (hc : c ≤ 2) (hm : m ≤ k) :
    (∏ j ∈ range m, (1+q^(2*(k-m+j)+c))) = progressionPrefix q⁻¹ (2-c) m := by
  rw [← prod_range_reflect (fun j => 1+q^(2*(k-m+j)+c)) m]
  apply prod_congr rfl
  intro j hj
  have hj' := mem_range.mp hj
  congr 1
  rw [inv_pow, ← one_div, eq_div_iff (pow_ne_zero _ hq0), ← pow_add,
    show 2*(k-m+(m-1-j))+c+(2*j+(2-c))=2*k by omega, hq2]

private theorem reversed_watson_term {q : ℂ} {k c : ℕ} (hk : 0 < k)
    (hq : IsPrimitiveRoot q (2*k)) (hc : c ≤ 2) (hparity : Odd (k+c)) (m : ℕ) (hm : m ≤ k) :
    2*watsonTerm c q (k-m) = (-q)^(m^2)*progressionPrefix q⁻¹ (2-c) m := by
  have hq0 := hq.ne_zero (by omega)
  have h2 : (-q)^(2*k) = 1 := by rw [(even_two.mul_right k).neg_pow, hq.pow_eq_one]
  have hnum : (-q)^((k-m)^2) = (-q)^(m^2) := by
    have he : (m+k)^2=(k-m)^2+(2*k)*(2*m) := by
      let n := k-m
      have hn : n+m=k := Nat.sub_add_cancel hm
      change (m+k)^2=n^2+(2*k)*(2*m)
      rw [← hn]
      ring
    rw [← watson_numerator_add_halfOrder hk hq m, he, pow_add, pow_mul (-q) (2*k), h2, one_pow, mul_one]
  have htail := reversed_watson_tail hq0 hq.pow_eq_one hc hm
  have hd : progressionPrefix q c (k-m)*progressionPrefix q⁻¹ (2-c) m = 2 := by
    rw [← htail, progressionPrefix, ← prod_range_add, Nat.sub_add_cancel hm]
    simpa only [zero_add] using watson_denominator_block hk hq c hparity 0
  have hd0 : progressionPrefix q c (k-m) ≠ 0 := by
    intro h
    rw [h, zero_mul] at hd
    norm_num at hd
  change 2*((-q)^((k-m)^2)/progressionPrefix q c (k-m)) = _
  rw [hnum, ← mul_div_assoc]
  apply (div_eq_iff hd0).mpr
  linear_combination -(-q)^(m^2)*hd

private theorem reversed_watson_sum {q : ℂ} {k c : ℕ} (hk : 0 < k)
    (hq : IsPrimitiveRoot q (2*k)) (hc : c ≤ 2) (hparity : Odd (k+c)) :
    2*(∑ n ∈ range k, watsonTerm c q n) =
      ∑ n ∈ range k, (-q)^((n+1)^2)*progressionPrefix q⁻¹ (2-c) (n+1) := by
  rw [← sum_range_reflect (watsonTerm c q) k, mul_sum]
  apply sum_congr rfl
  intro n hn
  have hn' := mem_range.mp hn
  rw [show k-1-n = k-(n+1) by omega]
  exact reversed_watson_term hk hq hc hparity (n+1) hn'

private theorem progression_succ (q : ℂ) (c n : ℕ) :
    progressionPrefix q c (n+1) = progressionPrefix q c n*(1+q^(2*n+c)) := prod_range_succ _ _

private theorem progression_inv {q : ℂ} (hq : q ≠ 0) (d n : ℕ) :
    q^(n*(n-1)+n*d)*progressionPrefix q⁻¹ d n = progressionPrefix q d n := by
  induction n with
  | zero => simp [progressionPrefix]
  | succ n ih =>
    have he : (n+1)*((n+1)-1)+(n+1)*d=(n*(n-1)+n*d)+(2*n+d) := by
      cases n with
      | zero => simp
      | succ n => simp only [Nat.add_sub_cancel]; ring
    rw [he, pow_add, progression_succ, progression_succ]
    calc
      _ = (q^(n*(n-1)+n*d)*progressionPrefix q⁻¹ d n)*(q^(2*n+d)*(1+(q⁻¹)^(2*n+d))) := by ring
      _ = _ := by rw [ih, inv_factor hq]

private theorem neg_square_pow (q : ℂ) (n : ℕ) : (-q)^(n^2) = (-1:ℂ)^n*q^(n^2) := by
  rw [neg_pow]
  have hs : (-1:ℂ)^(n^2) = (-1:ℂ)^n := by simp [neg_one_pow_eq_ite, sq, Nat.even_mul]
  rw [hs]

private theorem square_factorization (n : ℕ) : n^2=n*(n-1)+n := by
  cases n with
  | zero => rfl
  | succ n => simp only [Nat.add_sub_cancel]; ring

private theorem odd_progression_reversed {q : ℂ} (hq : q ≠ 0) (n : ℕ) :
    (-q)^(n^2)*progressionPrefix q⁻¹ 1 n = progressionPrefix q 1 n*(-1:ℂ)^n := by
  have hi := progression_inv hq 1 n
  rw [mul_one, ← square_factorization] at hi
  rw [neg_square_pow, mul_assoc, hi, mul_comm]

/-- At an even period with qᵏ = 1, reversing the cleared numerator gives
the alternating sum of odd progression products. -/
theorem watson_even_reversed_numerator {q : ℂ} {k : ℕ} (hk : 0 < k) (he : Even k) (hq : q^k = 1) :
    (∑ n ∈ range k, (-q)^(n^2)*∏ j ∈ Ico n k, (1+q^(2*j+1))) =
      ∑ m ∈ range k, (-1:ℂ)^(m+1)*∏ j ∈ range (m+1), (1+q^(2*j+1)) := by
  have hq0 : q ≠ 0 := by intro hz; simp [hz, hk.ne'] at hq
  have hq2 : q^(2*k) = 1 := by rw [mul_comm, pow_mul, hq, one_pow]
  have hneg : (-q)^k = 1 := by rw [he.neg_pow, hq]
  have hneg2 : (-q)^(2*k) = 1 := by rw [mul_comm, pow_mul, hneg, one_pow]
  conv_lhs => rw [← sum_range_reflect]
  apply sum_congr rfl
  intro j hj
  have hj' := mem_range.mp hj
  let m := j+1
  have hm : m ≤ k := by omega
  have hn : k-m+m = k := Nat.sub_add_cancel hm
  have hexp : (k-m)^2 + m*(2*k) = m^2+k*k := calc
    _ = (k-m)^2 + m*(2*(k-m+m)) := by rw [hn]
    _ = m^2+(k-m+m)*(k-m+m) := by ring
    _ = _ := by rw [hn]
  have hpow := congrArg (fun n : ℕ => (-q)^n) hexp
  change (-q)^((k-m)^2+m*(2*k)) = (-q)^(m^2+k*k) at hpow
  simp only [pow_add, pow_mul (-q) m (2*k), pow_right_comm (-q) m (2*k), hneg2,
    pow_mul (-q) k k, hneg, one_pow, mul_one] at hpow
  rw [show k-1-j = k-m by omega, prod_Ico_eq_prod_range, show k-(k-m)=m by omega,
    reversed_watson_tail hq0 hq2 (by decide : 1 ≤ 2) hm, hpow]
  simpa [m, progressionPrefix, mul_comm] using odd_progression_reversed hq0 m

/-- For odd h the alternating odd progression at a primitive 2h-th
root is the negative of the unimodal value. -/
theorem watson_odd_progression_at_odd_half_period {q : ℂ} {h : ℕ} (hh : Odd h)
    (hq : IsPrimitiveRoot q (2*h)) :
    (∑ n ∈ range h, (-1:ℂ)^n*∏ j ∈ range n, (1+q^(2*j+1))) = -uPartial h q := by
  have he : Even (h+1) := hh.add_odd (by decide : Odd 1)
  have h := progression_value hh.pos hq (Or.inl rfl : 1 = 1 ∨ 1 = 2)
  simp only [he.neg_one_pow, one_mul, Nat.sub_self, pow_zero, neg_one_mul] at h
  simpa only [progressionPrefix, mul_comm] using (neg_eq_iff_eq_neg.mp h)

private theorem even_progression_reversed {q : ℂ} (hq : q ≠ 0) (n : ℕ) :
    (-q)^((n+1)^2)*progressionPrefix q⁻¹ 0 (n+1) =
      2*((-q)*(progressionPrefix q 2 n*(-q)^n)) := by
  have hi := progression_inv hq 0 (n+1)
  simp only [Nat.add_sub_cancel, mul_zero, add_zero] at hi
  have hstep : progressionPrefix q 0 (n+1) = 2*progressionPrefix q 2 n := by
    unfold progressionPrefix
    rw [prod_range_succ']
    simp only [Nat.add_zero, mul_zero, pow_zero, one_add_one_eq_two]
    rw [mul_comm]
    congr 1
  calc
    _ = (-q)^(n+1)*(q^((n+1)*n)*progressionPrefix q⁻¹ 0 (n+1)) := by
      rw [neg_square_pow, square_factorization (n+1), Nat.add_sub_cancel, pow_add, neg_pow]
      ring
    _ = _ := by rw [hi, hstep, pow_succ]; ring

/-- At every primitive even root the finite Watson value equals the FOR
polynomial. The proof is uniform in the half-order. -/
theorem watsonFiniteBoundary_eq_boundaryValue {q : ℂ} {k : ℕ} (hk : 0 < k)
    (hq : IsPrimitiveRoot q (2*k)) : watsonFiniteBoundary k q = boundaryValue k q := by
  have hq0 := hq.ne_zero (by omega)
  by_cases he : Even k
  · have hparity := he.add_odd (by decide : Odd 1)
    have hu := progression_value hk hq (Or.inl rfl : 1 = 1 ∨ 1 = 2)
    simp only [hparity.neg_one_pow, Nat.sub_self, pow_zero, neg_one_mul, neg_inj] at hu
    have h := reversed_watson_sum hk hq (by decide : 1 ≤ 2) hparity
    simp only [Nat.reduceSub, odd_progression_reversed hq0] at h
    let A (n : ℕ) := progressionPrefix q 1 n*(-1:ℂ)^n
    have hshift : (∑ n ∈ range k, A (n+1)) = (∑ n ∈ range k,A n)+A k-A 0 := by
      linear_combination sum_range_succ A k - sum_range_succ' A k
    have ha₀ : A 0 = 1 := by simp [A, progressionPrefix]
    have haₖ : A k = 2 := by
      dsimp [A]
      rw [he.neg_one_pow, mul_one, progressionPrefix]
      simpa only [zero_add] using watson_denominator_block hk hq 1 hparity 0
    change 2*(∑ n ∈ range k, watsonTerm 1 q n) = ∑ n ∈ range k, A (n+1) at h
    rw [hshift, ha₀, haₖ] at h
    change (∑ n ∈ range k,A n) = uPartial k q at hu
    rw [hu] at h
    rw [watsonFiniteBoundary, if_pos he, boundaryValue]
    linear_combination -4*h
  · have hparity := (Nat.not_even_iff_odd.mp he).add_even (by decide : Even 2)
    have hu := progression_value hk hq (Or.inr rfl : 2 = 1 ∨ 2 = 2)
    simp only [hparity.neg_one_pow, neg_one_mul, Nat.reduceSub, pow_one] at hu
    have h := reversed_watson_sum hk hq (by decide : 2 ≤ 2) hparity
    simp only [Nat.reduceSub, even_progression_reversed hq0] at h
    rw [← mul_sum, ← mul_sum, hu] at h
    rw [watsonFiniteBoundary, if_neg he, boundaryValue]
    linear_combination 2*h

end MockThetaAnalytic
