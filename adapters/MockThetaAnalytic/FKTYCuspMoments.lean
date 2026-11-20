import BoundaryValues34
import MockThetaShadow

/-! For two even-denominator cusps, the first moment of the periodic unary
theta coefficients recovers the terminating FKTY value. The moment is the
finite Bernoulli expression for a zero-mean periodic coefficient sequence. -/

noncomputable section

namespace MockThetaAnalytic

open Complex KElimination.MockThetaShadow

/-- Signed periodic coefficient used in the finite moment. -/
def fktyCuspCoefficient (u : ℂ) (m : ℕ) : ℂ := (shadowSign m : ℂ) * u^(m^2)

theorem fktyCuspCoefficient_period (k : ℕ) (u : ℂ) (hu : u^(24*k) = 1) (m : ℕ) :
    fktyCuspCoefficient u (m+24*k) = fktyCuspCoefficient u m := by
  have hs : shadowSign (m+24*k) = shadowSign m := by
    unfold shadowSign
    have : (m+24*k)%6 = m%6 := by omega
    rw [this]
  have he : (m + 24*k)^2 = m^2 + (24*k)*(2*m+24*k) := by ring
  rw [fktyCuspCoefficient, hs, he, pow_add, pow_mul, hu, one_pow, mul_one]
  rfl

theorem sum_fktyCuspCoefficient_eq_zero (k : ℕ) (u : ℂ) (hu : u^(24*k) = 1) :
    ∑ m ∈ Finset.range (24*k), fktyCuspCoefficient u m = 0 := by
  have reflect (m : ℕ) (hm : m ≤ 24*k) :
      fktyCuspCoefficient u (24*k-m) = -fktyCuspCoefficient u m := by
    have hs : shadowSign (24*k-m) = -shadowSign m := by
      unfold shadowSign
      split_ifs <;> omega
    have he : (24*k-m)^2 + (24*k)*(2*m) = (24*k)* (24*k) + m^2 := by
      have h := Nat.sub_add_cancel hm
      nlinarith [congrArg (fun x : ℕ => x^2) h, congrArg (fun x : ℕ => x*m) h]
    have hpow := congrArg (u^·) he
    simp only [pow_add, pow_mul, hu, one_pow, mul_one, one_mul] at hpow
    simp [fktyCuspCoefficient, hs, hpow]
  have h := Finset.sum_range_reflect (fktyCuspCoefficient u) (24*k+1)
  simp only [Nat.add_sub_cancel] at h
  have hneg : (∑ m ∈ Finset.range (24*k+1), fktyCuspCoefficient u (24*k-m)) =
      ∑ m ∈ Finset.range (24*k+1), -fktyCuspCoefficient u m :=
    Finset.sum_congr rfl (fun m hm => reflect m (by have := Finset.mem_range.mp hm; omega))
  rw [hneg, Finset.sum_neg_distrib, Finset.sum_range_succ] at h
  have hz : fktyCuspCoefficient u (24*k) = 0 := by
    have : (24*k)%6 = 0 := by omega
    simp [fktyCuspCoefficient, shadowSign, this]
  rw [hz, add_zero] at h
  linear_combination -h/2

/-- The first moment −∑ₘ m a(m)/L over one period, with
a(m)=sign₆(m) u^(m²). At the two cusps below u=e(−1/L). -/
def fktyCuspMoment (L : ℕ) (u : ℂ) : ℂ :=
  -(∑ m ∈ Finset.range L, (m : ℂ) * fktyCuspCoefficient u m) / L

private def weight (m : ℕ) : ℤ := m * shadowSign m

-- For supported m, 24 divides m²−1. After a common phase u is removed,
-- the remaining exponent is the negative of (m²−1)/24 in the physical nome.
private def degree (k m : ℕ) : ℕ := (k - ((m*m-1)/24) % k) % k

private def mass (k j N : ℕ) : ℤ :=
  Nat.rec 0 (fun m previous => previous + if degree k m = j then weight m else 0) N

private theorem mass_eq (k j N : ℕ) :
    (mass k j N : ℂ) = ∑ m ∈ Finset.range N, if degree k m = j then (weight m : ℂ) else 0 := by
  induction N with
  | zero => simp [mass]
  | succ n ih =>
    change ((mass k j n + _ : ℤ) : ℂ) = _
    rw [Int.cast_add, ih, Finset.sum_range_succ]
    split_ifs <;> simp

private theorem pow_mod_period {u : ℂ} {L : ℕ} (hu : u^L = 1) (n : ℕ) :
    u^(n%L) = u^n := by
  conv_rhs => rw [← Nat.mod_add_div n L, pow_add, pow_mul, hu, one_pow, mul_one]

private def DegreeCorrect (k : ℕ) : Prop :=
  ∀ m : Fin (24*k), weight m ≠ 0 →
    (m.val^2) % (24*k) = (1 + 24*(k-1)*degree k m) % (24*k)

private theorem moment_from_mass (k : ℕ) (hk : 0 < k) (u q : ℂ)
    (hu : u^(24*k) = 1) (hq : u^(24*(k-1)) = q) (h : DegreeCorrect k) :
    fktyCuspMoment (24*k) u =
      -(u * ∑ j ∈ Finset.range k, (mass k j (24*k) : ℂ) * q^j) / (24*k : ℕ) := by
  have ht (m : ℕ) (hm : m < 24*k) : (weight m : ℂ) * u^(m^2) =
      u * ((weight m : ℂ) * q^(degree k m)) := by
    by_cases hw : weight m = 0
    · simp [hw]
    have hh := h ⟨m, hm⟩ hw
    have hp : u^(m^2) = u^(1 + 24*(k-1)*degree k m) :=
      (pow_mod_period hu _).symm.trans ((congrArg (u^·) hh).trans (pow_mod_period hu _))
    rw [hp, pow_add, pow_one, pow_mul, hq]
    ring
  have regroup : (∑ j ∈ Finset.range k, (mass k j (24*k) : ℂ)*q^j) =
      ∑ m ∈ Finset.range (24*k), (weight m : ℂ) * q^(degree k m) := by
    simp_rw [mass_eq, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro m _
    rw [Finset.sum_eq_single (degree k m)]
    · simp
    · intro j _ hj
      simp [Ne.symm hj]
    · simp [Nat.mod_lt _ hk, degree]
  unfold fktyCuspMoment
  rw [regroup, Finset.mul_sum]
  congr 2
  apply Finset.sum_congr rfl
  intro m hm
  simpa only [fktyCuspCoefficient, weight, Int.cast_mul, Int.cast_natCast, mul_assoc]
    using ht m (Finset.mem_range.mp hm)

/-- The mass tables and modular exponent identities use only integer arithmetic. -/
private def table (k : ℕ) : Vector ℤ k := Vector.ofFn fun j => mass k j (24*k)


private theorem nome_pow (z : ℂ) (n : ℕ) : integerNome z ^ n = integerNome (n*z) := by
  unfold integerNome
  rw [← Complex.exp_nat_mul]
  congr 1
  ring

private theorem nome_neg_one_shift (z : ℂ) : integerNome (z-1) = integerNome z := by
  unfold integerNome
  rw [mul_sub, Complex.exp_sub, mul_one, Complex.exp_two_pi_mul_I, div_one]


private theorem cuspMoment_table (k : ℕ) (hk : 0 < k) (h : DegreeCorrect k) :
    fktyCuspMoment (24*k) (integerNome (-1/(24*k))) =
      -(integerNome (-1/(24*k)) * ∑ j : Fin k,
        ((table k)[j.val] : ℂ) * integerNome (1/k)^j.val) / (24*k : ℕ) := by
  have hk' : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  have hu : integerNome (-1/(24*k))^(24*k : ℕ) = 1 := by
    rw [nome_pow, show ((24*k : ℕ) : ℂ) * (-1/(24*k)) = -1 by push_cast; field_simp]
    norm_num [integerNome, Complex.exp_neg]
  have hx : integerNome (-1/(24*k))^(24*(k-1) : ℕ) = integerNome (1/k) := by
    rw [nome_pow, show ((24*(k-1) : ℕ) : ℂ) * (-1/(24*k)) = 1/k-1 by
      push_cast [Nat.cast_sub (by omega : 1 ≤ k)]
      field_simp
      ring, nome_neg_one_shift]
  rw [moment_from_mass k hk _ _ hu hx h, ← Fin.sum_univ_eq_sum_range]
  simp [table]

private theorem primitive_relations {k : ℕ} {q : ℂ} (hk : 1 < k)
    (h : IsPrimitiveRoot q (2*k)) : q^k = -1 ∧ q+1 ≠ 0 := by
  have hs : (q^k)^2 = 1 := by simpa only [← pow_mul, Nat.mul_comm k 2] using h.pow_eq_one
  refine ⟨(sq_eq_one_iff.mp hs).resolve_left (h.pow_ne_one_of_pos_of_lt (by omega) (by omega)), ?_⟩
  intro he
  have hneg : q = -1 := by linear_combination he
  exact h.pow_ne_one_of_pos_of_lt (by decide : 2 ≠ 0) (by omega) (by rw [hneg]; norm_num)

-- Concrete cusp values.

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem degreeCorrect10 : DegreeCorrect 10 := by
  unfold DegreeCorrect
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem table10 : table 10 = #v[-320, 0, 0, -320, -160, 160, 0, 0, 160, 320] := by decide +kernel

/-- The finite first moment at the order-10 reflected cusp gives its normalized FKTY value. -/
theorem fktyPhi_eq_cuspMoment10 :
    fktyPhi (-1/10) = 2 * fktyScale * fktyCuspMoment 240 (integerNome (-1/240)) := by
  let q := integerNome (1/10)
  let u := integerNome (-1/240)
  have hq : IsPrimitiveRoot q 10 := by
    simpa [q, integerNome, mul_one_div] using Complex.isPrimitiveRoot_exp 10 (by decide)
  obtain ⟨hp, hne⟩ := primitive_relations (k := 5) (by decide) hq
  have hm := cuspMoment_table 10 (by decide) degreeCorrect10
  norm_num1 at hm
  rw [← neg_div] at hm
  rw [fktyPhi_neg_one_div_10, boundaryValue_cyclotomic10 _ hq, hm, table10]
  change (fktyScale * u) * _ = 2 * fktyScale * (-(u * ∑ j : Fin 10, _ * q^j.val) / 240)
  norm_num [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ]
  -- Multiplication by q+1 reduces the remaining identity to a multiple of q^(k/2)+1.
  apply (mul_right_cancel₀ hne)
  linear_combination (norm := ring_nf) fktyScale * u * (-8 + 4*q + 4*q^3 + 12*q^4 + 8*q^5) / 3 * hp

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem degreeCorrect34 : DegreeCorrect 34 := by
  unfold DegreeCorrect
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem table34 : table 34 =
    #v[-1088, 0, -1088, 0, 0, -544, 0, 0, -1088, 0, 544, -1088, 544, 0, 0, -1088, -1088,
       544, 0, 544, 0, 0, 1088, 0, 0, 544, 0, -1088, 544, 544, 0, 0, 544, 2176] := by
  decide +kernel

/-- The finite first moment at the order-34 reflected cusp gives its normalized FKTY value. -/
theorem fktyPhi_eq_cuspMoment34 :
    fktyPhi (-1/34) = 2 * fktyScale * fktyCuspMoment 816 (integerNome (-1/816)) := by
  let q := integerNome (1/34)
  let u := integerNome (-1/816)
  have hq : IsPrimitiveRoot q 34 := by
    simpa [q, integerNome, mul_one_div] using Complex.isPrimitiveRoot_exp 34 (by decide)
  obtain ⟨hp, hne⟩ := primitive_relations (k := 17) (by decide) hq
  have hm := cuspMoment_table 34 (by decide) degreeCorrect34
  norm_num1 at hm
  rw [← neg_div] at hm
  rw [fktyPhi_neg_one_div_34, boundaryValue_cyclotomic34 _ hq, hm, table34]
  change (fktyScale * u) * _ = 2 * fktyScale * (-(u * ∑ j : Fin 34, _ * q^j.val) / 816)
  norm_num [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ]
  -- Multiplication by q+1 reduces the remaining identity to a multiple of q^(k/2)+1.
  apply (mul_right_cancel₀ hne)
  linear_combination (norm := ring_nf) fktyScale * u *
    (-20 + 4*q + 4*q^2 + 4*q^3 + 8*q^5 + 8*q^6 + 4*q^8 + 4*q^9 - 8*q^10 - 4*q^11 +
      8*q^12 + 4*q^13 + 4*q^15 + 20*q^16 + 16*q^17) / 3 * hp

end MockThetaAnalytic
