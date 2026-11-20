import QuantumStrange
import Mathlib.Analysis.SpecialFunctions.Pow.Complex

/-! Exact algebraic cusp values at the reflected arguments of FKTY, (1.9).
The two finite series are compared in the same quotient ℤ[X]/(Xᵏ+1).
The signed physical endpoint is the one defined by Folsom–Ono–Rhoades. -/
noncomputable section
namespace MockThetaAnalytic
open Complex KElimination.QuantumRadial KElimination.ResidueSeries

/-- First N terms of FKTY F(−1;q) from (1.2), including the initial minus sign. -/
def fNegPartial (N : ℕ) (q : ℂ) : ℂ :=
  sumBelow N (fun n => (-1 : ℂ)^(n+1) * pochhammer (-q) q n)

-- Coefficient vectors of elements of ℤ[X]/(Xᵏ+1); every operation is certified by evaluation.
private abbrev Coeff (k : ℕ) := Vector ℤ k

private noncomputable def ev (q : ℂ) (f : ℕ → ℤ) (n : ℕ) : ℂ :=
  Nat.rec 0 (fun j previous => previous + f j * q^j) n

private theorem ev_zero (q : ℂ) (f : ℕ → ℤ) : ev q f 0 = 0 := rfl

private theorem ev_succ (q : ℂ) (f : ℕ → ℤ) (n : ℕ) :
    ev q f (n+1) = ev q f n + f n * q^n := rfl

private def val {k : ℕ} (q : ℂ) (a : Coeff k) : ℂ := ev q (fun j => a.toArray[j]?.getD 0) k

private theorem ev_congr (q : ℂ) (f g : ℕ → ℤ) (n : ℕ) (h : ∀ i < n, f i = g i) :
    ev q f n = ev q g n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [ev_succ, ev_succ, ih (fun i hi => h i (by omega)), h n (by omega)]

private theorem val_mk {k : ℕ} (q : ℂ) (f : ℕ → ℤ) :
    val q (Vector.ofFn (fun i : Fin k => f i)) = ev q f k := by
  apply ev_congr
  intro i hi
  simp [Vector.ofFn, hi]

private def entry {k : ℕ} (a : Coeff k) (i : ℕ) : ℤ := a.toArray[i]?.getD 0

private def addVec {k : ℕ} (a b : Coeff k) : Coeff k :=
  Vector.ofFn fun i => entry a i + entry b i

private def scaleVec {k : ℕ} (t : ℤ) (a : Coeff k) : Coeff k :=
  Vector.ofFn fun i => t * entry a i

private def rotateVec {k : ℕ} (a : Coeff k) : Coeff k :=
  Vector.ofFn fun i => if i.val = 0 then -entry a (k-1) else entry a (i-1)

private noncomputable def shiftVec {k : ℕ} (a : Coeff k) (n : ℕ) : Coeff k :=
  Nat.rec a (fun _ v => rotateVec v) n

private theorem shiftVec_succ {k : ℕ} (a : Coeff k) (n : ℕ) :
    shiftVec a (n+1) = rotateVec (shiftVec a n) := rfl

private theorem val_add {k : ℕ} (q : ℂ) (a b : Coeff k) :
    val q (addVec a b) = val q a + val q b := by
  rw [addVec, val_mk q (fun i => entry a i + entry b i)]
  change _ = ev q (entry a) k + ev q (entry b) k
  suffices h : ∀ n, ev q (fun i => entry a i + entry b i) n = ev q (entry a) n + ev q (entry b) n from h k
  intro n
  induction n with
  | zero => simp [ev_zero]
  | succ n ih => simp only [ev_succ, ih, Int.cast_add]; ring

private theorem val_scale {k : ℕ} (q : ℂ) (t : ℤ) (a : Coeff k) :
    val q (scaleVec t a) = t * val q a := by
  rw [scaleVec, val_mk q (fun i => t * entry a i)]
  change _ = t * ev q (entry a) k
  suffices h : ∀ n, ev q (fun i => t * entry a i) n = t * ev q (entry a) n from h k
  intro n
  induction n with
  | zero => simp [ev_zero]
  | succ n ih => simp only [ev_succ, ih, Int.cast_mul]; ring

private theorem ev_successor (q : ℂ) (a : ℕ → ℤ) (b : ℤ) (n : ℕ) :
    ev q (fun i => if i=0 then b else a (i-1)) (n+1) = b + q * ev q a n := by
  induction n with
  | zero => simp [ev_zero, ev_succ]
  | succ n ih =>
    rw [ev_succ, ih, ev_succ]
    simp only [Nat.succ_ne_zero, if_false, Nat.add_sub_cancel, pow_succ]
    ring

private theorem val_rotate {k : ℕ} (q : ℂ) (hk : 0<k) (hq : q^k = -1) (a : Coeff k) :
    val q (rotateVec a) = q * val q a := by
  rw [rotateVec, val_mk q (fun i => if i=0 then -entry a (k-1) else entry a (i-1))]
  cases k with
  | zero => omega
  | succ n =>
    rw [ev_successor]
    change _ = q * (ev q (entry a) n + entry a n * q^n)
    simp only [Int.cast_neg, Nat.add_sub_cancel]
    rw [pow_succ] at hq
    linear_combination -((entry a n : ℤ) : ℂ) * hq

private theorem val_shift {k : ℕ} (q : ℂ) (hk : 0<k) (hq : q^k = -1) (a : Coeff k) (j : ℕ) :
    val q (shiftVec a j) = q^j * val q a := by
  induction j with
  | zero => simp [shiftVec]
  | succ j ih => rw [shiftVec_succ, val_rotate q hk hq, ih, pow_succ]; ring

private def constantVec (k : ℕ) (c : ℤ) : Coeff k := Vector.ofFn fun i => if i.val=0 then c else 0

private theorem val_constant (q : ℂ) (k : ℕ) (hk : 0<k) (c : ℤ) : val q (constantVec k c) = c := by
  rw [constantVec, val_mk q (fun i => if i=0 then c else 0)]
  cases k with
  | zero => omega
  | succ n =>
    rw [ev_successor q (fun _ => 0) c]
    have hz : ev q (fun _ => 0) n = 0 := by induction n <;> simp_all [ev_zero, ev_succ]
    rw [hz, mul_zero, add_zero]

private def factorVec {k : ℕ} (j : ℕ) (a : Coeff k) : Coeff k := addVec a (shiftVec a j)

private theorem val_factor {k : ℕ} (q : ℂ) (hk : 0<k) (hq : q^k = -1) (j : ℕ) (a : Coeff k) :
    val q (factorVec j a) = val q a * (1 + q^j) := by
  rw [factorVec, val_add, val_shift q hk hq]
  ring

private def advance {k : ℕ} (squared : Bool) (n : ℕ) (v : Coeff k × Coeff k) :
    Coeff k × Coeff k :=
  let p := factorVec (n+1) v.1
  (if squared then factorVec (n+1) p else p,
    addVec v.2 (if squared then shiftVec v.1 (n+1) else scaleVec ((-1)^(n+1)) v.1))

/-- Current product and accumulated sum for finite U (squared=true) or F (false). -/
private noncomputable def states (k : ℕ) (squared : Bool) (N : ℕ) : Coeff k × Coeff k :=
  Nat.rec (constantVec k 1, constantVec k 0) (advance squared) N

private theorem states_succ (k : ℕ) (squared : Bool) (n : ℕ) :
    states k squared (n+1) = advance squared n (states k squared n) := rfl

private theorem states_correct {k : ℕ} (q : ℂ) (hk : 0<k) (hq : q^k = -1)
    (squared : Bool) (n : ℕ) :
    val q (states k squared n).1 = (if squared then uProduct q n else pochhammer (-q) q n) ∧
    val q (states k squared n).2 = (if squared then uPartial n q else fNegPartial n q) := by
  induction n with
  | zero =>
    cases squared <;> simp [states, val_constant q k hk, uPartial, uPolynomial, fNegPartial, sumBelow,
      uProduct, pochhammer]
  | succ n ih =>
    obtain ⟨hp,hs⟩ := ih
    cases squared <;> simp only [Bool.false_eq_true, ite_false, ite_true] at hp hs ⊢
    · rw [states_succ, advance]
      simp only [Bool.false_eq_true, ite_false, val_factor q hk hq, val_add, val_scale, hp, hs]
      change _ = pochhammer (-q) q n * _ ∧ _ = fNegPartial n q + _
      push_cast
      constructor <;> ring
    · rw [states_succ, advance]
      simp only [ite_true, val_factor q hk hq, val_add, val_shift q hk hq, hp, hs]
      change _ = uProduct q n * _ ∧ _ = uPartial n q + _
      constructor <;> ring

private theorem uPartial_reduced5 (q : ℂ) (hq : q^5 = -1) :
    uPartial 5 q = -1 - q^3 - q^4 := by
  have hc : (states 5 true 5).2 = #v[-1, 0, 0, -1, -1] := by decide +kernel
  have he := (states_correct q (by decide) hq true 5).2
  simp [hc] at he
  rw [← he]
  norm_num [val, ev_succ, ev_zero]
  ring

private theorem fNegPartial_reduced5 (q : ℂ) (hq : q^5 = -1) :
    fNegPartial 5 q = -1 + q + q^2 := by
  have hc : (states 5 false 5).2 = #v[-1, 1, 1, 0, 0] := by decide +kernel
  have he := (states_correct q (by decide) hq false 5).2
  simp [hc] at he
  rw [← he]
  norm_num [val, ev_succ, ev_zero]

private theorem uPartial_reduced17 (q : ℂ) (hq : q^17 = -1) :
    uPartial 17 q = -1 - q^2 - q^5 - q^8 + q^10 - q^11 - q^15 - 2 * q^16 := by
  have hc : (states 17 true 17).2 = #v[-1, 0, -1, 0, 0, -1, 0, 0, -1, 0, 1, -1, 0, 0, 0, -1, -2] := by decide +kernel
  have he := (states_correct q (by decide) hq true 17).2
  simp [hc] at he
  rw [← he]
  norm_num [val, ev_succ, ev_zero]
  ring

private theorem fNegPartial_reduced17 (q : ℂ) (hq : q^17 = -1) :
    fNegPartial 17 q = -1 + 2 * q + q^2 + q^6 - q^7 + q^9 + q^12 + q^15 := by
  have hc : (states 17 false 17).2 = #v[-1, 2, 1, 0, 0, 0, 1, -1, 0, 1, 0, 0, 1, 0, 0, 1, 0] := by decide +kernel
  have he := (states_correct q (by decide) hq false 17).2
  simp [hc] at he
  rw [← he]
  norm_num [val, ev_succ, ev_zero]
  ring

private theorem reflected_power {k : ℕ} (q : ℂ) (hk : 0 < k) (hq : q^k = -1) (j : ℕ) (hj : j ≤ k) :
    (q⁻¹)^j = -q^(k-j) := by
  have h0 : q ≠ 0 := by rintro rfl; simp [zero_pow hk.ne'] at hq
  apply mul_left_cancel₀ (pow_ne_zero j h0)
  rw [inv_pow, mul_inv_cancel₀ (pow_ne_zero j h0), mul_neg, pow_mul_pow_sub q hj, hq, neg_neg]

/-- Exact finite specialization of the FKTY reflection at half-order five. -/
theorem fNegPartial_reflection5 (q : ℂ) (hq : q^5 = -1) :
    fNegPartial 5 q⁻¹ = uPartial 5 q := by
  rw [fNegPartial_reduced5 _ (by rw [inv_pow, hq]; norm_num), uPartial_reduced5 q hq]
  have hp := reflected_power q (by decide) hq
  rw [hp 2 (by decide), show q⁻¹ = -q^4 by simpa using hp 1 (by decide)]
  norm_num
  ring

/-- Exact finite specialization of the FKTY reflection at half-order seventeen. -/
theorem fNegPartial_reflection17 (q : ℂ) (hq : q^17 = -1) :
    fNegPartial 17 q⁻¹ = uPartial 17 q := by
  rw [fNegPartial_reduced17 _ (by rw [inv_pow, hq]; norm_num), uPartial_reduced17 q hq]
  have hp := reflected_power q (by decide) hq
  rw [hp 2 (by decide), hp 6 (by decide), hp 7 (by decide), hp 9 (by decide),
    hp 12 (by decide), hp 15 (by decide), show q⁻¹ = -q^16 by simpa using hp 1 (by decide)]
  norm_num
  ring

private theorem primitive_half {k : ℕ} {q : ℂ} (hk : 0 < k) (h : IsPrimitiveRoot q (2*k)) :
    q^k = -1 := by
  have hs : (q^k)^2 = 1 := by rw [← pow_mul, Nat.mul_comm k, h.pow_eq_one]
  exact (sq_eq_one_iff.mp hs).resolve_left (h.pow_ne_one_of_pos_of_lt hk.ne' (by omega))

private theorem add_one_ne_zero {L : ℕ} {q : ℂ} (hL : 2 < L) (h : IsPrimitiveRoot q L) :
    q + 1 ≠ 0 := by
  intro he
  have hq : q = -1 := by linear_combination he
  exact h.pow_ne_one_of_pos_of_lt (by decide : 2 ≠ 0) hL (by rw [hq]; norm_num)

/-- The unique representative of degree below four at a primitive tenth root. -/
theorem boundaryValue_cyclotomic10 (q : ℂ) (h : IsPrimitiveRoot q 10) :
    boundaryValue 5 q = 4*q - 4*q^2 + 8*q^3 := by
  have hq := primitive_half (k := 5) (by decide) h
  rw [boundaryValue, uPartial_reduced5 q hq]
  apply mul_right_cancel₀ (add_one_ne_zero (by decide) h)
  linear_combination 4 * hq

/-- The unique representative of degree below sixteen at a primitive 34th root. -/
theorem boundaryValue_cyclotomic34 (q : ℂ) (h : IsPrimitiveRoot q 34) :
    boundaryValue 17 q = -4 + 8*q - 4*q^2 + 8*q^3 - 8*q^4 + 12*q^5 - 8*q^6 +
      8*q^7 - 4*q^8 + 8*q^9 - 12*q^10 + 12*q^11 - 8*q^12 + 8*q^13 - 8*q^14 + 12*q^15 := by
  have hq := primitive_half (k := 17) (by decide) h
  rw [boundaryValue, uPartial_reduced17 q hq]
  apply mul_right_cancel₀ (add_one_ne_zero (by decide) h)
  linear_combination 8 * hq

/- The product of the even factors clears all the denominators in the
order-34 Watson head. In the second component, Wₙ is Dₙ times the sum of
the first n terms. Thus Wₙ₊₁ = (Wₙ + (−q)^(n²)) (1 + q^(2n+2)). -/
private def watsonAdvance (k n : ℕ) (v : Coeff k × Coeff k) : Coeff k × Coeff k :=
  let monomial := shiftVec (constantVec k ((-1)^(n^2))) (n^2 % (2*k))
  (factorVec (2*n+2) v.1, factorVec (2*n+2) (addVec v.2 monomial))

private def watsonStates (k N : ℕ) : Coeff k × Coeff k :=
  Nat.rec (constantVec k 1, constantVec k 0) (watsonAdvance k) N

private def watsonDen (q : ℂ) (n : ℕ) : ℂ := ∏ j ∈ Finset.range n, (1+q^(2*j+2))

private theorem watsonStates_correct (q : ℂ) (hq : q^17 = -1) (n : ℕ) :
    val q (watsonStates 17 n).1 = watsonDen q n ∧
    val q (watsonStates 17 n).2 = watsonDen q n *
      ∑ j ∈ Finset.range n, (-q)^(j^2) / watsonDen q j := by
  have h34 : q^34 = 1 := by
    rw [show 34 = 17*2 by decide, pow_mul, hq]
    norm_num
  have even_factor (i : ℕ) : 1+q^(2*i+2) ≠ 0 := by
    intro hz
    have he : q^(2*i+2) = -1 := by linear_combination hz
    have h : (q^(2*i+2))^17 = (-1 : ℂ)^17 := congrArg (·^(17:ℕ)) he
    rw [← pow_mul, show (2*i+2)*17=34*(i+1) by omega, pow_mul, h34] at h
    norm_num at h
  have hd (j : ℕ) : watsonDen q j ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ => even_factor i
  induction n with
  | zero =>
    simp [watsonStates, val_constant q 17 (by decide), watsonDen]
  | succ n ih =>
    change val q (watsonAdvance 17 n (watsonStates 17 n)).1 = _ ∧
      val q (watsonAdvance 17 n (watsonStates 17 n)).2 = _
    have hp : q^(n^2 % 34) = q^(n^2) := by
      conv_rhs => rw [← Nat.mod_add_div (n^2) 34, pow_add, pow_mul, h34, one_pow, mul_one]
    have den : watsonDen q (n+1) = watsonDen q n * (1+q^(2*n+2)) := Finset.prod_range_succ _ _
    simp only [watsonAdvance, val_factor q (by decide) hq, val_add, val_shift q (by decide) hq,
      val_constant q 17 (by decide), ih.1, ih.2, den, Finset.sum_range_succ]
    refine ⟨True.intro, ?_⟩
    change (_ + q^(n^2 % 34) * _) * _ = _
    rw [hp]
    push_cast
    rw [← neg_one_mul q, mul_pow]
    field_simp [hd n]

set_option maxHeartbeats 700000 in
/-- At a primitive order-34 root, the first 17 terms of the denominator
expansion of φ(−q), multiplied by four, give the exact FOR boundary value. -/
theorem watsonPhi_head34 (q : ℂ) (h : IsPrimitiveRoot q 34) :
    4 * (∑ n ∈ Finset.range 17, (-q)^(n^2) /
      ∏ j ∈ Finset.range n, (1+q^(2*j+2))) = boundaryValue 17 q := by
  have hq := primitive_half (k := 17) (by decide) h
  obtain ⟨hD,hW⟩ := watsonStates_correct q hq 17
  have hc : watsonStates 17 17 =
      (#v[7712,-7710,7710,-7710,7710,-7710,7710,-7710,7710,-7710,7710,-7710,7710,-7710,7710,-7710,7710],
       #v[15422,-15420,15422,-15420,15420,-15418,15420,-15420,15422,-15420,15418,-15418,15420,-15420,15420,-15418,15424]) := by
    decide +kernel
  rw [hc] at hD hW
  norm_num [val, ev_succ, ev_zero] at hD hW
  have den : watsonDen q 17 = 2 := by
    rw [← hD]
    apply mul_right_cancel₀ (add_one_ne_zero (by decide) h)
    linear_combination 7710 * hq
  rw [den] at hW
  change 4 * (∑ n ∈ Finset.range 17, (-q)^(n^2) / watsonDen q n) = _
  rw [show 4 * (∑ n ∈ Finset.range 17, (-q)^(n^2) / watsonDen q n) =
      2 * (2 * (∑ n ∈ Finset.range 17, (-q)^(n^2) / watsonDen q n)) by ring, ← hW,
      boundaryValue_cyclotomic34 _ h]
  apply mul_right_cancel₀ (add_one_ne_zero (by decide) h)
  linear_combination 30848 * hq

/-- The FKTY scale (12i)^(1/2), with Mathlib's principal complex power. -/
def fktyScale : ℂ := (12 * Complex.I : ℂ)^(1/2 : ℂ)

/-- The finite formula for FKTY φ₁,₂,₀(x) at reduced even-denominator cusps. -/
def fktyPhi (x : ℚ) : ℂ :=
  -4 * fktyScale * integerNome ((x : ℂ)/24) *
    fNegPartial (x.den/2) (integerNome (x : ℂ))

/-- At half-period k the finite F equals its infinite series since all higher
Pochhammer factors contain the zero factor 1+q^k. -/
theorem hasSum_fNegPartial (q : ℂ) (k : ℕ) (hk : 0 < k) (hq : q^k = -1) :
    HasSum (fun n : ℕ => (-1 : ℂ)^(n+1) * pochhammer (-q) q n) (fNegPartial k q) := by
  have hs (j : ℕ) : fNegPartial j q =
      ∑ n ∈ Finset.range j, (-1 : ℂ)^(n+1) * pochhammer (-q) q n := by
    induction j with
    | zero => simp [fNegPartial, sumBelow]
    | succ n ih =>
      rw [Finset.sum_range_succ, ← ih]
      rfl
  rw [hs]
  apply hasSum_sum_of_ne_finset_zero
  intro n hn
  have h := uProduct_zero_of_le q k n hk hq (by simpa using hn)
  rw [uProduct_eq_pochhammer] at h
  rw [eq_zero_of_pow_eq_zero h, mul_zero]

/-- On the FKTY domain S₂, exactly the reduced even-denominator rationals,
the finite definition agrees with the actual normalized strange series. -/
theorem fktyPhi_eq_tsum (x : ℚ) (hd : Even x.den) :
    fktyPhi x = -4 * fktyScale * integerNome ((x : ℂ)/24) *
      ∑' n : ℕ, (-1 : ℂ)^(n+1) * pochhammer (-integerNome x) (integerNome x) n := by
  obtain ⟨k, hk⟩ := hd
  have he : x.den = 2*k := by omega
  have hpos : 0 < k := by have := x.den_pos; omega
  have hp : IsPrimitiveRoot (integerNome (x : ℂ)) x.den := Complex.isPrimitiveRoot_exp_rat x
  rw [he] at hp
  rw [fktyPhi, (hasSum_fNegPartial _ k hpos (primitive_half hpos hp)).tsum_eq,
    show x.den/2 = k by omega]

/-- Translation fixes the root of unity and changes the FKTY normalizing phase. -/
theorem fktyPhi_add_one (x : ℚ) : fktyPhi (x+1) = integerNome (1/24) * fktyPhi x := by
  have hd : (x+1).den = x.den := Rat.add_intCast_den x 1
  have nome_add (z w : ℂ) : integerNome (z+w) = integerNome z * integerNome w := by
    simp [integerNome, mul_add, Complex.exp_add]
  simp only [fktyPhi, hd, Rat.cast_add, Rat.cast_one]
  rw [show ((x : ℂ)+1)/24 = 1/24 + (x : ℂ)/24 by ring, nome_add, nome_add,
    show integerNome 1 = 1 by simp [integerNome], mul_one]
  ring

private theorem reflected_nome (z : ℂ) : integerNome (-z) = (integerNome z)⁻¹ := by
  simp [integerNome, Complex.exp_neg]

/-- FKTY's negative quantum cusp is paired with the positive physical root. -/
theorem fktyPhi_neg_one_div_34 :
    fktyPhi (-1/34) = (fktyScale * integerNome (-1/816)) *
      boundaryValue 17 (integerNome (1/34)) := by
  have hp : IsPrimitiveRoot (integerNome (1/34)) 34 := by
    simpa [integerNome, mul_one_div] using Complex.isPrimitiveRoot_exp 34 (by decide)
  have hr := fNegPartial_reflection17 _ (primitive_half (k := 17) (by decide) hp)
  unfold fktyPhi
  norm_num1
  rw [reflected_nome (1/34), hr, boundaryValue]
  ring

/-- The transformed cusp −1/10 is paired with the order-ten physical root. -/
theorem fktyPhi_neg_one_div_10 :
    fktyPhi (-1/10) = (fktyScale * integerNome (-1/240)) *
      boundaryValue 5 (integerNome (1/10)) := by
  have hp : IsPrimitiveRoot (integerNome (1/10)) 10 := by
    simpa [integerNome, mul_one_div] using Complex.isPrimitiveRoot_exp 10 (by decide)
  have hr := fNegPartial_reflection5 _ (primitive_half (k := 5) (by decide) hp)
  unfold fktyPhi
  norm_num1
  rw [reflected_nome (1/10), hr, boundaryValue]
  ring

end MockThetaAnalytic
