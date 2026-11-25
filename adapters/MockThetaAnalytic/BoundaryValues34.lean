import QuantumStrange
import FORWatsonTerms
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.RingTheory.RootsOfUnity.Complex

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

private def shiftWithin {k : ℕ} (a : Coeff k) (n : ℕ) : Coeff k :=
  Vector.ofFn fun i => if n ≤ i.val then entry a (i.val-n) else -entry a (i.val+k-n)

private def shiftVec {k : ℕ} (a : Coeff k) (n : ℕ) : Coeff k :=
  scaleVec ((-1)^(n/k)) (shiftWithin a (n%k))

private theorem entry_shiftWithin {k : ℕ} (a : Coeff k) (n i : ℕ) (hi : i < k) :
    entry (shiftWithin a n) i = (if n ≤ i then entry a (i-n) else -entry a (i+k-n)) := by
  simp [entry, shiftWithin, Vector.ofFn, hi]

private theorem shiftWithin_zero {k : ℕ} (a : Coeff k) : shiftWithin a 0 = a := by
  apply Vector.ext
  intro i hi
  simp only [shiftWithin, Vector.getElem_ofFn, Nat.zero_le, if_true, Nat.sub_zero]
  simp [entry, hi]

private theorem shiftWithin_succ {k : ℕ} (a : Coeff k) (n : ℕ) (hn : n+1 < k) :
    shiftWithin a (n+1) = rotateVec (shiftWithin a n) := by
  apply Vector.ext
  intro i hi
  have hl : (shiftWithin a (n+1))[i] =
      (if n+1 ≤ i then entry a (i-(n+1)) else -entry a (i+k-(n+1))) := by simp [shiftWithin]
  have hr : (rotateVec (shiftWithin a n))[i] =
      (if i=0 then -entry (shiftWithin a n) (k-1) else entry (shiftWithin a n) (i-1)) := by simp [rotateVec]
  rw [hl, hr]
  by_cases hzero : i = 0
  · subst i
    rw [if_pos rfl, if_neg (by omega), entry_shiftWithin a n (k-1) (by omega), if_pos (by omega)]
    rw [show 0+k-(n+1) = k-1-n by omega]
  · rw [if_neg hzero, entry_shiftWithin a n (i-1) (by omega)]
    by_cases hle : n+1 ≤ i
    · rw [if_pos hle, if_pos (by omega), show i-(n+1) = i-1-n by omega]
    · rw [if_neg hle, if_neg (by omega), show i+k-(n+1) = i-1+k-n by omega]

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

private theorem val_shiftWithin {k : ℕ} (q : ℂ) (hk : 0<k) (hq : q^k = -1)
    (a : Coeff k) (j : ℕ) (hj : j < k) : val q (shiftWithin a j) = q^j * val q a := by
  induction j with
  | zero => simp [shiftWithin_zero]
  | succ j ih =>
    rw [shiftWithin_succ a j hj, val_rotate q hk hq, ih (by omega), pow_succ]
    ring

private theorem val_shift {k : ℕ} (q : ℂ) (hk : 0<k) (hq : q^k = -1) (a : Coeff k) (j : ℕ) :
    val q (shiftVec a j) = q^j * val q a := by
  rw [shiftVec, val_scale, val_shiftWithin q hk hq a _ (Nat.mod_lt _ hk)]
  have hj : q^j = q^(j%k)*(-1)^(j/k) := by
    conv_lhs => rw [← Nat.mod_add_div j k, pow_add, pow_mul, hq]
  rw [hj]
  push_cast
  ring

private def constantVec (k : ℕ) (c : ℤ) : Coeff k := Vector.ofFn fun i => if i.val=0 then c else 0

private theorem val_constant (q : ℂ) (k : ℕ) (hk : 0<k) (c : ℤ) : val q (constantVec k c) = c := by
  rw [constantVec, val_mk q (fun i => if i=0 then c else 0)]
  cases k with
  | zero => omega
  | succ n =>
    rw [ev_successor q (fun _ => 0) c]
    have hz : ev q (fun _ => 0) n = 0 := by induction n <;> simp_all [ev_zero, ev_succ]
    rw [hz, mul_zero, add_zero]

/-- The roots of Xᵏ+1 determine every complex polynomial of degree below k. -/
theorem polynomial_eq_zero_of_half_power_roots {k : ℕ} (p : Polynomial ℂ)
    (hdeg : p.natDegree < k) (h : ∀ q : ℂ, q^k = -1 → p.eval q = 0) : p = 0 := by
  have hk : 0 < k := Nat.zero_lt_of_lt hdeg
  let z := Complex.exp (2 * Real.pi * Complex.I / (2*k : ℕ))
  have hz : IsPrimitiveRoot z (2*k) := Complex.isPrimitiveRoot_exp _ (by omega)
  let root (i : Fin k) := z^(2*i.val+1)
  have hinj : Function.Injective root := by
    intro i j hij
    have he := hz.pow_inj (i := 2*i.val+1) (j := 2*j.val+1) (by omega) (by omega) hij
    exact Fin.ext (by omega)
  apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero p hinj
  · intro i
    apply h
    change (z^(2*i.val+1))^k = -1
    rw [pow_right_comm, primitive_even_half_power hk hz, pow_add, pow_mul]
    norm_num
  · simpa using hdeg

private theorem coeff_eq_zero_of_evaluations {k : ℕ} (hk : 0 < k) (a : Coeff k)
    (h : ∀ q : ℂ, q^k = -1 → val q a = 0) : a = constantVec k 0 := by
  let p : Polynomial ℂ := ∑ j ∈ Finset.range k, Polynomial.monomial j (entry a j : ℂ)
  have heval (q : ℂ) : p.eval q = val q a := by
    dsimp only [p]
    rw [Polynomial.eval_finset_sum]
    simp only [Polynomial.eval_monomial]
    change (∑ j ∈ Finset.range k, (entry a j : ℂ) * q^j) = ev q (entry a) k
    have hs (n : ℕ) : (∑ j ∈ Finset.range n, (entry a j : ℂ) * q^j) = ev q (entry a) n := by
      induction n with
      | zero => simp [ev_zero]
      | succ n ih => rw [Finset.sum_range_succ, ev_succ, ih]
    exact hs k
  have hp : p = 0 := by
    apply polynomial_eq_zero_of_half_power_roots (k := k) p
    · have hdeg : p.natDegree ≤ k-1 := by
        apply Polynomial.natDegree_sum_le_of_forall_le
        intro j hj
        have hjlt := Finset.mem_range.mp hj
        exact (Polynomial.natDegree_monomial_le (entry a j : ℂ) (m := j)).trans (by omega)
      omega
    · intro q hq
      exact (heval q).trans (h q hq)
  apply Vector.ext
  intro i hi
  have hc : p.coeff i = 0 := by simp [hp]
  have hentry : entry a i = 0 := by
    simpa [p, Polynomial.finset_sum_coeff, Polynomial.coeff_monomial, Finset.sum_ite_eq', hi] using hc
  simpa [entry, constantVec, hi] using hentry

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
private def states (k : ℕ) (squared : Bool) (N : ℕ) : Coeff k × Coeff k :=
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

/-- Reduction of the twelve terminating FKTY terms at the order-24 cusp. -/
theorem fNegPartial_reduced12 (q : ℂ) (hq : q^12 = -1) :
    fNegPartial 12 q = -1 + q - q^2 + q^3 - q^6 - q^9 - q^10 := by
  have hc : (states 12 false 12).2 = #v[-1,1,-1,1,0,0,-1,0,0,-1,-1,0] := by decide +kernel
  have he := (states_correct q (by decide) hq false 12).2
  simp [hc] at he
  rw [← he]
  norm_num [val, ev_succ, ev_zero]
  ring

private theorem uPartial_reduced12 (q : ℂ) (hq : q^12 = -1) :
    uPartial 12 q = -1 + q^2 + q^3 + q^6 - q^9 + q^10 - q^11 := by
  have hc : (states 12 true 12).2 = #v[-1,0,1,1,0,0,1,0,0,-1,1,-1] := by decide +kernel
  have he := (states_correct q (by decide) hq true 12).2
  simp [hc] at he
  rw [← he]
  norm_num [val, ev_succ, ev_zero]
  ring

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

/-- The reflected order-24 strange sum is the finite FOR unimodal sum. -/
theorem fNegPartial_reflection12 (q : ℂ) (hq : q^12 = -1) :
    fNegPartial 12 q⁻¹ = uPartial 12 q := by
  rw [fNegPartial_reduced12 _ (by rw [inv_pow, hq]; norm_num), uPartial_reduced12 q hq]
  have hp := reflected_power q (by decide) hq
  rw [hp 2 (by decide), hp 3 (by decide), hp 6 (by decide), hp 9 (by decide),
    hp 10 (by decide), show q⁻¹ = -q^11 by simpa using hp 1 (by decide)]
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

/- For a progression 1+q^(2j+first), Wₙ is Dₙ times the sum of
the first n terms. Thus Wₙ₊₁ = (Wₙ + (−q)^(n²)) (1 + q^(2n+first)). -/
private def watsonAdvance (k first n : ℕ) (v : Coeff k × Coeff k) : Coeff k × Coeff k :=
  let monomial := shiftVec (constantVec k ((-1)^(n^2))) (n^2 % (2*k))
  (factorVec (2*n+first) v.1, factorVec (2*n+first) (addVec v.2 monomial))

private def watsonStates (k first N : ℕ) : Coeff k × Coeff k :=
  Nat.rec (constantVec k 1, constantVec k 0) (watsonAdvance k first) N

/-- Product of the first n factors in a Watson denominator progression. -/
def watsonDen {R : Type*} [CommRing R] (q : R) (first n : ℕ) : R :=
  ∏ j ∈ Finset.range n, (1+q^(2*j+first))

private theorem watsonStates_correct {k first : ℕ} (q : ℂ) (hk : 0 < k) (hq : q^k = -1)
    (hfactor : ∀ j : ℕ, 1+q^(2*j+first) ≠ 0) (n : ℕ) :
    val q (watsonStates k first n).1 = watsonDen q first n ∧
    val q (watsonStates k first n).2 = watsonDen q first n *
      ∑ j ∈ Finset.range n, (-q)^(j^2) / watsonDen q first j := by
  have horder : q^(2*k) = 1 := by
    rw [Nat.mul_comm 2 k, pow_mul, hq]
    norm_num
  have hd (j : ℕ) : watsonDen q first j ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ => hfactor i
  induction n with
  | zero =>
    simp [watsonStates, val_constant q k hk, watsonDen]
  | succ n ih =>
    change val q (watsonAdvance k first n (watsonStates k first n)).1 = _ ∧
      val q (watsonAdvance k first n (watsonStates k first n)).2 = _
    have hp : q^(n^2 % (2*k)) = q^(n^2) := by
      conv_rhs => rw [← Nat.mod_add_div (n^2) (2*k), pow_add, pow_mul, horder, one_pow, mul_one]
    have den : watsonDen q first (n+1) = watsonDen q first n * (1+q^(2*n+first)) :=
      Finset.prod_range_succ _ _
    simp only [watsonAdvance, val_factor q hk hq, val_add, val_shift q hk hq,
      val_constant q k hk, ih.1, ih.2, den, Finset.sum_range_succ]
    refine ⟨True.intro, ?_⟩
    change (_ + q^(n^2 % (2*k)) * _) * _ = _
    rw [hp]
    push_cast
    rw [← neg_one_mul q, mul_pow]
    field_simp [hd n]

private def convolution {k : ℕ} (a b : Coeff k) (n : ℕ) : Coeff k :=
  Nat.rec (constantVec k 0) (fun j v => addVec v (scaleVec (entry b j) (shiftVec a j))) n

private theorem val_convolution {k : ℕ} (q : ℂ) (hk : 0 < k) (hq : q^k = -1)
    (a b : Coeff k) (n : ℕ) : val q (convolution a b n) = val q a * ev q (entry b) n := by
  induction n with
  | zero => simp [convolution, ev_zero, val_constant q k hk]
  | succ n ih =>
    change val q (addVec (convolution a b n) (scaleVec (entry b n) (shiftVec a n))) = _
    rw [val_add, val_scale, val_shift q hk hq, ih, ev_succ]
    ring

/-- The finite value given by the convergent Watson series at order 2k. -/
def watsonFiniteBoundary (k : ℕ) (q : ℂ) : ℂ :=
  if Even k then -4 * (2 * ∑ n ∈ Finset.range k, watsonTerm 1 q n) + 4
  else 4 * ∑ n ∈ Finset.range k, watsonTerm 2 q n

private def watsonBoundaryDifference (k : ℕ) : Coeff k :=
  let c := if Even k then 1 else 2
  let (denominator, numerator) := watsonStates k c k
  let u := (states k true k).2
  let target := if Even k then addVec u (constantVec k 1) else scaleVec (-2) u
  let product := convolution target (addVec denominator (constantVec k (-1))) k
  addVec numerator (scaleVec (-1) product)

/-- Check the denominator-cleared Watson identity in ℤ[X]/(Xᵏ+1).
For primitive order 2k the evaluated denominator is 2. Retaining its
polynomial before evaluation also handles imprimitive roots in this quotient. -/
def watsonBoundaryCertificate (k : ℕ) : Bool :=
  decide (watsonBoundaryDifference k = constantVec k 0)

/-- The scalar difference computed by the denominator-cleared quotient certificate. -/
def watsonClearedDifference (k : ℕ) (q : ℂ) : ℂ :=
  let c := if Even k then 1 else 2
  let D := ∏ j ∈ Finset.range k, (1+q^(2*j+c))
  D * (∑ j ∈ Finset.range k, watsonTerm c q j) -
    (D-1) * (if Even k then 1 + uPartial k q else -2 * uPartial k q)

private theorem val_watsonBoundaryDifference {q : ℂ} {k : ℕ} (hk : 0 < k) (hq : q^k = -1) :
    val q (watsonBoundaryDifference k) = watsonClearedDifference k q := by
  let c := if Even k then 1 else 2
  have hc : Odd (k+c) := by
    by_cases he : Even k
    · simp [c, he]
    · simpa [c, he] using (Nat.not_even_iff_odd.mp he).add_even (by decide : Even 2)
  obtain ⟨hD,hW⟩ := watsonStates_correct (first := c) q hk hq
    (watson_factor_ne_zero_of_half_power hq hc) k
  have hU : val q (states k true k).2 = uPartial k q := by
    simpa using (states_correct q hk hq true k).2
  unfold watsonBoundaryDifference
  dsimp only
  simp only [val_add, val_scale, val_convolution q hk hq]
  change val q (watsonStates k c k).2 + (-1:ℤ) *
    (val q (if Even k then addVec (states k true k).2 (constantVec k 1) else
      scaleVec (-2) (states k true k).2) * val q (addVec (watsonStates k c k).1 (constantVec k (-1)))) =
    watsonDen q c k * (∑ j ∈ Finset.range k, watsonTerm c q j) -
      (watsonDen q c k-1) * (if Even k then 1 + uPartial k q else -2 * uPartial k q)
  rw [val_add, val_constant q k hk, hD, hW]
  by_cases he : Even k <;>
    simp only [he, if_pos, if_false, val_add, val_scale, hU, val_constant q k hk] <;>
    push_cast <;> change watsonDen q c k * (∑ j ∈ Finset.range k, watsonTerm c q j) + _ = _ <;>
    ring

/-- The integer vector vanishes exactly when its cleared identity holds at
every root of Xᵏ+1. This includes roots with smaller order than 2k. -/
theorem watsonBoundaryCertificate_iff_cleared_zero {k : ℕ} (hk : 0 < k) :
    watsonBoundaryCertificate k = true ↔
      ∀ q : ℂ, q^k = -1 → watsonClearedDifference k q = 0 := by
  constructor
  · intro hcert q hq
    rw [← val_watsonBoundaryDifference hk hq, of_decide_eq_true hcert, val_constant q k hk]
    simp
  · intro h
    apply decide_eq_true
    apply coeff_eq_zero_of_evaluations hk
    intro q hq
    rw [val_watsonBoundaryDifference hk hq, h q hq]

/-- A checked integer polynomial gives the equality at every primitive
root of the specified order. -/
theorem watsonFiniteBoundary_eq_of_certificate {q : ℂ} {k : ℕ} (hk : 0 < k)
    (hroot : IsPrimitiveRoot q (2*k)) (hcert : watsonBoundaryCertificate k = true) :
    watsonFiniteBoundary k q = boundaryValue k q := by
  have hzero := (watsonBoundaryCertificate_iff_cleared_zero hk).mp hcert q
    (primitive_even_half_power hk hroot)
  by_cases he : Even k
  · have hD : (∏ j ∈ Finset.range k, (1+q^(2*j+1))) = 2 := by
      simpa using watson_denominator_block hk hroot 1 (by simpa using he.add_odd odd_one) 0
    simp only [watsonClearedDifference, he, if_pos, hD, watsonFiniteBoundary, boundaryValue] at hzero ⊢
    linear_combination (-4)*hzero
  · have hc := (Nat.not_even_iff_odd.mp he).add_even (by decide : Even 2)
    have hD : (∏ j ∈ Finset.range k, (1+q^(2*j+2))) = 2 := by
      simpa using watson_denominator_block hk hroot 2 hc 0
    simp only [watsonClearedDifference, he, if_false, hD, watsonFiniteBoundary, boundaryValue] at hzero ⊢
    linear_combination 2*hzero

set_option maxHeartbeats 700000 in
/-- At a primitive order-34 root, the first 17 terms of the denominator
expansion of φ(−q), multiplied by four, give the exact FOR boundary value. -/
theorem watsonPhi_head34 (q : ℂ) (h : IsPrimitiveRoot q 34) :
    4 * (∑ n ∈ Finset.range 17, (-q)^(n^2) /
      ∏ j ∈ Finset.range n, (1+q^(2*j+2))) = boundaryValue 17 q := by
  have hq := primitive_half (k := 17) (by decide) h
  have hfactor (i : ℕ) : 1+q^(2*i+2) ≠ 0 := by
    intro hz
    have he : q^(2*i+2) = -1 := by linear_combination hz
    have hp : (q^(2*i+2))^17 = (-1:ℂ)^17 := congrArg (·^(17:ℕ)) he
    rw [← pow_mul, show (2*i+2)*17=34*(i+1) by omega, pow_mul, h.pow_eq_one, one_pow] at hp
    norm_num at hp
  obtain ⟨hD,hW⟩ := watsonStates_correct q (by decide) hq hfactor 17
  have hc : watsonStates 17 2 17 =
      (#v[7712,-7710,7710,-7710,7710,-7710,7710,-7710,7710,-7710,7710,-7710,7710,-7710,7710,-7710,7710],
       #v[15422,-15420,15422,-15420,15420,-15418,15420,-15420,15422,-15420,15418,-15418,15420,-15420,15420,-15418,15424]) := by
    decide +kernel
  rw [hc] at hD hW
  norm_num [val, ev_succ, ev_zero] at hD hW
  have den : watsonDen q 2 17 = 2 := by
    rw [← hD]
    apply mul_right_cancel₀ (add_one_ne_zero (by decide) h)
    linear_combination 7710 * hq
  rw [den] at hW
  change 4 * (∑ n ∈ Finset.range 17, (-q)^(n^2) / watsonDen q 2 n) = _
  rw [show 4 * (∑ n ∈ Finset.range 17, (-q)^(n^2) / watsonDen q 2 n) =
      2 * (2 * (∑ n ∈ Finset.range 17, (-q)^(n^2) / watsonDen q 2 n)) by ring, ← hW,
      boundaryValue_cyclotomic34 _ h]
  apply mul_right_cancel₀ (add_one_ne_zero (by decide) h)
  linear_combination 30848 * hq

set_option maxHeartbeats 700000 in
/-- The finite head of ψ(−q), including its temporary zero-index term,
gives the FOR value at every primitive 24th root. -/
theorem watsonPsi_head24 (q : ℂ) (h : IsPrimitiveRoot q 24) :
    -4 * (2 * (∑ n ∈ Finset.range 12, (-q)^(n^2) /
      ∏ j ∈ Finset.range n, (1+q^(2*j+1))) - 1) = boundaryValue 12 q := by
  have hq := primitive_half (k := 12) (by decide) h
  have hfactor (i : ℕ) : 1+q^(2*i+1) ≠ 0 := by
    intro hz
    have he : q^(2*i+1) = -1 := by linear_combination hz
    have hp : (q^(2*i+1))^12 = (-1:ℂ)^12 := congrArg (·^(12:ℕ)) he
    rw [pow_right_comm, hq, pow_add, pow_mul] at hp
    norm_num at hp
  have hc : watsonStates 12 1 12 =
      (#v[4,0,0,0,-2,0,0,0,2,0,0,0], #v[0,-2,3,1,0,2,-1,0,0,-3,3,-1]) := by decide +kernel
  obtain ⟨hD,hW⟩ := watsonStates_correct q (by decide) hq hfactor 12
  rw [hc] at hD hW
  norm_num [val, ev_succ, ev_zero] at hD hW
  have hfactor4 : q^4+1 ≠ 0 := by
    intro hz
    have he : q^4 = -1 := by linear_combination hz
    apply h.pow_ne_one_of_pos_of_lt (by decide : 8 ≠ 0) (by decide : 8 < 24)
    rw [show 8=4*2 by decide, pow_mul, he]
    norm_num
  have hcycl : q^8-q^4+1 = 0 := by
    apply mul_right_cancel₀ hfactor4
    linear_combination hq
  have den : watsonDen q 1 12 = 2 := by
    rw [← hD]
    linear_combination 2*hcycl
  rw [den] at hW
  change (-4) * (2 * (∑ n ∈ Finset.range 12, (-q)^(n^2) / watsonDen q 1 n) - 1) = _
  rw [← hW, boundaryValue, uPartial_reduced12 q hq]
  linear_combination (-4)*(2*q^2-2*q)*hcycl

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

/-- The reflected order-24 value carries the same normalization as at orders 10 and 34. -/
theorem fktyPhi_neg_one_div_24 :
    fktyPhi (-1/24) = (fktyScale * integerNome (-1/576)) *
      boundaryValue 12 (integerNome (1/24)) := by
  have hp : IsPrimitiveRoot (integerNome (1/24)) 24 := by
    simpa [integerNome, mul_one_div] using Complex.isPrimitiveRoot_exp 24 (by decide)
  have hr := fNegPartial_reflection12 _ (primitive_half (k := 12) (by decide) hp)
  unfold fktyPhi
  norm_num1
  rw [reflected_nome (1/24), hr, boundaryValue]
  ring

end MockThetaAnalytic
