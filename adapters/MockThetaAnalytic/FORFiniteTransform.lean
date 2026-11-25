import FORCyclotomicBlock
import QuantumRadial
import Mathlib.Tactic.LinearCombination

/-! A root-of-unity case of Lovejoy's finite transformation, equation (2.3).
The monomial and Newton sums obey the same first-order recurrence on the
root orbit. The equation at one supplies the initial value at the next root. -/

noncomputable section
namespace MockThetaAnalytic

open Finset KElimination.QuantumRadial

theorem pochhammer_eq_prod (b Q : ℂ) (n : ℕ) :
    pochhammer b Q n = ∏ j ∈ range n, (1 - b*Q^j) := by
  induction n with
  | zero => simp [pochhammer]
  | succ n ih => rw [pochhammer, prod_range_succ, ih]

private def newtonFactor (Q z : ℂ) (n : ℕ) : ℂ := ∏ j ∈ range n, (z-Q^(j+1))

private def newtonCoeff (Q b : ℂ) (n : ℕ) : ℂ := pochhammer b Q n / (b^n*Q^(n*(n+1)))

private def powerSum (Q b z : ℂ) (N : ℕ) : ℂ := ∑ n ∈ range N, pochhammer b Q n*z^n

private def newtonSum (Q b z : ℂ) (N : ℕ) : ℂ :=
  ∑ n ∈ range N, newtonCoeff Q b n * newtonFactor Q z n

private theorem powerSum_step (Q b z : ℂ) (N : ℕ) :
    (1-z)*powerSum Q b z (N+1) + b*z*powerSum Q b (Q*z) (N+1) =
      1-pochhammer b Q (N+1)*z^(N+1) := by
  induction N with
  | zero => simp [powerSum, pochhammer]; ring
  | succ n ih =>
    have step (x : ℂ) : powerSum Q b x (n+1+1) =
        powerSum Q b x (n+1)+pochhammer b Q (n+1)*x^(n+1) := sum_range_succ _ _
    rw [step, step, show pochhammer b Q (n+1+1) = pochhammer b Q (n+1)*(1-b*Q^(n+1)) by rfl,
      pow_succ z (n+1), mul_pow Q z]
    linear_combination ih

private theorem newtonCoeff_step {Q b : ℂ} (hQ : Q ≠ 0) (hb : b ≠ 0) (n : ℕ) :
    newtonCoeff Q b (n+1)*b*Q^(2*(n+1)) = newtonCoeff Q b n*(1-b*Q^n) := by
  rw [newtonCoeff, newtonCoeff, pochhammer, pow_succ b n, show
    (n+1)*(n+1+1)=n*(n+1)+2*(n+1) by ring, pow_add]
  field_simp

private theorem newtonFactor_step (Q z : ℂ) (n : ℕ) :
    newtonFactor Q (Q*z) (n+1) = Q^(n+1)*(z-1)*newtonFactor Q z n := by
  calc
    _ = ∏ j ∈ range (n+1), Q*(z-Q^j) := by
      apply prod_congr rfl
      intro j _
      rw [pow_succ' Q j, mul_sub]
    _ = _ := by
      rw [prod_mul_distrib, prod_const, card_range, prod_range_succ']
      simp only [pow_zero, newtonFactor]
      ring

private theorem newtonSum_step {Q b : ℂ} (hQ : Q ≠ 0) (hb : b ≠ 0) (z : ℂ) (N : ℕ) :
    (1-z)*newtonSum Q b z (N+1) + b*z*newtonSum Q b (Q*z) (N+1) =
      b+(1-z)*newtonCoeff Q b N*(1-b*Q^N)*newtonFactor Q z N := by
  induction N with
  | zero => simp [newtonSum, newtonCoeff, newtonFactor, pochhammer]; ring
  | succ n ih =>
    have step (x : ℂ) : newtonSum Q b x (n+1+1) =
        newtonSum Q b x (n+1)+newtonCoeff Q b (n+1)*newtonFactor Q x (n+1) := sum_range_succ _ _
    rw [step, step, newtonFactor_step]
    have hf : newtonFactor Q z (n+1) = newtonFactor Q z n*(z-Q^(n+1)) := prod_range_succ _ _
    rw [hf]
    have hc := newtonCoeff_step hQ hb n
    rw [Nat.mul_comm 2 (n+1), pow_mul Q (n+1) 2] at hc
    linear_combination ih - (1-z)*newtonFactor Q z n*hc

private theorem newtonFactor_last {Q z : ℂ} {k : ℕ} (hk : 0 < k) (hQ : IsPrimitiveRoot Q k)
    (hz : z^k = 1) : (1-z)*newtonFactor Q z (k-1) = 0 := by
  letI : NeZero k := ⟨hk.ne'⟩
  by_cases hz1 : z = 1
  · simp [hz1]
  obtain ⟨j,hj,he⟩ := hQ.eq_pow_of_pow_eq_one hz
  have hj0 : 0 < j := by
    by_contra h
    have he' : j = 0 := by omega
    exact hz1 (by simpa [he'] using he.symm)
  have hp : newtonFactor Q z (k-1) = 0 := by
    apply prod_eq_zero (i := j-1) (mem_range.mpr (by omega))
    rw [Nat.sub_add_cancel hj0, he, sub_self]
  rw [hp, mul_zero]

/-- Lovejoy's finite root transformation, evaluated at a point of the same
root orbit as the base. The right side is written in the Newton basis. -/
theorem finite_root_transform {Q z : ℂ} {k : ℕ} (hk : 0 < k)
    (hQ : IsPrimitiveRoot Q k) (hz : z^k = 1) {b : ℂ} (hb : b ≠ 0) :
    (∑ n ∈ range k, pochhammer b Q n*z^n) = b^(k-1)*
      ∑ n ∈ range k, (pochhammer b Q n / (b^n*Q^(n*(n+1))))*
        ∏ j ∈ range n, (z-Q^(j+1)) := by
  letI : NeZero k := ⟨hk.ne'⟩
  let d (x : ℂ) := powerSum Q b x k - b^(k-1)*newtonSum Q b x k
  have hq0 := hQ.ne_zero hk.ne'
  have hs : pochhammer b Q k = 1-b^k := by
    rw [pochhammer_eq_prod]
    simpa only [neg_mul, sub_eq_add_neg, neg_neg] using prod_one_add_pow hk hQ (-b)
  have hbpow : b^(k-1)*b = b^k := by rw [← pow_succ, Nat.sub_add_cancel hk]
  have hd (x : ℂ) (hx : x^k = 1) : (1-x)*d x+b*x*d (Q*x) = 0 := by
    have hp := powerSum_step Q b x (k-1)
    rw [Nat.sub_add_cancel hk, hs, hx, mul_one, sub_sub_cancel] at hp
    have hn := newtonSum_step hq0 hb x (k-1)
    rw [Nat.sub_add_cancel hk] at hn
    have hn' : (1-x)*newtonSum Q b x k+b*x*newtonSum Q b (Q*x) k = b := by
      linear_combination hn + newtonCoeff Q b (k-1)*(1-b*Q^(k-1))*newtonFactor_last hk hQ hx
    dsimp [d]
    linear_combination hp - b^(k-1)*hn' - hbpow
  have hpow (n : ℕ) : d (Q^(n+1)) = 0 := by
    induction n with
    | zero =>
      have h := hd 1 (one_pow k)
      simp only [sub_self, zero_mul, mul_one, zero_add] at h
      simpa only [Nat.zero_add, pow_one] using (mul_eq_zero.mp h).resolve_left hb
    | succ n ih =>
      have hx : (Q^(n+1))^k = 1 := by rw [pow_right_comm, hQ.pow_eq_one, one_pow]
      have h := hd _ hx
      rw [ih, mul_zero, zero_add, ← pow_succ' Q] at h
      exact (mul_eq_zero.mp h).resolve_left (mul_ne_zero hb (pow_ne_zero _ hq0))
  obtain ⟨j,_,he⟩ := hQ.eq_pow_of_pow_eq_one hz
  have hdz : d z = 0 := by
    rw [← he]
    cases j with
    | zero => simpa only [Nat.sub_add_cancel hk, hQ.pow_eq_one, pow_zero] using hpow (k-1)
    | succ n => exact hpow n
  exact sub_eq_zero.mp hdz

open Polynomial in
/-- Both sides have degree below k, so agreement on the primitive orbit
gives the finite transformation at every argument. -/
theorem finite_root_transform_at {Q : ℂ} {k : ℕ} (hk : 0 < k)
    (hQ : IsPrimitiveRoot Q k) {b : ℂ} (hb : b ≠ 0) (z : ℂ) :
    (∑ n ∈ range k, pochhammer b Q n*z^n) = b^(k-1)*
      ∑ n ∈ range k, (pochhammer b Q n / (b^n*Q^(n*(n+1))))*
        ∏ j ∈ range n, (z-Q^(j+1)) := by
  classical
  let P : ℂ[X] := ∑ n ∈ range k, C (pochhammer b Q n)*X^n
  let N : ℂ[X] := C (b^(k-1)) * ∑ n ∈ range k,
    C (newtonCoeff Q b n) * ∏ j ∈ range n, (X-C (Q^(j+1)))
  have hP (w : ℂ) : P.eval w = powerSum Q b w k := by simp [P, powerSum, eval_finset_sum]
  have hN (w : ℂ) : N.eval w = b^(k-1)*newtonSum Q b w k := by
    simp [N, newtonSum, newtonFactor, eval_finset_sum, eval_prod]
  have hPdeg : P.natDegree ≤ k-1 := by
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro n hn
    exact (Polynomial.natDegree_C_mul_le _ _).trans <| by
      simpa using Nat.le_pred_of_lt (mem_range.mp hn)
  have hNdeg : N.natDegree ≤ k-1 := by
    apply (Polynomial.natDegree_C_mul_le _ _).trans
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro n hn
    refine (Polynomial.natDegree_C_mul_le _ _).trans ((Polynomial.natDegree_prod_le _ _).trans ?_)
    simpa only [Polynomial.natDegree_X_sub_C, sum_const, card_range, nsmul_eq_mul, mul_one] using
      Nat.le_pred_of_lt (mem_range.mp hn)
  have he : P = N := by
    apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq P N
      (f := fun i : Fin k => Q^i.val) (fun i j h => Fin.ext (hQ.pow_inj i.isLt j.isLt h))
    · intro i
      rw [hP, hN]
      exact finite_root_transform hk hQ (by rw [pow_right_comm, hQ.pow_eq_one, one_pow]) hb
    · simpa using (max_le hPdeg hNdeg).trans_lt (Nat.pred_lt hk.ne')
  change powerSum Q b z k = b^(k-1)*newtonSum Q b z k
  rw [← hP, ← hN, he]

end MockThetaAnalytic
