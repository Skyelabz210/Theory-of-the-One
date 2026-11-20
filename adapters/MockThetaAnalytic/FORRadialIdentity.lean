import MockHolomorphic
import Mathlib.Analysis.SpecialFunctions.Log.Summable

/-! A least-part expansion in the proof of Watson's third-order identity.
The adjacent square exponents pair the even and odd product tails. -/
noncomputable section

namespace MockThetaAnalytic

open Filter
open scoped Topology

private def progressionTail (q : ℂ) (c j : ℕ) : ℂ :=
  ∏' n : ℕ, (1 + q^(2*(n+j)+c))

/-- Odd factors strictly beyond the first j odd exponents. -/
def watsonOddTail (q : ℂ) (j : ℕ) : ℂ := progressionTail q 1 j

/-- Even factors strictly beyond the first j even exponents. -/
def watsonEvenTail (q : ℂ) (j : ℕ) : ℂ := progressionTail q 2 j

/-- The contribution in which an odd part is selected first, after a k by k square. -/
def watsonA (q : ℂ) (k : ℕ) : ℂ :=
  ∑' j : ℕ, q^(k*k+2*j+1) * watsonOddTail q (j+1) * watsonEvenTail q (k+j)

/-- The nonnegative half of the alternating square theta series. -/
def watsonThetaHalf (q : ℂ) : ℂ := ∑' k : ℕ, (-1:ℂ)^k * q^(k*k)

private theorem progression_norm_summable {q : ℂ} (hq : ‖q‖ < 1) (c j : ℕ) :
    Summable (fun n : ℕ => ‖q^(2*(n+j)+c)‖) := by
  simp only [norm_pow]
  exact (summable_geometric_of_lt_one (norm_nonneg q) hq).comp_injective
    (i := fun n : ℕ => 2*(n+j)+c) (fun _ _ h => by dsimp at h; omega)

theorem watsonOddTail_hasProd {q : ℂ} (hq : ‖q‖ < 1) (j : ℕ) :
    HasProd (fun n : ℕ => 1 + q^(2*(n+j)+1)) (watsonOddTail q j) :=
  (multipliable_one_add_of_summable (progression_norm_summable hq 1 j)).hasProd

theorem watsonEvenTail_hasProd {q : ℂ} (hq : ‖q‖ < 1) (j : ℕ) :
    HasProd (fun n : ℕ => 1 + q^(2*(n+j)+2)) (watsonEvenTail q j) :=
  (multipliable_one_add_of_summable (progression_norm_summable hq 2 j)).hasProd

private theorem progression_factor_ne {q : ℂ} (hq : ‖q‖ < 1) {c : ℕ} (hc : 0<c) (n : ℕ) :
    1 + q^(2*n+c) ≠ 0 := by
  intro h
  have hneg : q^(2*n+c) = -1 := by linear_combination h
  have lt : ‖q^(2*n+c)‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg q) hq (by omega)
  simp [hneg] at lt

private theorem tendsto_progressionTail {q : ℂ} (hq : ‖q‖ < 1) {c : ℕ} (hc : 0<c) :
    Tendsto (progressionTail q c) atTop (𝓝 1) := by
  let f (n : ℕ) : ℂ := 1 + q^(2*n+c)
  have hnorm : Summable (fun n : ℕ => ‖q^(2*n+c)‖) := by
    simpa using progression_norm_summable hq c 0
  have hP : Multipliable f := multipliable_one_add_of_summable hnorm
  have hn : (∏' n, f n) ≠ 0 := tprod_one_add_ne_zero_of_summable (progression_factor_ne hq hc) hnorm
  have h := (tendsto_const_nhds (x := ∏' n, f n)).div hP.tendsto_prod_tprod_nat hn
  rw [div_self hn] at h
  apply h.congr
  intro j
  have ht : HasProd (fun n => f (n+j)) (progressionTail q c j) :=
    (multipliable_one_add_of_summable (progression_norm_summable hq c j)).hasProd
  apply (div_eq_iff (Finset.prod_ne_zero_iff.mpr fun i _ => progression_factor_ne hq hc i)).2
  rw [mul_comm]
  exact ht.prod_range_mul.tprod_eq

private theorem progression_split {q : ℂ} (hq : ‖q‖ < 1) (c j : ℕ) :
    progressionTail q c j = (1+q^(2*j+c))*progressionTail q c (j+1) := by
  let f (n : ℕ) := 1 + q^(2*(n+j)+c)
  have ht : HasProd (fun n => f (n+1)) (progressionTail q c (j+1)) := by
    have h := (multipliable_one_add_of_summable (progression_norm_summable hq c (j+1))).hasProd
    simpa only [f, Nat.add_right_comm _ 1 j, Nat.add_assoc] using h
  simpa [f, progressionTail] using ht.zero_mul.tprod_eq

private theorem tail_bounds {q : ℂ} (hq : ‖q‖ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ (∀ j, ‖watsonOddTail q j‖ ≤ C) ∧ (∀ j, ‖watsonEvenTail q j‖ ≤ C) := by
  obtain ⟨a, ha⟩ := (tendsto_progressionTail hq (c := 1) (by decide)).norm.bddAbove_range
  obtain ⟨b, hb⟩ := (tendsto_progressionTail hq (c := 2) (by decide)).norm.bddAbove_range
  refine ⟨max 0 (max a b), le_max_left .., fun j => ?_, fun j => ?_⟩
  · exact (ha ⟨j,rfl⟩).trans ((le_max_left a b).trans (le_max_right ..))
  · exact (hb ⟨j,rfl⟩).trans ((le_max_right a b).trans (le_max_right ..))

private def oddChoice (q : ℂ) (k j : ℕ) :=
  q^(k*k+2*j+1) * watsonOddTail q (j+1) * watsonEvenTail q (k+j)

private theorem oddChoice_bound {q : ℂ} (hq : ‖q‖ < 1) {C : ℝ} (hc : 0 ≤ C)
    (ho : ∀ j, ‖watsonOddTail q j‖ ≤ C) (he : ∀ j, ‖watsonEvenTail q j‖ ≤ C) (k j : ℕ) :
    ‖oddChoice q k j‖ ≤ (‖q‖^k * C*C)*‖q‖^j := by
  have h : k+j ≤ k*k+2*j+1 := by
    have : k ≤ k*k := Nat.le_self_pow (by decide : 2 ≠ 0) k |>.trans_eq (pow_two k)
    omega
  have hpow := pow_le_pow_of_le_one (norm_nonneg q) hq.le h
  rw [oddChoice, norm_mul, norm_mul, norm_pow]
  calc
    _ ≤ (‖q‖^(k+j))*C*C :=
      mul_le_mul (mul_le_mul hpow (ho _) (norm_nonneg _) (by positivity)) (he _)
        (norm_nonneg _) (by positivity)
    _ = _ := by rw [pow_add]; ring

theorem watsonA_hasSum {q : ℂ} (hq : ‖q‖ < 1) (k : ℕ) :
    HasSum (fun j : ℕ => q^(k*k+2*j+1)*watsonOddTail q (j+1)*watsonEvenTail q (k+j))
      (watsonA q k) := by
  obtain ⟨C,hC,ho,he⟩ := tail_bounds hq
  exact ((summable_geometric_of_lt_one (norm_nonneg q) hq).mul_left
    (‖q‖^k*C*C)).of_norm_bounded (oddChoice_bound hq hC ho he k) |>.hasSum

private theorem summable_watsonA {q : ℂ} (hq : ‖q‖ < 1) : Summable (watsonA q) := by
  obtain ⟨C,hC,ho,he⟩ := tail_bounds hq
  let S := ∑' j : ℕ, ‖q‖^j
  have hg := summable_geometric_of_lt_one (norm_nonneg q) hq
  apply (hg.mul_right (C*C*S)).of_norm_bounded
  intro k
  have h := tsum_of_norm_bounded (hg.hasSum.mul_left (‖q‖^k*C*C)) (oddChoice_bound hq hC ho he k)
  change ‖watsonA q k‖ ≤ ‖q‖^k * (C*C*S)
  convert h using 1
  dsimp [S]
  ring


private def tailSquare (q : ℂ) (k j : ℕ) :=
  q^(k*k) * watsonOddTail q j * watsonEvenTail q (k+j)

private theorem tailSquare_sub (q : ℂ) (hq : ‖q‖ < 1) (k j : ℕ) :
    tailSquare q k j - tailSquare q k (j+1) = oddChoice q k j + oddChoice q (k+1) j := by
  have ho : watsonOddTail q j = (1 + q^(2*j+1))*watsonOddTail q (j+1) :=
    progression_split hq 1 j
  have he : watsonEvenTail q (k+j) = (1+q^(2*(k+j)+2))*watsonEvenTail q (k+(j+1)) := by
    simpa [Nat.add_assoc] using progression_split hq 2 (k+j)
  rw [tailSquare, tailSquare, oddChoice, oddChoice, ho, he]
  rw [show k*k+2*j+1 = k*k+(2*j+1) by omega,
      show (k+1)*(k+1)+2*j+1 = k*k+(2*(k+j)+2) by ring,
      show k+1+j = k+(j+1) by omega, pow_add q (k*k), pow_add q (k*k)]
  ring

/-- In the product of the odd and even progressions above a square, removing
the empty choice splits the remaining terms into two consecutive odd choices. -/
theorem watson_least_part_split {q : ℂ} (hq : ‖q‖ < 1) (k : ℕ) :
    q^(k*k)*watsonOddTail q 0*watsonEvenTail q k - q^(k*k) =
    watsonA q k + watsonA q (k+1) := by
  have hh : HasSum (fun j => tailSquare q k j - tailSquare q k (j+1))
      (watsonA q k + watsonA q (k+1)) :=
    ((watsonA_hasSum hq k).add (watsonA_hasSum hq (k+1))).congr_fun (tailSquare_sub q hq k)
  have ho : Tendsto (watsonOddTail q) atTop (𝓝 1) := tendsto_progressionTail hq (by decide : 0<1)
  have he : Tendsto (fun j => watsonEvenTail q (k+j)) atTop (𝓝 1) := by
    simpa [Nat.add_comm, Function.comp_def] using
      (tendsto_progressionTail hq (by decide : 0<2)).comp (tendsto_add_atTop_nat k)
  have ht : Tendsto (tailSquare q k) atTop (𝓝 (q^(k*k))) := by
    simpa [tailSquare] using (ho.const_mul (q^(k*k))).mul he
  have e := tendsto_nhds_unique ((tendsto_const_nhds (x := tailSquare q k 0)).sub ht)
    (show Tendsto (fun j => tailSquare q k 0 - tailSquare q k j) atTop _ by
      simpa only [Finset.sum_range_sub'] using hh.tendsto_sum_nat)
  simpa [tailSquare] using e

theorem watsonThetaHalf_hasSum {q : ℂ} (hq : ‖q‖ < 1) :
    HasSum (fun k : ℕ => (-1:ℂ)^k * q^(k*k)) (watsonThetaHalf q) := by
  apply Summable.hasSum
  apply (summable_geometric_of_lt_one (norm_nonneg q) hq).of_norm_bounded
  intro k
  simp only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  exact pow_le_pow_of_le_one (norm_nonneg q) hq.le
    ((Nat.le_self_pow (by decide : 2 ≠ 0) k).trans_eq (pow_two k))

/-- The square-weighted product sum underlying P(q)φ(−q) splits into the
alternating theta half-series and the terms with least part odd. -/
theorem watson_weighted_phi_eq_theta_add_leastOdd {q : ℂ} (hq : ‖q‖ < 1) :
    ∑' k : ℕ, (-1:ℂ)^k * q^(k*k) * watsonOddTail q 0 * watsonEvenTail q k =
      watsonThetaHalf q + watsonA q 0 := by
  let B (k : ℕ) := (-1:ℂ)^k * watsonA q k
  have hB : Summable B := by
    apply (summable_watsonA hq).norm.of_norm_bounded
    intro k
    simp [B]
  have hshift := (summable_nat_add_iff 1).2 hB
  have htel : HasSum (fun k => B k - B (k+1)) (watsonA q 0) := by
    have h := hB.sum_add_tsum_nat_add 1
    rw [Finset.sum_range_one] at h
    have hh := hB.hasSum.sub hshift.hasSum
    convert hh using 1
    change watsonA q 0 = _
    rw [← h]
    simp [B]
  apply ((watsonThetaHalf_hasSum hq).add htel).congr_fun _ |>.tsum_eq
  intro k
  have h := watson_least_part_split hq k
  dsimp [B]
  rw [pow_succ (-1:ℂ) k]
  linear_combination (-1:ℂ)^k * h

end MockThetaAnalytic
