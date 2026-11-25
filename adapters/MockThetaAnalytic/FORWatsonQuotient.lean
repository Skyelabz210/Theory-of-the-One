import FORWatsonBoundary

/-! The cleared Watson identity in the full integer quotient by Xᵏ+1.
If a root has order 2h, its denominator splits into an odd number of
blocks of length h. The quotient certificate is true for every k > 0. -/

noncomputable section
namespace MockThetaAnalytic

open Finset KElimination.QuantumRadial

/-- If qᵏ = −1, k is an odd multiple of half the order of q. -/
theorem even_root_order_of_half_power {q : ℂ} {k : ℕ} (hq : q^k = -1) :
    ∃ h m : ℕ, 0 < h ∧ Odd m ∧ k = m*h ∧ IsPrimitiveRoot q (2*h) := by
  have hk : k ≠ 0 := by rintro rfl; norm_num at hq
  let d := orderOf q
  let h := k % d
  have hd : 0 < d := orderOf_pos_iff.mpr
    (isOfFinOrder_iff_pow_eq_one.mpr ⟨2*k, by omega, twice_half_period q k hq⟩)
  have hq' : q^h = -1 := (pow_mod_orderOf q k).trans hq
  have hh : 0 < h := by
    by_contra! hh
    have hz : h = 0 := by omega
    rw [hz, pow_zero] at hq'
    norm_num at hq'
  have hlt : h < d := Nat.mod_lt _ hd
  have hdvd : d ∣ 2*h := orderOf_dvd_of_pow_eq_one (twice_half_period q h hq')
  have horder : 2*h = d := Nat.eq_of_dvd_of_lt_two_mul (by omega) hdvd (by omega)
  refine ⟨h, 2*(k/d)+1, hh, ⟨k/d, rfl⟩, ?_, ?_⟩
  · calc
      k = h+d*(k/d) := (Nat.mod_add_div k d).symm
      _ = (2*(k/d)+1)*h := by rw [← horder]; ring
  · rw [horder]
    exact IsPrimitiveRoot.orderOf q

/-- Each primitive half-period contributes the same factor two. -/
theorem watson_denominator_blocks {q : ℂ} {h : ℕ} (hh : 0 < h)
    (hq : IsPrimitiveRoot q (2*h)) {c : ℕ} (hc : Odd (h+c)) (m : ℕ) :
    (∏ j ∈ range (m*h), (1+q^(2*j+c))) = (2:ℂ)^m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.succ_mul, prod_range_add, ih, watson_denominator_block hh hq c hc (m*h), pow_succ]

private theorem watson_geometric_sum {q : ℂ} {h : ℕ} (hh : 0 < h)
    (hq : IsPrimitiveRoot q (2*h)) {c : ℕ} (hc : Odd (h+c)) (m : ℕ) :
    (2:ℂ)^m * (∑ j ∈ range (m*h), watsonTerm c q j) =
      ((2:ℂ)^m - 1) * (2 * ∑ j ∈ range h, watsonTerm c q j) := by
  have hsegment (m : ℕ) :
      (2:ℂ)^m * (∑ j ∈ range h, watsonTerm c q (m*h+j)) =
        ∑ j ∈ range h, watsonTerm c q j := by
    rw [mul_sum]
    apply sum_congr rfl
    intro j _
    rw [watsonTerm_geometric hh hq hc, ← mul_assoc, ← mul_pow]
    norm_num
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.succ_mul, sum_range_add, pow_succ]
    linear_combination 2 * ih + 2 * hsegment m

/-- The cleared Watson identity holds at every complex root of Xᵏ+1. -/
theorem watson_cleared_identity {q : ℂ} {k : ℕ} (hq : q^k = -1) :
    watsonClearedDifference k q = 0 := by
  obtain ⟨h,m,hh,hm,hkm,hprim⟩ := even_root_order_of_half_power hq
  let c := if Even k then 1 else 2
  have hparity : Even k ↔ Even h := by
    rw [hkm, Nat.even_mul]
    simp only [Nat.not_even_iff_odd.mpr hm, false_or]
  have hle : h ≤ k := by simpa [hkm] using Nat.mul_le_mul_right h hm.pos
  have hU : uPartial k q = uPartial h q :=
    uPolynomial_stable k h q q hh (primitive_even_half_power hh hprim) hle
  have hc : Odd (h+c) := by
    by_cases he : Even k
    · simpa [c, he] using (hparity.mp he).add_odd (by decide : Odd 1)
    · have ho := Nat.not_even_iff_odd.mp (hparity.not.mp he)
      simpa [c, he] using ho.add_even (by decide : Even 2)
  have hhalf : (2 * ∑ j ∈ range h, watsonTerm c q j) =
      (if Even k then 1 + uPartial k q else -2 * uPartial k q) := by
    have hw := watsonFiniteBoundary_eq_boundaryValue hh hprim
    by_cases he : Even k
    · simp only [watsonFiniteBoundary, if_pos (hparity.mp he), boundaryValue] at hw
      simp only [c, he, if_true, hU]
      linear_combination (-1/4:ℂ) * hw
    · simp only [watsonFiniteBoundary, if_neg (hparity.not.mp he), boundaryValue] at hw
      simp only [c, he, if_false, hU]
      linear_combination (1/2:ℂ) * hw
  have hD : (∏ j ∈ range k, (1+q^(2*j+c))) = (2:ℂ)^m := by
    rw [hkm]
    exact watson_denominator_blocks hh hprim hc m
  have hW : (2:ℂ)^m * (∑ j ∈ range k, watsonTerm c q j) =
      ((2:ℂ)^m - 1) * (2 * ∑ j ∈ range h, watsonTerm c q j) := by
    rw [hkm]
    exact watson_geometric_sum hh hprim hc m
  change (∏ j ∈ range k, (1+q^(2*j+c))) * (∑ j ∈ range k, watsonTerm c q j) -
    ((∏ j ∈ range k, (1+q^(2*j+c)))-1) *
      (if Even k then 1 + uPartial k q else -2 * uPartial k q) = 0
  rw [hD, hW, hhalf, sub_self]

/-- The executable Watson certificate succeeds in ℤ[X]/(Xᵏ+1) for every k > 0. -/
theorem watsonBoundaryCertificate_all {k : ℕ} (hk : 0 < k) :
    watsonBoundaryCertificate k = true :=
  (watsonBoundaryCertificate_iff_cleared_zero hk).mpr fun _ hq => watson_cleared_identity hq

end MockThetaAnalytic
