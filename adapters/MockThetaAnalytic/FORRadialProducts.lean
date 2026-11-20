import QuantumRadialLimit
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Tactic.LinearCombination

/-! Euler products for the modular correction in Ramanujan’s radial limit.
Inside the open unit disk every product below converges to a nonzero value.
The same convergence controls all shifted denominator products in Fine’s rank expansion. -/

noncomputable section
namespace MockThetaAnalytic
open Complex Filter
open scoped Topology

/-- Euler's product (q;q)∞. -/
def radialEulerProduct (q : ℂ) : ℂ := ∏' n : ℕ, (1 - q^(n+1))

/-- The product (−q;q)∞ appearing in the denominator of b. -/
def radialPlusProduct (q : ℂ) : ℂ := ∏' n : ℕ, (1 + q^(n+1))

private theorem summable_norm_radial_pow {q : ℂ} (hq : ‖q‖ < 1) :
    Summable (fun n : ℕ => ‖q^(n+1)‖) := by
  simpa [norm_pow] using (summable_nat_add_iff 1).2
    (summable_geometric_of_lt_one (norm_nonneg q) hq)

private theorem radial_pow_norm_lt_one {q : ℂ} (hq : ‖q‖ < 1) (n : ℕ) :
    ‖q^(n+1)‖ < 1 := by
  rw [norm_pow]
  exact pow_lt_one₀ (norm_nonneg q) hq (Nat.succ_ne_zero _)

/-- Both Pochhammer products converge in the disk. -/
theorem hasProd_radialPochhammers {q : ℂ} (hq : ‖q‖ < 1) :
    HasProd (fun n : ℕ => 1 - q^(n+1)) (radialEulerProduct q) ∧
    HasProd (fun n : ℕ => 1 + q^(n+1)) (radialPlusProduct q) := by
  have hs := summable_norm_radial_pow hq
  exact ⟨by simpa [sub_eq_add_neg, radialEulerProduct] using
    (multipliable_one_add_of_summable (f := fun n : ℕ => -q^(n+1)) (by simpa using hs)).hasProd,
    (multipliable_one_add_of_summable hs).hasProd⟩

private theorem plusFactor_ne_zero {q : ℂ} (hq : ‖q‖ < 1) (n : ℕ) : 1+q^(n+1) ≠ 0 := by
  intro h
  have he : q^(n+1) = -1 := by linear_combination h
  simpa [he] using radial_pow_norm_lt_one hq n

/-- Neither Pochhammer vanishes in the open disk. -/
theorem radialPochhammers_ne_zero {q : ℂ} (hq : ‖q‖ < 1) :
    radialEulerProduct q ≠ 0 ∧ radialPlusProduct q ≠ 0 := by
  have hs := summable_norm_radial_pow hq
  constructor
  · unfold radialEulerProduct
    simp_rw [sub_eq_add_neg]
    apply tprod_one_add_ne_zero_of_summable _ (by simpa using hs)
    intro n h
    have he : q^(n+1) = 1 := by linear_combination -h
    simpa [he] using radial_pow_norm_lt_one hq n
  · exact tprod_one_add_ne_zero_of_summable (plusFactor_ne_zero hq) hs

/-- The finite denominator products stay bounded and bounded away from zero
at each interior nome, uniformly in the cutoff. -/
theorem exists_radialPlus_prefix_bounds (q : ℂ) (hq : ‖q‖ < 1) :
    ∃ c C : ℝ, 0 < c ∧ ∀ n : ℕ, c ≤ ‖∏ j ∈ Finset.range n, (1+q^(j+1))‖ ∧
      ‖∏ j ∈ Finset.range n, (1+q^(j+1))‖ ≤ C := by
  let D (n : ℕ) : ℂ := ∏ j ∈ Finset.range n, (1+q^(j+1))
  have hD : ∀ n, D n ≠ 0 := fun n =>
    Finset.prod_ne_zero_iff.mpr fun j _ => plusFactor_ne_zero hq j
  have ht : Tendsto D atTop (𝓝 (radialPlusProduct q)) :=
    (hasProd_radialPochhammers hq).2.tendsto_prod_nat
  obtain ⟨C, hC⟩ := ht.norm.bddAbove_range
  obtain ⟨B, hB⟩ := (ht.inv₀ (radialPochhammers_ne_zero hq).2).norm.bddAbove_range
  have hp : 0 < |B|+1 := by positivity
  refine ⟨(|B|+1)⁻¹, C, inv_pos.mpr hp, fun n => ⟨?_, hC ⟨n, rfl⟩⟩⟩
  have h : ‖(D n)⁻¹‖ ≤ B := hB ⟨n, rfl⟩
  rw [norm_inv] at h
  change (|B|+1)⁻¹ ≤ ‖D n‖
  apply (inv_le_comm₀ hp (norm_pos_iff.mpr (hD n))).mpr
  linarith [le_abs_self B]

/-- The same bounds hold for all shifted denominator products, including
simultaneously varying start and length in the Fine transformations. -/
theorem exists_radialPlus_interval_bounds (q : ℂ) (hq : ‖q‖ < 1) :
    ∃ c C : ℝ, 0 < c ∧ ∀ s n : ℕ,
      c ≤ ‖∏ j ∈ Finset.range n, (1+q^(s+j+1))‖ ∧
      ‖∏ j ∈ Finset.range n, (1+q^(s+j+1))‖ ≤ C := by
  obtain ⟨c,C,hc,H⟩ := exists_radialPlus_prefix_bounds q hq
  let D (n : ℕ) : ℂ := ∏ j ∈ Finset.range n, (1+q^(j+1))
  have hC : 0 < C := hc.trans_le ((H 0).1.trans (H 0).2)
  refine ⟨c/C, C/c, div_pos hc hC, fun s n => ?_⟩
  have hDs : 0 < ‖D s‖ := hc.trans_le (H s).1
  have hprod : D (s+n) = D s * ∏ j ∈ Finset.range n, (1+q^(s+j+1)) :=
    Finset.prod_range_add (fun i => 1+q^(i+1)) s n
  have he : (∏ j ∈ Finset.range n, (1+q^(s+j+1))) = D (s+n) / D s :=
    (eq_div_iff (norm_pos_iff.mp hDs)).2 (mul_comm _ _ |>.trans hprod.symm)
  rw [he, norm_div]
  exact ⟨div_le_div₀ (norm_nonneg _) (H (s+n)).1 hDs (H s).2,
    div_le_div₀ hC.le (H (s+n)).2 hc (H s).1⟩

theorem exists_radialPlus_shift_lower (q : ℂ) (hq : ‖q‖ < 1) :
    ∃ c : ℝ, 0 < c ∧ ∀ s n : ℕ, c ≤ ‖∏ j ∈ Finset.range n, (1+q^(s+j+1))‖ := by
  obtain ⟨c, _, hc, h⟩ := exists_radialPlus_interval_bounds q hq
  exact ⟨c, hc, fun s n => (h s n).1⟩

/-- Multiplication of the two Pochhammers gives (q²;q²)∞. -/
theorem radialEuler_mul_plus {q : ℂ} (hq : ‖q‖ < 1) :
    radialEulerProduct q * radialPlusProduct q = radialEulerProduct (q^2) := by
  obtain ⟨ha, hb⟩ := hasProd_radialPochhammers hq
  have hf (n : ℕ) : (1-q^(n+1))*(1+q^(n+1)) = 1-(q^2)^(n+1) := by
    rw [← pow_mul, Nat.mul_comm, pow_mul]
    ring
  simpa only [radialEulerProduct, hf] using (ha.mul hb).tprod_eq.symm

private theorem radialB_product_quotient {q : ℂ} (hq : ‖q‖ < 1) :
    HasProd (fun n : ℕ => (1-q^(n+1))/(1+q^(n+1))^2)
      (radialEulerProduct q / radialPlusProduct q ^ 2) := by
  obtain ⟨ha, hb⟩ := hasProd_radialPochhammers hq
  unfold HasProd at ha hb ⊢
  simp only [Finset.prod_div_distrib, Finset.prod_pow]
  exact ha.div (hb.pow 2) (pow_ne_zero _ (radialPochhammers_ne_zero hq).2)

/-- The named correction is the limit of its actual products in the disk. -/
theorem hasProd_radialB {q : ℂ} (hq : ‖q‖ < 1) :
    HasProd (fun n : ℕ => (1-q^(n+1))/(1+q^(n+1))^2) (radialB q) :=
  (radialB_product_quotient hq).multipliable.hasProd

theorem radialB_eq_pochhammers {q : ℂ} (hq : ‖q‖ < 1) :
    radialB q = radialEulerProduct q / (radialPlusProduct q)^2 :=
  (radialB_product_quotient hq).tprod_eq

theorem radialB_ne_zero {q : ℂ} (hq : ‖q‖ < 1) : radialB q ≠ 0 := by
  obtain ⟨ha, hb⟩ := radialPochhammers_ne_zero hq
  rw [radialB_eq_pochhammers hq]
  exact div_ne_zero ha (pow_ne_zero _ hb)

end MockThetaAnalytic
