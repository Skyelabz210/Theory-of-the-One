import QuantumRadialLimit
import ShadowProjection
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! Holomorphicity of Ramanujan's third-order f inside the unit disk. On
‖q‖ ≤ r < 1 each factor 1+q^j has norm at least 1−r. The square exponent
n² in the numerator makes the resulting majorant eventually geometric. -/

noncomputable section

namespace MockThetaAnalytic

open Filter
open scoped Topology

/-- The nth defining hypergeometric summand of the named third-order f. -/
def radialFTerm (n : ℕ) (q : ℂ) : ℂ :=
  q^(n*n) / ∏ j ∈ Finset.range n, (1 + q^(j+1))^2

private def majorant (r : ℝ) (n : ℕ) : ℝ := (r^n / (1-r)^2)^n

private theorem summable_majorant {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) :
    Summable (majorant r) := by
  have hgeom := summable_geometric_of_norm_lt_one (by norm_num : ‖(1/2 : ℝ)‖ < 1)
  apply hgeom.of_norm_bounded_eventually_nat
  have hd : 0 < (1-r)^2 := pow_pos (sub_pos.mpr hr1) _
  have ht := tendsto_pow_atTop_nhds_zero_of_lt_one hr hr1
  filter_upwards [ht.eventually_lt_const (show 0 < (1/2 : ℝ)*(1-r)^2 by positivity)] with n hn
  rw [majorant, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact pow_le_pow_left₀ (by positivity) ((div_le_iff₀ hd).2 hn.le) n

private theorem factor_lower_bound {r : ℝ} {q : ℂ} (hr1 : r < 1) (hq : ‖q‖ ≤ r) (j : ℕ) :
    1-r ≤ ‖1+q^(j+1)‖ := by
  have hp : ‖q^(j+1)‖ ≤ r := by
    rw [norm_pow]
    exact (pow_le_of_le_one (norm_nonneg q) (hq.trans hr1.le) (Nat.succ_ne_zero j)).trans hq
  have h := norm_sub_norm_le (1 : ℂ) (-(q^(j+1)))
  simp only [norm_one, norm_neg, sub_neg_eq_add] at h
  exact (sub_le_sub_left hp 1).trans h

private theorem norm_radialFTerm_le {r : ℝ} {q : ℂ} (hr1 : r < 1) (hq : ‖q‖ ≤ r) (n : ℕ) :
    ‖radialFTerm n q‖ ≤ majorant r n := by
  have hp : ((1-r)^2)^n ≤ ∏ j ∈ Finset.range n, ‖(1+q^(j+1))^2‖ := by
    calc
      _ = ∏ _j ∈ Finset.range n, (1-r)^2 := by simp
      _ ≤ _ := Finset.prod_le_prod (fun _ _ => sq_nonneg _) (fun j _ => by
        rw [norm_pow]
        exact pow_le_pow_left₀ (sub_nonneg.mpr hr1.le) (factor_lower_bound hr1 hq j) 2)
  rw [radialFTerm, norm_div, norm_pow, norm_prod, majorant, div_pow, ← pow_mul]
  exact div_le_div₀ (pow_nonneg ((norm_nonneg q).trans hq) _) (pow_le_pow_left₀ (norm_nonneg q) hq _)
    (pow_pos (pow_pos (sub_pos.mpr hr1) _) _) hp

/-- The defining series has an actual sum at every interior point. -/
theorem summable_radialFTerm (q : ℂ) (hq : ‖q‖ < 1) : Summable (fun n => radialFTerm n q) :=
  (summable_majorant (norm_nonneg q) hq).of_norm_bounded
    (fun n => norm_radialFTerm_le hq (le_refl _) n)

theorem hasSum_radialF (q : ℂ) (hq : ‖q‖ < 1) :
    HasSum (fun n => radialFTerm n q) (radialF q) := (summable_radialFTerm q hq).hasSum

private theorem differentiableAt_term (n : ℕ) (q : ℂ) (hq : ‖q‖ < 1) :
    DifferentiableAt ℂ (radialFTerm n) q := by
  unfold radialFTerm
  apply DifferentiableAt.div
  · fun_prop
  · fun_prop
  · apply Finset.prod_ne_zero_iff.mpr
    intro j _
    apply pow_ne_zero
    exact norm_ne_zero_iff.mp (ne_of_gt ((sub_pos.mpr hq).trans_le
      (factor_lower_bound hq (le_refl _) j)))

/-- Weierstrass' theorem on every disk of radius less than one gives
holomorphicity of the named infinite hypergeometric series in the unit disk. -/
theorem differentiableAt_radialF (q : ℂ) (hq : ‖q‖ < 1) : DifferentiableAt ℂ radialF q := by
  obtain ⟨r, hqr, hr⟩ := exists_between hq
  have hopen : IsOpen {w : ℂ | ‖w‖ < r} := isOpen_lt continuous_norm continuous_const
  have h := Complex.differentiableOn_tsum_of_summable_norm
    (summable_majorant ((norm_nonneg q).trans hqr.le) hr)
    (fun n w hw => (differentiableAt_term n w (lt_trans hw hr)).differentiableWithinAt)
    hopen (fun n w hw => norm_radialFTerm_le hr (le_of_lt hw) n)
  exact h.differentiableAt (hopen.mem_nhds hqr)

/-- The holomorphic part in the rescaled variable, q⁻¹ f(q²⁴), q=e(z). -/
def normalizedF (z : ℂ) : ℂ := (integerNome z)⁻¹ * radialF ((integerNome z)^24)

theorem differentiableAt_normalizedF (z : ℂ) (hz : 0 < z.im) :
    DifferentiableAt ℂ normalizedF z := by
  have hn : DifferentiableAt ℂ integerNome z := by unfold integerNome; fun_prop
  have hn0 : integerNome z ≠ 0 := Complex.exp_ne_zero _
  have hd : ‖(integerNome z)^24‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg _) (norm_integerNome_lt_one z hz) (by decide)
  have hp : DifferentiableAt ℂ (fun w => integerNome w ^ 24) z := hn.fun_pow 24
  have hf := (differentiableAt_radialF (integerNome z ^ 24) hd).comp z hp
  exact (hn.fun_inv hn0).mul hf

end MockThetaAnalytic
