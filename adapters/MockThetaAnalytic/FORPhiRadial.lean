import FORCyclotomicBlock
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.Normed.Ring.InfiniteSum

/-! Boundary convergence of Watson's third-order φ(−q) at primitive order 34.
Each radial term is bounded by its endpoint norm and the endpoint terms halve
after seventeen steps. -/

noncomputable section

namespace MockThetaAnalytic

open Complex Finset Filter Set
open scoped Topology

/-- The nth term of Watson's third-order φ evaluated at −q. -/
def watsonPhiTerm (q : ℂ) (n : ℕ) : ℂ :=
  (-q)^(n^2) / ∏ j ∈ range n, (1 + q^(2*j+2))

/-- Watson's third-order φ(−q), in the same radial coordinate as f(q). -/
def watsonPhi (q : ℂ) : ℂ := ∑' n : ℕ, watsonPhiTerm q n

private theorem watsonEvenFactor_ne_zero (ζ : ℂ) (hζ : IsPrimitiveRoot ζ 34) (j : ℕ) :
    1 + ζ^(2*j+2) ≠ 0 := by
  intro he
  have he' : ζ^(2*j+2) = -1 := by linear_combination he
  have hh : (ζ^(2*j+2))^17 = 1 := by
    rw [← pow_mul, show (2*j+2)*17=34*(j+1) by ring, pow_mul, hζ.pow_eq_one, one_pow]
  rw [he'] at hh
  norm_num at hh

private theorem radialFactor_le (x : ℝ) (v : ℂ) (hv : ‖v‖ = 1) :
    x * ‖1+v‖ ≤ ‖1+(x:ℂ)^2*v‖ := by
  have hnorm : normSq v = 1 := by rw [normSq_eq_norm_sq, hv]; norm_num
  have h1 : ‖1+v‖^2 = 2+2*v.re := by
    simp [Complex.sq_norm, normSq_add, hnorm]; ring
  have h2 : ‖1+(x:ℂ)^2*v‖^2 = 1+x^4+2*x^2*v.re := by
    simp [Complex.sq_norm, normSq_add, normSq_mul, normSq_ofReal, hnorm,
      ← Complex.ofReal_pow, mul_assoc]; ring
  have h3 : (x * ‖1+v‖)^2 ≤ ‖1+(x:ℂ)^2*v‖^2 := by
    rw [mul_pow, h1, h2]; nlinarith [sq_nonneg (x^2-1)]
  exact le_of_sq_le_sq h3 (norm_nonneg _)

theorem watsonPhiTerm_succ (q : ℂ) (n : ℕ) :
    watsonPhiTerm q (n+1) = watsonPhiTerm q n * ((-q)^(2*n+1) / (1+q^(2*n+2))) := by
  rw [watsonPhiTerm, watsonPhiTerm, prod_range_succ, show (n+1)^2=n^2+(2*n+1) by ring,
    pow_add, div_mul_div_comm]

/-- The radial terms are dominated by their actual boundary magnitudes. -/
theorem norm_watsonPhiTerm_radial_le (ζ : ℂ) (hζ : IsPrimitiveRoot ζ 34)
    (t : ℝ) (ht : 0 < t) (ht' : t ≤ 1) (n : ℕ) :
    ‖watsonPhiTerm ((t:ℂ)*ζ) n‖ ≤ ‖watsonPhiTerm ζ n‖ := by
  have hz := hζ.norm'_eq_one (by decide)
  induction n with
  | zero => simp [watsonPhiTerm]
  | succ n ih =>
    rw [watsonPhiTerm_succ, watsonPhiTerm_succ, norm_mul, norm_mul]
    apply mul_le_mul ih _ (norm_nonneg _) (norm_nonneg _)
    let v := ζ^(2*n+2)
    have hv : ‖v‖ = 1 := by simp [v, hz]
    have hp : 0 < ‖1+v‖ := norm_pos_iff.mpr (watsonEvenFactor_ne_zero ζ hζ n)
    have hfac := radialFactor_le (t^(n+1)) v hv
    have he : (t:ℂ)^(2*n+2) = ((t^(n+1):ℝ):ℂ)^2 := by
      push_cast; rw [← pow_mul]; congr 1; ring
    have hx : 0 < ‖1+(t:ℂ)^(2*n+2)*v‖ := by rw [he]; exact (mul_pos (pow_pos ht _) hp).trans_le hfac
    simp only [norm_div, norm_pow, norm_neg, norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos ht,
      hz, mul_one, one_pow, mul_pow]
    change t^(2*n+1) / ‖1+(t:ℂ)^(2*n+2)*v‖ ≤ 1 / ‖1+v‖
    apply (div_le_div_iff₀ hx hp).mpr
    rw [one_mul, he]
    exact (mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one ht.le ht' (by omega : n+1≤2*n+1)) hp.le).trans hfac

private theorem watsonPhiTerm_continuousAt (ζ : ℂ) (hζ : IsPrimitiveRoot ζ 34) (n : ℕ) :
    ContinuousAt (fun t : ℝ => watsonPhiTerm ((t:ℂ)*ζ) n) 1 := by
  unfold watsonPhiTerm
  apply ContinuousAt.div (by fun_prop) (by fun_prop)
  simpa using Finset.prod_ne_zero_iff.mpr (fun j (_ : j ∈ Finset.range n) => watsonEvenFactor_ne_zero ζ hζ j)

/-- The exact endpoint terms form seventeen geometric progressions with ratio one half. -/
theorem watsonPhiTerm_add_seventeen (ζ : ℂ) (hζ : IsPrimitiveRoot ζ 34) (n : ℕ) :
    watsonPhiTerm ζ (n+17) = watsonPhiTerm ζ n / 2 := by
  have hs : (ζ^17)^2 = 1 := by rw [← pow_mul]; exact hζ.pow_eq_one
  have hn : ζ^17 ≠ 1 := hζ.pow_ne_one_of_pos_of_lt (by decide) (by decide)
  have h17 : (-ζ)^17 = 1 := by
    rw [(by decide : Odd 17).neg_pow, (sq_eq_one_iff.mp hs).resolve_left hn, neg_neg]
  have hblock : (∏ j ∈ Finset.range 17, (1+ζ^(2*(n+j)+2))) = 2 := by
    simpa only [mul_add, Complex.ofReal_one, one_mul, one_pow, one_add_one_eq_two] using order34_even_block ζ hζ n 1
  rw [watsonPhiTerm, watsonPhiTerm, Finset.prod_range_add, hblock,
    show (n+17)^2 = n^2+17*(2*n+17) by ring, pow_add, pow_mul, h17, one_pow, mul_one,
    div_div]

private theorem watsonPhiTerm_geometric (ζ : ℂ) (hζ : IsPrimitiveRoot ζ 34) (k r : ℕ) :
    watsonPhiTerm ζ (k*17+r) = (1/2:ℂ)^k * watsonPhiTerm ζ r := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show (k+1)*17+r = k*17+r+17 by omega, watsonPhiTerm_add_seventeen ζ hζ, ih, pow_succ]
    ring

theorem summable_norm_watsonPhiTerm (ζ : ℂ) (hζ : IsPrimitiveRoot ζ 34) :
    Summable (fun n : ℕ => ‖watsonPhiTerm ζ n‖) := by
  apply (Nat.divModEquiv 17).symm.summable_iff.mp
  have hg : Summable (fun k : ℕ => (1/2:ℝ)^k) := summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have hf := (hasSum_fintype (fun r : Fin 17 => ‖watsonPhiTerm ζ r.val‖)).summable
  apply (hg.mul_of_nonneg hf (fun k => by positivity) (fun _ => norm_nonneg _)).congr
  intro p
  simp [Nat.divModEquiv_symm_apply, watsonPhiTerm_geometric ζ hζ]

/-- At a primitive order-34 root the convergent value equals twice the first seventeen terms. -/
theorem watsonPhi_eq_two_mul_sum (ζ : ℂ) (hζ : IsPrimitiveRoot ζ 34) :
    watsonPhi ζ = 2 * ∑ n ∈ range 17, watsonPhiTerm ζ n := by
  have hs := (summable_norm_watsonPhiTerm ζ hζ).of_norm
  have hh := hs.sum_add_tsum_nat_add 17
  simp_rw [watsonPhiTerm_add_seventeen ζ hζ, div_eq_mul_inv] at hh
  rw [tsum_mul_right] at hh
  unfold watsonPhi
  linear_combination -2 * hh

/-- The actual disk series φ(−tζ) converges radially to its endpoint sum. -/
theorem watsonPhi_radial_limit (ζ : ℂ) (hζ : IsPrimitiveRoot ζ 34) :
    Tendsto (fun t : ℝ => watsonPhi ((t:ℂ)*ζ)) (𝓝[<] 1) (𝓝 (watsonPhi ζ)) := by
  apply tendsto_tsum_of_dominated_convergence (summable_norm_watsonPhiTerm ζ hζ)
  · intro n
    simpa using ((watsonPhiTerm_continuousAt ζ hζ n).tendsto.mono_left (nhdsWithin_le_nhds (s := Iio 1)))
  · filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds (by norm_num : (0:ℝ)<1))] with t ht h0 n
    exact norm_watsonPhiTerm_radial_le ζ hζ t h0 (le_of_lt ht) n

end MockThetaAnalytic
