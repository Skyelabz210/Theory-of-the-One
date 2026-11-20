import ShadowProjection
import Mathlib.Analysis.Normed.Group.Tannery

/-! Analytic support of the eleven unary theta series. Factoring out the first
nonzero Fourier monomial detects a nonzero bin at positive imaginary heights. -/

noncomputable section

namespace MockThetaAnalytic

open Filter Complex KElimination.MockThetaShadow KElimination.ShadowConvergence
open scoped Topology

private def reducedTerm (r : Fin 11) (k : ℕ) (u : ℂ) (m : ℕ) : ℂ :=
  if degreeClass m = r ∧ k ≤ m then (shadowWeight m : ℂ) * u^(m^2-k^2) else 0

/-- At a bin's first occupied index, dividing by its leading monomial
leaves a series with a nonzero limit at the origin. -/
private theorem reducedTerm_limit (r : Fin 11) (k : ℕ) (hk : degreeClass k = r) :
    Tendsto (fun u : ℂ => ∑' m, reducedTerm r k u m) (𝓝 0) (𝓝 (shadowWeight k : ℂ)) := by
  let bound := fun m : ℕ => (m : ℝ) * (1/2 : ℝ)^m + if m = k then (k : ℝ) else 0
  have hgeom : Summable (fun m : ℕ => (m : ℝ) * (1/2 : ℝ)^m) := by
    simpa only [pow_one] using summable_pow_mul_geometric_of_norm_lt_one
      (r := (1/2 : ℝ)) 1 (by norm_num)
  have hb : Summable bound := hgeom.add (hasSum_single k (fun m hm => if_neg hm)).summable
  have hcont (m : ℕ) : Continuous (fun u : ℂ => reducedTerm r k u m) := by
    unfold reducedTerm
    split <;> fun_prop
  have hlim := @tendsto_tsum_of_dominated_convergence ℂ ℕ ℂ (𝓝 0) _ _
    (fun u m => reducedTerm r k u m) (reducedTerm r k 0) bound hb
    (fun m => (hcont m).continuousAt.tendsto)
  have hsmall : ∀ᶠ u : ℂ in 𝓝 0, ‖u‖ < (1/2 : ℝ) :=
    by simpa [Metric.ball, dist_zero_right] using (Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1/2))
  have hl := hlim (by
    filter_upwards [hsmall] with u hu m
    have hw : ‖(shadowWeight m : ℂ)‖ ≤ (m : ℝ) := by
      simpa [Complex.norm_intCast, Nat.cast_natAbs, Int.cast_abs] using
        (show ((shadowWeight m).natAbs : ℝ) ≤ m by exact_mod_cast shadowWeight_natAbs_le m)
    by_cases hm : m = k
    · subst m
      simpa [bound, reducedTerm, hk] using
        (hw.trans (le_add_of_nonneg_left (by positivity : 0 ≤ (k : ℝ) * (1/2 : ℝ)^k)))
    · simp only [bound, if_neg hm, add_zero, reducedTerm]
      split_ifs with h
      · have hkm : k < m := lt_of_le_of_ne h.2 (Ne.symm hm)
        have hh : m ≤ m^2 - k^2 := by
          nlinarith [Nat.sub_add_cancel (Nat.pow_le_pow_left h.2 2),
            Nat.mul_le_mul_left m hkm, Nat.mul_le_mul_left k h.2]
        rw [norm_mul, norm_pow]
        exact mul_le_mul hw ((pow_le_pow_left₀ (norm_nonneg u) hu.le _).trans
          (pow_le_pow_of_le_one (by norm_num) (by norm_num) hh)) (by positivity) (by positivity)
      · simp only [norm_zero]
        positivity)
  have hzero (m : ℕ) :
      reducedTerm r k 0 m = if m = k then (shadowWeight k : ℂ) else 0 := by
    by_cases h : m = k
    · subst m
      simp [reducedTerm, hk]
    · simp only [reducedTerm, if_neg h]
      split_ifs with hm
      · have hs : k^2 < m^2 := Nat.pow_lt_pow_left (lt_of_le_of_ne hm.2 (Ne.symm h)) (by decide)
        simp [Nat.sub_ne_zero_of_lt hs]
      · rfl
  have hsum := (hasSum_single (f := reducedTerm r k 0) k (fun m hm => by simp [hzero, hm])).tsum_eq
  rw [hsum] at hl
  simpa only [hzero, if_pos rfl] using hl

private theorem bin_factor (r : Fin 11) (k : ℕ)
    (hfirst : ∀ m < k, degreeClass m = r → shadowWeight m = 0) (u : ℂ) :
    shadowDegreeBin r u = u^(k^2) * ∑' m, reducedTerm r k u m := by
  rw [← tsum_mul_left]
  unfold shadowDegreeBin
  apply tsum_congr
  intro m
  by_cases hr : degreeClass m = r
  · by_cases hkm : k ≤ m
    · simp only [hr, hkm, and_self, if_true, reducedTerm, shadowTerm]
      rw [mul_left_comm, ← pow_add, Nat.add_sub_of_le (Nat.pow_le_pow_left hkm 2)]
    · simp [reducedTerm, hr, hkm, shadowTerm, hfirst m (Nat.lt_of_not_ge hkm) hr]
  · simp [reducedTerm, hr]

/-- A degree bin vanishes throughout the upper half-plane exactly when its
residue is outside the six square classes modulo eleven. -/
theorem shadowDegreeBin_identically_zero_iff (r : Fin 11) :
    (∀ z : ℂ, 0 < z.im → shadowDegreeBin r (integerNome z) = 0) ↔
      r.val ∉ ([0, 1, 3, 4, 5, 9] : List ℕ) := by
  classical
  constructor
  · intro hz hr
    obtain ⟨d, hd, hw⟩ := (shadowCoeff_sector_support_iff r).2 hr
    obtain ⟨m, rfl, hm⟩ := (shadowCoeff_ne_zero_iff _).1 hw
    have hex : ∃ k, degreeClass k = r ∧ shadowWeight k ≠ 0 :=
      ⟨m, Fin.ext (by simpa [degreeClass, pow_two] using hd), (shadowWeight_ne_zero_iff _).2 hm⟩
    let k := Nat.find hex
    obtain ⟨hk, hne⟩ := Nat.find_spec hex
    have hf (m : ℕ) (hm : m < k) (hrm : degreeClass m = r) : shadowWeight m = 0 := by
      by_contra h
      exact Nat.find_min hex hm ⟨hrm, h⟩
    let z := fun n : ℕ => ((n : ℂ)+1)*I
    have hy (n : ℕ) : 0 < (z n).im := by simp [z]; positivity
    have hq (n : ℕ) : integerNome (z n) = integerNome I ^(n+1) := by
      unfold integerNome z
      rw [← Complex.exp_nat_mul]
      push_cast
      congr 1
      ring
    have hlim : Tendsto (fun n : ℕ => integerNome (z n)) atTop (𝓝 0) := by
      simp_rw [hq]
      exact (tendsto_pow_atTop_nhds_zero_of_norm_lt_one (norm_integerNome_lt_one I (by simp))).comp
        (tendsto_add_atTop_nat 1)
    have hn (n : ℕ) : (∑' m, reducedTerm r k (integerNome (z n)) m) = 0 := by
      have h := hz (z n) (hy n)
      have hu : integerNome (z n) ≠ 0 := Complex.exp_ne_zero _
      rw [bin_factor r k hf _] at h
      exact (mul_eq_zero.mp h).resolve_left (pow_ne_zero _ hu)
    have hl := (reducedTerm_limit r k hk).comp hlim
    simp only [Function.comp_def, hn] at hl
    have hzero : (0 : ℂ) = (shadowWeight k : ℂ) := tendsto_nhds_unique tendsto_const_nhds hl
    exact hne (by exact_mod_cast hzero.symm)
  · intro hr z _
    unfold shadowDegreeBin
    have he (m : ℕ) : (if degreeClass m = r then shadowTerm (integerNome z) m else 0) = 0 := by
      split_ifs with hm
      · have hw : shadowWeight m = 0 := by
          by_contra hn
          apply hr
          apply (shadowCoeff_sector_support_iff r).1
          exact ⟨m*m, by simpa [degreeClass, pow_two] using congrArg Fin.val hm,
            (shadowCoeff_square m).symm ▸ hn⟩
        simp [shadowTerm, hw]
      · rfl
    simp only [he, tsum_zero]

end MockThetaAnalytic
