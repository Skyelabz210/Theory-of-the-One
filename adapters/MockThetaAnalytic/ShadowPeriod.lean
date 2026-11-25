import ShadowReconstruction
import FKTYPeriodRegularity
import Order34QuantumPackets
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Algebra.Order.Floor.Div

/-! Recover the FKTY cusp period from the degree-labeled observations of f.
Pair the omitted modes only in the error proof. The finite approximation
integrates the same recovered polynomial that is used at positive height. -/

noncomputable section

namespace MockThetaAnalytic.ShadowPeriod

open Complex Filter MeasureTheory Set ShadowReadings ShadowHecke
open KElimination.MockTheta KElimination.MockThetaShadow KElimination.ShadowConvergence
open scoped BigOperators Topology

def modeCount (D : ℕ) : ℕ := (24 * D + 1).sqrt + 1

/-- The first N square-index slots read from the S6 prefix in FKTY normalization. -/
def recoveredThetaUpTo {D : ℕ} (reading : Prefix D) (w : Phase → ℂ) (N : ℕ) (u : ℂ) : ℂ :=
  (∑ m ∈ Finset.range N,
    w (phase m) * (shadowMode reading m : ℂ) * shadowNome u ^ (m ^ 2)) / 2

def recoveredTheta {D : ℕ} (reading : Prefix D) (w : Phase → ℂ) (u : ℂ) : ℂ :=
  recoveredThetaUpTo reading w (modeCount D) u

def cuspRay (t : ℝ) : ℂ := (-1/24 : ℂ) + (t : ℂ) * I
def gaussianRate : ℝ := Real.pi / 12
private def kernel (x t : ℝ) : ℂ := fktyVerticalKernel (-1/24) x t

/-- Integrate the finite recovered polynomial on the complete open cusp ray. -/
def recoveredPeriod {D : ℕ} (reading : Prefix D) (w : Phase → ℂ) (x : ℝ) : ℂ :=
  ∫ t in Ioi (0 : ℝ), kernel x t * recoveredTheta reading w (cuspRay t)

def weightedCuspTheta (w : Phase → ℂ) (t : ℝ) : ℂ :=
  2 * ∑' m : ℕ, w (phase m) * (fktyCuspPhase m * (gaussianMode gaussianRate m t : ℂ))

def weightedCuspPeriod (w : Phase → ℂ) (x : ℝ) : ℂ :=
  ∫ t in Ioi (0 : ℝ), kernel x t * weightedCuspTheta w t

private theorem rate_pos : 0 < gaussianRate := by unfold gaussianRate; positivity

theorem modeCount_ge_two (D : ℕ) : 2 ≤ modeCount D := by
  have h : 1 ≤ (24*D+1).sqrt := Nat.le_sqrt.mpr (by omega)
  unfold modeCount
  omega

private theorem integral_norm_gaussianMode (m : ℕ) (hm : 0 < m) :
    (∫ t in Ioi (0 : ℝ), ‖gaussianMode gaussianRate m t‖) = 1 / (gaussianRate * (m : ℝ)) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have ha := rate_pos
  have h t : 0 ≤ gaussianMode gaussianRate m t := by unfold gaussianMode; positivity
  simp_rw [Real.norm_of_nonneg (h _)]
  unfold gaussianMode
  rw [integral_const_mul, integral_exp_mul_Ioi (neg_lt_zero.mpr (by positivity))]
  simp only [mul_zero, Real.exp_zero, neg_div]
  field_simp

theorem squareTail_le (N : ℕ) (hN : 2 ≤ N) :
    (∑' j : ℕ, 1 / (((N+j : ℕ) : ℝ)^2)) ≤ 1 / ((N : ℝ) - 1) := by
  have hN' : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  let v (j : ℕ) : ℝ := 1 / ((N : ℝ) - 1 + (j : ℝ))
  have hv (j : ℕ) : 0 < (N : ℝ) - 1 + (j : ℝ) :=
    add_pos_of_pos_of_nonneg (sub_pos.mpr hN') (Nat.cast_nonneg j)
  have hstep (j : ℕ) : 1 / (((N+j : ℕ) : ℝ)^2) ≤ v j - v (j+1) := by
    let y := (N : ℝ) - 1 + (j : ℝ)
    have hy : 0 < y := hv j
    have hy' : 0 < y+1 := by positivity
    have hx : ((N+j : ℕ) : ℝ) = y+1 := by push_cast; dsimp [y]; ring
    have hx' : (N : ℝ) - 1 + ((j+1 : ℕ) : ℝ) = y+1 := by push_cast; dsimp [y]; ring
    change _ ≤ 1/y - 1/((N : ℝ)-1+((j+1 : ℕ) : ℝ))
    rw [hx, hx']
    calc
      _ ≤ 1 / (y*(y+1)) := one_div_le_one_div_of_le (by positivity) (by nlinarith)
      _ = _ := by field_simp; ring
  have hs : Summable (fun j : ℕ => 1 / (((N+j : ℕ) : ℝ)^2)) := by
    simpa only [Nat.add_comm N] using (summable_nat_add_iff N).2
      (Real.summable_one_div_nat_pow.mpr (by decide : 1 < 2))
  apply le_of_tendsto hs.hasSum.tendsto_sum_nat
  apply Eventually.of_forall
  intro k
  calc
    _ ≤ ∑ j ∈ Finset.range k, (v j - v (j+1)) := Finset.sum_le_sum (fun j _ => hstep j)
    _ = v 0 - v k := by rw [Finset.sum_range_sub']
    _ ≤ _ := by simpa only [v, Nat.cast_zero, add_zero] using
      sub_le_self (v 0) (one_div_nonneg.mpr (hv k).le : 0 ≤ v k)

private theorem kernel_bound (x δ t : ℝ) (hδ : 0 < δ) (hx : δ ≤ |-1/24 - x|) :
    ‖kernel x t‖ ≤ 1 / Real.sqrt δ := by
  have hne : (-1/24 : ℝ) ≠ x := by
    intro he
    rw [he, sub_self, abs_zero] at hx
    exact (not_lt_of_ge hx) hδ
  change ‖fktyVerticalKernel (-1/24) x t‖ ≤ _
  exact (norm_fktyVerticalKernel_le (-1/24) x t hne).trans
    (one_div_le_one_div_of_le (Real.sqrt_pos.2 hδ) (Real.sqrt_le_sqrt hx))

private theorem kernel_integrable {x δ : ℝ} (hδ : 0 < δ) (hx : δ ≤ |-1/24 - x|)
    (v : ℂ) {g : ℝ → ℝ} (hg : IntegrableOn g (Ioi 0)) :
    IntegrableOn (fun t => kernel x t * (v * (g t : ℂ))) (Ioi 0) := by
  exact (hg.ofReal.const_mul v).bdd_mul
    ((continuousOn_fktyVerticalKernel (-1/24) x).aestronglyMeasurable measurableSet_Ioi)
    (Eventually.of_forall (fun t => kernel_bound x δ t hδ hx))

private theorem integral_kernel_norm_le {x δ : ℝ} (hδ : 0 < δ) (hx : δ ≤ |-1/24 - x|)
    {v : ℂ} (hv : ‖v‖ ≤ 1) {g : ℝ → ℝ} (hg : IntegrableOn g (Ioi 0)) :
    (∫ t in Ioi (0 : ℝ), ‖kernel x t * (v * (g t : ℂ))‖) ≤
      (1 / Real.sqrt δ) * ∫ t in Ioi (0 : ℝ), ‖g t‖ := by
  rw [← integral_const_mul]
  apply integral_mono (kernel_integrable hδ hx v hg).norm (hg.norm.const_mul _)
  intro t
  simp only [norm_mul, Complex.norm_real, ← mul_assoc]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  calc
    _ ≤ ‖kernel x t‖ * 1 := mul_le_mul_of_nonneg_left hv (norm_nonneg _)
    _ ≤ _ := by simpa only [mul_one] using kernel_bound x δ t hδ hx

/-- Shifting the omitted tail by a sign-reversing block splits it into a finite
edge and paired differences. This identity is pointwise at positive height. -/
private theorem pairedTail (S N : ℕ) (v : ℕ → ℂ)
    (hanti : ∀ m, v (m+S) = -v m) (t : ℝ)
    (hs : Summable (fun m => v m * (gaussianMode gaussianRate m t : ℂ))) :
    2 * (∑' m : ℕ, v m * (gaussianMode gaussianRate m t : ℂ)) =
      2 * (∑ m ∈ Finset.range N, v m * (gaussianMode gaussianRate m t : ℂ)) +
      (∑ j ∈ Finset.range S, v (N+j) * (gaussianMode gaussianRate (N+j) t : ℂ)) +
      ∑' j : ℕ, v (N+j) *
        ((gaussianMode gaussianRate (N+j) t - gaussianMode gaussianRate (N+j+S) t : ℝ) : ℂ) := by
  let f (m : ℕ) := v m * (gaussianMode gaussianRate m t : ℂ)
  have h0 : Summable (fun j => f (N+j)) := by
    simpa only [Nat.add_comm N] using (summable_nat_add_iff N).2 hs
  have h1 : Summable (fun j => f (N+j+S)) := by
    simpa only [Nat.add_assoc] using (summable_nat_add_iff S).2 h0
  have hp (j : ℕ) : v (N+j) *
      ((gaussianMode gaussianRate (N+j) t - gaussianMode gaussianRate (N+j+S) t : ℝ) : ℂ) =
        f (N+j) + f (N+j+S) := by
    simp only [f, hanti, ofReal_sub]
    ring
  simp_rw [hp]
  rw [h0.tsum_add h1]
  have hf : Summable f := hs
  have hhead := hf.sum_add_tsum_nat_add N
  have hedge := h0.sum_add_tsum_nat_add S
  simp only [← Nat.add_assoc] at hedge
  have hhead' : (∑ m ∈ Finset.range N, f m) + (∑' j : ℕ, f (N+j)) = ∑' m, f m := by
    simpa only [Nat.add_comm N] using hhead
  change 2 * (∑' m, f m) = 2 * (∑ m ∈ Finset.range N, f m) +
    (∑ j ∈ Finset.range S, f (N+j)) + ((∑' j : ℕ, f (N+j)) + ∑' j : ℕ, f (N+j+S))
  linear_combination -2*hhead' - hedge

theorem weightedPhase_bound (w : Phase → ℂ) (hw : ∀ r, ‖w r‖ ≤ 1) (m : ℕ) :
    ‖w (phase m) * fktyCuspPhase m‖ ≤ 1 := by
  rw [norm_mul, ← one_mul (1 : ℝ)]
  exact mul_le_mul (hw _) (norm_fktyCuspPhase_le_one m) (norm_nonneg _) zero_le_one

theorem weightedModes_summable (w : Phase → ℂ) (hw : ∀ r, ‖w r‖ ≤ 1)
    (t : ℝ) (ht : 0 < t) :
    Summable (fun m => (w (phase m) * fktyCuspPhase m) * (gaussianMode gaussianRate m t : ℂ)) := by
  apply (summable_fktyCuspModes t ht).norm.of_norm_bounded
  intro m
  rw [mul_assoc, norm_mul]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right (hw (phase m))
    (norm_nonneg (fktyCuspPhase m * (gaussianMode gaussianRate m t : ℂ)))

theorem recoveredThetaUpTo_ray (D N : ℕ) (w : Phase → ℂ) (t : ℝ) (hN : N ≤ modeCount D) :
    recoveredThetaUpTo (observe D mockCoeff) w N (cuspRay t) =
      2 * ∑ m ∈ Finset.range N,
        (w (phase m) * fktyCuspPhase m) * (gaussianMode gaussianRate m t : ℂ) := by
  rw [recoveredThetaUpTo, Finset.sum_div, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  have h : m ≤ (24*D+1).sqrt := Nat.lt_succ_iff.mp ((Finset.mem_range.mp hm).trans_le hN)
  rw [ShadowReconstruction.mock_shadowMode_eq_cutoff, if_pos h]
  have he := shadowTerm_cusp t m
  change (shadowWeight m : ℂ) * shadowNome (cuspRay t) ^ (m ^ 2) =
    fktyCuspPhase m * (gaussianMode gaussianRate m t : ℂ) at he
  push_cast
  rw [mul_assoc (w (phase m)), mul_assoc (4 : ℂ), he]
  ring

private theorem recoveredTheta_ray (D : ℕ) (w : Phase → ℂ) (t : ℝ) :
    recoveredTheta (observe D mockCoeff) w (cuspRay t) =
      2 * ∑ m ∈ Finset.range (modeCount D),
        (w (phase m) * fktyCuspPhase m) * (gaussianMode gaussianRate m t : ℂ) :=
  recoveredThetaUpTo_ray D (modeCount D) w t le_rfl

private theorem cuspPhase_shift (m k : ℕ) :
    fktyCuspPhase (m + 144*k) = (-1 : ℂ)^k * fktyCuspPhase m := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.mul_succ, ← Nat.add_assoc, fktyCuspPhase_add_144, ih, pow_succ]
    ring

private theorem phase_shift (m : ℕ) : phase (m+1584) = phase m := by
  unfold phase
  push_cast
  rw [show (1584 : Phase) = 0 by decide, add_zero]

/-- The sector mask survives eleven 144-mode shifts, which still reverse the
cusp phase. A single 144-mode shift may change the sector. -/
theorem weightedPhase_add_1584 (w : Phase → ℂ) (m : ℕ) :
    w (phase (m+1584)) * fktyCuspPhase (m+1584) =
      -(w (phase m) * fktyCuspPhase m) := by
  have h : fktyCuspPhase (m+1584) = -fktyCuspPhase m := by
    simpa only [show 144*11 = 1584 by decide, show (-1 : ℂ)^11 = -1 by norm_num, neg_one_mul]
      using cuspPhase_shift m 11
  rw [phase_shift, h, mul_neg]

theorem phase_add_144_changes_sector : phase (1+144) ≠ phase 1 := by decide +kernel

/-- Quantitative convergence on the whole cusp ray. The bound holds uniformly
when the boundary parameter stays at least δ from the starting cusp. -/
private theorem recoveredPeriod_error_of_shift (D S : ℕ) (w : Phase → ℂ)
    (hw : ∀ r, ‖w r‖ ≤ 1)
    (hanti : ∀ m, w (phase (m+S)) * fktyCuspPhase (m+S) =
      -(w (phase m) * fktyCuspPhase m))
    {x δ : ℝ} (hδ : 0 < δ) (hx : δ ≤ |-1/24 - x|) :
    ‖recoveredPeriod (observe D mockCoeff) w x - weightedCuspPeriod w x‖ ≤
      (1 / Real.sqrt δ) * (4 * S / gaussianRate) * (1 / ((modeCount D : ℝ) - 1)) := by
  let N := modeCount D
  let B : ℝ := 1 / Real.sqrt δ
  let v (m : ℕ) := w (phase m) * fktyCuspPhase m
  let F (m : ℕ) (t : ℝ) := kernel x t * (v m * (gaussianMode gaussianRate m t : ℂ))
  let difference (j : ℕ) (t : ℝ) := gaussianMode gaussianRate (N+j) t -
      gaussianMode gaussianRate (N+j+S) t
  let G (j : ℕ) (t : ℝ) := kernel x t * (v (N+j) * (difference j t : ℂ))
  have hB : 0 ≤ B := by positivity
  have ha := rate_pos
  have hN := modeCount_ge_two D
  have hN' : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hv := weightedPhase_bound w hw
  have hmode m := integrableOn_gaussianMode gaussianRate ha m
  have hF m : IntegrableOn (F m) (Ioi 0) := kernel_integrable hδ hx _ (hmode m)
  have hdiff j : IntegrableOn (difference j) (Ioi 0) := (hmode _).sub (hmode _)
  have hG j : IntegrableOn (G j) (Ioi 0) := kernel_integrable hδ hx _ (hdiff j)
  have hE j : (∫ t in Ioi (0:ℝ), ‖F (N+j) t‖) ≤ B * (1 / (gaussianRate * N)) := by
    have hj : 0 < N+j := by omega
    calc
      _ ≤ B * ∫ t in Ioi (0:ℝ), ‖gaussianMode gaussianRate (N+j) t‖ :=
        integral_kernel_norm_le hδ hx (hv _) (hmode _)
      _ ≤ _ := by
        rw [integral_norm_gaussianMode _ hj]
        gcongr
        exact_mod_cast (Nat.le_add_right N j)
  have hP j : (∫ t in Ioi (0:ℝ), ‖G j t‖) ≤
      (B * (3 * S / gaussianRate)) * (1 / (((N+j : ℕ) : ℝ)^2)) := by
    have hj : 0 < N+j := by omega
    calc
      _ ≤ B * ∫ t in Ioi (0:ℝ), ‖difference j t‖ :=
        integral_kernel_norm_le hδ hx (hv _) (hdiff j)
      _ ≤ B * (3 * S / (gaussianRate * (((N+j : ℕ) : ℝ)^2))) :=
        mul_le_mul_of_nonneg_left (integral_norm_gaussianMode_sub_le _ ha _ _ hj) hB
      _ = _ := by ring
  have hsq : Summable (fun j : ℕ => 1 / (((N+j : ℕ) : ℝ)^2)) := by
    simpa only [Nat.add_comm N] using (summable_nat_add_iff N).2
      (Real.summable_one_div_nat_pow.mpr (by decide : 1 < 2))
  have hmajor := hsq.mul_left (B * (3 * S / gaussianRate))
  have hsum : Summable (fun j => ∫ t in Ioi (0:ℝ), ‖G j t‖) :=
    Summable.of_nonneg_of_le (fun _ => integral_nonneg (fun _ => norm_nonneg _)) hP hmajor
  have hpolynomial (t : ℝ) : kernel x t * recoveredTheta (observe D mockCoeff) w (cuspRay t) =
      2 * ∑ m ∈ Finset.range N, F m t := by
    rw [recoveredTheta_ray]
    simp only [F, ← Finset.mul_sum]
    ring
  have hpoint (t : ℝ) (ht : 0 < t) :
      kernel x t * weightedCuspTheta w t -
        kernel x t * recoveredTheta (observe D mockCoeff) w (cuspRay t) =
        (∑ j ∈ Finset.range S, F (N+j) t) + ∑' j, G j t := by
    rw [hpolynomial, weightedCuspTheta]
    simp only [← mul_assoc (w _), F, G, ← Finset.mul_sum, tsum_mul_left]
    have h : Summable (fun m => v m * (gaussianMode gaussianRate m t : ℂ)) :=
      weightedModes_summable w hw t ht
    rw [pairedTail S N v hanti t h]
    dsimp only [difference]
    ring
  have hrec : IntegrableOn (fun t => kernel x t * recoveredTheta (observe D mockCoeff) w (cuspRay t))
      (Ioi 0) := by
    simp_rw [hpolynomial]
    have hi : IntegrableOn (fun t => ∑ m ∈ Finset.range N, F m t) (Ioi 0) :=
      integrable_finset_sum _ (fun m _ => hF m)
    exact hi.const_mul _
  have hedge : IntegrableOn (fun t => ∑ j ∈ Finset.range S, F (N+j) t) (Ioi 0) :=
    integrable_finset_sum _ (fun _ _ => hF _)
  have htail : IntegrableOn (fun t => ∑' j, G j t) (Ioi 0) :=
    integrable_tsum_of_summable_integral_norm G hG hsum
  have he : IntegrableOn (fun t => (∑ j ∈ Finset.range S, F (N+j) t) + ∑' j, G j t) (Ioi 0) :=
    hedge.add htail
  have herr := he.congr_fun (fun t ht => (hpoint t ht).symm) measurableSet_Ioi
  have htotal : IntegrableOn (fun t => kernel x t * weightedCuspTheta w t) (Ioi 0) := by
    exact (herr.add hrec).congr (Eventually.of_forall (fun _ => sub_add_cancel _ _))
  have hval : weightedCuspPeriod w x - recoveredPeriod (observe D mockCoeff) w x =
      (∑ j ∈ Finset.range S, ∫ t in Ioi (0:ℝ), F (N+j) t) +
        ∑' j, ∫ t in Ioi (0:ℝ), G j t := by
    unfold weightedCuspPeriod recoveredPeriod
    rw [← integral_sub htotal hrec, setIntegral_congr_fun measurableSet_Ioi hpoint,
      integral_add hedge htail, integral_finset_sum _ (fun _ _ => hF _),
      ← integral_tsum_of_summable_integral_norm hG hsum]
  have hfinite : ‖∑ j ∈ Finset.range S, ∫ t in Ioi (0:ℝ), F (N+j) t‖ ≤
      (S : ℝ) * (B * (1 / (gaussianRate * N))) := by
    refine (norm_sum_le _ _).trans ?_
    calc
      _ ≤ ∑ _j ∈ Finset.range S, B * (1 / (gaussianRate * N)) :=
        Finset.sum_le_sum (fun j _ => (norm_integral_le_integral_norm _).trans (hE j))
      _ = _ := by simp
  have hnorm : Summable (fun j => ‖∫ t in Ioi (0:ℝ), G j t‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun _ => norm_integral_le_integral_norm _) hsum
  have hinfinite : ‖∑' j, ∫ t in Ioi (0:ℝ), G j t‖ ≤
      (B * (3 * S / gaussianRate)) * (1 / ((N : ℝ) - 1)) := by
    refine (norm_tsum_le_tsum_norm hnorm).trans ?_
    calc
      _ ≤ ∑' j : ℕ, (B * (3 * S / gaussianRate)) * (1 / (((N+j : ℕ) : ℝ)^2)) :=
        hnorm.tsum_le_tsum (fun j => (norm_integral_le_integral_norm _).trans (hP j)) hmajor
      _ ≤ _ := by
        rw [hsq.tsum_mul_left]
        exact mul_le_mul_of_nonneg_left (squareTail_le N hN) (by positivity)
  rw [norm_sub_rev, hval]
  refine (norm_add_le _ _).trans ((add_le_add hfinite hinfinite).trans ?_)
  change (S:ℝ) * (B * (1 / (gaussianRate * N))) +
    (B * (3 * S / gaussianRate)) * (1 / ((N : ℝ) - 1)) ≤
    B * (4 * S / gaussianRate) * (1 / ((N : ℝ) - 1))
  have hinv : 1 / (N : ℝ) ≤ 1 / ((N : ℝ) - 1) :=
    one_div_le_one_div_of_le (sub_pos.mpr hN') (by linarith)
  calc
    _ = (B * (S / gaussianRate)) * (1 / (N : ℝ)) +
        (B * (3 * S / gaussianRate)) * (1 / ((N : ℝ) - 1)) := by ring
    _ ≤ (B * (S / gaussianRate)) * (1 / ((N : ℝ) - 1)) +
        (B * (3 * S / gaussianRate)) * (1 / ((N : ℝ) - 1)) :=
      add_le_add (mul_le_mul_of_nonneg_left hinv
        (show 0 ≤ B * ((S : ℝ) / gaussianRate) by positivity)) le_rfl
    _ = _ := by ring

theorem recoveredPeriod_error (D : ℕ) (w : Phase → ℂ) (hw : ∀ r, ‖w r‖ ≤ 1)
    {x δ : ℝ} (hδ : 0 < δ) (hx : δ ≤ |-1/24 - x|) :
    ‖recoveredPeriod (observe D mockCoeff) w x - weightedCuspPeriod w x‖ ≤
      (1 / Real.sqrt δ) * (4 * 1584 / gaussianRate) * (1 / ((modeCount D : ℝ) - 1)) :=
  recoveredPeriod_error_of_shift D 1584 w hw (weightedPhase_add_1584 w) hδ hx

theorem weightedCuspPeriod_one (x : ℝ) :
    weightedCuspPeriod (fun _ => 1) x = fktyCuspPeriod x := by
  unfold weightedCuspPeriod fktyCuspPeriod
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  simp only [weightedCuspTheta, one_mul, gaussianRate, kernel]
  rw [fktyTheta_cusp t ht]

theorem recoveredFullPeriod_error (D : ℕ) {x δ : ℝ}
    (hδ : 0 < δ) (hx : δ ≤ |-1/24 - x|) :
    ‖recoveredPeriod (observe D mockCoeff) (fun _ => 1) x - fktyCuspPeriod x‖ ≤
      (1 / Real.sqrt δ) * (4 * 144 / gaussianRate) * (1 / ((modeCount D : ℝ) - 1)) := by
  rw [← weightedCuspPeriod_one]
  exact recoveredPeriod_error_of_shift D 144 (fun _ => 1) (fun _ => by simp)
    (by simpa only [one_mul] using fktyCuspPhase_add_144) hδ hx

/-- Select one prime-11 sector of the differential shadow. -/
def sectorWeight (r s : Phase) : ℂ := if s = r then 1 else 0

theorem recoveredTheta_sector {D : ℕ} (reading : Prefix D) (r : Phase) (u : ℂ) :
    recoveredTheta reading (sectorWeight r) u =
      ShadowReconstruction.reconstruct reading r (shadowNome u) / 2 := by
  unfold recoveredTheta recoveredThetaUpTo ShadowReconstruction.reconstruct
  congr 1
  apply Finset.sum_congr rfl
  intro m _
  by_cases h : phase m = r <;> simp [sectorWeight, h, pow_two]

theorem weightedCuspTheta_sector_eq_xiHalf (r : Phase) (t : ℝ) (ht : 0 < t) :
    weightedCuspTheta (sectorWeight r) t = xiHalf (project11 r mockCompletion) (cuspRay t / 24) / 2 := by
  have hpos : 0 < (cuspRay t / 24).im := by
    rw [Complex.div_ofNat_im, show (cuspRay t).im = t by simp [cuspRay]]
    positivity
  rw [xiHalf_project11_mockCompletion _ _ hpos, integerNome_eq_shadowNome,
    show 24 * (cuspRay t / 24) = cuspRay t by ring, weightedCuspTheta]
  have h : (∑' m : ℕ, sectorWeight r (phase m) *
      (fktyCuspPhase m * (gaussianMode gaussianRate m t : ℂ))) =
      shadowDegreeBin ⟨(-r).val,(-r).val_lt⟩ (shadowNome (cuspRay t)) := by
    rw [shadowDegreeBin]
    apply tsum_congr
    intro m
    have hm : phase m = r ↔ degreeClass m = ⟨(-r).val,(-r).val_lt⟩ := by
      have hb : degreeClass m = ⟨(-r).val,(-r).val_lt⟩ ↔ m^2 % 11 = (-r).val := Fin.ext_iff
      rw [hb, phase, neg_eq_iff_eq_neg, ← (ZMod.val_injective 11).eq_iff,
        ← Nat.cast_pow, ZMod.val_natCast]
    have hterm := shadowTerm_cusp t m
    change shadowTerm (shadowNome (cuspRay t)) m =
      fktyCuspPhase m * (gaussianMode gaussianRate m t : ℂ) at hterm
    by_cases hs : phase m = r
    · simp only [sectorWeight, if_pos hs, one_mul, if_pos (hm.mp hs), hterm]
    · simp only [sectorWeight, if_neg hs, zero_mul, if_neg (mt hm.mpr hs)]
  rw [h]
  ring

private theorem inverse_modeCount_tendsto :
    Tendsto (fun D : ℕ => 1 / ((modeCount D : ℝ) - 1)) atTop (𝓝 0) := by
  have hs : Tendsto (fun D : ℕ => (24*D+1).sqrt) atTop atTop := by
    apply tendsto_atTop.2
    intro K
    filter_upwards [eventually_ge_atTop (K*K)] with D hD
    exact Nat.le_sqrt.mpr (by omega)
  apply ((tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).comp hs).congr
  intro D
  simp [modeCount]

theorem recoveredPeriod_uniform (w : Phase → ℂ) (hw : ∀ r, ‖w r‖ ≤ 1)
    {δ : ℝ} (hδ : 0 < δ) :
    TendstoUniformlyOn (fun D x => recoveredPeriod (observe D mockCoeff) w x)
      (weightedCuspPeriod w) atTop {x : ℝ | δ ≤ |-1/24 - x|} := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hlim := inverse_modeCount_tendsto.const_mul ((1 / Real.sqrt δ) * (4 * 1584 / gaussianRate))
  rw [mul_zero] at hlim
  have hsmall := (tendsto_order.1 hlim).2 ε hε
  filter_upwards [hsmall] with D hD
  intro x hx
  rw [dist_eq_norm, norm_sub_rev]
  exact (recoveredPeriod_error D w hw hδ hx).trans_lt hD

open KElimination.QuantumRadial

private theorem weightedCuspPeriod_one_order34 :
    weightedCuspPeriod (fun _ => 1) (-1/34) = fktyVerticalPeriod fktyTheta (-1/24) (-1/34) := by
  rw [weightedCuspPeriod_one]
  rw [← show ((-1/34 : ℚ) : ℝ) = (-1/34 : ℝ) by norm_num]
  exact fktyCuspPeriod_rat (-1/34)

private theorem recoveredFullPeriod_tendsto_order34 :
    Tendsto (fun D => recoveredPeriod (observe D mockCoeff) (fun _ => 1) (-1/34))
      atTop (𝓝 (fktyVerticalPeriod fktyTheta (-1/24) (-1/34))) := by
  rw [← weightedCuspPeriod_one_order34]
  exact (recoveredPeriod_uniform (fun _ => 1) (fun _ => by simp)
    (δ := 5/408) (by norm_num)).tendsto_at (by norm_num : (-1/34 : ℝ) ∈
      {x : ℝ | (5/408 : ℝ) ≤ |-1/24 - x|})

/-- The period recovered from f's S6 prefixes tends to the exact normalized
order-34 to order-10 defect for every signed source and stabilized packet pair. -/
theorem recoveredPeriod_tendsto_normalizedPacketDefect (X : ℤ) (N34 N10 : ℕ)
    (h34 : 17 ≤ N34) (h10 : 5 ≤ N10) :
    Tendsto (fun D => recoveredPeriod (observe D mockCoeff) (fun _ => 1) (-1/34))
      atTop (𝓝 (Order34Source.normalizedPacketDefect N34 N10 (Order34Source.observe X))) := by
  rw [Order34Source.normalizedPacketDefect_eq_boundary X N34 N10 h34 h10,
    ← fktyPhi_neg_one_div_34, ← fktyPhi_neg_one_div_10, fkty_defect34_eq_period]
  exact recoveredFullPeriod_tendsto_order34

private def transportTo34 {D : ℕ} (reading : Prefix D) (endpoint10 : ℂ) : ℂ :=
  (recoveredPeriod reading (fun _ => 1) (-1/34) +
    (Real.sqrt (17/5) : ℂ) * ((fktyScale * integerNome (-1/240)) * endpoint10)) /
    (fktyScale * integerNome (-1/816))

/-- Use the order-10 endpoint with the period recovered from S6 observations. -/
def recoveredBoundary34 {D : ℕ} (reading : Prefix D) : ℂ :=
  transportTo34 reading (boundaryValue 5 (integerNome (1/10)))

theorem recoveredBoundary34_tendsto :
    Tendsto (fun D => recoveredBoundary34 (observe D mockCoeff)) atTop
      (𝓝 (boundaryValue 17 (integerNome (1/34)))) := by
  rw [boundary34_from_period_and_ten_unconditional]
  exact (recoveredFullPeriod_tendsto_order34.add_const _).div_const _

/-- Remove the source phase from the order-10 packets, then apply the order-34
phase read from parity and the same-source mod-17 anchor. -/
def recoveredTranslatedBoundary34 {D : ℕ} (reading : Prefix D) (lanes : Order34Source.Lanes)
    (N10 : ℕ) : ℂ :=
  let ζ := integerNome (1/34)
  let η := integerNome (1/10)
  ζ ^ Order34Source.exponent34 lanes * transportTo34 reading
    (Order34Source.translatedPacketValue η N10 30030 Order34Source.exponent10 lanes /
      η ^ Order34Source.exponent10 lanes)

private theorem order34_period_error (D : ℕ) :
    ‖recoveredBoundary34 (observe D mockCoeff) - boundaryValue 17 (integerNome (1/34))‖ ≤
      7680 / ((24*D+1).sqrt : ℝ) := by
  have h := recoveredFullPeriod_error D (x := -1/34) (δ := 1/100) (by norm_num) (by norm_num)
  have hp : fktyVerticalPeriod fktyTheta (-1/24) (-1/34) = fktyCuspPeriod (-1/34) :=
    weightedCuspPeriod_one_order34.symm.trans (weightedCuspPeriod_one _)
  have hscale : ‖fktyScale‖ = Real.sqrt 12 := by
    rw [fktyScale, show (1/2 : ℂ) = ((1/2 : ℝ) : ℂ) by push_cast; rfl,
      Complex.norm_cpow_real, norm_mul, Complex.norm_I, mul_one, Real.sqrt_eq_rpow]
    norm_num
  have hroot : ‖integerNome (-1/816)‖ = 1 := by
    norm_num [integerNome, Complex.norm_exp, Complex.mul_re, Complex.mul_im]
  have hg : 1/4 ≤ gaussianRate := by unfold gaussianRate; linarith [Real.pi_gt_three]
  have hs : 3 ≤ Real.sqrt 12 := (Real.le_sqrt (by norm_num) (by norm_num)).2 (by norm_num)
  have hrad : Real.sqrt (1/100) = 1/10 := (Real.sqrt_eq_iff_eq_sq (by norm_num)
    (by norm_num)).2 (by norm_num)
  have hD : 0 < ((24*D+1).sqrt : ℝ) := by
    exact_mod_cast (show 0 < (24*D+1).sqrt from Nat.le_sqrt.mpr (by omega))
  rw [hrad] at h
  simp only [modeCount, Nat.cast_add, Nat.cast_one, add_sub_cancel_right] at h
  rw [recoveredBoundary34, transportTo34, boundary34_from_period_and_ten_unconditional,
    ← sub_div, add_sub_add_right_eq_sub, hp, norm_div, norm_mul, hroot, mul_one, hscale]
  apply (div_le_iff₀ (by positivity)).2
  refine h.trans ?_
  have hr : 4 * 144 / gaussianRate ≤ 2304 :=
    (div_le_iff₀ rate_pos).2 (by linarith)
  calc
    _ ≤ (1 / (1/10)) * 2304 * (1 / ((24*D+1).sqrt : ℝ)) := by gcongr
    _ = 7680 / ((24*D+1).sqrt : ℝ) * 3 := by ring
    _ ≤ _ := by gcongr

/-- A finite prefix controls the translated packet endpoint for every signed source. -/
theorem recoveredTranslatedBoundary34_error (D : ℕ) (X : ℤ) (N34 N10 : ℕ)
    (h34 : 17 ≤ N34) (h10 : 5 ≤ N10) :
    ‖recoveredTranslatedBoundary34 (observe D mockCoeff) (Order34Source.observe X) N10 -
      Order34Source.translatedPacketValue (integerNome (1/34)) N34 510510
        Order34Source.exponent34 (Order34Source.observe X)‖ ≤ 7680 / ((24*D+1).sqrt : ℝ) := by
  have hζ : IsPrimitiveRoot (integerNome (1/34)) 34 := by
    simpa [integerNome, mul_one_div] using Complex.isPrimitiveRoot_exp 34 (by decide)
  have hη : IsPrimitiveRoot (integerNome (1/10)) 10 := by
    simpa [integerNome, mul_one_div] using Complex.isPrimitiveRoot_exp 10 (by decide)
  obtain ⟨p34, p10⟩ := Order34Source.source_packet_endpoints X N34 N10 hζ hη h34 h10
  obtain ⟨e34, e10⟩ := Order34Source.source_phase_shift 0 X hζ hη
  simp only [Order34Source.translate_observe, zero_add, zpow_zero, one_mul] at e34 e10
  rw [recoveredTranslatedBoundary34, p34, p10, e34, e10,
    mul_div_cancel_left₀ _ (zpow_ne_zero X (hη.ne_zero (by decide))), ← mul_sub, norm_mul,
    norm_zpow, hζ.norm'_eq_one (by decide), one_zpow, one_mul]
  exact order34_period_error D

/-- Sufficient last coefficient degree for reciprocal precision 1/n. -/
def boundary34Degree (n : ℕ) : ℕ := 2457600 * n^2

theorem recoveredTranslatedBoundary34_precision (D n : ℕ) (X : ℤ) (N34 N10 : ℕ)
    (hn : 0 < n) (hD : boundary34Degree n ≤ D) (h34 : 17 ≤ N34) (h10 : 5 ≤ N10) :
    ‖recoveredTranslatedBoundary34 (observe D mockCoeff) (Order34Source.observe X) N10 -
      Order34Source.translatedPacketValue (integerNome (1/34)) N34 510510
        Order34Source.exponent34 (Order34Source.observe X)‖ ≤ 1 / (n : ℝ) := by
  have hm : 7680*n ≤ (24*D+1).sqrt := Nat.le_sqrt.mpr (by
    unfold boundary34Degree at hD
    nlinarith)
  have hmr : 7680*(n : ℝ) ≤ ((24*D+1).sqrt : ℝ) := by exact_mod_cast hm
  have hnr : 0 < (n : ℝ) := by exact_mod_cast hn
  exact (recoveredTranslatedBoundary34_error D X N34 N10 h34 h10).trans
    ((div_le_div_iff₀ (by linarith : 0 < ((24*D+1).sqrt : ℝ)) hnr).2 (by linarith))

/-- Integer ceiling division selects a prefix for a positive rational tolerance a/b. -/
def boundary34ToleranceDegree (a b : ℕ) : ℕ := boundary34Degree (b ⌈/⌉ a)

theorem recoveredTranslatedBoundary34_tolerance (D a b : ℕ) (X : ℤ) (N34 N10 : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hD : boundary34ToleranceDegree a b ≤ D)
    (h34 : 17 ≤ N34) (h10 : 5 ≤ N10) :
    ‖recoveredTranslatedBoundary34 (observe D mockCoeff) (Order34Source.observe X) N10 -
      Order34Source.translatedPacketValue (integerNome (1/34)) N34 510510
        Order34Source.exponent34 (Order34Source.observe X)‖ ≤ (a : ℝ) / b := by
  have hceil : b ≤ a * (b ⌈/⌉ a) := (ceilDiv_le_iff_le_mul ha).1 le_rfl
  have hn : 0 < b ⌈/⌉ a := by
    by_contra! hz
    simp [Nat.eq_zero_of_le_zero hz] at hceil
    omega
  apply (recoveredTranslatedBoundary34_precision D _ X N34 N10 hn hD h34 h10).trans
  apply (div_le_div_iff₀ (by exact_mod_cast hn) (by exact_mod_cast hb)).2
  simpa only [one_mul] using (show (b : ℝ) ≤ a * ((b ⌈/⌉ a : ℕ) : ℝ) by exact_mod_cast hceil)

end MockThetaAnalytic.ShadowPeriod
