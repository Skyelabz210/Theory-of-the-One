import ShadowHecke
import ShadowPentagonal
import MockCompletion
import Mathlib.Topology.MetricSpace.Pseudo.Constructions
import Mathlib.Topology.UniformSpace.UniformConvergence
import Mathlib.Tactic.Positivity

/-! Read the normalized shadow from a degree-labeled coefficient observation.
The observation rule uses only the signed reciprocal-support calculation. The
existing completion, imported here on the verification side, supplies the target. -/

namespace MockThetaAnalytic.ShadowReconstruction

noncomputable section

open ShadowReadings ShadowHecke
open KElimination.MockTheta KElimination.MockThetaShadow KElimination.ShadowConvergence
open scoped BigOperators Topology
open Filter

/-- The exact coefficient form of the Euler reciprocal calculation. -/
def ReciprocalSupport (a : ℕ → ℤ) : Prop :=
  ∀ d, reciprocalBit (fun i => (a i : ZMod 2)) d = pentagonalBit d

private theorem chi_sign (m : ℕ) : chiFour m * etaSign m = shadowSign m := by
  have h : ∀ r : Fin 12, chiFour r.val * etaSign r.val = shadowSign r.val := by decide +kernel
  have hm₄ : (m%12)%4 = m%4 := by omega
  have hm₆ : (m%12)%6 = m%6 := by omega
  simpa only [chiFour, etaSign, shadowSign, hm₄, hm₆, Nat.mod_mod] using
    h ⟨m%12,Nat.mod_lt _ (by decide)⟩

private theorem etaSign_of_off_lattice (m : ℕ) (h : (m*m)%24 ≠ 1) : etaSign m = 0 := by
  have hm := mt (square_lattice m).mpr h
  unfold etaSign
  split_ifs <;> (try rfl) <;> omega

theorem etaMode_eq_cutoff (a : ℕ → ℤ) (hs : ReciprocalSupport a) (D m : ℕ) :
    etaMode (observe D a) m = if m ≤ (24*D+1).sqrt then etaSign m else 0 := by
  simp only [Nat.le_sqrt]
  by_cases hl : (m*m)%24 = 1
  · have hcut : (m*m-1)/24 ≤ D ↔ m*m ≤ 24*D+1 := by omega
    by_cases hw : (m*m-1)/24 ≤ D
    · have hsq : 24*((m*m-1)/24)+1 = m*m := by omega
      have p : pentagonalBit ((m*m-1)/24) = 1 := by simp [pentagonalBit, hsq, Nat.sqrt_eq]
      rw [etaMode, etaFromParity, reciprocal_prefix a hw, hs, p]
      simp [hl, hw, hcut.mp hw]
    · simp [etaMode, etaFromParity, hl, hw, mt hcut.mpr hw]
  · simp [etaMode, etaFromParity, hl, etaSign_of_off_lattice m hl]

private theorem moment_etaSign (m : ℕ) : firstMoment m * etaSign m = 4 * shadowWeight m := by
  rw [firstMoment, mul_assoc, chi_sign, shadowWeight]
  ring

theorem shadowMode_eq_cutoff (a : ℕ → ℤ) (hs : ReciprocalSupport a) (D m : ℕ) :
    shadowMode (observe D a) m =
      if m ≤ (24*D+1).sqrt then 4 * shadowWeight m else 0 := by
  rw [shadowMode, etaMode_eq_cutoff a hs]
  split_ifs <;> simp [moment_etaSign]

theorem hecke_from_observations (a : ℕ → ℤ) (hs : ReciprocalSupport a)
    (D m : ℕ) (r : Phase) (h : 5*m ≤ (24*D+1).sqrt) :
    targetFive (moment (sectorPacket (etaMode (observe D a)))) m r =
      -6 * moment (sectorPacket etaSign) m (4*r) := by
  have hc : sectorPacket (etaMode (observe D a)) = cut (24*D+1).sqrt (sectorPacket etaSign) := by
    funext k s
    rw [sectorPacket, etaMode_eq_cutoff a hs]
    unfold cut sectorPacket
    split_ifs <;> rfl
  rw [← hecke_moment, hc]
  unfold moment
  rw [sourceFive_lookahead _ h, sourceFive_eta]
  ring

def reconstruct {D : ℕ} (reading : Prefix D) (r : Phase) (q : ℂ) : ℂ :=
    ∑ m ∈ Finset.range ((24*D+1).sqrt+1),
      if phase m = r then (shadowMode reading m : ℂ) * q^(m*m) else 0

private def sectorTerm (r : Phase) (q : ℂ) (m : ℕ) : ℂ :=
  if phase m = r then (4:ℂ) * shadowTerm q m else 0

private theorem sum_sectorTerm (r : Phase) (q : ℂ) (hq : ‖q‖ < 1) :
    ∑' m, sectorTerm r q m = 4 * shadowDegreeBin ⟨(-r).val, (-r).val_lt⟩ q := by
  rw [shadowDegreeBin, ← (shadowDegreeBin_summable ⟨(-r).val,(-r).val_lt⟩ q hq).tsum_mul_left]
  apply tsum_congr
  intro m
  have hm : phase m = r ↔ degreeClass m = ⟨(-r).val,(-r).val_lt⟩ := by
    have hb : degreeClass m = ⟨(-r).val,(-r).val_lt⟩ ↔ m^2 % 11 = (-r).val := Fin.ext_iff
    rw [hb, phase, neg_eq_iff_eq_neg, ← (ZMod.val_injective 11).eq_iff,
      ← Nat.cast_pow, ZMod.val_natCast]
  by_cases h : phase m = r <;> simp [sectorTerm, h, hm.mp, mt hm.mpr]

private theorem reconstruct_as_sum (a : ℕ → ℤ) (hs : ReciprocalSupport a) (D : ℕ)
    (r : Phase) (q : ℂ) :
    reconstruct (observe D a) r q =
      ∑ m ∈ Finset.range ((24*D+1).sqrt+1), sectorTerm r q m := by
  apply Finset.sum_congr rfl
  intro m hm
  have h : m ≤ (24*D+1).sqrt := by have := Finset.mem_range.mp hm; omega
  rw [sectorTerm, shadowMode_eq_cutoff a hs, if_pos h]
  simp [shadowTerm, pow_two, mul_assoc]

private theorem term_majorant (r : Phase) {q : ℂ} {ρ : ℝ}
    (hρ : 0 ≤ ρ) (hq : ‖q‖ ≤ ρ) (m : ℕ) :
    ‖sectorTerm r q m‖ ≤ 4 * (m : ℝ) * ρ^(m*m) := by
  have hw : |(shadowWeight m : ℝ)| ≤ m := by
    rw [← Int.cast_abs, Int.abs_eq_natAbs]
    exact_mod_cast shadowWeight_natAbs_le m
  by_cases hr : phase m = r
  · simp only [sectorTerm, if_pos hr, shadowTerm, norm_mul, Complex.norm_intCast, norm_pow,
      pow_two]
    rw [show ‖(4:ℂ)‖ = 4 by norm_num, ← mul_assoc]
    exact mul_le_mul (mul_le_mul_of_nonneg_left hw (by norm_num))
      (pow_le_pow_left₀ (norm_nonneg q) hq _) (by positivity) (by positivity)
  · simp [sectorTerm, hr, mul_nonneg, hρ]

private theorem summable_majorant {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ₁ : ρ < 1) :
    Summable (fun m : ℕ => 4 * (m : ℝ) * ρ^(m*m)) := by
  have hgeom : Summable (fun m : ℕ => (m:ℝ)*ρ^m) := by
    simpa [abs_of_nonneg hρ] using summable_pow_mul_geometric_of_norm_lt_one
      (r := ρ) 1 (by simpa [Real.norm_eq_abs, abs_of_nonneg hρ] using hρ₁)
  refine Summable.of_nonneg_of_le (fun _ => by positivity)
    (fun m => ?_) (hgeom.mul_left 4)
  rw [← mul_assoc]
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_of_le_one hρ hρ₁.le (Nat.le_mul_self m)) (by positivity)

def tail (D : ℕ) (ρ : ℝ) : ℝ :=
  ∑' j : ℕ, 4 * ((j+((24*D+1).sqrt+1) : ℕ) : ℝ) * ρ^((j+((24*D+1).sqrt+1))^2)

private theorem norm_trunc_tsum_le (g : ℕ → ℂ) (G : ℕ → ℝ) (N : ℕ)
    (hG : Summable G) (hb : ∀ m, ‖g m‖ ≤ G m) :
    ‖(∑ m ∈ Finset.range N, g m) - (∑' m, g m)‖ ≤ ∑' j, G (j+N) := by
  have hg : Summable g := Summable.of_norm_bounded hG hb
  have hs := hg.sum_add_tsum_nat_add N
  have htail : Summable (fun j : ℕ => ‖g (j+N)‖) := (summable_nat_add_iff N).2 hg.norm
  have hmajor : Summable (fun j : ℕ => G (j+N)) := (summable_nat_add_iff N).2 hG
  rw [← hs, sub_add_cancel_left, norm_neg]
  exact (norm_tsum_le_tsum_norm htail).trans (htail.tsum_le_tsum (fun j => hb (j+N)) hmajor)

theorem reconstruct_tail_le (a : ℕ → ℤ) (hs : ReciprocalSupport a) (D : ℕ)
    (r : Phase) {q : ℂ} {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ₁ : ρ < 1) (hq : ‖q‖ ≤ ρ) :
    ‖reconstruct (observe D a) r q - 4 * shadowDegreeBin ⟨(-r).val,(-r).val_lt⟩ q‖ ≤ tail D ρ := by
  rw [reconstruct_as_sum a hs, ← sum_sectorTerm r q (hq.trans_lt hρ₁)]
  let N := (24*D+1).sqrt+1
  have h := norm_trunc_tsum_le (sectorTerm r q) (fun m : ℕ => 4*(m:ℝ)*ρ^(m*m)) N
      (summable_majorant hρ hρ₁) (term_majorant r hρ hq)
  simpa only [tail, pow_two, N] using h

theorem tail_tendsto_zero {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ₁ : ρ < 1) :
    Tendsto (fun D : ℕ => tail D ρ) atTop (𝓝 0) := by
  have h := summable_majorant hρ hρ₁
  have hN : Tendsto (fun D : ℕ => (24*D+1).sqrt+1) atTop atTop := by
    apply tendsto_atTop.2
    intro K
    filter_upwards [eventually_ge_atTop (K*K)] with D hD
    have hk : K ≤ (24*D+1).sqrt := Nat.le_sqrt.mpr (by omega)
    omega
  have hg := h.hasSum.tendsto_sum_nat
  have htail := (tendsto_const_nhds (x := ∑' m : ℕ, 4 * (m:ℝ) * ρ^(m*m))).sub hg
  rw [sub_self] at htail
  apply (htail.comp hN).congr
  intro D
  have ht := h.sum_add_tsum_nat_add ((24*D+1).sqrt+1)
  unfold tail
  simp only [Function.comp_apply, pow_two]
  linarith

theorem reconstruct_xiHalf_uniform (hs : ReciprocalSupport (mockCoeff (R:=ℤ)))
    (r : Phase) {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ₁ : ρ < 1) :
    TendstoUniformlyOn (fun D z => reconstruct (observe D mockCoeff) r (integerNome z))
      (xiHalf (project11 r mockCompletion)) atTop
      {z : ℂ | 0 < z.im ∧ ‖integerNome z‖ ≤ ρ} := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have ht := (tendsto_order.1 (tail_tendsto_zero hρ hρ₁)).2 ε hε
  filter_upwards [ht] with D hD
  intro z hz
  rw [dist_eq_norm, norm_sub_rev, xiHalf_project11_mockCompletion r z hz.1]
  exact (reconstruct_tail_le _ hs D r hρ hρ₁ hz.2).trans_lt hD

theorem mock_reciprocal_support : ReciprocalSupport (mockCoeff (R:=ℤ)) :=
  ShadowPentagonal.reciprocal_mock_pentagonal

theorem mock_shadowMode_eq_cutoff (D m : ℕ) :
    shadowMode (observe D mockCoeff) m =
      if m ≤ (24*D+1).sqrt then 4 * shadowWeight m else 0 :=
  shadowMode_eq_cutoff _ mock_reciprocal_support D m

theorem mock_reconstruct_xiHalf_uniform (r : Phase) {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ₁ : ρ < 1) :
    TendstoUniformlyOn (fun D z => reconstruct (observe D mockCoeff) r (integerNome z))
      (xiHalf (project11 r mockCompletion)) atTop
      {z : ℂ | 0 < z.im ∧ ‖integerNome z‖ ≤ ρ} :=
  reconstruct_xiHalf_uniform mock_reciprocal_support r hρ hρ₁

/-- Apply the target stencil to the reconstructed packet, then evaluate the
requested output window. The prefix theorem gives its lookahead requirement. -/
def heckePolynomial {D : ℕ} (reading : Prefix D) (E : ℕ) (r : Phase) (q : ℂ) : ℂ :=
  ∑ m ∈ Finset.range ((24*E+1).sqrt+1),
    (targetFive (moment (sectorPacket (etaMode reading))) m r : ℂ) * q^(m*m)

theorem mock_hecke_prefix (D E : ℕ) (r : Phase) (q : ℂ)
    (h : 5*(24*E+1).sqrt ≤ (24*D+1).sqrt) :
    heckePolynomial (observe D mockCoeff) E r q =
      (-6:ℂ) * reconstruct (observe E mockCoeff) (4*r) q := by
  rw [heckePolynomial, reconstruct_as_sum _ mock_reciprocal_support, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  have hbound : m ≤ (24*E+1).sqrt := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
  rw [hecke_from_observations _ mock_reciprocal_support _ _ _ ((Nat.mul_le_mul_left _ hbound).trans h)]
  by_cases hsector : phase m = 4*r
  · simp [moment, sectorPacket, sectorTerm, hsector, shadowTerm, moment_etaSign, pow_two, mul_assoc]
  · simp [moment, sectorPacket, sectorTerm, hsector, Ne.symm hsector]

private theorem hecke_lookahead_cutoff (D : ℕ) :
    5*(24*D+1).sqrt ≤ (24*(25*D+1)+1).sqrt := by
  apply Nat.le_sqrt.mpr
  calc
    _ = 25*((24*D+1).sqrt*(24*D+1).sqrt) := by ring
    _ ≤ 25*(24*D+1) := Nat.mul_le_mul_left _ (Nat.sqrt_le _)
    _ = _ := by ring

theorem mock_hecke_uniform (r : Phase) {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ₁ : ρ < 1) :
    TendstoUniformlyOn
      (fun D z => heckePolynomial (observe (25*D+1) mockCoeff) D r (integerNome z))
      (fun z => (-6:ℂ)*xiHalf (project11 (4*r) mockCompletion) z) atTop
      {z : ℂ | 0 < z.im ∧ ‖integerNome z‖ ≤ ρ} := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hbase := Metric.tendstoUniformlyOn_iff.mp
    (mock_reconstruct_xiHalf_uniform (4*r) hρ hρ₁) (ε/6) (by positivity)
  filter_upwards [hbase] with D hD
  intro z hz
  have he := hD z hz
  rw [dist_eq_norm] at he
  rw [mock_hecke_prefix _ _ _ _ (hecke_lookahead_cutoff D), dist_eq_norm,
    ← mul_sub, norm_mul, show ‖(-6:ℂ)‖ = 6 by norm_num]
  linarith

end
end MockThetaAnalytic.ShadowReconstruction
