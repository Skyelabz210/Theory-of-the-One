import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Tactic.Ring

/-! The weight-one-half ξ operator on real-differentiable complex functions,
and its action on the eleven finite Fourier projections by real translations. -/

noncomputable section

namespace MockThetaAnalytic

open Complex

def xiHalf (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  2 * I * (Real.sqrt z.im : ℂ) * starRingEnd ℂ ((fderiv ℝ f z 1 + I * fderiv ℝ f z I) / 2)

/-- Real translations used in the degree projector for the integer-scaled variable. -/
def shift11 (j : ZMod 11) : ℝ := (j.val : ℝ) / 11

/-- Real translations in z project integral Fourier degrees in q = exp(2πiz) onto r modulo 11. -/
def project11 (r : ZMod 11) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  ∑ j : ZMod 11, (ZMod.stdAddChar (-(r*j)) / 11) * f (z + (shift11 j : ℂ))

theorem xiHalf_const_mul (c : ℂ) (f : ℂ → ℂ) (z : ℂ) (hf : DifferentiableAt ℝ f z) :
    xiHalf (fun w => c * f w) z = (starRingEnd ℂ) c * xiHalf f z := by
  simp [xiHalf, fderiv_const_mul hf, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

theorem xiHalf_add (f g : ℂ → ℂ) (z : ℂ)
    (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) :
    xiHalf (fun w => f w + g w) z = xiHalf f z + xiHalf g z := by
  simp [xiHalf, fderiv_fun_add hf hg]
  ring

theorem xiHalf_sum {ι : Type*} (s : Finset ι) (f : ι → ℂ → ℂ) (z : ℂ)
    (hf : ∀ i ∈ s, DifferentiableAt ℝ (f i) z) :
    xiHalf (fun w => ∑ i ∈ s, f i w) z = ∑ i ∈ s, xiHalf (f i) z := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [xiHalf]
  | insert a s ha ih =>
    have h₁ := hf a (Finset.mem_insert_self a s)
    have h₂ (i) (hi : i ∈ s) := hf i (Finset.mem_insert_of_mem hi)
    simp only [Finset.sum_insert ha]
    rw [xiHalf_add _ _ _ h₁ (DifferentiableAt.fun_sum h₂), ih h₂]

theorem xiHalf_real_translate (f : ℂ → ℂ) (z : ℂ) (a : ℝ) :
    xiHalf (fun w => f (w + a)) z = xiHalf f (z + a) := by
  simp [xiHalf, fderiv_comp_add_right]

/-- Complex conjugation in ξ reverses the Fourier sector of a finite translation sum. -/
theorem xiHalf_project11 (r : ZMod 11) (f : ℂ → ℂ) (z : ℂ)
    (hf : ∀ j, DifferentiableAt ℝ f (z + (shift11 j : ℂ))) :
    xiHalf (project11 r f) z = project11 (-r) (xiHalf f) z := by
  have ht (j : ZMod 11) : DifferentiableAt ℝ (fun w : ℂ => f (w + (shift11 j : ℂ))) z :=
    (differentiableAt_comp_add_right _).2 (hf j)
  unfold project11
  rw [xiHalf_sum _ _ z (fun j _ => (ht j).const_mul _)]
  apply Finset.sum_congr rfl
  intro j _
  rw [xiHalf_const_mul _ _ _ (ht j), xiHalf_real_translate]
  have hc := (ZMod.stdAddChar (N := 11)).map_neg_eq_conj (-(r*j))
  simp only [neg_neg] at hc
  have h11 : (starRingEnd ℂ) 11 = 11 := map_ofNat _ _
  simp [map_div₀, ← hc, neg_mul, h11]

end MockThetaAnalytic
