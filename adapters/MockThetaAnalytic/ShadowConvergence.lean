import MockThetaShadow
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-! Absolute convergence and the eleven Fourier-degree packets of the integer-normalized
unary theta series for the third-order shadow. The summation index is the positive or zero
magnitude `m`, while the exponent of `u` is its square. -/

noncomputable section

namespace KElimination.ShadowConvergence

open MockThetaShadow

/-- The signed contribution of magnitude `m`, at Fourier degree `m²`. -/
def shadowTerm (u : ℂ) (m : ℕ) : ℂ := (shadowWeight m : ℂ) * u ^ (m ^ 2)

def shadowSeries (u : ℂ) : ℂ := ∑' m, shadowTerm u m

/-- An elementary absolute majorant on the closed unit disk. -/
theorem norm_shadowTerm_le (u : ℂ) (hu : ‖u‖ ≤ 1) (m : ℕ) :
    ‖shadowTerm u m‖ ≤ (m : ℝ) * ‖u‖ ^ m := by
  have hw : ((shadowWeight m).natAbs : ℝ) ≤ m := by exact_mod_cast shadowWeight_natAbs_le m
  have hm : m ≤ m ^ 2 := Nat.le_self_pow (by decide) m
  rw [shadowTerm, Complex.norm_mul, Complex.norm_pow, Complex.norm_intCast]
  rw [Nat.cast_natAbs, Int.cast_abs] at hw
  exact mul_le_mul hw (pow_le_pow_of_le_one (norm_nonneg u) hu hm) (by positivity) (by positivity)

/-- The series of absolute values is summable at each point of the open unit disk. -/
theorem norm_shadowTerm_summable (u : ℂ) (hu : ‖u‖ < 1) : Summable (fun m => ‖shadowTerm u m‖) := by
  have hgeom : Summable (fun m : ℕ => (m : ℝ) * ‖u‖ ^ m) := by
    simpa only [pow_one] using summable_pow_mul_geometric_of_norm_lt_one
      (r := ‖u‖) 1 (by simpa only [Real.norm_eq_abs, abs_norm] using hu)
  exact Summable.of_nonneg_of_le (fun m => norm_nonneg (shadowTerm u m)) (norm_shadowTerm_le u hu.le) hgeom

theorem shadowTerm_summable (u : ℂ) (hu : ‖u‖ < 1) : Summable (shadowTerm u) :=
  (norm_shadowTerm_summable u hu).of_norm

/-- The packet is selected by the exponent `m² mod 11`. -/
def degreeClass (m : ℕ) : Fin 11 := ⟨m ^ 2 % 11, Nat.mod_lt _ (by decide)⟩

def shadowDegreeBin (r : Fin 11) (u : ℂ) : ℂ :=
  ∑' m, if degreeClass m = r then shadowTerm u m else 0

theorem shadowDegreeBin_summable (r : Fin 11) (u : ℂ) (hu : ‖u‖ < 1) :
    Summable (fun m => if degreeClass m = r then shadowTerm u m else 0) := by
  exact ((shadowTerm_summable u hu).indicator {m | degreeClass m = r}).congr
    (fun m => by simp [Set.indicator_apply])

theorem shadowSeries_eq_sum_degreeBins (u : ℂ) (hu : ‖u‖ < 1) :
    shadowSeries u = ∑ r : Fin 11, shadowDegreeBin r u := by
  calc
    shadowSeries u = ∑' m, ∑ r : Fin 11, if degreeClass m = r then shadowTerm u m else 0 := by
      simp [shadowSeries]
    _ = ∑ r : Fin 11, shadowDegreeBin r u :=
      Summable.tsum_finsetSum (fun r _ => shadowDegreeBin_summable r u hu)

/-- The nome for Fourier exponents `m²/24`. -/
def shadowNome (τ : ℂ) : ℂ := Complex.exp ((((2 * Real.pi / 24 : ℝ) : ℂ) * τ) * Complex.I)

theorem norm_shadowNome_lt_one (τ : ℂ) (hτ : 0 < τ.im) : ‖shadowNome τ‖ < 1 := by
  rw [shadowNome, Complex.norm_exp, Real.exp_lt_one_iff, Complex.mul_I_re]
  simpa [Complex.mul_im] using neg_neg_of_pos (mul_pos (show 0 < 2 * Real.pi / 24 by positivity) hτ)

theorem upperHalfPlane_shadow (τ : ℂ) (hτ : 0 < τ.im) :
    Summable (fun m => ‖shadowTerm (shadowNome τ) m‖) ∧
      shadowSeries (shadowNome τ) = ∑ r : Fin 11, shadowDegreeBin r (shadowNome τ) :=
  ⟨norm_shadowTerm_summable _ (norm_shadowNome_lt_one τ hτ),
   shadowSeries_eq_sum_degreeBins _ (norm_shadowNome_lt_one τ hτ)⟩

end KElimination.ShadowConvergence
