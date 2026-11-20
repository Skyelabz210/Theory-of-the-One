import BoundaryObservation34
import QuantumRadialLimit
import BoundaryValues34
import FKTYTheta
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! Folsom–Ki–Truong Vu–Yang, Theorem 1.8, equation (1.13), specialized to
(a,b,c) = (1,2,0). The matrix sends the reflected cusp −1/34 to −1/10.
The analytic transformation law is an explicit input. Its finite endpoint
specializations, branch factor, level membership, and packet identities are checked. -/

noncomputable section

namespace MockThetaAnalytic

open Complex MeasureTheory Set KElimination.ResidueSeries KElimination.QuantumRadial
open scoped MatrixGroups Topology

/-- The matrix in Γ(24) used in FKTY Example 1, acting here on −1/34. -/
def transportMatrix34 : SL(2, ℤ) :=
  ⟨!![1, 0; 24, 1], by norm_num [Matrix.det_fin_two]⟩

theorem transportMatrix34_mem : transportMatrix34 ∈ CongruenceSubgroup.Gamma 24 := by
  apply CongruenceSubgroup.Gamma_mem.mpr
  decide +kernel

/-- Denominator in the fractional linear action at a rational cusp. -/
def cuspDenom (g : SL(2, ℤ)) (x : ℚ) : ℚ := (g 1 0 : ℚ) * x + (g 1 1 : ℚ)

def cuspAction (g : SL(2, ℤ)) (x : ℚ) : ℚ :=
  ((g 0 0 : ℚ) * x + (g 0 1 : ℚ)) / cuspDenom g x

theorem transportMatrix34_cusps :
    Even ((-1/34 : ℚ).den) ∧ Even ((-1/10 : ℚ).den) ∧
    cuspDenom transportMatrix34 (-1/34) = 5/17 ∧
    cuspAction transportMatrix34 (-1/34) = -1/10 := by
  exact ⟨⟨17, by decide +kernel⟩, ⟨5, by decide +kernel⟩, by decide +kernel, by decide +kernel⟩

/-- FKTY (3.13) for matrices in Γ(24) with positive lower-right entry δ.
Then δ ≡ 1 mod 4, εδ = 1, and both Kronecker symbols have positive odd
denominator, so they are Jacobi symbols. -/
def fktyMultiplier (g : SL(2, ℤ)) : ℂ :=
  ((jacobiSym 12 (g 1 1).natAbs * jacobiSym (2 * g 1 0) (g 1 1).natAbs : ℤ) : ℂ)

theorem transportMatrix34_multiplier : fktyMultiplier transportMatrix34 = 1 := by
  change ((jacobiSym 12 1 * jacobiSym 48 1 : ℤ) : ℂ) = 1
  simp [jacobiSym.one_right]

/-- The principal negative half power is positive real for this pair. -/
theorem transportMatrix34_weight :
    ((cuspDenom transportMatrix34 (-1/34) : ℚ) : ℂ) ^ (-1/2 : ℂ) =
      (Real.sqrt (17/5) : ℂ) := by
  rw [transportMatrix34_cusps.2.2.1]
  push_cast
  have hp := Complex.ofReal_cpow (by norm_num : (0 : ℝ) ≤ 5/17) (-1/2)
  push_cast at hp
  rw [← hp, Complex.ofReal_inj]
  rw [show (-1/2 : ℝ) = -(1/2) by ring, Real.rpow_neg (by norm_num),
    ← Real.sqrt_eq_rpow, ← Real.sqrt_inv]
  norm_num

/-- Vertical path from s to i∞, with du = i dt and the principal square root.
The integral is over the open ray, so all theta evaluations have positive height. -/
def fktyVerticalPeriod (theta : ℂ → ℂ) (s x : ℚ) : ℂ :=
  ∫ t : ℝ in Ioi 0, let u : ℂ := (s : ℂ) + (t : ℂ)*I
    I * theta u / ((u - (x : ℂ)) ^ (1/2 : ℂ))

/-- The positive-denominator portion of FKTY (1.13) needed here. The boundary
function is the paper's normalized φ₁,₂,₀, and the
period uses its bilateral theta series. Restricting to γ ≠ 0 permits a
finite starting cusp for the integral. -/
def FKTYWeightHalfLaw : Prop :=
  ∀ (g : SL(2, ℤ)), g ∈ CongruenceSubgroup.Gamma 24 → 0 < g 1 1 → g 1 0 ≠ 0 →
    ∀ (x : ℚ), Even x.den → 0 < cuspDenom g x →
      fktyPhi x - ((cuspDenom g x : ℂ) ^ (-1/2 : ℂ)) * (fktyMultiplier g)⁻¹ *
        fktyPhi (cuspAction g x) =
        fktyVerticalPeriod fktyTheta (-(g 1 1 : ℚ) / (g 1 0 : ℚ)) x

/-- At the two reflected cusps the published law yields the finite
compensated f boundary values with their separate e(x/24) phases. -/
theorem boundary34_transport10 (hFKTY : FKTYWeightHalfLaw) :
    (fktyScale * integerNome (-1/816)) * boundaryValue 17 (integerNome (1/34)) -
      (Real.sqrt (17/5) : ℂ) *
        ((fktyScale * integerNome (-1/240)) * boundaryValue 5 (integerNome (1/10))) =
      fktyVerticalPeriod fktyTheta (-1/24) (-1/34) := by
  obtain ⟨h34, _, hd, hx⟩ := transportMatrix34_cusps
  have h := hFKTY transportMatrix34 transportMatrix34_mem (by decide) (by decide)
    (-1/34) h34 (by rw [hd]; norm_num)
  rw [hx, transportMatrix34_weight, transportMatrix34_multiplier, inv_one, mul_one,
    fktyPhi_neg_one_div_34, fktyPhi_neg_one_div_10] at h
  exact h

/-- Solving the transformation for the physical order-34 value requires the
period and the order-10 value. The normalizing factor at order 34 is nonzero. -/
theorem boundary34_from_period_and_ten (hFKTY : FKTYWeightHalfLaw) :
    boundaryValue 17 (integerNome (1/34)) =
      (fktyVerticalPeriod fktyTheta (-1/24) (-1/34) +
        (Real.sqrt (17/5) : ℂ) *
          ((fktyScale * integerNome (-1/240)) * boundaryValue 5 (integerNome (1/10)))) /
        (fktyScale * integerNome (-1/816)) := by
  have hs : fktyScale ≠ 0 := by
    unfold fktyScale
    apply Complex.cpow_ne_zero_iff.mpr
    exact Or.inl (mul_ne_zero (by norm_num) I_ne_zero)
  apply (eq_div_iff (mul_ne_zero hs (Complex.exp_ne_zero _))).2
  rw [mul_comm]
  exact sub_eq_iff_eq_add.mp (boundary34_transport10 hFKTY)

/-- The theta integrand in this FKTY period is half the previously proved
ξ-image of the infinite mock theta completion at the scaled argument. -/
theorem fktyPeriod34_eq_completionPeriod :
    fktyVerticalPeriod fktyTheta (-1/24) (-1/34) =
      fktyVerticalPeriod (fun u => xiHalf mockCompletion (u/24) / 2) (-1/24) (-1/34) := by
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  dsimp only
  rw [fktyTheta_eq_xiHalf _ (by simpa using ht)]

/-- Packet evaluation at the two admitted periods recovers the FKTY period.
The root-of-unity arguments are computed from the rational cusps. -/
theorem boundary34_transport10_from_packets (hFKTY : FKTYWeightHalfLaw) :
    (fktyScale * integerNome (-1/816)) *
      ((-4) * sumBelow 510510 (fun r =>
        uPacket (integerNome (1/34)) 17 510510 r * integerNome (1/34)^r)) -
      (Real.sqrt (17/5) : ℂ) * ((fktyScale * integerNome (-1/240)) *
        ((-4) * sumBelow 30030 (fun r =>
          uPacket (integerNome (1/10)) 5 30030 r * integerNome (1/10)^r))) =
      fktyVerticalPeriod (fun u => xiHalf mockCompletion (u/24) / 2) (-1/24) (-1/34) := by
  have h34 : IsPrimitiveRoot (integerNome (1/34)) 34 := by
    simpa [integerNome, mul_one_div] using Complex.isPrimitiveRoot_exp 34 (by decide)
  have h10 : IsPrimitiveRoot (integerNome (1/10)) 10 := by
    simpa [integerNome, mul_one_div] using Complex.isPrimitiveRoot_exp 10 (by decide)
  rw [BoundaryObservation34.endpoint34_from_packets 17 _ h34 le_rfl,
    BoundaryObservation34.endpoint10_from_packets 5 _ h10 le_rfl,
    boundary34_transport10 hFKTY, fktyPeriod34_eq_completionPeriod]

/-- Along a radial approach to e(1/34), sufficiently long degree packets of the
original f have the transported compensated limit. The Taylor identification
and the FOR radial limit are the two inputs of the previous packet theorem.
At half-order 17 the compensating term is added. -/
theorem fPackets34_tendsto_order10_period (hFKTY : FKTYWeightHalfLaw)
    (r : ℕ → ℝ) (hr : ∀ j, 0 < r j ∧ r j < 1)
    (hrlim : Filter.Tendsto r Filter.atTop (𝓝[<] (1 : ℝ)))
    (hTaylor : ∀ t : ℝ, 0 < t → t < 1 → HasSum
      (fun d => complexFCoeff d * ((t : ℂ) * integerNome (1/34))^d)
      (radialF ((t : ℂ) * integerNome (1/34))))
    (hFOR : Filter.Tendsto (fun t : ℝ => radialF ((t : ℂ)*integerNome (1/34)) +
      radialB ((t : ℂ)*integerNome (1/34))) (𝓝[<] (1 : ℝ))
        (𝓝 (boundaryValue 17 (integerNome (1/34))))) :
    ∃ K : ℕ → ℕ, (∀ j, j ≤ K j) ∧ ∀ N : ℕ → ℕ, (∀ j, K j ≤ N j) →
      Filter.Tendsto (fun j => fPacketAtRadius (N j) 510510 (r j) (integerNome (1/34)) +
        radialB ((r j : ℂ) * integerNome (1/34))) Filter.atTop
        (𝓝 ((fktyVerticalPeriod fktyTheta (-1/24) (-1/34) +
          (Real.sqrt (17/5) : ℂ) *
            ((fktyScale * integerNome (-1/240)) * boundaryValue 5 (integerNome (1/10)))) /
          (fktyScale * integerNome (-1/816)))) := by
  have h34 : IsPrimitiveRoot (integerNome (1/34)) 34 := by
    simpa [integerNome, mul_one_div] using Complex.isPrimitiveRoot_exp 34 (by decide)
  rw [← boundary34_from_period_and_ten hFKTY]
  have hsign : (-1 : ℂ)^17 = -1 := by norm_num
  simpa only [hsign, neg_one_mul, sub_neg_eq_add] using
    for_limit_from_f_packets _ 17 510510 h34 (by decide) (by decide) r hr hrlim hTaylor
      (by simpa only [hsign, neg_one_mul, sub_neg_eq_add] using hFOR)

end MockThetaAnalytic
