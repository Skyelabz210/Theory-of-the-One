import FORGaussLimit
import FORRankProduct
import FORPhiProduct
import Order34QuantumPackets

/-! The compensated radial limit of the actual third-order f at primitive
34th roots, and its consequence for the CRAM packets and the FKTY period. -/

noncomputable section
namespace MockThetaAnalytic
open Complex Filter KElimination.QuantumRadial
open scoped Topology

/-- Watson's identity between the hypergeometric f, its compensating product,
and twice the third-order φ at the negative nome. -/
theorem watson_compensated_identity (q : ℂ) (hq : ‖q‖ < 1) :
    radialF q + radialB q = 2 * watsonPhi q := by
  have hf := radialPlus_mul_radialF q hq
  have hb : radialPlusProduct q * radialB q = 2 * watsonThetaHalf q - 1 :=
    radialPlus_mul_radialB_eq_thetaHalf q hq
  have hphi := (radialPlus_mul_watsonPhi hq).trans (watson_weighted_phi_eq_theta_add_leastOdd hq)
  apply mul_left_cancel₀ (radialPochhammers_ne_zero hq).2
  linear_combination hf + hb - 2 * hphi

/-- The finite FOR boundary is the actual radial limit for every primitive
34th root. The plus sign comes from the odd half-order 17. -/
theorem radialF_add_radialB_tendsto_order34 (ζ : ℂ) (hζ : IsPrimitiveRoot ζ 34) :
    Tendsto (fun t : ℝ => radialF ((t : ℂ)*ζ) + radialB ((t : ℂ)*ζ))
      (𝓝[<] 1) (𝓝 (boundaryValue 17 ζ)) := by
  have he : 2 * watsonPhi ζ = boundaryValue 17 ζ := by
    rw [watsonPhi_eq_two_mul_sum ζ hζ, ← mul_assoc]
    norm_num
    exact watsonPhi_head34 ζ hζ
  rw [← he]
  apply ((watsonPhi_radial_limit ζ hζ).const_mul 2).congr'
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds (by norm_num : (0:ℝ) < 1))] with t ht hpos
  apply (watson_compensated_identity _ _).symm
  simpa [norm_mul, hζ.norm'_eq_one (by decide), abs_of_pos (show 0 < t from hpos)] using (show t < 1 from ht)

/-- For the positive-angle order-34 root, compensated coefficient packets
converge to the value obtained from the order-10 endpoint and the shadow period. -/
theorem fPackets34_tendsto_order10_period_unconditional
    (r : ℕ → ℝ) (hr : ∀ j, 0 < r j ∧ r j < 1)
    (hrlim : Tendsto r atTop (𝓝[<] (1 : ℝ))) :
    ∃ K : ℕ → ℕ, (∀ j, j ≤ K j) ∧ ∀ N : ℕ → ℕ, (∀ j, K j ≤ N j) →
      Tendsto (fun j => fPacketAtRadius (N j) 510510 (r j) (integerNome (1/34)) +
        radialB ((r j : ℂ) * integerNome (1/34))) atTop
        (𝓝 ((fktyVerticalPeriod fktyTheta (-1/24) (-1/34) +
          (Real.sqrt (17/5) : ℂ) *
            ((fktyScale * integerNome (-1/240)) * boundaryValue 5 (integerNome (1/10)))) /
          (fktyScale * integerNome (-1/816)))) := by
  apply fPackets34_tendsto_order10_period_of_FOR r hr hrlim
  apply radialF_add_radialB_tendsto_order34
  simpa [integerNome, mul_one_div] using Complex.isPrimitiveRoot_exp 34 (by decide)

end MockThetaAnalytic
