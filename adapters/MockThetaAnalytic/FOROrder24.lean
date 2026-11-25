import FORPsiRadial
import ShadowEndpointValue24
import ThirdOrderTaylor

/-! The even half-order cusp closes by the complementary Watson identity.
The translated boundary packets use the primary and the dependent mod-eight
anchor of that same source. -/

noncomputable section
namespace MockThetaAnalytic

open Complex Filter KElimination.QuantumRadial KElimination.ResidueSeries
open KElimination.ProfiniteObservations KElimination.MockTheta
open scoped Topology

/-- The compensated disk series has the finite FOR limit at every primitive
24th root. The half-order is even, so its compensation is subtraction. -/
theorem radialF_sub_radialB_tendsto_order24 (ζ : ℂ) (hζ : IsPrimitiveRoot ζ 24) :
    Tendsto (fun t : ℝ => radialF ((t:ℂ)*ζ) - radialB ((t:ℂ)*ζ))
      (𝓝[<] 1) (𝓝 (boundaryValue 12 ζ)) := by
  have hv : -4 * watsonPsi ζ = boundaryValue 12 ζ := by
    rw [watsonPsi_eq_head24 ζ hζ]
    exact watsonPsi_head24 ζ hζ
  rw [← hv]
  apply ((watsonPsi_radial_limit24 ζ hζ).const_mul (-4)).congr'
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds (by norm_num : (0:ℝ) < 1))] with t ht ht0
  apply (watson_compensated_sub_identity _ _).symm
  simpa [norm_mul, hζ.norm'_eq_one (by decide), abs_of_pos (show 0 < t from ht0)] using (show t < 1 from ht)

namespace Order24Source

/-- Four distinguishable winding classes are necessary and sufficient. -/
theorem order24_quotient_requirement (r : ℤ) (H : ℕ) :
    KElimination.ExactObservation.FiberConstant (quotientObservation H)
      (affineTarget selectedPrimary 24 r) ↔ 4 ∣ H := by
  rw [target_constant_on_quotient_fibers_iff _ _ _ _ (by decide : 0 < (24:ℕ))]
  rfl

theorem anchor_resolutions :
    KElimination.CoupledAnchors.resolution selectedPrimary [8] = 4 ∧
    KElimination.CoupledAnchors.resolution selectedPrimary [4] = 2 ∧
    selectedPrimary * KElimination.CoupledAnchors.resolution selectedPrimary [8] = 120120 := by
  decide +kernel

theorem least_order24_packet_period (L : ℕ) :
    (selectedPrimary ∣ L ∧ 24 ∣ L) ↔ 120120 ∣ L := by
  rw [← Nat.lcm_dvd_iff, show Nat.lcm selectedPrimary 24 = 120120 by decide]

/-- Eight is the least positive single anchor modulus for the order-24
target in every chart. The already observed parity is the overlap. -/
theorem smaller_anchor_loses_target (A : ℕ) (hA : 0 < A) (h : A < 8) (r : ℤ) :
    ¬ KElimination.ExactObservation.FiberConstant (anchorObservation selectedPrimary [A] r)
      (affineTarget selectedPrimary 24 r) := by
  rw [combined_target_fiber_constant_iff _ _ _ _ (by decide : 0 < (24:ℕ))
    (by simpa using hA), show reducedTargetPeriod selectedPrimary 24 = 4 by decide]
  have hf : ∀ a : Fin 8, 0 < a.val →
      ¬4 ∣ KElimination.CoupledAnchors.resolution selectedPrimary [a.val] := by decide +kernel
  exact hf ⟨A,h⟩ hA

structure Lanes where
  primary : ℤ
  mod8 : ℤ

def observe (X : ℤ) : Lanes := ⟨X % 30030, X % 8⟩

def translate (a : Lanes) (d : ℤ) : Lanes :=
  ⟨(a.primary+d) % 30030, (a.mod8+d) % 8⟩

theorem translate_observe (X d : ℤ) : translate (observe X) d = observe (X+d) := by
  simp [translate, observe, Int.emod_add_emod]

/-- Cancel the common parity before using the inverse of 15015 modulo four. -/
def winding4 (a : Lanes) : ℤ := (3 * ((a.mod8-a.primary)/2)) % 4

def exponent24 (a : Lanes) : ℤ := (a.primary % 24 + 6*winding4 a) % 24

theorem source_winding4 (X : ℤ) : winding4 (observe X) = (X/30030) % 4 := by
  unfold winding4 observe
  dsimp
  omega

theorem source_exponent24 (X : ℤ) : exponent24 (observe X) = X % 24 := by
  rw [exponent24, source_winding4]
  simp only [observe]
  omega

theorem source_phase24 (X : ℤ) (ζ : ℂ) (hζ : IsPrimitiveRoot ζ 24) :
    ζ^(exponent24 (observe X)) = ζ^X := by
  rw [source_exponent24]
  exact Order34Source.zpow_residue X (by decide) hζ

theorem source_phase_shift (X d : ℤ) (ζ : ℂ) (hζ : IsPrimitiveRoot ζ 24) :
    ζ^(exponent24 (translate (observe X) d)) = ζ^X * ζ^d := by
  rw [translate_observe, source_phase24 _ ζ hζ, zpow_add₀ (hζ.ne_zero (by decide))]

/-- Zero and 60060 agree mod the primary and mod four, but differ by a sign
at every primitive 24th root. -/
theorem no_mod4_phase24 (ζ : ℂ) (hζ : IsPrimitiveRoot ζ 24) :
    ¬ ∃ f : ℤ → ℤ → ℂ, ∀ X : ℤ, f (X % 30030) (X % 4) = ζ^X := by
  rintro ⟨f,h⟩
  have hzero : f 0 0 = 1 := by simpa using h 0
  have hother := (h 60060).trans (Order34Source.zpow_residue 60060 (by decide) hζ).symm
  rw [show (60060:ℤ)%30030 = 0 by norm_num, show (60060:ℤ)%4 = 0 by norm_num,
    show (60060:ℤ)%((24:ℕ):ℤ) = 12 by norm_num, hzero] at hother
  have hhalf : ζ^(12:ℤ) = -1 := by
    change ζ^((12:ℕ):ℤ) = -1
    rw [zpow_natCast, order24_half_power ζ hζ]
  exact (by norm_num : (1:ℂ) ≠ -1) (hother.trans hhalf)

private theorem translated_sum24 (X : ℤ) (ζ : ℂ) (hζ : IsPrimitiveRoot ζ 24) (c : ℕ → ℂ) :
    sumBelow 120120 (fun d => c d * ζ^(exponent24 (translate (observe X) d))) =
      ζ^X * sumBelow 120120 (fun d => c d * ζ^d) := by
  rw [← sumBelow_mul_left]
  apply sumBelow_congr
  intro d _
  rw [source_phase_shift X d ζ hζ, zpow_natCast]
  ring

/-- Translate the outer exponents lane by lane before applying the character. -/
def translatedPacket24 (ζ : ℂ) (N : ℕ) (a : Lanes) : ℂ :=
  (-4) * sumBelow 120120 (fun d => uPacket ζ N 120120 d * ζ^(exponent24 (translate a d)))

theorem translatedPacket24_eq_boundary (X : ℤ) (ζ : ℂ) (hζ : IsPrimitiveRoot ζ 24)
    (N : ℕ) (hN : 12 ≤ N) :
    translatedPacket24 ζ N (observe X) = ζ^X * boundaryValue 12 ζ := by
  have he := boundaryValue_from_packets N 12 120120 ζ (by decide) (order24_half_power ζ hζ)
    hN (by decide) (by decide)
  rw [translatedPacket24, translated_sum24 X ζ hζ, ← he]
  ring

/-- Apply the same translated character to the actual Taylor coefficient packets. -/
def translatedFPacketAtRadius24 (N : ℕ) (t : ℝ) (ζ : ℂ) (a : Lanes) : ℂ :=
  sumBelow 120120 (fun d => weightedPacket complexFCoeff (fun n => (t:ℂ)^n) N 120120 d *
    ζ^(exponent24 (translate a d)))

theorem translatedFPacketAtRadius24_eq (X : ℤ) (N : ℕ) (t : ℝ) (ζ : ℂ)
    (hζ : IsPrimitiveRoot ζ 24) :
    translatedFPacketAtRadius24 N t ζ (observe X) = ζ^X * fPacketAtRadius N 120120 t ζ :=
  translated_sum24 X ζ hζ _

def normalizedPacket24 (N : ℕ) (a : Lanes) : ℂ :=
  let ζ := integerNome (1/24)
  (fktyScale * integerNome (-1/576)) * (translatedPacket24 ζ N a / ζ^(exponent24 a))

theorem positive_order24_root : IsPrimitiveRoot (integerNome (1/24)) 24 := by
  simpa [integerNome, mul_one_div] using Complex.isPrimitiveRoot_exp 24 (by decide)

theorem normalizedPacket24_eq_cusp (X : ℤ) (N : ℕ) (hN : 12 ≤ N) :
    normalizedPacket24 N (observe X) = fktyPhi (-1/24) := by
  let ζ := integerNome (1/24)
  have hζ : IsPrimitiveRoot ζ 24 := positive_order24_root
  change (fktyScale*integerNome (-1/576)) *
    (translatedPacket24 ζ N (observe X) / ζ^(exponent24 (observe X))) = _
  rw [translatedPacket24_eq_boundary X ζ hζ N hN, source_phase24 X ζ hζ,
    mul_div_cancel_left₀ _ (zpow_ne_zero X (hζ.ne_zero (by decide))), fktyPhi_neg_one_div_24]

theorem normalizedPacket24_eq_averaged (X : ℤ) (N D : ℕ) (hN : 12 ≤ N)
    (hD : 144 ≤ ShadowPeriod.modeCount D) :
    normalizedPacket24 N (observe X) =
      ShadowEndpoint.averagedPeriod (ShadowReadings.observe D mockCoeff) (fun _ => 1) 144 (-1/24) := by
  rw [normalizedPacket24_eq_cusp X N hN, ShadowEndpoint.averagedFullPeriod_eq_fktyPhi24 D hD]

end Order24Source

/-- The actual Taylor packets converge at any primitive order-24 root
along every radial sequence with a sufficiently large diagonal cutoff. -/
theorem fPackets24_tendsto_boundary (ζ : ℂ) (hζ : IsPrimitiveRoot ζ 24)
    (r : ℕ → ℝ) (hr : ∀ j, 0 < r j ∧ r j < 1) (hl : Tendsto r atTop (𝓝[<] (1:ℝ))) :
    ∃ K : ℕ → ℕ, (∀ j, j ≤ K j) ∧ ∀ N : ℕ → ℕ, (∀ j, K j ≤ N j) →
      Tendsto (fun j => fPacketAtRadius (N j) 120120 (r j) ζ - radialB ((r j:ℂ)*ζ))
        atTop (𝓝 (boundaryValue 12 ζ)) := by
  have h := for_limit_from_f_packets_of_radial_law ζ 12 120120 hζ (by decide) (by decide) r hr hl
  have hs : (-1:ℂ)^12 = 1 := by norm_num
  simpa only [hs, one_mul] using h (by
    simpa only [hs, one_mul] using radialF_sub_radialB_tendsto_order24 ζ hζ)

/-- At the positive-angle root, the lane-normalized Taylor packets from
any signed source converge to the value of the S6 shadow prefix. -/
theorem normalized_fPackets24_tendsto_averaged (X : ℤ) (D : ℕ)
    (hD : 144 ≤ ShadowPeriod.modeCount D)
    (r : ℕ → ℝ) (hr : ∀ j, 0 < r j ∧ r j < 1) (hl : Tendsto r atTop (𝓝[<] (1:ℝ))) :
    let ζ := integerNome (1/24)
    let a := Order24Source.observe X
    ∃ K : ℕ → ℕ, (∀ j, j ≤ K j) ∧ ∀ N : ℕ → ℕ, (∀ j, K j ≤ N j) →
      Tendsto (fun j => (fktyScale*integerNome (-1/576)) *
        (Order24Source.translatedFPacketAtRadius24 (N j) (r j) ζ a / ζ^(Order24Source.exponent24 a) -
          radialB ((r j:ℂ)*ζ))) atTop
        (𝓝 (ShadowEndpoint.averagedPeriod (ShadowReadings.observe D mockCoeff) (fun _ => 1) 144 (-1/24))) := by
  dsimp only
  rw [ShadowEndpoint.averagedFullPeriod_eq_fktyPhi24 D hD, fktyPhi_neg_one_div_24]
  have hζ := Order24Source.positive_order24_root
  obtain ⟨K,hK,hlim⟩ := fPackets24_tendsto_boundary _ hζ r hr hl
  refine ⟨K,hK,fun N hN => ((hlim N hN).const_mul _).congr' (Eventually.of_forall ?_)⟩
  intro j
  dsimp only
  rw [Order24Source.translatedFPacketAtRadius24_eq X _ _ _ hζ,
    Order24Source.source_phase24 X _ hζ, mul_div_cancel_left₀ _ (zpow_ne_zero X (hζ.ne_zero (by decide)))]

end MockThetaAnalytic
