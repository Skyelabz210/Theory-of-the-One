import FOROrder34
import FORPsiRadial
import FORWatsonQuotient

/-! At every primitive even root, the compensated radial series and the
diagonal Taylor packets converge to the finite FOR polynomial. At the
reflected rational cusp this also gives the normalized FKTY value. -/

noncomputable section
namespace MockThetaAnalytic

open Complex Filter KElimination.QuantumRadial KElimination.ProfiniteObservations
open scoped Topology

theorem radialF_compensated_tendsto_watson {ζ : ℂ} {k : ℕ} (hk : 0 < k)
    (hζ : IsPrimitiveRoot ζ (2*k)) :
    Tendsto (fun t : ℝ => radialF ((t:ℂ)*ζ) - (-1:ℂ)^k*radialB ((t:ℂ)*ζ))
      (𝓝[<] 1) (𝓝 (watsonFiniteBoundary k ζ)) := by
  have hd : ∀ᶠ t : ℝ in 𝓝[<] 1, ‖(t:ℂ)*ζ‖ < 1 := by
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds (by norm_num : (0:ℝ)<1))]
      with t ht hpos
    simpa [norm_mul, hζ.norm'_eq_one (by omega), abs_of_pos (show 0 < t from hpos)] using (show t < 1 from ht)
  by_cases he : Even k
  · have hval : (-4)*watsonPsi ζ = watsonFiniteBoundary k ζ := by
      rw [watsonPsi_eq_head hk hζ he, watsonFiniteBoundary, if_pos he]
      change -4 * (2 * (∑ n ∈ Finset.range k, watsonTerm 1 ζ n) - 1) = _
      ring
    rw [← hval, he.neg_one_pow]
    apply ((watsonPsi_radial_limit_of_even hk hζ he).const_mul (-4)).congr'
    filter_upwards [hd] with t ht
    simpa only [one_mul] using (watson_compensated_sub_identity _ ht).symm
  · have ho := Nat.not_even_iff_odd.mp he
    have hval : 2*watsonPhi ζ = watsonFiniteBoundary k ζ := by
      rw [watsonPhi_eq_two_mul_head hk hζ ho, watsonFiniteBoundary, if_neg he]
      change 2 * (2 * ∑ n ∈ Finset.range k, watsonTerm 2 ζ n) = _
      ring
    rw [← hval, ho.neg_one_pow]
    apply ((watsonPhi_radial_limit_of_odd hk hζ ho).const_mul 2).congr'
    filter_upwards [hd] with t ht
    simpa only [neg_one_mul, sub_neg_eq_add] using (watson_compensated_identity _ ht).symm

theorem radialF_compensated_tendsto_boundary_of_certificate {ζ : ℂ} {k : ℕ} (hk : 0 < k)
    (hζ : IsPrimitiveRoot ζ (2*k)) (hcert : watsonBoundaryCertificate k = true) :
    Tendsto (fun t : ℝ => radialF ((t:ℂ)*ζ) - (-1:ℂ)^k*radialB ((t:ℂ)*ζ))
      (𝓝[<] 1) (𝓝 (boundaryValue k ζ)) := by
  rw [← watsonFiniteBoundary_eq_of_certificate hk hζ hcert]
  exact radialF_compensated_tendsto_watson hk hζ

/-- The compensated radial limit at every primitive even root. -/
theorem radialF_compensated_tendsto_boundary {ζ : ℂ} {k : ℕ} (hk : 0 < k)
    (hζ : IsPrimitiveRoot ζ (2*k)) :
    Tendsto (fun t : ℝ => radialF ((t:ℂ)*ζ) - (-1:ℂ)^k*radialB ((t:ℂ)*ζ))
      (𝓝[<] 1) (𝓝 (boundaryValue k ζ)) := by
  rw [← watsonFiniteBoundary_eq_boundaryValue hk hζ]
  exact radialF_compensated_tendsto_watson hk hζ

/-- The same radial formula holds for any half-period, including multiples
of the primitive half-order. -/
theorem radialF_compensated_tendsto_boundary_of_half_power {ζ : ℂ} {k : ℕ} (hζ : ζ^k = -1) :
    Tendsto (fun t : ℝ => radialF ((t:ℂ)*ζ) - (-1:ℂ)^k*radialB ((t:ℂ)*ζ))
      (𝓝[<] 1) (𝓝 (boundaryValue k ζ)) := by
  obtain ⟨h,m,hh,hm,hkm,hprim⟩ := even_root_order_of_half_power hζ
  have hle : h ≤ k := by simpa [hkm] using Nat.mul_le_mul_right h hm.pos
  have hsign : (-1:ℂ)^k = (-1:ℂ)^h := by rw [hkm, pow_mul, hm.neg_one_pow]
  have hvalue : boundaryValue k ζ = boundaryValue h ζ :=
    boundaryValue_stable k h ζ hh (primitive_even_half_power hh hprim) hle
  rw [hsign, hvalue]
  exact radialF_compensated_tendsto_boundary hh hprim

/-- A primitive character distinguishes exactly the residue classes of its order. -/
theorem primitive_phase_eq_iff_residue {ζ : ℂ} {b : ℕ} (hb : 0 < b)
    (hζ : IsPrimitiveRoot ζ b) (X Y : ℤ) :
    ζ^X = ζ^Y ↔ X % (b:ℤ) = Y % (b:ℤ) := by
  rw [Int.emod_eq_emod_iff_emod_sub_eq_zero, ← Int.dvd_iff_emod_eq_zero,
    ← hζ.zpow_eq_one_iff_dvd, zpow_sub₀ (hζ.ne_zero hb.ne'),
    div_eq_one_iff_eq (zpow_ne_zero Y (hζ.ne_zero hb.ne'))]

/-- The primitive character has the same exact observation requirement as
the target residue on every signed quotient chart. -/
theorem coupled_phase_fiber_constant_iff {ζ : ℂ} {b : ℕ} (hb : 0 < b)
    (hζ : IsPrimitiveRoot ζ b) (M : ℕ) (anchors : List ℕ) (r : ℤ)
    (hpos : ∀ a ∈ anchors, 0 < a) :
    KElimination.ExactObservation.FiberConstant (anchorObservation M anchors r)
        (fun K : ℤ => ζ^(r+(M:ℤ)*K)) ↔
      reducedTargetPeriod M b ∣ KElimination.CoupledAnchors.resolution M anchors := by
  rw [← combined_target_fiber_constant_iff M b anchors r hb hpos]
  simp only [KElimination.ExactObservation.FiberConstant, primitive_phase_eq_iff_residue hb hζ, affineTarget]

/-- The order-22 phase is lost when the prime 11 is omitted from S6 and
is recovered when the same source supplies that anchor. -/
theorem order22_shadow_anchor (ζ : ℂ) (hζ : IsPrimitiveRoot ζ 22) (r : ℤ) :
    KElimination.ExactObservation.FiberConstant (anchorObservation 2730 [11] r)
        (fun K : ℤ => ζ^(r+((2730:ℕ):ℤ)*K)) ∧
      ¬KElimination.ExactObservation.FiberConstant (anchorObservation 2730 [] r)
        (fun K : ℤ => ζ^(r+((2730:ℕ):ℤ)*K)) := by
  rw [coupled_phase_fiber_constant_iff (by decide) hζ 2730 [11] r (by simp),
    coupled_phase_fiber_constant_iff (by decide) hζ 2730 [] r (by simp)]
  decide +kernel

/-- Every admitted packet period gives the compensated diagonal Taylor limit. -/
theorem fPackets_tendsto_boundary_of_certificate {ζ : ℂ} {k L : ℕ} (hk : 0 < k)
    (hζ : IsPrimitiveRoot ζ (2*k)) (hcert : watsonBoundaryCertificate k = true)
    (hL : 0 < L) (hperiod : 2*k ∣ L) (r : ℕ → ℝ) (hr : ∀ j, 0 < r j ∧ r j < 1)
    (hlim : Tendsto r atTop (𝓝[<] (1:ℝ))) :
    ∃ K : ℕ → ℕ, (∀ j, j ≤ K j) ∧ ∀ N : ℕ → ℕ, (∀ j, K j ≤ N j) →
      Tendsto (fun j => fPacketAtRadius (N j) L (r j) ζ - (-1:ℂ)^k*radialB ((r j:ℂ)*ζ))
        atTop (𝓝 (boundaryValue k ζ)) :=
  for_limit_from_f_packets_of_radial_law ζ k L hζ hL hperiod r hr hlim
    (radialF_compensated_tendsto_boundary_of_certificate hk hζ hcert)

/-- A primary and coupled anchors giving enough quotient resolution also give
a period for the actual compensated Taylor packets. -/
theorem fPackets_tendsto_boundary_from_anchors {ζ : ℂ} {k M : ℕ} (hk : 0 < k)
    (hζ : IsPrimitiveRoot ζ (2*k)) (hcert : watsonBoundaryCertificate k = true)
    (hM : 0 < M) (anchors : List ℕ) (hpos : ∀ a ∈ anchors, 0 < a)
    (hresolution : reducedTargetPeriod M (2*k) ∣ KElimination.CoupledAnchors.resolution M anchors)
    (r : ℕ → ℝ) (hr : ∀ j, 0 < r j ∧ r j < 1) (hlim : Tendsto r atTop (𝓝[<] (1:ℝ))) :
    let L := M*KElimination.CoupledAnchors.resolution M anchors
    ∃ K : ℕ → ℕ, (∀ j, j ≤ K j) ∧ ∀ N : ℕ → ℕ, (∀ j, K j ≤ N j) →
      Tendsto (fun j => fPacketAtRadius (N j) L (r j) ζ - (-1:ℂ)^k*radialB ((r j:ℂ)*ζ))
        atTop (𝓝 (boundaryValue k ζ)) :=
  fPackets_tendsto_boundary_of_certificate hk hζ hcert
    (Nat.mul_pos hM (KElimination.CoupledAnchors.resolution_pos M anchors hpos))
    (target_divides_source_period M (2*k) _ (by omega) hresolution) r hr hlim

/-- Every positive packet period divisible by the root order supports the
actual compensated Taylor limit. -/
theorem fPackets_tendsto_boundary {ζ : ℂ} {k L : ℕ} (hk : 0 < k)
    (hζ : IsPrimitiveRoot ζ (2*k)) (hL : 0 < L) (hperiod : 2*k ∣ L)
    (r : ℕ → ℝ) (hr : ∀ j, 0 < r j ∧ r j < 1) (hlim : Tendsto r atTop (𝓝[<] (1:ℝ))) :
    ∃ K : ℕ → ℕ, (∀ j, j ≤ K j) ∧ ∀ N : ℕ → ℕ, (∀ j, K j ≤ N j) →
      Tendsto (fun j => fPacketAtRadius (N j) L (r j) ζ - (-1:ℂ)^k*radialB ((r j:ℂ)*ζ))
        atTop (𝓝 (boundaryValue k ζ)) :=
  for_limit_from_f_packets_of_radial_law ζ k L hζ hL hperiod r hr hlim
    (radialF_compensated_tendsto_boundary hk hζ)

/-- Enough coupled-anchor resolution supplies the period for compensated
Taylor packets at any primitive even root. -/
theorem fPackets_tendsto_boundary_from_coupled_anchors {ζ : ℂ} {k M : ℕ} (hk : 0 < k)
    (hζ : IsPrimitiveRoot ζ (2*k)) (hM : 0 < M) (anchors : List ℕ)
    (hpos : ∀ a ∈ anchors, 0 < a)
    (hresolution : reducedTargetPeriod M (2*k) ∣ KElimination.CoupledAnchors.resolution M anchors)
    (r : ℕ → ℝ) (hr : ∀ j, 0 < r j ∧ r j < 1) (hlim : Tendsto r atTop (𝓝[<] (1:ℝ))) :
    let L := M*KElimination.CoupledAnchors.resolution M anchors
    ∃ K : ℕ → ℕ, (∀ j, j ≤ K j) ∧ ∀ N : ℕ → ℕ, (∀ j, K j ≤ N j) →
      Tendsto (fun j => fPacketAtRadius (N j) L (r j) ζ - (-1:ℂ)^k*radialB ((r j:ℂ)*ζ))
        atTop (𝓝 (boundaryValue k ζ)) :=
  fPackets_tendsto_boundary hk hζ
    (Nat.mul_pos hM (KElimination.CoupledAnchors.resolution_pos M anchors hpos))
    (target_divides_source_period M (2*k) _ (by omega) hresolution) r hr hlim

/-- With the FKTY phase and scale, the compensated Taylor packets tend to
the strange value at any rational cusp with even reduced denominator. -/
theorem normalized_fPackets_tendsto_fkty (x : ℚ) {k L : ℕ} (hden : x.den = 2*k)
    (hL : 0 < L) (hperiod : 2*k ∣ L) (r : ℕ → ℝ) (hr : ∀ j, 0 < r j ∧ r j < 1)
    (hlim : Tendsto r atTop (𝓝[<] (1:ℝ))) :
    let ζ := integerNome (-(x:ℂ))
    ∃ K : ℕ → ℕ, (∀ j, j ≤ K j) ∧ ∀ N : ℕ → ℕ, (∀ j, K j ≤ N j) →
      Tendsto (fun j => (fktyScale*integerNome ((x:ℂ)/24)) *
        (fPacketAtRadius (N j) L (r j) ζ - (-1:ℂ)^k*radialB ((r j:ℂ)*ζ)))
        atTop (𝓝 (fktyPhi x)) := by
  have hk : 0 < k := by have := x.den_pos; omega
  have hζ : IsPrimitiveRoot (integerNome (-(x:ℂ))) (2*k) := by
    simpa only [Rat.cast_neg, Rat.neg_den, hden, integerNome] using Complex.isPrimitiveRoot_exp_rat (-x)
  obtain ⟨K,hK,h⟩ := fPackets_tendsto_boundary hk hζ hL hperiod r hr hlim
  refine ⟨K,hK,fun N hN => ?_⟩
  rw [fktyPhi_reflected_boundary x hden]
  exact (h N hN).const_mul _

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
/-- The kernel checks the finite identities for every even order through 34. -/
theorem watsonBoundaryCertificate_through_seventeen (k : ℕ) (hk : 0 < k) (h : k ≤ 17) :
    watsonBoundaryCertificate k = true := by
  interval_cases k <;> decide +kernel

theorem radialF_compensated_tendsto_boundary_through_order34 {ζ : ℂ} {k : ℕ} (hk : 0 < k)
    (h : k ≤ 17) (hζ : IsPrimitiveRoot ζ (2*k)) :
    Tendsto (fun t : ℝ => radialF ((t:ℂ)*ζ) - (-1:ℂ)^k*radialB ((t:ℂ)*ζ))
      (𝓝[<] 1) (𝓝 (boundaryValue k ζ)) :=
  radialF_compensated_tendsto_boundary_of_certificate hk hζ
    (watsonBoundaryCertificate_through_seventeen k hk h)

theorem fPackets_tendsto_boundary_through_order34 {ζ : ℂ} {k L : ℕ} (hk : 0 < k)
    (h : k ≤ 17) (hζ : IsPrimitiveRoot ζ (2*k)) (hL : 0 < L) (hperiod : 2*k ∣ L)
    (r : ℕ → ℝ) (hr : ∀ j, 0 < r j ∧ r j < 1) (hlim : Tendsto r atTop (𝓝[<] (1:ℝ))) :
    ∃ K : ℕ → ℕ, (∀ j, j ≤ K j) ∧ ∀ N : ℕ → ℕ, (∀ j, K j ≤ N j) →
      Tendsto (fun j => fPacketAtRadius (N j) L (r j) ζ - (-1:ℂ)^k*radialB ((r j:ℂ)*ζ))
        atTop (𝓝 (boundaryValue k ζ)) :=
  fPackets_tendsto_boundary_of_certificate hk hζ (watsonBoundaryCertificate_through_seventeen k hk h)
    hL hperiod r hr hlim

end MockThetaAnalytic
