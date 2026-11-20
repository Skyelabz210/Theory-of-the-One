import IntegerSpecialization
import QuantumRadial
import Mathlib.Algebra.Ring.GrindInstances
import Mathlib.Analysis.Complex.Basic
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-! Target admission for the orders 10 and 34 of the cusps −1/10 and −1/34.
The primary is the six-factor value already defined in ProfiniteObservations.
The integers r and k in the affine description are semantic variables. The
target-lane calculation uses a residue of the base point and a bound reading
of the quotient. The endpoint theorems consume the full finite packets. -/

namespace MockThetaAnalytic.BoundaryObservation34

open KElimination.ProfiniteObservations KElimination.IntegerSpecialization
open KElimination.CoupledAnchors KElimination.QuantumRadial KElimination.ResidueSeries

theorem reduced_periods :
    reducedTargetPeriod selectedPrimary 10 = 1 ∧
    reducedTargetPeriod selectedPrimary 34 = 17 := by decide

/-- Every signed lift of one primary remainder gives the same order-ten reading. -/
theorem target10_primary (r k : ℤ) : affineTarget selectedPrimary 10 r k = r % 10 := by
  unfold affineTarget selectedPrimary
  omega

/-- At a fixed base point the order-34 target detects exactly the quotient class modulo 17. -/
theorem target34_same_iff (r k j : ℤ) :
    affineTarget selectedPrimary 34 r k = affineTarget selectedPrimary 34 r j ↔
      quotientObservation 17 k = quotientObservation 17 j := by
  unfold affineTarget selectedPrimary quotientObservation
  omega

/-- The universal query can be answered on the image of an admitted quotient
observation precisely when its modulus is a multiple of 17. -/
theorem target34_recoverable_iff (r : ℤ) (H : ℕ) :
    (∃ answer : KElimination.ExactObservation.Observed (quotientObservation H) → ℤ,
      ∀ k, answer (KElimination.ExactObservation.reading (quotientObservation H) k) =
        affineTarget selectedPrimary 34 r k) ↔ 17 ∣ H := by
  rw [target_recoverable_iff selectedPrimary 34 H r (by decide), reduced_periods.2]

/-- The primary remainder alone cannot distinguish the sources r and r+30030
although their target residues differ, at every base point. -/
theorem primary_only_witness (r : ℤ) :
    r % 30030 = (r + 30030) % 30030 ∧ r % 34 ≠ (r + 30030) % 34 := by omega

theorem order34_outside_primary_powers (n : ℕ) : ¬ 34 ∣ selectedPrimary ^ n := by
  intro h
  exact (show ¬ 17 ∣ selectedPrimary by decide)
    ((show Nat.Prime 17 by decide).dvd_of_dvd_pow (dvd_trans (by decide : 17 ∣ 34) h))

/-- The target-lane projection only requires the remainder lane and the
quotient class. The public coefficient is 30030 mod 34 = 8. -/
theorem target34_projection (r k : ℤ) :
    (r % 34 + 8 * quotientObservation 17 k) % 34 = affineTarget selectedPrimary 34 r k := by
  unfold quotientObservation affineTarget selectedPrimary
  omega

/-- The same formula in the canonical signed Euclidean decomposition of X. -/
theorem target34_signed_euclidean (X : ℤ) :
    ((X % 30030) % 34 + 8 * ((X / 30030) % 17)) % 34 = X % 34 := by
  change ((X % 30030) % 34 + 8 * quotientObservation 17 (X / 30030)) % 34 = X % 34
  rw [target34_projection]
  change (X % 30030 + 30030 * (X / 30030)) % 34 = X % 34
  rw [mul_comm (30030 : ℤ), Int.emod_add_ediv_mul]

/-- A source-bound seventeenth lane and a base-point chart determine k mod 17.
The inverse of 30030 in that lane is 15. -/
theorem quotient_from_anchor17 (X r k chart s : ℤ)
    (hX : X = r + 30030 * k) (hc : chart = r % 17) (hs : s = X % 17) :
    query chart s 17 15 = quotientObservation 17 k :=
  query_chart_of_decomposition X r chart s 30030 17 15 k hX hc hs (by decide)

/-- Execute the existing query and target-lane primitives on three certified
readings. The proof relates the result to the mathematical source. -/
theorem target34_from_anchor17 (X r k chart s t : ℤ)
    (hX : X = r + 30030 * k) (hc : chart = r % 17) (hs : s = X % 17)
    (ht : t = r % 34) :
    targetLaneProjection t (query chart s 17 15) 8 34 = X % 34 :=
  chart_query_target_lane_transport X r chart s k t 30030 17 15 8 34
    hX hc hs ht (by decide) (by decide) (by decide)

/-- General coupled anchors are admitted exactly by their combined resolution. -/
theorem target34_coupled_iff (anchors : List ℕ) (r : ℤ) (hpos : ∀ a ∈ anchors, 0 < a) :
    KElimination.ExactObservation.FiberConstant (anchorObservation selectedPrimary anchors r)
      (affineTarget selectedPrimary 34 r) ↔ 17 ∣ resolution selectedPrimary anchors := by
  rw [combined_target_fiber_constant_iff selectedPrimary 34 anchors r (by decide) hpos,
    reduced_periods.2]

theorem source_periods :
    selectedPrimary * resolution selectedPrimary [] = 30030 ∧
    selectedPrimary * resolution selectedPrimary [17] = 510510 ∧
    selectedPrimary * resolution selectedPrimary [34] = 510510 := by decide

/-- Every source period that retains the fixed primary and admits order 34
is a multiple of 510510, including when further anchors are present. -/
theorem target34_minimal_primary_multiple (L : ℕ) :
    selectedPrimary ∣ L ∧ 34 ∣ L ↔ 510510 ∣ L := by
  rw [← Nat.lcm_dvd_iff, show Nat.lcm selectedPrimary 34 = 510510 by decide]

private theorem half_power {k : ℕ} {ζ : ℂ} (hk : 0 < k) (hζ : IsPrimitiveRoot ζ (2*k)) :
    ζ^k = -1 := by
  have hsq : (ζ^k)^2 = 1 := by simpa only [← pow_mul, Nat.mul_comm k 2] using hζ.pow_eq_one
  exact (sq_eq_one_iff.mp hsq).resolve_left (hζ.pow_ne_one_of_pos_of_lt hk.ne' (by omega))

/-- Pair complete endpoint packets at the primary period for an order-ten cusp. -/
theorem endpoint10_from_packets (N : ℕ) (ζ : ℂ) (hζ : IsPrimitiveRoot ζ 10) (hN : 5 ≤ N) :
    (-4) * sumBelow 30030 (fun r => uPacket ζ N 30030 r * ζ^r) = boundaryValue 5 ζ :=
  boundaryValue_from_packets N 5 30030 ζ (by decide) (half_power (by decide) hζ) hN
    (by decide) (by decide)

/-- Pair complete endpoint packets at the least multiple of the primary
admitting the order-34 query, after retaining the quotient class modulo 17. -/
theorem endpoint34_from_packets (N : ℕ) (ζ : ℂ) (hζ : IsPrimitiveRoot ζ 34) (hN : 17 ≤ N) :
    (-4) * sumBelow 510510 (fun r => uPacket ζ N 510510 r * ζ^r) = boundaryValue 17 ζ :=
  boundaryValue_from_packets N 17 510510 ζ (by decide) (half_power (by decide) hζ) hN
    (by decide) (by decide)

end MockThetaAnalytic.BoundaryObservation34
