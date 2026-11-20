import BridgeArithmetic
import KElimination.UniversalResearch.IntegerSpecialization
import KElimination.UniversalResearch.StarLift
import CoefficientObservations
import MockThetaPhi
import MockThetaPsi
import MockThetaChi

/-! Signed NINE65 readouts paired with finite mock theta evaluations on the
period admitted by the observation. The main and sister readings share X.
The weights in a transform are computed from the supplied coefficient series.
-/

namespace CRAMMockThetaBridge

open Lean.Grind
open KElimination
open KElimination.IntegerSpecialization KElimination.StarLift
open KElimination.ProfiniteObservations KElimination.ResidueSeries
open KElimination.CoefficientObservations

/-- The observed quotient coordinate and the corresponding target residue
of the same signed source. -/
structure ReadoutCertificate (M A b : Nat) (X r κ : Int) : Prop where
  quotient : κ = (X / (M : Int)) % (A : Int)
  target : KElimination.IntegerSpecialization.targetLaneProjection (r % (b : Int)) κ ((M : Int) % (b : Int)) b = X % (b : Int)

/-- A public integer inverse forces precisely the coprimality needed by the
singleton resolution formula, including the trivial anchor A=1. -/
theorem gcd_eq_one_of_inverse (M A : Nat) (u : Int)
    (hinv : (u * (M : Int)) % (A : Int) = 1 % (A : Int)) : Nat.gcd M A = 1 := by
  let g := Nat.gcd M A
  have hgM : (g : Int) ∣ (M : Int) := Int.ofNat_dvd.mpr (Nat.gcd_dvd_left M A)
  have hgA : (g : Int) ∣ (A : Int) := Int.ofNat_dvd.mpr (Nat.gcd_dvd_right M A)
  have hdiff := Int.dvd_of_emod_eq_zero (Int.emod_eq_emod_iff_emod_sub_eq_zero.mp hinv)
  have hgprod : (g : Int) ∣ u * (M : Int) := Int.dvd_mul_of_dvd_right hgM
  have hone : (g : Int) ∣ 1 := by
    have h := Int.dvd_sub hgprod (Int.dvd_trans hgA hdiff)
    simpa only [Int.sub_sub_self] using h
  exact Nat.eq_one_of_dvd_one (Int.ofNat_dvd.mp hone)

theorem singleton_resolution_of_inverse (M A : Nat) (u : Int)
    (hinv : (u * (M : Int)) % (A : Int) = 1 % (A : Int)) :
    CoupledAnchors.resolution M [A] = A := by
  simp [CoupledAnchors.resolution, CoupledAnchors.anchorLCM, gcd_eq_one_of_inverse M A u hinv]

/-- Universal query admission for the singleton view on the affine fiber r+M*k. -/
theorem target_fiber_constant_of_inverse (M A b : Nat) (r u : Int)
    (hA : 0 < A) (hb : 0 < b) (hinv : (u * (M : Int)) % (A : Int) = 1 % (A : Int))
    (hadmit : b / Nat.gcd M b ∣ A) :
    ExactObservation.FiberConstant (anchorObservation M [A] r) (affineTarget M b r) := by
  apply (combined_target_fiber_constant_iff M b [A] r hb (by simpa using hA)).mpr
  rw [singleton_resolution_of_inverse M A u hinv]
  exact hadmit

theorem readout_and_target (M A b : Nat) (X r s u : Int)
    (_hM : 0 < M) (_hA : 0 < A) (hb : 0 < b)
    (hr : r = X % (M : Int)) (hs : s = X % (A : Int))
    (hinv : (u * (M : Int)) % (A : Int) = 1 % (A : Int))
    (hadmit : b / Nat.gcd M b ∣ A) :
    ReadoutCertificate M A b X r (query r s A u) := by
  refine ⟨query_quotient_congruence X r s M A u hr hs hinv, ?_⟩
  have hperiod : (b : Int) ∣ (M : Int) * (A : Int) :=
    (int_dvd_mul_iff_period_dvd M b A hb).mp (Int.ofNat_dvd.mpr hadmit)
  have hsource : X = r + (M : Int) * (X / (M : Int)) := by
    rw [hr, Int.emod_add_mul_ediv]
  have htransport := chart_query_target_lane_transport X r (r % (A : Int)) s (X / M)
    (r % (b : Int)) M A u ((M : Int) % (b : Int)) b hsource rfl hs rfl rfl hinv hperiod
  simpa only [query, Int.sub_emod_emod] using htransport

universe u
variable {R : Type u} [CommRing R]

/-- Pair the NINE65 unit-anchor readout with the full finite coefficient
transform at the singleton joint period M*A. -/
theorem finite_evaluation_from_nine65_anchor (a : Nat → R) (t z : R) (N M A b : Nat)
    (X r s u : Int) (hM : 0 < M) (hA : 0 < A) (hb : 0 < b)
    (hr : r = X % (M : Int)) (hs : s = X % (A : Int))
    (hinv : (u * (M : Int)) % (A : Int) = 1 % (A : Int))
    (hadmit : b / Nat.gcd M b ∣ A) (hz : z ^ b = 1) :
    ReadoutCertificate M A b X r (query r s A u) ∧
      sumBelow (M * A) (fun j => weightedPacket a (fun d => t ^ d) N (M * A) j * z ^ j) =
        sumBelow N (fun d => a d * (t * z) ^ d) := by
  refine ⟨readout_and_target M A b X r s u hM hA hb hr hs hinv hadmit, ?_⟩
  have hquery := target_fiber_constant_of_inverse M A b r u hA hb hinv hadmit
  have evaluation := finite_root_evaluation_from_coupled_anchors a t z N M b [A] r hM hb
    (by simpa using hA) hquery hz
  rwa [singleton_resolution_of_inverse M A u hinv] at evaluation

/-- Specialize the joint theorem to the NINE65 main-minus-sister readout. -/
theorem finite_evaluation_from_nine65_adjacent (a : Nat → R) (t z : R) (N M b : Nat)
    (X r s : Int) (hM : 0 < M) (hb : 0 < b)
    (hr : r = X % (M : Int)) (hs : s = X % ((M + 1 : Nat) : Int))
    (hadmit : b / Nat.gcd M b ∣ M + 1) (hz : z ^ b = 1) :
    ReadoutCertificate M (M + 1) b X r (positiveAdjacent r s M) ∧
      sumBelow (M * (M + 1)) (fun j =>
        weightedPacket a (fun d => t ^ d) N (M * (M + 1)) j * z ^ j) =
        sumBelow N (fun d => a d * (t * z) ^ d) := by
  have hinv : ((-1 : Int) * (M : Int)) % ((M + 1 : Nat) : Int) =
      1 % ((M + 1 : Nat) : Int) := by
    simpa using star_inverse_certificate (M : Int) 1
  have h := finite_evaluation_from_nine65_anchor a t z N M (M + 1) b X r s (-1)
    hM (Nat.zero_lt_succ _) hb hr hs hinv hadmit hz
  change ReadoutCertificate M (M + 1) b X r (query r s ((M : Int) + 1) (-1)) ∧ _ at h
  rw [adjacent_query_subtraction] at h
  exact h

theorem mockTheta_from_nine65_adjacent (t z : R) (N M b : Nat) (X r s : Int)
    (hM : 0 < M) (hb : 0 < b)
    (hr : r = X % (M : Int)) (hs : s = X % ((M + 1 : Nat) : Int))
    (hadmit : b / Nat.gcd M b ∣ M + 1) (hz : z ^ b = 1) :
    ReadoutCertificate M (M + 1) b X r (positiveAdjacent r s M) ∧
      sumBelow (M * (M + 1)) (fun j =>
        MockTheta.mockWeightedPacket t N (M * (M + 1)) j * z ^ j) =
        MockTheta.mockPolynomial N (t * z) :=
  finite_evaluation_from_nine65_adjacent MockTheta.mockCoeff t z N M b X r s hM hb hr hs hadmit hz

theorem phi_from_nine65_adjacent (t z : R) (N M b : Nat) (X r s : Int)
    (hM : 0 < M) (hb : 0 < b)
    (hr : r = X % (M : Int)) (hs : s = X % ((M + 1 : Nat) : Int))
    (hadmit : b / Nat.gcd M b ∣ M + 1) (hz : z ^ b = 1) :
    ReadoutCertificate M (M + 1) b X r (positiveAdjacent r s M) ∧
      sumBelow (M * (M + 1)) (fun j =>
        MockThetaPhi.phiWeightedPacket t N (M * (M + 1)) j * z ^ j) =
        MockThetaPhi.phiPolynomial N (t * z) :=
  finite_evaluation_from_nine65_adjacent MockThetaPhi.phiCoeff t z N M b X r s hM hb hr hs hadmit hz

theorem psi_from_nine65_adjacent (t z : R) (N M b : Nat) (X r s : Int)
    (hM : 0 < M) (hb : 0 < b)
    (hr : r = X % (M : Int)) (hs : s = X % ((M + 1 : Nat) : Int))
    (hadmit : b / Nat.gcd M b ∣ M + 1) (hz : z ^ b = 1) :
    ReadoutCertificate M (M + 1) b X r (positiveAdjacent r s M) ∧
      sumBelow (M * (M + 1)) (fun j =>
        MockThetaPsi.psiWeightedPacket t N (M * (M + 1)) j * z ^ j) =
        MockThetaPsi.psiPolynomial N (t * z) :=
  finite_evaluation_from_nine65_adjacent MockThetaPsi.psiCoeff t z N M b X r s hM hb hr hs hadmit hz

theorem chi_from_nine65_adjacent (t z : R) (N M b : Nat) (X r s : Int)
    (hM : 0 < M) (hb : 0 < b)
    (hr : r = X % (M : Int)) (hs : s = X % ((M + 1 : Nat) : Int))
    (hadmit : b / Nat.gcd M b ∣ M + 1) (hz : z ^ b = 1) :
    ReadoutCertificate M (M + 1) b X r (positiveAdjacent r s M) ∧
      sumBelow (M * (M + 1)) (fun j =>
        MockThetaChi.chiWeightedPacket t N (M * (M + 1)) j * z ^ j) =
        MockThetaChi.chiPolynomial N (t * z) :=
  finite_evaluation_from_nine65_adjacent MockThetaChi.chiCoeff t z N M b X r s hM hb hr hs hadmit hz

end CRAMMockThetaBridge

#print axioms CRAMMockThetaBridge.ReadoutCertificate
#print axioms CRAMMockThetaBridge.gcd_eq_one_of_inverse
#print axioms CRAMMockThetaBridge.singleton_resolution_of_inverse
#print axioms CRAMMockThetaBridge.target_fiber_constant_of_inverse
#print axioms CRAMMockThetaBridge.readout_and_target
#print axioms CRAMMockThetaBridge.finite_evaluation_from_nine65_anchor
#print axioms CRAMMockThetaBridge.finite_evaluation_from_nine65_adjacent
#print axioms CRAMMockThetaBridge.mockTheta_from_nine65_adjacent
#print axioms CRAMMockThetaBridge.phi_from_nine65_adjacent
#print axioms CRAMMockThetaBridge.psi_from_nine65_adjacent
#print axioms CRAMMockThetaBridge.chi_from_nine65_adjacent
