import ResidueSeries
import ProfiniteObservations

/-! Degree cylinders and admitted finite character evaluations for any
coefficient sequence. The anchor contract determines a usable period for the
transform. The caller supplies the coefficient sequence. -/

namespace KElimination.CoefficientObservations

open Lean.Grind KElimination.ResidueSeries KElimination.ProfiniteObservations

universe u

section Cylinders

variable {R : Type u} [Semiring R] {F : PeriodFamily}

/-- Read the degree-d packet at one coordinate of a compatible residue point. -/
def coefficientCylinder (a : Nat → R) (m : F.Period) (d : Nat) : ResiduePoint F → R :=
  ofResidueFunction m (fun r => packet a m.val r d)

theorem coefficientCylinder_observable (a : Nat → R) (m : F.Period) (d : Nat) :
    ExactObservation.FiberConstant (fun x : ResiduePoint F => x.residue m)
      (coefficientCylinder a m d) :=
  cylinder_fiber_constant m (fun r => packet a m.val r d)

theorem coefficientCylinder_refinement (a : Nat → R) (m n : F.Period)
    (hdiv : m.val ∣ n.val) (d : Nat) (x : ResiduePoint F) :
    sumBelow n.val (fun s => if s % m.val = x.residue n % m.val then
      packet a n.val s d else 0) = coefficientCylinder a m d x := by
  rw [x.coherent m n hdiv]
  exact packet_refinement a m.val n.val (x.residue m) d (F.positive n.val n.property) hdiv

end Cylinders

variable {R : Type u} [CommRing R]

theorem finite_root_evaluation_from_reduced_winding (a : Nat → R) (t z : R)
    (N M H b : Nat) (hM : 0 < M) (hH : 0 < H) (hb : 0 < b)
    (hresolve : reducedTargetPeriod M b ∣ H) (hz : z ^ b = 1) :
    sumBelow (M * H) (fun s => weightedPacket a (fun d => t ^ d) N (M * H) s * z ^ s) =
      sumBelow N (fun d => a d * (t * z) ^ d) :=
  finite_root_evaluation_of_dvd a t z N b (M * H) (Nat.mul_pos hM hH)
    (target_divides_source_period M b H hb hresolve) hz

/-- The coupled-anchor observation criterion supplies a period divisible by b
for the transform of every finite coefficient truncation. -/
theorem finite_root_evaluation_from_coupled_anchors (a : Nat → R) (t z : R)
    (N M b : Nat) (anchors : List Nat) (r : Int) (hM : 0 < M) (hb : 0 < b)
    (hpos : ∀ m ∈ anchors, 0 < m)
    (hquery : ExactObservation.FiberConstant (anchorObservation M anchors r)
      (affineTarget M b r)) (hz : z ^ b = 1) :
    sumBelow (M * CoupledAnchors.resolution M anchors) (fun s =>
      weightedPacket a (fun d => t ^ d) N (M * CoupledAnchors.resolution M anchors) s * z ^ s) =
      sumBelow N (fun d => a d * (t * z) ^ d) :=
  finite_root_evaluation_from_reduced_winding a t z N M (CoupledAnchors.resolution M anchors) b
    hM (CoupledAnchors.resolution_pos M anchors hpos) hb
    ((combined_target_fiber_constant_iff M b anchors r hb hpos).mp hquery) hz

end KElimination.CoefficientObservations

#print axioms KElimination.CoefficientObservations.coefficientCylinder_observable
#print axioms KElimination.CoefficientObservations.coefficientCylinder_refinement
#print axioms KElimination.CoefficientObservations.finite_root_evaluation_from_reduced_winding
#print axioms KElimination.CoefficientObservations.finite_root_evaluation_from_coupled_anchors
