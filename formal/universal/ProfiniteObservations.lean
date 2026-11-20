import CoupledAnchors
import ExactObservation

/-!
Compatible residue tuples and finite target-observation requirements.

The tuple construction is the algebraic data of an inverse system over an
admitted positive-modulus family. No topology, compactness, Pontryagin duality,
analytic convergence, or production observation constructor is asserted here.
Coordinates are residues with bounds and compatibility proofs, not a stored
scalar source or winding. Diagonal sources occur in mathematical specifications.
The selected primary remains S6; additional admitted observations do not change
that primary or assert independent capacity.
-/

namespace KElimination.ProfiniteObservations

universe u

/-- The admissible observation periods, each strictly positive. -/
structure PeriodFamily where
  admits : Nat → Prop
  positive : ∀ m, admits m → 0 < m

def PeriodFamily.Period (F : PeriodFamily) := {m : Nat // F.admits m}

/-- All positive integer periods; admission is mathematical, not a producer. -/
def positivePeriods : PeriodFamily where
  admits m := 0 < m
  positive _ h := h

/-- Powers of one fixed positive primary period. -/
def powerPeriods (M : Nat) (hM : 0 < M) : PeriodFamily where
  admits m := ∃ n : Nat, m = M ^ n
  positive m hm := by
    obtain ⟨n, rfl⟩ := hm
    exact Nat.pow_pos hM

def selectedPrimary : Nat := 30030

theorem selected_primary_factorization :
    selectedPrimary = 2 * 3 * 5 * 7 * 11 * 13 := by decide

def selectedPrimaryPowers : PeriodFamily :=
  powerPeriods selectedPrimary (by decide)

/-- Canonical coordinates with all divisibility transition equations.
This structure contains no global integer or quotient coordinate. -/
structure ResiduePoint (F : PeriodFamily) where
  residue : F.Period → Nat
  bound : ∀ m, residue m < m.val
  coherent : ∀ m n, m.val ∣ n.val → residue n % m.val = residue m

theorem point_ext {F : PeriodFamily} (x y : ResiduePoint F)
    (h : ∀ m, x.residue m = y.residue m) : x = y := by
  cases x with
  | mk xr xb xc =>
    cases y with
    | mk yr yb yc =>
      have heq : xr = yr := funext h
      cases heq
      rfl

/-- Natural sources give compatible diagonal points, without reconstructing
a source from an arbitrary tuple. -/
def natPoint (F : PeriodFamily) (source : Nat) : ResiduePoint F where
  residue m := source % m.val
  bound m := Nat.mod_lt source (F.positive m.val m.property)
  coherent _ _ h := Nat.mod_mod_of_dvd source h

/-- Signed sources give their nonnegative Euclidean residue coordinates. -/
def intPoint (F : PeriodFamily) (source : Int) : ResiduePoint F where
  residue m := (source % (m.val : Int)).toNat
  bound m := by
    have hp : 0 < (m.val : Int) := by
      exact_mod_cast F.positive m.val m.property
    have hnonneg := Int.emod_nonneg source (Int.ne_of_gt hp)
    have hlt := Int.emod_lt_of_pos source hp
    omega
  coherent m n h := by
    have hn : (n.val : Int) ≠ 0 := by
      have := F.positive n.val n.property
      omega
    have hd : (m.val : Int) ∣ (n.val : Int) := Int.ofNat_dvd.mpr h
    calc
      (source % (n.val : Int)).toNat % m.val =
          ((source % (n.val : Int)) % (m.val : Int)).toNat := by
        simpa only [Int.toNat_natCast] using
          (Int.toNat_emod (Int.emod_nonneg source hn)
            (Int.natCast_nonneg m.val)).symm
      _ = (source % (m.val : Int)).toNat :=
        congrArg Int.toNat (Int.emod_emod_of_dvd source hd)

theorem nat_point_projection (F : PeriodFamily) (source : Nat) (m : F.Period) :
    (natPoint F source).residue m = source % m.val := rfl

theorem int_point_projection (F : PeriodFamily) (source : Int) (m : F.Period) :
    (intPoint F source).residue m = (source % (m.val : Int)).toNat := rfl

theorem int_point_of_nat (F : PeriodFamily) (source : Nat) :
    intPoint F (source : Int) = natPoint F source := by
  apply point_ext
  intro m
  rfl

/-- A cylinder function evaluates one finite residue coordinate. -/
def ofResidueFunction {F : PeriodFamily} {Y : Type u}
    (m : F.Period) (f : Nat → Y) : ResiduePoint F → Y :=
  fun x => f (x.residue m)

theorem cylinder_evaluation_nat {F : PeriodFamily} {Y : Type u}
    (m : F.Period) (f : Nat → Y) (source : Nat) :
    ofResidueFunction m f (natPoint F source) = f (source % m.val) := rfl

theorem cylinder_evaluation_int {F : PeriodFamily} {Y : Type u}
    (m : F.Period) (f : Nat → Y) (source : Int) :
    ofResidueFunction m f (intPoint F source) =
      f ((source % (m.val : Int)).toNat) := rfl

/-- Pulling a cylinder to a finer coordinate preserves its value. -/
theorem cylinder_refinement {F : PeriodFamily} {Y : Type u}
    (m n : F.Period) (h : m.val ∣ n.val) (f : Nat → Y) (x : ResiduePoint F) :
    ofResidueFunction n (fun a => f (a % m.val)) x = ofResidueFunction m f x := by
  exact congrArg f (x.coherent m n h)

theorem cylinder_fiber_constant {F : PeriodFamily} {Y : Type u}
    (m : F.Period) (f : Nat → Y) :
    ExactObservation.FiberConstant (fun x : ResiduePoint F => x.residue m)
      (ofResidueFunction m f) := by
  intro x y h
  exact congrArg f h

/-- Existing observation refinement applies to the actual residue transition. -/
theorem refined_cylinder_fiber_constant {F : PeriodFamily} {Y : Type u}
    (m n : F.Period) (h : m.val ∣ n.val) (f : Nat → Y) :
    ExactObservation.FiberConstant (fun x : ResiduePoint F => x.residue n)
      (ofResidueFunction m f) := by
  exact ExactObservation.refined_observation_suffices
    (fun x : ResiduePoint F => x.residue m)
    (fun x : ResiduePoint F => x.residue n)
    (fun a => a % m.val) (ofResidueFunction m f)
    (fun x => x.coherent m n h) (cylinder_fiber_constant m f)

/-- Forgetting admitted coordinates preserves every retained transition law. -/
def restrictPoint {F G : PeriodFamily}
    (inclusion : ∀ m, F.admits m → G.admits m) (x : ResiduePoint G) :
    ResiduePoint F where
  residue m := x.residue ⟨m.val, inclusion m.val m.property⟩
  bound m := x.bound ⟨m.val, inclusion m.val m.property⟩
  coherent m n h := x.coherent
    ⟨m.val, inclusion m.val m.property⟩
    ⟨n.val, inclusion n.val n.property⟩ h

theorem restriction_cylinder {F G : PeriodFamily} {Y : Type u}
    (inclusion : ∀ m, F.admits m → G.admits m)
    (m : F.Period) (f : Nat → Y) (x : ResiduePoint G) :
    ofResidueFunction m f (restrictPoint inclusion x) =
      ofResidueFunction (⟨m.val, inclusion m.val m.property⟩ : G.Period) f x := rfl

theorem restriction_nat_point {F G : PeriodFamily}
    (inclusion : ∀ m, F.admits m → G.admits m) (source : Nat) :
    restrictPoint inclusion (natPoint G source) = natPoint F source := by
  apply point_ext
  intro m
  rfl

/-- Required quotient resolution for target b at fixed primary coefficient M. -/
def reducedTargetPeriod (M b : Nat) : Nat := b / Nat.gcd M b

def quotientObservation (H : Nat) (k : Int) : Int := k % H

def affineTarget (M b : Nat) (r k : Int) : Int := (r + (M : Int) * k) % b

theorem reduced_target_period_pos (M b : Nat) (hb : 0 < b) :
    0 < reducedTargetPeriod M b :=
  Nat.div_gcd_pos_of_pos_right M hb

/-- The reduced requirement and the source-period divisibility are equivalent. -/
theorem reduced_target_dvd_iff (M b H : Nat) (hb : 0 < b) :
    reducedTargetPeriod M b ∣ H ↔ b ∣ M * H :=
  (CoupledAnchors.nat_reduced_kernel M b H hb).symm

/-- Direct interface for finite root/cylinder evaluation at period M*H. -/
theorem target_divides_source_period (M b H : Nat) (hb : 0 < b)
    (h : reducedTargetPeriod M b ∣ H) : b ∣ M * H :=
  (reduced_target_dvd_iff M b H hb).mp h

theorem quotient_observation_eq_iff (H : Nat) (k j : Int) :
    quotientObservation H k = quotientObservation H j ↔ (H : Int) ∣ k - j := by
  simp only [quotientObservation, Int.emod_eq_emod_iff_emod_sub_eq_zero,
    ← Int.dvd_iff_emod_eq_zero]

/-- Exact target criterion on the quotient-H fibers. Integer coordinates here
are semantic variables, not a stored field of a ResiduePoint. -/
theorem target_constant_on_quotient_fibers_iff (M b H : Nat) (r : Int)
    (hb : 0 < b) :
    ExactObservation.FiberConstant (quotientObservation H) (affineTarget M b r) ↔
      reducedTargetPeriod M b ∣ H := by
  rw [reduced_target_dvd_iff M b H hb,
    ← CoupledAnchors.target_period_iff M H b r]
  constructor
  · intro h k j hd
    exact h k j ((quotient_observation_eq_iff H k j).mpr hd)
  · intro h k j heq
    exact h k j ((quotient_observation_eq_iff H k j).mp heq)

/-- Existence is on the image of the quotient observation, as in the universal
fiber criterion. No implementation complexity or observation producer follows. -/
theorem target_recoverable_iff (M b H : Nat) (r : Int) (hb : 0 < b) :
    (∃ answer : ExactObservation.Observed (quotientObservation H) → Int,
      ∀ k, answer (ExactObservation.reading (quotientObservation H) k) =
        affineTarget M b r k) ↔ reducedTargetPeriod M b ∣ H := by
  rw [ExactObservation.recoverable_iff]
  exact target_constant_on_quotient_fibers_iff M b H r hb

def anchorObservation (M : Nat) (anchors : List Nat) (r k : Int) : List Int :=
  anchors.map (fun (a : Nat) => (r + (M : Int) * k) % (a : Int))

theorem anchor_observation_eq_iff (M : Nat) (anchors : List Nat) (r k j : Int)
    (hpos : ∀ a ∈ anchors, 0 < a) :
    anchorObservation M anchors r k = anchorObservation M anchors r j ↔
      (CoupledAnchors.resolution M anchors : Int) ∣ k - j := by
  simp only [anchorObservation, List.map_inj_left]
  exact CoupledAnchors.same_affine_readings_iff M anchors r k j hpos

/-- Repeated/shared-factor anchors meet exactly the same reduced target
requirement, using their actual LCM/GCD resolution. -/
theorem combined_target_fiber_constant_iff (M b : Nat) (anchors : List Nat)
    (r : Int) (hb : 0 < b) (hpos : ∀ a ∈ anchors, 0 < a) :
    ExactObservation.FiberConstant (anchorObservation M anchors r)
      (affineTarget M b r) ↔
      reducedTargetPeriod M b ∣ CoupledAnchors.resolution M anchors := by
  rw [reduced_target_dvd_iff M b (CoupledAnchors.resolution M anchors) hb,
    CoupledAnchors.source_period]
  simpa only [ExactObservation.FiberConstant, anchorObservation, affineTarget,
    List.map_inj_left] using CoupledAnchors.combined_target_iff M b anchors r hpos

theorem combined_target_recoverable_iff (M b : Nat) (anchors : List Nat)
    (r : Int) (hb : 0 < b) (hpos : ∀ a ∈ anchors, 0 < a) :
    (∃ answer : ExactObservation.Observed (anchorObservation M anchors r) → Int,
      ∀ k, answer (ExactObservation.reading (anchorObservation M anchors r) k) =
        affineTarget M b r k) ↔
      reducedTargetPeriod M b ∣ CoupledAnchors.resolution M anchors := by
  rw [ExactObservation.recoverable_iff]
  exact combined_target_fiber_constant_iff M b anchors r hb hpos

end KElimination.ProfiniteObservations

#print axioms KElimination.ProfiniteObservations.selected_primary_factorization
#print axioms KElimination.ProfiniteObservations.point_ext
#print axioms KElimination.ProfiniteObservations.nat_point_projection
#print axioms KElimination.ProfiniteObservations.int_point_projection
#print axioms KElimination.ProfiniteObservations.int_point_of_nat
#print axioms KElimination.ProfiniteObservations.cylinder_evaluation_nat
#print axioms KElimination.ProfiniteObservations.cylinder_evaluation_int
#print axioms KElimination.ProfiniteObservations.cylinder_refinement
#print axioms KElimination.ProfiniteObservations.cylinder_fiber_constant
#print axioms KElimination.ProfiniteObservations.refined_cylinder_fiber_constant
#print axioms KElimination.ProfiniteObservations.restriction_cylinder
#print axioms KElimination.ProfiniteObservations.restriction_nat_point
#print axioms KElimination.ProfiniteObservations.reduced_target_period_pos
#print axioms KElimination.ProfiniteObservations.reduced_target_dvd_iff
#print axioms KElimination.ProfiniteObservations.target_divides_source_period
#print axioms KElimination.ProfiniteObservations.quotient_observation_eq_iff
#print axioms KElimination.ProfiniteObservations.target_constant_on_quotient_fibers_iff
#print axioms KElimination.ProfiniteObservations.target_recoverable_iff
#print axioms KElimination.ProfiniteObservations.anchor_observation_eq_iff
#print axioms KElimination.ProfiniteObservations.combined_target_fiber_constant_iff
#print axioms KElimination.ProfiniteObservations.combined_target_recoverable_iff
