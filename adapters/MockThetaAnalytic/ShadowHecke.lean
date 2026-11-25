import ShadowReadings
import PartitionCrank11
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.Ring

/-! The square-index restrictions of the arithmetic Hecke operators at 5.
In the even character decomposition the middle and down terms act on a
negative-square sector by diamond shifts. These stencils are specified
before applying the first moment. -/

namespace MockThetaAnalytic.ShadowHecke

open ShadowReadings
open scoped BigOperators Matrix

abbrev Phase := ZMod 11
abbrev Packet := ℕ → Phase → ℤ

def phase (m : ℕ) : Phase := -((m : Phase)^2)

def sectorPacket (a : ℕ → ℤ) (m : ℕ) (r : Phase) : ℤ :=
  if r = phase m then a m else 0

def moment (a : Packet) (m : ℕ) (r : Phase) : ℤ := firstMoment m * a m r

/-- The arithmetic normalization is five times the weight-one-half operator. -/
def sourceFive (a : Packet) (m : ℕ) (r : Phase) : ℤ :=
  5*a (5*m) r - (if 5 ∣ m then 0 else a m (4*r)) +
    if 5 ∣ m then a (m/5) (5*r) else 0

/-- Weight-three-halves operator in the same diamond coordinates.
The two square Legendre symbols agree at five since −1 is a square there. -/
def targetFive (a : Packet) (m : ℕ) (r : Phase) : ℤ :=
  a (5*m) r - (if 5 ∣ m then 0 else a m (4*r)) +
    if 5 ∣ m then 5*a (m/5) (5*r) else 0

theorem firstMoment_five (m : ℕ) : firstMoment (5*m) = 5*firstMoment m := by
  have h : 5*m % 4 = m % 4 := by omega
  have hc : chiFour (5*m) = chiFour m := by simp only [chiFour, h]
  simp only [firstMoment, hc, Nat.cast_mul, Nat.cast_ofNat]
  rw [mul_left_comm (4 : ℤ) 5, mul_assoc 5]

private theorem div_five {m : ℕ} (h : 5 ∣ m) : 5*(m/5) = m := by omega

theorem hecke_moment (a : Packet) : moment (sourceFive a) = targetFive (moment a) := by
  funext m r
  simp only [moment, sourceFive, targetFive, firstMoment_five]
  by_cases h : 5 ∣ m
  · have hm := (firstMoment_five (m/5)).symm
    rw [div_five h] at hm
    simp only [if_pos h, ← hm]
    ring
  · simp only [if_neg h]
    ring

theorem etaSign_five (m : ℕ) : etaSign (5*m) = -etaSign m := by
  have h : ∀ r : Fin 12, etaSign (5*r.val) = -etaSign r.val := by decide +kernel
  have hm : 5*m % 12 = (5*(m%12)) % 12 := by omega
  simpa only [etaSign, hm, Nat.mod_mod] using h ⟨m%12,Nat.mod_lt _ (by decide)⟩

private theorem phase_five (m : ℕ) : phase (5*m) = 3*phase m := by
  unfold phase
  push_cast
  have h : (5:Phase)^2 = 3 := by decide
  simp only [mul_pow, h, mul_neg]

private theorem upper_phase (m : ℕ) (r : Phase) :
    r = phase (5*m) ↔ 4*r = phase m := by
  rw [phase_five]
  have h : (4:Phase)*3 = 1 := by decide
  constructor
  · intro hr
    rw [hr, ← mul_assoc, h, one_mul]
  · intro hr
    rw [← hr, ← mul_assoc, mul_comm 3 (4:Phase), h, one_mul]

private theorem lower_phase (m : ℕ) (r : Phase) (h : 5 ∣ m) :
    5*r = phase (m/5) ↔ 4*r = phase m := by
  have hp := phase_five (m/5)
  rw [div_five h] at hp
  have a : (3:Phase)*5 = 4 := by decide
  have b : (4:Phase)*4 = 5 := by decide
  have c : (4:Phase)*3 = 1 := by decide
  constructor
  · intro hr
    rw [hp, ← hr, ← mul_assoc, a]
  · intro hr
    have hh := congrArg (fun k : Phase => 4*k) hr
    simpa only [hp, ← mul_assoc, b, c, one_mul] using hh

theorem sourceFive_eta (m : ℕ) (r : Phase) :
    sourceFive (sectorPacket etaSign) m r = -6 * sectorPacket etaSign m (4*r) := by
  simp only [sourceFive, sectorPacket, upper_phase, etaSign_five]
  by_cases hd : 5 ∣ m
  · have he := etaSign_five (m/5)
    rw [div_five hd] at he
    have hh : etaSign (m/5) = -etaSign m := by omega
    simp only [if_pos hd, lower_phase m r hd, hh]
    split_ifs <;> ring
  · simp only [if_neg hd]
    split_ifs <;> ring

theorem targetFive_eta_moment (m : ℕ) (r : Phase) :
    targetFive (moment (sectorPacket etaSign)) m r =
      -6 * moment (sectorPacket etaSign) m (4*r) := by
  rw [← hecke_moment]
  unfold moment
  rw [sourceFive_eta]
  ring

def cut (N : ℕ) (a : Packet) (m : ℕ) (r : Phase) : ℤ := if m ≤ N then a m r else 0

theorem sourceFive_lookahead (a : Packet) {N m : ℕ} (h : 5*m ≤ N) (r : Phase) :
    sourceFive (cut N a) m r = sourceFive a m r := by
  have hm : m ≤ N := by omega
  have hd : m/5 ≤ N := by omega
  simp [sourceFive, cut, h, hm, hd]

theorem targetFive_lookahead (a : Packet) {N m : ℕ} (h : 5*m ≤ N) (r : Phase) :
    targetFive (cut N a) m r = targetFive a m r := by
  have hm : m ≤ N := by omega
  have hd : m/5 ≤ N := by omega
  simp [targetFive, cut, h, hm, hd]

theorem one_loses_lookahead :
    targetFive (moment (sectorPacket etaSign)) 1 8 = -24 ∧
      (∑ r : Phase, targetFive (cut 1 (moment (sectorPacket etaSign))) 1 r) = -4 := by
  decide +kernel

abbrev Row := Fin 6
def occupied : Row → ℕ := ![0,2,6,7,8,10]

open KElimination.PartitionCrank11 in
def crankMatrix : Matrix Row Row ℤ := fun i j =>
  countClass crank (partitions (i.val+2)) (occupied j)

theorem crank_matrix :
    crankMatrix = !![0,1,0,0,0,0; 1,0,0,0,1,0; 1,1,0,1,0,0;
      1,0,1,0,1,1; 1,1,1,1,1,1; 1,1,1,2,1,2] := by
  funext i j
  exact (by decide +kernel : ∀ i j : Row, crankMatrix i j =
    (!![0,1,0,0,0,0; 1,0,0,0,1,0; 1,1,0,1,0,0;
      1,0,1,0,1,1; 1,1,1,1,1,1; 1,1,1,2,1,2] : Matrix Row Row ℤ) i j) i j

private def crankInverse : Matrix Row Row ℤ :=
  !![0,0,1,1,-1,0; 1,0,0,0,0,0; -1,-1,0,0,2,-1;
     -1,0,0,-1,1,0; 0,1,-1,-1,1,0; 1,0,0,1,-2,1]

theorem crank_integer_basis :
    ∃ inverse : Matrix Row Row ℤ, crankMatrix * inverse = 1 ∧ inverse * crankMatrix = 1 := by
  refine ⟨crankInverse, ?_, ?_⟩
  · ext i j
    exact (by decide +kernel : ∀ i j : Row, (crankMatrix * crankInverse) i j =
      (1 : Matrix Row Row ℤ) i j) i j
  · ext i j
    exact (by decide +kernel : ∀ i j : Row, (crankInverse * crankMatrix) i j =
      (1 : Matrix Row Row ℤ) i j) i j

/-- The full crank vector supports the induced action of any sector matrix,
in particular the Hecke rotation with its scalar factor. -/
theorem crank_basis_transport (shift : Matrix Row Row ℤ) :
    ∃ transfer : Matrix Row Row ℤ, ∀ v : Row → ℤ,
      transfer.mulVec (crankMatrix.mulVec v) = crankMatrix.mulVec (shift.mulVec v) := by
  obtain ⟨inverse, _, h⟩ := crank_integer_basis
  refine ⟨crankMatrix * shift * inverse, ?_⟩
  intro v
  rw [Matrix.mulVec_mulVec, mul_assoc (crankMatrix * shift), h, mul_one, Matrix.mulVec_mulVec]

open KElimination.PartitionCrank11 in
theorem size_three_fixed_mask_fails :
    (∑ r : Phase, (countClass crank (partitions 3) r.val : ℤ) *
      targetFive (moment (sectorPacket etaSign)) 1 r) = -24 ∧
    (countClass crank (partitions 3) 10 : ℤ) *
      (∑ r : Phase, targetFive (moment (sectorPacket etaSign)) 1 r) = 0 := by
  decide +kernel

end MockThetaAnalytic.ShadowHecke
