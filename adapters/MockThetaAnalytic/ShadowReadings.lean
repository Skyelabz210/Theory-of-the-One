import MockTheta
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Sqrt
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.IntervalCases

/-! Degree-labeled S6 observations of the input coefficients. The reciprocal
is taken in the formal series ring over F₂ with constant coefficient one. -/

namespace MockThetaAnalytic.ShadowReadings

open KElimination.ProfiniteObservations
open scoped BigOperators

abbrev Prefix (D : ℕ) := Fin (D+1) → ℤ

def observe (D : ℕ) (a : ℕ → ℤ) : Prefix D :=
  fun d => a d.val % (selectedPrimary : ℤ)

theorem observe_add_lifts (D : ℕ) (a k : ℕ → ℤ) :
    observe D (fun d => a d + (selectedPrimary : ℤ) * k d) = observe D a := by
  funext d
  simp only [observe, selectedPrimary, Nat.cast_ofNat]
  omega

def parity {D : ℕ} (reading : Prefix D) (d : ℕ) : ZMod 2 :=
  if h : d < D+1 then (reading ⟨d,h⟩ : ZMod 2) else 0

theorem observes_parity {D d : ℕ} (a : ℕ → ℤ) (hd : d ≤ D) :
    parity (observe D a) d = (a d : ZMod 2) := by
  rw [parity, dif_pos (by omega : d < D+1)]
  unfold observe
  have h : (a d % (selectedPrimary : ℤ)) % 2 = a d % 2 := by
    simp only [selectedPrimary, Nat.cast_ofNat]
    omega
  have p (x : ℤ) : ((x % 2 : ℤ) : ZMod 2) = (x : ZMod 2) := by
    rw [Int.emod_def, Int.cast_sub, Int.cast_mul]
    rw [show ((2 : ℤ) : ZMod 2) = 0 by decide, zero_mul, sub_zero]
  rw [← p (a d % (selectedPrimary : ℤ)), h, p]

theorem odd_modulus_loses_parity :
    (0 : ℤ) % 15015 = 15015 % 15015 ∧ (0 : ZMod 2) ≠ (15015 : ℤ) := by decide

-- Store the prefix in reverse degree order so the next coefficient is
-- the dot product with a₁, …, aₙ at the corresponding decreasing degrees.
private def reciprocalPrefix (a : ℕ → ZMod 2) (d : ℕ) : List (ZMod 2) :=
  Nat.rec [1] (fun n previous =>
    (∑ i ∈ Finset.range (n+1), a (i+1) * previous[i]?.getD 0) :: previous) d

def reciprocalBit (a : ℕ → ZMod 2) (d : ℕ) : ZMod 2 :=
  (reciprocalPrefix a d)[0]?.getD 0

private theorem reciprocalPrefix_get (a : ℕ → ZMod 2) (d i : ℕ) (h : i ≤ d) :
    (reciprocalPrefix a d)[i]?.getD 0 = reciprocalBit a (d-i) := by
  induction d generalizing i with
  | zero =>
    have hi : i = 0 := by omega
    subst i
    rfl
  | succ d ih =>
    cases i with
    | zero => rfl
    | succ i =>
      simpa only [reciprocalPrefix, List.getElem?_cons_succ, Nat.succ_sub_succ_eq_sub] using
        ih i (by omega)

theorem reciprocalBit_zero (a : ℕ → ZMod 2) : reciprocalBit a 0 = 1 := rfl

theorem reciprocalBit_succ (a : ℕ → ZMod 2) (d : ℕ) :
    reciprocalBit a (d+1) = ∑ i ∈ Finset.range (d+1), a (i+1) * reciprocalBit a (d-i) := by
  change (∑ i ∈ Finset.range (d+1), a (i+1) * (reciprocalPrefix a d)[i]?.getD 0) = _
  apply Finset.sum_congr rfl
  intro i hi
  rw [reciprocalPrefix_get a d i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))]

theorem reciprocalBit_congr (a b : ℕ → ZMod 2) (d : ℕ) (h : ∀ i ≤ d, a i = b i) :
    reciprocalBit a d = reciprocalBit b d := by
  induction d using Nat.strong_induction_on with
  | h d ih =>
    cases d with
    | zero => simp [reciprocalBit_zero]
    | succ d =>
      rw [reciprocalBit_succ, reciprocalBit_succ]
      apply Finset.sum_congr rfl
      intro i hi
      have hi := Finset.mem_range.mp hi
      rw [h _ (by omega), ih _ (by omega) (fun j hj => h j (by omega))]

theorem reciprocal_prefix (a : ℕ → ℤ) {D d : ℕ} (hd : d ≤ D) :
    reciprocalBit (parity (observe D a)) d = reciprocalBit (fun i => (a i : ZMod 2)) d :=
  reciprocalBit_congr _ _ d (fun _ hi => observes_parity a (hi.trans hd))

theorem reciprocal_fiber_constant {D d : ℕ} (hd : d ≤ D) :
    KElimination.ExactObservation.FiberConstant (observe D)
      (fun a => reciprocalBit (fun i => (a i : ZMod 2)) d) := by
  intro a b h
  dsimp only
  rw [← reciprocal_prefix a hd, ← reciprocal_prefix b hd, h]

def pentagonalBit (d : ℕ) : ZMod 2 :=
  if (24*d+1).sqrt * (24*d+1).sqrt = 24*d+1 then 1 else 0

theorem square_lattice (m : ℕ) : (m*m)%24 = 1 ↔ m%6 = 1 ∨ m%6 = 5 := by
  have h : ∀ r : Fin 24, (r.val*r.val)%24 = 1 ↔ r.val%6 = 1 ∨ r.val%6 = 5 := by decide +kernel
  have hm : (m%24)%6 = m%6 := by omega
  rw [Nat.mul_mod m m 24]
  simpa only [hm] using h ⟨m%24,Nat.mod_lt _ (by decide)⟩

def etaSign (m : ℕ) : ℤ :=
  if m % 12 = 1 ∨ m % 12 = 11 then 1 else if m % 12 = 5 ∨ m % 12 = 7 then -1 else 0

def chiFour (m : ℕ) : ℤ :=
  if m % 4 = 1 then 1 else if m % 4 = 3 then -1 else 0

def firstMoment (m : ℕ) : ℤ := 4 * m * chiFour m

def etaFromParity (D : ℕ) (bits : ℕ → ZMod 2) (m : ℕ) : ℤ :=
  if (m*m) % 24 = 1 ∧ (m*m-1)/24 ≤ D ∧
      reciprocalBit bits ((m*m-1)/24) = 1 then etaSign m else 0

def etaMode {D : ℕ} (reading : Prefix D) (m : ℕ) : ℤ :=
  etaFromParity D (parity reading) m

def shadowMode {D : ℕ} (reading : Prefix D) (m : ℕ) : ℤ :=
  firstMoment m * etaMode reading m

theorem eta_observation (a : ℕ → ℤ) (D m : ℕ) :
    etaMode (observe D a) m = etaFromParity D (fun i => (a i : ZMod 2)) m := by
  by_cases h : (m*m-1)/24 ≤ D
  · simp only [etaMode, etaFromParity, reciprocal_prefix a h]
  · simp [etaMode, etaFromParity, h]

theorem shadow_fiber_constant (D m : ℕ) :
    KElimination.ExactObservation.FiberConstant (observe D)
      (fun a => firstMoment m * etaFromParity D (fun i => (a i : ZMod 2)) m) := by
  intro a b h
  dsimp only
  rw [← eta_observation a, ← eta_observation b, h]

theorem etaMode_prefix (a : ℕ → ℤ) {D E m : ℕ} (hD : D ≤ E) (hm : (m*m-1)/24 ≤ D) :
    etaMode (observe D a) m = etaMode (observe E a) m := by
  simp only [etaMode, etaFromParity, reciprocal_prefix a hm, reciprocal_prefix a (hm.trans hD),
    hm, hm.trans hD, true_and]

end MockThetaAnalytic.ShadowReadings
