import Std

/-!
Exact formal-series packets and finite character evaluation.

A coefficient packet retains the original power-series degree: `packet a M r n`
is the coefficient of degree `n` in the residue-`r` part of `a`. It does not
collapse infinitely many coefficients into an unqualified scalar sum. Finite
weighted packets do perform a finite pushforward, and their compatibility and
root evaluations are proved below over Lean's bundled algebra hierarchy.

These are coefficientwise and finite algebraic identities. They make no claim
about convergence, complex analysis, radial limits, modular transformation laws,
or a completed analytic measure. A named coefficient series can instantiate the
results without adding any of those assertions as assumptions.
-/

namespace KElimination.ResidueSeries

open Lean.Grind

universe u

section Basic

variable {R : Type u} [Semiring R]

/-- The exact sum over natural indices strictly below `N`. -/
def sumBelow : Nat → (Nat → R) → R
  | 0, _ => 0
  | n + 1, f => sumBelow n f + f n

theorem sumBelow_zero_bound (f : Nat → R) : sumBelow 0 f = 0 := rfl

theorem sumBelow_succ (N : Nat) (f : Nat → R) :
    sumBelow (N + 1) f = sumBelow N f + f N := rfl

theorem sumBelow_congr (N : Nat) (f g : Nat → R)
    (h : ∀ n, n < N → f n = g n) : sumBelow N f = sumBelow N g := by
  induction N with
  | zero => rfl
  | succ N ih =>
      rw [sumBelow, sumBelow, ih (fun n hn => h n (by omega)), h N (by omega)]

theorem sumBelow_zero (N : Nat) : sumBelow N (fun _ => (0 : R)) = 0 := by
  induction N with
  | zero => rfl
  | succ N ih => rw [sumBelow, ih, Semiring.add_zero]

theorem sumBelow_zero_of (N : Nat) (f : Nat → R)
    (h : ∀ n, n < N → f n = 0) : sumBelow N f = 0 := by
  rw [sumBelow_congr N f (fun _ => 0) h, sumBelow_zero]

theorem sumBelow_add (N : Nat) (f g : Nat → R) :
    sumBelow N (fun n => f n + g n) = sumBelow N f + sumBelow N g := by
  induction N with
  | zero => simp [sumBelow, Semiring.add_zero]
  | succ N ih =>
      rw [sumBelow, sumBelow, sumBelow, ih]
      grind

theorem sumBelow_mul_right (N : Nat) (f : Nat → R) (c : R) :
    sumBelow N (fun n => f n * c) = sumBelow N f * c := by
  induction N with
  | zero => simp [sumBelow, Semiring.zero_mul]
  | succ N ih => rw [sumBelow, sumBelow, ih, Semiring.right_distrib]

theorem sumBelow_mul_left (N : Nat) (f : Nat → R) (c : R) :
    sumBelow N (fun n => c * f n) = c * sumBelow N f := by
  induction N with
  | zero => simp [sumBelow, Semiring.mul_zero]
  | succ N ih => rw [sumBelow, sumBelow, ih, Semiring.left_distrib]

theorem sumBelow_swap (N M : Nat) (f : Nat → Nat → R) :
    sumBelow N (fun n => sumBelow M (f n)) =
      sumBelow M (fun r => sumBelow N (fun n => f n r)) := by
  induction N with
  | zero => exact (sumBelow_zero M).symm
  | succ N ih =>
      change sumBelow N (fun n => sumBelow M (f n)) + sumBelow M (f N) =
        sumBelow M (fun r => sumBelow N (fun n => f n r) + f N r)
      rw [ih, sumBelow_add]

/-- A finite sum selects exactly one index, including the out-of-range case. -/
theorem sumBelow_single (N i : Nat) (x : R) :
    sumBelow N (fun j => if i = j then x else 0) = if i < N then x else 0 := by
  induction N with
  | zero => simp [sumBelow]
  | succ N ih =>
      rw [sumBelow, ih]
      by_cases hi : i = N
      · subst i
        simp [AddCommMonoid.zero_add]
      · by_cases hlt : i < N
        · simp [hi, hlt, Nat.lt_trans hlt (Nat.lt_succ_self N), Semiring.add_zero]
        · have hn : ¬ i < N + 1 := by omega
          simp [hi, hlt, hn, Semiring.add_zero]

theorem sumBelow_extend_one (N : Nat) (f : Nat → R) (hz : f N = 0) :
    sumBelow (N + 1) f = sumBelow N f := by
  rw [sumBelow, hz, Semiring.add_zero]

/-- Extending a truncation across a certified zero tail changes no coefficient. -/
theorem sumBelow_eq_of_tail_zero (K N : Nat) (f : Nat → R) (hKN : K ≤ N)
    (hz : ∀ n, K ≤ n → n < N → f n = 0) :
    sumBelow N f = sumBelow K f := by
  induction N generalizing K with
  | zero =>
      have hK : K = 0 := by omega
      subst K
      rfl
  | succ N ih =>
      by_cases hK : K = N + 1
      · subst K
        rfl
      · have hKN' : K ≤ N := by omega
        rw [sumBelow, hz N hKN' (by omega), Semiring.add_zero]
        exact ih K hKN' (fun n hlow hhigh => hz n hlow (by omega))

/-- A formal coefficient mask. The degree `n` is retained. -/
def packet (a : Nat → R) (M r n : Nat) : R :=
  if n % M = r then a n else 0

/-- An exact finite pushforward of weighted coefficients to residue `r`. -/
def weightedPacket (a w : Nat → R) (N M r : Nat) : R :=
  sumBelow N (fun n => packet (fun k => a k * w k) M r n)

theorem packet_at_degree (a : Nat → R) (M n : Nat) :
    packet a M (n % M) n = a n := by
  simp [packet]

theorem packet_outside (a : Nat → R) (M r n : Nat) (hM : 0 < M) (hr : M ≤ r) :
    packet a M r n = 0 := by
  have hneq : n % M ≠ r := by have := Nat.mod_lt n hM; omega
  simp [packet, hneq]

theorem packet_reconstruction (a : Nat → R) (M n : Nat) (hM : 0 < M) :
    sumBelow M (fun r => packet a M r n) = a n := by
  unfold packet
  rw [sumBelow_single]
  simp [Nat.mod_lt n hM]

/-- Coefficientwise pushforward along a divisibility refinement. -/
theorem packet_refinement (a : Nat → R) (m M r n : Nat)
    (hM : 0 < M) (hdiv : m ∣ M) :
    sumBelow M (fun s => if s % m = r then packet a M s n else 0) =
      packet a m r n := by
  calc
    _ = sumBelow M (fun s =>
        if n % M = s then (if (n % M) % m = r then a n else 0) else 0) := by
      apply sumBelow_congr
      intro s _
      by_cases hs : n % M = s
      · subst s
        simp [packet]
      · simp [packet, hs]
    _ = packet a m r n := by
      rw [sumBelow_single]
      simp [Nat.mod_lt n hM, Nat.mod_mod_of_dvd n hdiv, packet]

theorem weightedPacket_zero (a w : Nat → R) (M r : Nat) :
    weightedPacket a w 0 M r = 0 := rfl

theorem weightedPacket_outside (a w : Nat → R) (N M r : Nat)
    (hM : 0 < M) (hr : M ≤ r) : weightedPacket a w N M r = 0 := by
  apply sumBelow_zero_of
  intro n _
  exact packet_outside (fun k => a k * w k) M r n hM hr

/-- The finite evaluated packets conserve the full finite weighted sum. -/
theorem weightedPacket_mass (a w : Nat → R) (N M : Nat) (hM : 0 < M) :
    sumBelow M (weightedPacket a w N M) = sumBelow N (fun n => a n * w n) := by
  unfold weightedPacket
  rw [sumBelow_swap]
  apply sumBelow_congr
  intro n _
  exact packet_reconstruction (fun k => a k * w k) M n hM

/-- Finite scalar packets push forward compatibly under `m ∣ M`. -/
theorem weightedPacket_refinement (a w : Nat → R) (N m M r : Nat)
    (hM : 0 < M) (hdiv : m ∣ M) :
    sumBelow M (fun s => if s % m = r then weightedPacket a w N M s else 0) =
      weightedPacket a w N m r := by
  calc
    _ = sumBelow M (fun s => sumBelow N (fun n =>
        if s % m = r then packet (fun k => a k * w k) M s n else 0)) := by
      apply sumBelow_congr
      intro s _
      by_cases hs : s % m = r
      · simp [hs, weightedPacket]
      · simp [hs, sumBelow_zero]
    _ = sumBelow N (fun n => sumBelow M (fun s =>
        if s % m = r then packet (fun k => a k * w k) M s n else 0)) :=
      sumBelow_swap M N _
    _ = weightedPacket a w N m r := by
      apply sumBelow_congr
      intro n _
      exact packet_refinement (fun k => a k * w k) m M r n hM hdiv

/-- Pairing a degree packet with any residue test function is exact. -/
theorem packet_pairing (a χ : Nat → R) (M n : Nat) (hM : 0 < M) :
    sumBelow M (fun r => packet a M r n * χ r) = a n * χ (n % M) := by
  calc
    _ = sumBelow M (fun r => if n % M = r then a n * χ (n % M) else 0) := by
      apply sumBelow_congr
      intro r _
      by_cases hr : n % M = r
      · subst r
        simp [packet]
      · simp [packet, hr, Semiring.zero_mul]
    _ = a n * χ (n % M) := by
      rw [sumBelow_single]
      simp [Nat.mod_lt n hM]

/-- Exact finite residue evaluation before any periodicity assumption. -/
theorem finite_residue_evaluation (a w χ : Nat → R) (N M : Nat) (hM : 0 < M) :
    sumBelow M (fun r => weightedPacket a w N M r * χ r) =
      sumBelow N (fun n => (a n * w n) * χ (n % M)) := by
  calc
    _ = sumBelow M (fun r => sumBelow N (fun n =>
        packet (fun k => a k * w k) M r n * χ r)) := by
      apply sumBelow_congr
      intro r _
      exact (sumBelow_mul_right N _ (χ r)).symm
    _ = sumBelow N (fun n => sumBelow M (fun r =>
        packet (fun k => a k * w k) M r n * χ r)) := sumBelow_swap M N _
    _ = sumBelow N (fun n => (a n * w n) * χ (n % M)) := by
      apply sumBelow_congr
      intro n _
      exact packet_pairing (fun k => a k * w k) χ M n hM

/-- This applies to every periodic test function, in particular to characters. -/
theorem finite_periodic_evaluation (a w χ : Nat → R) (N M : Nat)
    (hM : 0 < M) (hχ : ∀ n, χ (n % M) = χ n) :
    sumBelow M (fun r => weightedPacket a w N M r * χ r) =
      sumBelow N (fun n => (a n * w n) * χ n) := by
  rw [finite_residue_evaluation a w χ N M hM]
  apply sumBelow_congr
  intro n _
  rw [hχ n]

theorem root_power_multiple (z : R) (M k : Nat) (hz : z ^ M = 1) :
    z ^ (M * k) = 1 := by
  induction k with
  | zero => simp [Semiring.pow_zero]
  | succ k ih => rw [Nat.mul_succ, Semiring.pow_add, ih, hz, Semiring.mul_one]

/-- A root of order dividing `M` gives a periodic power function. -/
theorem root_power_mod (z : R) (M n : Nat) (hz : z ^ M = 1) :
    z ^ (n % M) = z ^ n := by
  symm
  calc
    z ^ n = z ^ (n % M + M * (n / M)) := by rw [Nat.mod_add_div]
    _ = z ^ (n % M) * z ^ (M * (n / M)) := Semiring.pow_add z _ _
    _ = z ^ (n % M) := by rw [root_power_multiple z M (n / M) hz, Semiring.mul_one]

theorem root_of_dividing_order (z : R) (b M : Nat)
    (hdiv : b ∣ M) (hz : z ^ b = 1) : z ^ M = 1 := by
  obtain ⟨k, rfl⟩ := hdiv
  exact root_power_multiple z b k hz

end Basic

section Commutative

variable {R : Type u} [CommRing R]

theorem product_power (t z : R) (n : Nat) : (t * z) ^ n = t ^ n * z ^ n := by
  induction n with
  | zero => simp [Semiring.pow_zero, Semiring.one_mul]
  | succ n ih =>
      rw [Semiring.pow_succ, Semiring.pow_succ, Semiring.pow_succ, ih]
      grind

/-- The finite Fourier/root identity for a weighted truncation. No primitive
root or exact-order claim is inferred from `z ^ M = 1`. -/
theorem finite_root_evaluation (a : Nat → R) (t z : R) (N M : Nat)
    (hM : 0 < M) (hz : z ^ M = 1) :
    sumBelow M (fun r => weightedPacket a (fun n => t ^ n) N M r * z ^ r) =
      sumBelow N (fun n => a n * (t * z) ^ n) := by
  rw [finite_periodic_evaluation a (fun n => t ^ n) (fun n => z ^ n) N M hM
    (fun n => root_power_mod z M n hz)]
  apply sumBelow_congr
  intro n _
  rw [product_power, Semiring.mul_assoc]

/-- A target root whose order divides a retained packet period is observable
from those packets. This uses the same divisibility criterion as finite CRT
target transport, with no claim that arbitrary roots have exact order `b`. -/
theorem finite_root_evaluation_of_dvd (a : Nat → R) (t z : R) (N b M : Nat)
    (hM : 0 < M) (hdiv : b ∣ M) (hz : z ^ b = 1) :
    sumBelow M (fun r => weightedPacket a (fun n => t ^ n) N M r * z ^ r) =
      sumBelow N (fun n => a n * (t * z) ^ n) :=
  finite_root_evaluation a t z N M hM (root_of_dividing_order z b M hdiv hz)

end Commutative

end KElimination.ResidueSeries

#print axioms KElimination.ResidueSeries.sumBelow_zero_bound
#print axioms KElimination.ResidueSeries.sumBelow_succ
#print axioms KElimination.ResidueSeries.sumBelow_congr
#print axioms KElimination.ResidueSeries.sumBelow_zero
#print axioms KElimination.ResidueSeries.sumBelow_zero_of
#print axioms KElimination.ResidueSeries.sumBelow_add
#print axioms KElimination.ResidueSeries.sumBelow_mul_right
#print axioms KElimination.ResidueSeries.sumBelow_mul_left
#print axioms KElimination.ResidueSeries.sumBelow_swap
#print axioms KElimination.ResidueSeries.sumBelow_single
#print axioms KElimination.ResidueSeries.sumBelow_extend_one
#print axioms KElimination.ResidueSeries.sumBelow_eq_of_tail_zero
#print axioms KElimination.ResidueSeries.packet_at_degree
#print axioms KElimination.ResidueSeries.packet_outside
#print axioms KElimination.ResidueSeries.packet_reconstruction
#print axioms KElimination.ResidueSeries.packet_refinement
#print axioms KElimination.ResidueSeries.weightedPacket_zero
#print axioms KElimination.ResidueSeries.weightedPacket_outside
#print axioms KElimination.ResidueSeries.weightedPacket_mass
#print axioms KElimination.ResidueSeries.weightedPacket_refinement
#print axioms KElimination.ResidueSeries.packet_pairing
#print axioms KElimination.ResidueSeries.finite_residue_evaluation
#print axioms KElimination.ResidueSeries.finite_periodic_evaluation
#print axioms KElimination.ResidueSeries.root_power_multiple
#print axioms KElimination.ResidueSeries.root_power_mod
#print axioms KElimination.ResidueSeries.root_of_dividing_order
#print axioms KElimination.ResidueSeries.product_power
#print axioms KElimination.ResidueSeries.finite_root_evaluation
#print axioms KElimination.ResidueSeries.finite_root_evaluation_of_dvd
