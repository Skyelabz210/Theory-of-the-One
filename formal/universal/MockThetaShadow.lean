import MockTheta

/-! The two Fourier series attached to the first component of the third-order
completion in Bringmann–Ono, “The f(q) mock theta function conjecture and
partition ranks”, equations (2.2)–(2.5) and §2. Write q=u²⁴. The holomorphic
component is u⁻¹ f(u²⁴). The primitive integral unary theta series below is
−6g₁(24τ), in the variable u=exp(2πiτ). Its coefficient at u^(m²) is +m for
m ≡ 1 (mod 6), −m for m ≡ 5 (mod 6), and zero otherwise.
-/

namespace KElimination.MockThetaShadow

open Lean.Grind KElimination.ResidueSeries KElimination.MockTheta

universe u
variable {R : Type u} [CommRing R]
attribute [local instance] Ring.intCast

/-- Exponent of the original degree-d coefficient after the change of variable. -/
def normalizedExponent (d : Nat) : Int := 24 * (d : Int) - 1

/-- Formal Laurent coefficient of u⁻¹f(u²⁴). -/
def holomorphicCoeff (k : Int) : R :=
  if -1 ≤ k ∧ (k + 1) % 24 = 0 then mockCoeff ((k+1) / 24).toNat else 0

theorem holomorphicCoeff_at_degree (d : Nat) :
    (holomorphicCoeff (normalizedExponent d) : R) = mockCoeff d := by
  have h : -1 ≤ normalizedExponent d ∧ (normalizedExponent d + 1) % 24 = 0 := by
    unfold normalizedExponent
    omega
  rw [holomorphicCoeff, if_pos h]
  congr 1
  unfold normalizedExponent
  omega

theorem exponent_range_iff (k : Int) :
    (∃ d : Nat, normalizedExponent d = k) ↔ -1 ≤ k ∧ k % 24 = 23 := by
  constructor
  · rintro ⟨d, rfl⟩
    unfold normalizedExponent
    omega
  · rintro ⟨hk, hm⟩
    refine ⟨((k+1)/24).toNat, ?_⟩
    unfold normalizedExponent
    omega

theorem holomorphicCoeff_off_lattice (k : Int) (hk : k < -1 ∨ k % 24 ≠ 23) :
    (holomorphicCoeff k : R) = 0 := by
  exact if_neg (by omega)

/-- Evaluate an integral Laurent power using the supplied inverse for negative degrees. -/
def laurentPower (v vinv : R) : Int → R
  | .ofNat n => v ^ n
  | .negSucc n => vinv ^ (n + 1)

theorem laurentPower_normalized (d : Nat) (v vinv : R) (hinv : v * vinv = 1) :
    laurentPower v vinv (normalizedExponent d) = vinv * (v ^ 24) ^ d := by
  have hpow (k : Nat) : v ^ (24*k) = (v^24)^k := by
    induction k with
    | zero => simp [Semiring.pow_zero]
    | succ k ih =>
      rw [Nat.mul_succ, Semiring.pow_add, ih]
      exact (Semiring.pow_succ (v^24) k).symm
  cases d with
  | zero =>
    change vinv ^ 1 = vinv * (v ^ 24) ^ 0
    rw [Semiring.pow_one, Semiring.pow_zero, Semiring.mul_one]
  | succ d =>
    have hd : normalizedExponent (d + 1) = Int.ofNat (24*d + 23) := by
      simp only [normalizedExponent, Int.ofNat_eq_natCast]
      omega
    rw [hd]
    change v ^ (24*d + 23) = vinv * (v^24)^(d+1)
    rw [Semiring.pow_add, hpow, Semiring.pow_succ (v^24) d]
    have h24 : v^24 = v^23 * v := Semiring.pow_succ v 23
    grind

/-- Truncate by the number N of original coefficient degrees and evaluate
at the reindexed Laurent exponents, including the polar term at −1. -/
def normalizedTrunc (N : Nat) (v vinv : R) : R :=
  sumBelow N (fun d => holomorphicCoeff (normalizedExponent d) *
    laurentPower v vinv (normalizedExponent d))

theorem normalizedTrunc_eq (N : Nat) (v vinv : R) (hinv : v * vinv = 1) :
    normalizedTrunc N v vinv = vinv * mockPolynomial N (v ^ 24) := by
  unfold normalizedTrunc mockPolynomial
  rw [← sumBelow_mul_left]
  apply sumBelow_congr
  intro d _
  rw [holomorphicCoeff_at_degree, laurentPower_normalized d v vinv hinv]
  grind

/-- The sign character of the positive root magnitude in −6g₁(24τ). -/
def shadowSign (m : Nat) : Int :=
  if m % 6 = 1 then 1 else if m % 6 = 5 then -1 else 0

def shadowWeight (m : Nat) : Int := shadowSign m * (m : Int)

theorem shadowSign_period (m : Nat) : shadowSign (m+6) = shadowSign m := by simp [shadowSign]

theorem shadowWeight_natAbs_le (m : Nat) : (shadowWeight m).natAbs ≤ m := by
  unfold shadowWeight shadowSign
  split <;> (try split) <;> simp

theorem shadowWeight_ne_zero_iff (m : Nat) :
    shadowWeight m ≠ 0 ↔ m % 6 = 1 ∨ m % 6 = 5 := by
  unfold shadowWeight shadowSign
  split <;> (try split) <;> simp_all <;> omega

/-- On the signed summation lattice of the published g₁, the positive-root
weight recovers the signed integer 6n+1, including negative indices. -/
theorem shadowWeight_signed_lattice (n : Int) :
    shadowWeight (6*n + 1).natAbs = 6*n + 1 := by
  cases n with
  | ofNat n =>
    have he : 6 * (n : Int) + 1 = ((6*n + 1 : Nat) : Int) := by omega
    simp only [Int.ofNat_eq_natCast] at *
    rw [he, Int.natAbs_natCast]
    simp [shadowWeight, shadowSign, Nat.add_mod]
  | negSucc n =>
    have he : 6 * Int.negSucc n + 1 = -((6*n + 5 : Nat) : Int) := by omega
    rw [he, Int.natAbs_neg, Int.natAbs_natCast]
    simp [shadowWeight, shadowSign, Nat.add_mod]

/-- For each nonzero weight its signed value represents the source lattice,
and its magnitude is the original positive index. -/
theorem shadowWeight_lattice_of_ne_zero (m : Nat) (hm : shadowWeight m ≠ 0) :
    (shadowWeight m) % 6 = 1 ∧ (shadowWeight m).natAbs = m := by
  rcases (shadowWeight_ne_zero_iff m).mp hm with h | h
  · simp [shadowWeight, shadowSign, h]; omega
  · simp [shadowWeight, shadowSign, h]; omega

/-- Coefficient at degree d of the integral square-supported theta series. -/
def shadowCoeff (d : Nat) : Int :=
  sumBelow (d+1) (fun m => if m*m = d then shadowWeight m else 0)

theorem shadowCoeff_stable (d N : Nat) (hN : d < N*N) :
    sumBelow N (fun m => if m*m = d then shadowWeight m else 0) = shadowCoeff d :=
  squareSum_stable _ (fun _ _ hk => if_neg (Nat.ne_of_gt hk)) d N hN

theorem shadowCoeff_square (m : Nat) : shadowCoeff (m*m) = shadowWeight m := by
  unfold shadowCoeff
  calc
    _ = sumBelow (m*m+1) (fun j => if m = j then shadowWeight m else 0) := by
      apply sumBelow_congr
      intro j _
      by_cases h : j = m
      · subst j; simp
      · simp [Nat.mul_self_inj, h, Ne.symm h]
    _ = _ := by
      rw [sumBelow_single, if_pos (Nat.lt_succ_of_le (Nat.le_mul_self m))]

theorem shadowCoeff_ne_zero_iff (d : Nat) :
    shadowCoeff d ≠ 0 ↔ ∃ m : Nat, d = m*m ∧ (m % 6 = 1 ∨ m % 6 = 5) := by
  constructor
  · intro hd
    apply Classical.byContradiction
    intro hn
    apply hd
    apply sumBelow_zero_of
    intro m _
    by_cases h : m*m = d
    · rw [if_pos h]
      apply Classical.byContradiction
      intro hw
      exact hn ⟨m, h.symm, (shadowWeight_ne_zero_iff m).mp hw⟩
    · exact if_neg h
  · rintro ⟨m, rfl, hm⟩
    rw [shadowCoeff_square, shadowWeight_ne_zero_iff]
    exact hm

theorem shadowCoeff_mod_24 (d : Nat) (hd : shadowCoeff d ≠ 0) : d % 24 = 1 := by
  obtain ⟨m, rfl, hm⟩ := (shadowCoeff_ne_zero_iff d).mp hd
  have h : m % 24 = 1 ∨ m % 24 = 5 ∨ m % 24 = 7 ∨ m % 24 = 11 ∨
      m % 24 = 13 ∨ m % 24 = 17 ∨ m % 24 = 19 ∨ m % 24 = 23 := by omega
  rw [Nat.mul_mod]
  rcases h with h|h|h|h|h|h|h|h <;> rw [h] <;> decide

theorem eleven_dvd_shadowCoeff_square_iff (m : Nat) (hm : shadowWeight m ≠ 0) :
    (11 : Int) ∣ shadowCoeff (m*m) ↔ 11 ∣ m := by
  rw [shadowCoeff_square]
  rcases (shadowWeight_ne_zero_iff m).mp hm with h | h <;>
    simp [shadowWeight, shadowSign, h] <;> exact Int.ofNat_dvd

/-- On the nonzero support, bin zero modulo eleven consists exactly of
coefficients whose integral amplitude is divisible by eleven. -/
theorem shadowCoeff_bin_zero_iff (d : Nat) (hd : shadowCoeff d ≠ 0) :
    d % 11 = 0 ↔ (11 : Int) ∣ shadowCoeff d := by
  obtain ⟨m, rfl, hm⟩ := (shadowCoeff_ne_zero_iff d).mp hd
  rw [eleven_dvd_shadowCoeff_square_iff m ((shadowWeight_ne_zero_iff m).mpr hm),
    Nat.dvd_iff_mod_eq_zero, Nat.mul_mod]
  have reduced : ∀ a : Fin 11, (a.val * a.val) % 11 = 0 ↔ a.val = 0 := by decide
  exact reduced ⟨m % 11, Nat.mod_lt _ (by decide)⟩

/-- A residue sector modulo eleven has a nonzero coefficient precisely at the
six square residues. For those residues in the displayed order, witnesses have
magnitudes 11, 1, 5, 13, 7 and 19. -/
theorem shadowCoeff_sector_support_iff (r : Fin 11) :
    (∃ d : Nat, d % 11 = r.val ∧ shadowCoeff d ≠ 0) ↔
      r.val ∈ ([0, 1, 3, 4, 5, 9] : List Nat) := by
  constructor
  · rintro ⟨d, hr, hd⟩
    obtain ⟨m, rfl, _⟩ := (shadowCoeff_ne_zero_iff d).mp hd
    have residues : ∀ k : Fin 11,
        (k.val * k.val) % 11 ∈ ([0, 1, 3, 4, 5, 9] : List Nat) := by decide
    rw [← hr, Nat.mul_mod]
    exact residues ⟨m % 11, Nat.mod_lt _ (by decide)⟩
  · intro hr
    have witness (m : Nat) (hm : m % 6 = 1 ∨ m % 6 = 5) (hbin : (m*m) % 11 = r.val) :
        ∃ d : Nat, d % 11 = r.val ∧ shadowCoeff d ≠ 0 :=
      ⟨m*m, hbin, (shadowCoeff_ne_zero_iff _).mpr ⟨m, rfl, hm⟩⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with h|h|h|h|h|h
    · exact witness 11 (by decide) h.symm
    · exact witness 1 (by decide) h.symm
    · exact witness 5 (by decide) h.symm
    · exact witness 13 (by decide) h.symm
    · exact witness 7 (by decide) h.symm
    · exact witness 19 (by decide) h.symm

/-- Truncation by ordinary u-degree, evaluated in the supplied ring. -/
def shadowTrunc (N : Nat) (v : R) : R :=
  sumBelow N (fun d => Int.cast (shadowCoeff d) * v^d)

/-- The polynomial formed from the Fourier coefficients through degree N−1
is the finite unary theta sum over square exponents in the same range. -/
theorem shadowTrunc_eq_magnitude_sum (N : Nat) (v : R) :
    shadowTrunc N v = sumBelow N (fun m =>
      if m*m < N then Int.cast (shadowWeight m) * v^(m*m) else 0) := by
  have hcast (B : Nat) (f : Nat → Int) :
      (Int.cast (sumBelow B f) : R) = sumBelow B (fun k => Int.cast (f k)) := by
    induction B with
    | zero => exact Ring.intCast_zero
    | succ k ih => rw [sumBelow_succ, sumBelow_succ, Ring.intCast_add, ih]
  calc
    _ = sumBelow N (fun d => sumBelow N (fun m =>
        if m*m = d then (Int.cast (shadowWeight m) : R) * v^(m*m) else 0)) := by
      apply sumBelow_congr
      intro d hd
      rw [← shadowCoeff_stable d N (Nat.lt_of_lt_of_le hd (Nat.le_mul_self N)), hcast,
        ← sumBelow_mul_right]
      apply sumBelow_congr
      intro m _
      by_cases h : m*m = d
      · simp [h]
      · simp only [if_neg h, Ring.intCast_zero, Semiring.zero_mul]
    _ = sumBelow N (fun m => sumBelow N (fun d =>
        if m*m = d then Int.cast (shadowWeight m) * v^(m*m) else 0)) := sumBelow_swap N N _
    _ = _ := by
      apply sumBelow_congr
      intro m _
      exact sumBelow_single N (m*m) _

end KElimination.MockThetaShadow

#print axioms KElimination.MockThetaShadow.holomorphicCoeff_at_degree
#print axioms KElimination.MockThetaShadow.exponent_range_iff
#print axioms KElimination.MockThetaShadow.holomorphicCoeff_off_lattice
#print axioms KElimination.MockThetaShadow.laurentPower_normalized
#print axioms KElimination.MockThetaShadow.normalizedTrunc_eq
#print axioms KElimination.MockThetaShadow.shadowSign_period
#print axioms KElimination.MockThetaShadow.shadowWeight_natAbs_le
#print axioms KElimination.MockThetaShadow.shadowWeight_ne_zero_iff
#print axioms KElimination.MockThetaShadow.shadowWeight_signed_lattice
#print axioms KElimination.MockThetaShadow.shadowWeight_lattice_of_ne_zero
#print axioms KElimination.MockThetaShadow.shadowCoeff_stable
#print axioms KElimination.MockThetaShadow.shadowCoeff_square
#print axioms KElimination.MockThetaShadow.shadowCoeff_ne_zero_iff
#print axioms KElimination.MockThetaShadow.shadowCoeff_mod_24
#print axioms KElimination.MockThetaShadow.eleven_dvd_shadowCoeff_square_iff
#print axioms KElimination.MockThetaShadow.shadowCoeff_bin_zero_iff
#print axioms KElimination.MockThetaShadow.shadowCoeff_sector_support_iff
#print axioms KElimination.MockThetaShadow.shadowTrunc_eq_magnitude_sum
