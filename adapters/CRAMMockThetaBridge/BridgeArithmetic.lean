import Std

/-! Arithmetic for transporting a quotient residue to a target lane.
The period b / gcd M b is defined for a positive target b. -/

namespace CRAMMockThetaBridge

theorem nat_dvd_mul_iff_period_dvd (M b k : Nat) (hb : 0 < b) :
    b / Nat.gcd M b ∣ k ↔ b ∣ M * k := by
  rw [Nat.div_dvd_iff_dvd_mul (Nat.gcd_dvd_right M b)
    (Nat.gcd_pos_of_pos_right M hb)]
  rw [Nat.gcd_comm M b, Nat.dvd_gcd_mul_iff_dvd_mul]

theorem int_dvd_mul_iff_period_dvd (M b : Nat) (k : Int) (hb : 0 < b) :
    ((b / Nat.gcd M b : Nat) : Int) ∣ k ↔ (b : Int) ∣ (M : Int) * k := by
  simpa only [Int.ofNat_dvd_left, Int.natAbs_mul, Int.natAbs_natCast] using
    nat_dvd_mul_iff_period_dvd M b k.natAbs hb

/-- Equality of quotient coordinates modulo H transports through r + M*k
to equality modulo b whenever the reduced target period divides H. -/
theorem fiber_constant_of_period_dvd (M b H : Nat) (r k₁ k₂ : Int)
    (hb : 0 < b) (hperiod : b / Nat.gcd M b ∣ H)
    (hk : k₁ % (H : Int) = k₂ % (H : Int)) :
    (r + (M : Int) * k₁) % (b : Int) = (r + (M : Int) * k₂) % (b : Int) := by
  have hd : (H : Int) ∣ k₁ - k₂ :=
    Int.dvd_of_emod_eq_zero (Int.emod_eq_emod_iff_emod_sub_eq_zero.mp hk)
  have hmul := (int_dvd_mul_iff_period_dvd M b (k₁ - k₂) hb).mp
    (Int.dvd_trans (Int.ofNat_dvd.mpr hperiod) hd)
  apply Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr
  have heq : r + (M : Int) * k₁ - (r + (M : Int) * k₂) = (M : Int) * (k₁ - k₂) := by
    grind
  rw [heq]
  exact Int.emod_eq_zero_of_dvd hmul

end CRAMMockThetaBridge

#print axioms CRAMMockThetaBridge.nat_dvd_mul_iff_period_dvd
#print axioms CRAMMockThetaBridge.int_dvd_mul_iff_period_dvd
#print axioms CRAMMockThetaBridge.fiber_constant_of_period_dvd
