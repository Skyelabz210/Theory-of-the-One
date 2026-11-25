import Mathlib.Analysis.Complex.Basic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.Tactic.Ring

/-! The complete denominator block of Watson's third-order φ at order 34. -/

namespace MockThetaAnalytic
open Polynomial

theorem prod_one_add_pow {ζ : ℂ} {L : ℕ} (hL : 0 < L)
    (hζ : IsPrimitiveRoot ζ L) (a : ℂ) :
    (∏ j ∈ Finset.range L, (1 + a * ζ^j)) = 1 - (-a)^L := by
  classical
  letI : NeZero L := ⟨hL.ne'⟩
  have h := hζ.pow_sub_pow_eq_prod_sub_mul (1 : ℂ) (-a) hL
  simp only [one_pow, mul_neg, sub_neg_eq_add] at h
  rw [h]
  apply Finset.prod_bij (fun j _ => ζ^j)
  · intro j _
    exact (mem_nthRootsFinset hL 1).2 (by rw [pow_right_comm, hζ.pow_eq_one, one_pow])
  · intro i hi j hj heq
    exact hζ.pow_inj (Finset.mem_range.mp hi) (Finset.mem_range.mp hj) heq
  · intro y hy
    obtain ⟨j, hj, heq⟩ := hζ.eq_pow_of_pow_eq_one ((mem_nthRootsFinset hL 1).1 hy)
    exact ⟨j, Finset.mem_range.mpr hj, heq⟩
  · intro j _
    rw [mul_comm]

/-- The halfway power of a primitive root of even order is −1. -/
theorem primitive_even_half_power {ζ : ℂ} {k : ℕ} (hk : 0 < k)
    (hζ : IsPrimitiveRoot ζ (2*k)) : ζ^k = -1 := by
  have hs : (ζ^k)^2 = 1 := by rw [← pow_mul, Nat.mul_comm k, hζ.pow_eq_one]
  exact (sq_eq_one_iff.mp hs).resolve_left
    (hζ.pow_ne_one_of_pos_of_lt hk.ne' (by omega))

/-- The selected parity of denominator factors has product two over a block. -/
theorem watson_denominator_block {ζ : ℂ} {k : ℕ} (hk : 0 < k)
    (hζ : IsPrimitiveRoot ζ (2*k)) (c : ℕ) (hc : Odd (k+c)) (r : ℕ) :
    (∏ j ∈ Finset.range k, (1+ζ^(2*(r+j)+c))) = 2 := by
  have hη : IsPrimitiveRoot (ζ^2) k := by
    simpa using hζ.pow_of_dvd (by decide : 2 ≠ 0) (dvd_mul_right 2 k)
  have h := prod_one_add_pow hk hη (ζ^(2*r+c))
  calc
    _ = ∏ j ∈ Finset.range k, (1+ζ^(2*r+c)*(ζ^2)^j) := by
      apply Finset.prod_congr rfl
      intro j _
      rw [← pow_mul, ← pow_add]
      congr 2
      omega
    _ = _ := by
      rw [h, neg_pow, pow_right_comm ζ, primitive_even_half_power hk hζ, pow_add (-1:ℂ) (2*r),
        pow_mul (-1:ℂ) 2]
      norm_num
      rw [← pow_add, hc.neg_one_pow]
      norm_num

/-- Every shifted block of seventeen even powers at a primitive 34th root
has product 1+s^17. In particular the unsmoothed denominator doubles per block. -/
theorem order34_even_block (ζ : ℂ) (hζ : IsPrimitiveRoot ζ 34) (r : ℕ) (s : ℝ) :
    (∏ j ∈ Finset.range 17, (1 + (s : ℂ) * ζ^(2*r + 2*j + 2))) = 1 + (s : ℂ)^17 := by
  have hη : IsPrimitiveRoot (ζ^2) 17 := hζ.pow_of_dvd (by decide) (by decide)
  have h := prod_one_add_pow (by decide) hη ((s : ℂ) * (ζ^2)^(r+1))
  convert h using 1
  · apply Finset.prod_congr rfl
    intro j _
    rw [mul_assoc, ← pow_add, ← pow_mul]
    congr 3
    omega
  · rw [neg_pow, mul_pow, pow_right_comm, hη.pow_eq_one, one_pow, mul_one]
    ring

end MockThetaAnalytic
