import Mathlib.Analysis.Complex.Basic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.Tactic.Ring

/-! The complete denominator block of Watson's third-order φ at order 34. -/

namespace MockThetaAnalytic
open Polynomial

private theorem prod_one_add_pow {ζ : ℂ} {L : ℕ} (hL : 0 < L)
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
