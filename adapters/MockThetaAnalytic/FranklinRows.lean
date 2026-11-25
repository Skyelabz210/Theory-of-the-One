import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.Nat.Find

/-! Franklin's involution on the strictly decreasing rows of a distinct
partition. Positions past the last row are zero. -/

namespace MockThetaAnalytic.Franklin

open Finset
open scoped BigOperators
noncomputable section

@[ext] structure Rows where
  length : ℕ
  part : ℕ → ℕ
  desc : ∀ i < length, part (i+1) < part i
  zero : ∀ i ≥ length, part i = 0

def size (p : Rows) : ℕ := ∑ i ∈ range p.length, p.part i

def smallest (p : Rows) : ℕ := p.part (p.length-1)

private abbrev gap (p : Rows) (i : ℕ) : Prop :=
  p.length ≤ i+1 ∨ p.part (i+1)+1 < p.part i

private theorem exists_gap (p : Rows) : ∃ i, gap p i :=
  ⟨p.length, Or.inl (by omega)⟩

def slope (p : Rows) : ℕ := Nat.find (exists_gap p)+1

theorem slope_pos (p : Rows) : 0 < slope p := Nat.zero_lt_succ _

theorem slope_le (p : Rows) (h : 0 < p.length) : slope p ≤ p.length := by
  have hg : gap p (p.length-1) := Or.inl (by omega)
  have hm := Nat.find_min' (exists_gap p) hg
  unfold slope
  omega

theorem consecutive (p : Rows) {i : ℕ} (h : i+1 < slope p) :
    p.part i = p.part (i+1)+1 := by
  have hn := Nat.find_min (exists_gap p) (m:=i) (by unfold slope at h; omega)
  have hi : i < p.length := by
    by_contra! hl
    exact hn (Or.inl (by omega))
  have hp := p.desc _ hi
  by_contra! he
  exact hn (Or.inr (by omega))

theorem break_at_slope (p : Rows) (h : slope p < p.length) :
    p.part (slope p)+1 < p.part (slope p-1) := by
  have hs := Nat.find_spec (exists_gap p)
  unfold slope at h ⊢
  simp only [Nat.add_sub_cancel]
  exact hs.resolve_left (by omega)

private theorem part_pos (p : Rows) {i : ℕ} (h : i < p.length) : 0 < p.part i :=
  Nat.zero_le (p.part (i+1)) |>.trans_lt (p.desc i h)

private theorem smallest_pos (p : Rows) (h : 0 < p.length) : 0 < smallest p :=
  part_pos p (by omega)

private theorem consecutive_slope (p : Rows) {k : ℕ} (hk : 0 < k) (hl : k ≤ p.length)
    (h : ∀ i, i+1 < k → p.part i = p.part (i+1)+1)
    (hb : k < p.length → p.part k + 1 < p.part (k-1)) : slope p = k := by
  have hf : Nat.find (exists_gap p) = k-1 := by
    apply (Nat.find_eq_iff _).2
    constructor
    · by_cases he : k = p.length
      · exact Or.inl (by omega)
      · exact Or.inr (by have hb' := hb (by omega); rwa [show k-1+1=k by omega])
    · intro i hi hp
      have hl' := h i (by omega)
      exact hp.elim (by omega) (by omega)
  unfold slope
  omega

private theorem slope_ge_of_consecutive (p : Rows) {k : ℕ} (hl : k ≤ p.length)
    (h : ∀ i, i+1 < k → p.part i = p.part (i+1)+1) : k ≤ slope p := by
  by_contra! hk
  have hs := slope_pos p
  have hb := break_at_slope p (by omega : slope p < p.length)
  have he := h (slope p-1) (by omega)
  rw [show slope p-1+1=slope p by omega] at he
  omega

def CanRaise (p : Rows) : Prop := smallest p ≤ slope p ∧ smallest p < p.length

def CanLower (p : Rows) : Prop :=
  slope p < smallest p ∧ (slope p < p.length ∨ slope p+1 < smallest p)

private theorem raise_length_pos (p : Rows) (h : CanRaise p) : 0 < p.length-1 := by
  have hs := smallest_pos p (by have := h.2; omega)
  have := h.2
  omega

def raise (p : Rows) (_ : CanRaise p) : Rows where
  length := p.length-1
  part i := if i < p.length-1 then p.part i + (if i < smallest p then 1 else 0) else 0
  desc := by
    intro i hi
    have hp := p.desc i (by omega : i < p.length)
    simp only [if_pos hi]
    split_ifs <;> omega
  zero := by intro i hi; simp [Nat.not_lt.mpr hi]

def lower (p : Rows) (h : CanLower p) : Rows where
  length := p.length+1
  part i := if i < p.length then p.part i - (if i < slope p then 1 else 0)
    else if i = p.length then slope p else 0
  desc := by
    intro i hi
    by_cases hp : i < p.length
    · by_cases hn : i+1 < p.length
      · have hd := p.desc i hp
        have hpos := part_pos p hn
        simp only [if_pos hp, if_pos hn]
        by_cases hc : i+1 = slope p
        · have hb := break_at_slope p (by omega : slope p < p.length)
          rw [← hc, Nat.add_sub_cancel] at hb
          split_ifs <;> omega
        · split_ifs <;> omega
      · have eq : i+1=p.length := by omega
        have hm : p.part i = smallest p := by unfold smallest; congr 1; omega
        have hh : slope p ≤ p.length := slope_le p (by omega)
        simp only [if_pos hp, if_neg hn, if_pos eq, hm]
        rcases h with ⟨h₁,h₂|h₂⟩ <;> split_ifs <;> omega
    · have eq : i = p.length := by omega
      simp [eq, slope_pos]
  zero := by
    intro i hi
    simp [show ¬i < p.length by omega, show i ≠ p.length by omega]

theorem raise_slope (p : Rows) (h : CanRaise p) : slope (raise p h) = smallest p := by
  have hx := smallest_pos p (by have := h.2; omega)
  have hlen : smallest p ≤ p.length-1 := by have := h.2; omega
  apply consecutive_slope _ hx hlen
  · intro i hi
    have hc := consecutive p (hi.trans_le h.1)
    simp only [raise, if_pos (by omega : i < p.length-1),
      if_pos (by omega : i+1 < p.length-1),
      if_pos (by omega : i < smallest p), if_pos hi]
    omega
  · intro hs
    change smallest p < p.length-1 at hs
    have hd := p.desc (smallest p-1) (by omega : smallest p-1 < p.length)
    rw [show smallest p-1+1=smallest p by omega] at hd
    simp only [raise, if_pos hs, if_pos (by omega : smallest p-1 < p.length-1),
      lt_irrefl, if_false, if_pos (by omega : smallest p-1 < smallest p)]
    omega

theorem raise_canLower (p : Rows) (h : CanRaise p) : CanLower (raise p h) := by
  have hlen := raise_length_pos p h
  have hh : p.length-1-1+1 = p.length-1 := by omega
  have hp := p.desc (p.length-1-1) (by omega : p.length-1-1 < p.length)
  rw [hh] at hp
  have hlt : p.length-1-1 < p.length-1 := by omega
  have hm : p.part (p.length-1) = smallest p := rfl
  rw [hm] at hp
  unfold CanLower
  rw [raise_slope]
  simp only [smallest, raise, if_pos hlt]
  constructor
  · split_ifs <;> omega
  · by_cases hl : smallest p < p.length-1
    · exact Or.inl hl
    · right
      simp only [hm, if_pos (by have := h.2; omega : p.length-1-1 < smallest p)]
      omega

theorem lower_smallest (p : Rows) (h : CanLower p) : smallest (lower p h) = slope p := by
  simp [lower, smallest]

theorem lower_canRaise (p : Rows) (h : CanLower p) : CanRaise (lower p h) := by
  have hlen : 0 < p.length := by
    by_contra! hn
    have hz := p.zero (p.length-1) (by omega)
    have hh := h.1
    unfold smallest at hh
    omega
  have hsl := slope_le p hlen
  refine ⟨?_, ?_⟩ <;> rw [lower_smallest]
  · apply slope_ge_of_consecutive _ (by simpa [lower] using Nat.le_succ_of_le hsl)
    intro i hi
    have hh := consecutive p hi
    have hp := part_pos p (by omega : i+1 < p.length)
    simp only [lower, if_pos hi, if_pos (by omega : i < slope p),
      if_pos (by omega : i < p.length), if_pos (by omega : i+1 < p.length)]
    omega
  · simpa [lower] using Nat.lt_succ_of_le hsl

theorem lower_raise (p : Rows) (h : CanRaise p) : lower (raise p h) (raise_canLower p h) = p := by
  have hp : 0 < p.length := by have := h.2; omega
  apply Rows.ext (by simp [lower, raise, show p.length-1+1=p.length by omega])
  funext i
  change (if i < p.length-1 then (raise p h).part i -
      (if i < slope (raise p h) then 1 else 0)
    else if i=p.length-1 then slope (raise p h) else 0) = p.part i
  rw [raise_slope]
  by_cases hi : i < p.length-1
  · simp [hi, raise]
  · by_cases he : i = p.length-1
    · simp [he, smallest]
    · simp [hi, he, p.zero i (by omega)]

theorem raise_lower (p : Rows) (h : CanLower p) : raise (lower p h) (lower_canRaise p h) = p := by
  apply Rows.ext (by simp [lower, raise])
  funext i
  change (if i < p.length+1-1 then (lower p h).part i +
    (if i < smallest (lower p h) then 1 else 0) else 0) = p.part i
  rw [lower_smallest, Nat.add_sub_cancel]
  by_cases hi : i < p.length
  · have hp := part_pos p hi
    simp only [lower, if_pos hi]
    split_ifs <;> omega
  · simp [hi, p.zero i (by omega)]

theorem raise_size (p : Rows) (h : CanRaise p) : size (raise p h) = size p := by
  have hh : p.length-1+1 = p.length := by have := h.2; omega
  have hcut : smallest p ≤ p.length-1 := by have := h.2; omega
  have hfilter : (range (p.length-1)).filter (· < smallest p) = range (smallest p) := by
    ext i
    simp only [mem_filter, mem_range]
    omega
  unfold size
  rw [← hh, sum_range_succ _ (p.length-1)]
  change (∑ i ∈ range (p.length-1), (raise p h).part i) = _
  have hsum : ∑ i ∈ range (p.length-1), (raise p h).part i =
      ∑ i ∈ range (p.length-1), (p.part i + if i < smallest p then 1 else 0) := by
    apply sum_congr rfl
    intro i hi
    simp [raise, mem_range.mp hi]
  rw [hsum, sum_add_distrib, sum_ite, hfilter]
  simp [smallest]
  rfl

theorem lower_size (p : Rows) (h : CanLower p) : size (lower p h) = size p := by
  rw [← raise_size (lower p h) (lower_canRaise p h), raise_lower p h]

open Classical in
noncomputable def flip (p : Rows) : Rows :=
  if h : CanRaise p then raise p h
  else if h : CanLower p then lower p h else p

private theorem disjoint_moves (p : Rows) (h : CanLower p) : ¬ CanRaise p :=
  fun g => (Nat.not_lt_of_ge g.1) h.1

theorem flip_involution (p : Rows) : flip (flip p) = p := by
  by_cases h : CanRaise p
  · have hr : flip p = raise p h := by simp [flip, h]
    rw [hr]
    have hl : CanLower (raise p h) := raise_canLower p h
    rw [show flip (raise p h) = lower (raise p h) hl by simp [flip, disjoint_moves _ hl, hl]]
    exact lower_raise p h
  · by_cases hl : CanLower p
    · have he : flip p = lower p hl := by simp [flip, h, hl]
      rw [he]
      have hr := lower_canRaise p hl
      rw [show flip (lower p hl) = raise (lower p hl) hr by simp [flip, hr]]
      exact raise_lower p hl
    · have he : flip p = p := by simp [flip, h, hl]
      rw [he, he]

theorem flip_size (p : Rows) : size (flip p) = size p := by
  unfold flip
  split_ifs with h g
  · exact raise_size p h
  · exact lower_size p g
  · rfl

theorem flip_fixed (p : Rows) :
    flip p = p ↔ p.length = 0 ∨ (slope p = p.length ∧
      (smallest p = p.length ∨ smallest p = p.length+1)) := by
  have hi : flip p = p ↔ ¬ CanRaise p ∧ ¬ CanLower p := by
    unfold flip
    split_ifs with h g
    · have hh (he : raise p h = p) : False := by
        have hc := congrArg Rows.length he
        change p.length-1=p.length at hc
        have := h.2
        omega
      simp [h]
      exact hh
    · have hh (he : lower p g = p) : False := by
        have hc := congrArg Rows.length he
        change p.length+1=p.length at hc
        omega
      simp [g]
      exact hh
    · simp [h,g]
  rw [hi]
  by_cases hf : p.length=0
  · have hm : smallest p = 0 := p.zero _ (by omega)
    simp [hf, hm, CanRaise, CanLower]
  · have hs := slope_le p (by omega)
    simp only [CanRaise, CanLower]
    omega

end
end MockThetaAnalytic.Franklin
