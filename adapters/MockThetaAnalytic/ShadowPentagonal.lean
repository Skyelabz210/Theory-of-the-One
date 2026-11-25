import FranklinRows
import ShadowParity
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.GetD
import Mathlib.Data.List.OfFn
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Zify

/-! Euler's pentagonal support modulo two. Expand the product by distinct
partitions and cancel every two-cycle of Franklin's involution. -/

namespace MockThetaAnalytic.ShadowPentagonal

open Franklin ShadowReadings ShadowParity PowerSeries Finset
open scoped PowerSeries BigOperators
noncomputable section

private theorem part_strict (p : Rows) {i j : ℕ} (h : i < j) (hj : j ≤ p.length) :
    p.part j < p.part i := by
  induction j with
  | zero => omega
  | succ j ih =>
    have hstep := p.desc j (by omega)
    by_cases he : i = j
    · simpa [he] using hstep
    · exact hstep.trans (ih (by omega) (by omega))

private def rowsList (p : Rows) : List ℕ := List.ofFn (fun i : Fin p.length => p.part i)

private theorem rowsList_sorted (p : Rows) : (rowsList p).SortedGT := by
  rw [List.sortedGT_iff_getElem_gt_getElem_of_lt]
  intro i j hi _ hij
  simp only [rowsList, List.getElem_ofFn]
  apply part_strict p hij
  simpa [rowsList] using hi.le

private def parts (p : Rows) : Finset ℕ := (rowsList p).toFinset

private theorem parts_pos (p : Rows) {x : ℕ} (hx : x ∈ parts p) : 0 < x := by
  have hl : x ∈ rowsList p := List.mem_toFinset.mp hx
  rw [rowsList, List.mem_ofFn] at hl
  obtain ⟨i, rfl⟩ := hl
  exact (Nat.zero_le _).trans_lt (p.desc i i.isLt)

private def sortedParts (s : Finset ℕ) : List ℕ := (s.erase 0).sort (· ≥ ·)

private def ofParts (s : Finset ℕ) : Rows where
  length := (sortedParts s).length
  part i := (sortedParts s).getD i 0
  desc := by
    intro i hi
    by_cases hj : i+1 < (sortedParts s).length
    · rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hj]
      exact (sortedGT_sort (s.erase 0)).getElem_gt_getElem_of_lt (hi:=hj) (hj:=hi) (by omega)
    · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_getElem _ _ hi]
      have hmem : (sortedParts s)[i] ∈ s.erase 0 :=
        (mem_sort _).mp (List.getElem_mem hi)
      exact Nat.pos_of_ne_zero (mem_erase.mp hmem).1
  zero := fun i hi => List.getD_eq_default _ _ hi

private theorem parts_ofParts (s : Finset ℕ) : parts (ofParts s) = s.erase 0 := by
  have h : rowsList (ofParts s) = sortedParts s := by
    change (List.ofFn (fun i : Fin (sortedParts s).length => (sortedParts s).getD i 0)) = sortedParts s
    conv_rhs => rw [← List.ofFn_getElem (sortedParts s)]
    congr 1
    funext i
    exact List.getD_eq_getElem _ _ i.isLt
  simp [parts, h, sortedParts]

private theorem ofParts_parts (p : Rows) : ofParts (parts p) = p := by
  have hz : 0 ∉ parts p := by intro h; have := parts_pos p h; omega
  have hsort : sortedParts (parts p) = rowsList p := by
    unfold sortedParts
    rw [erase_eq_of_notMem hz]
    apply List.Subset.antisymm_of_sortedGT _ _ (sortedGT_sort _) (rowsList_sorted p)
    · intro n hn
      exact List.mem_toFinset.mp ((mem_sort _).mp hn)
    · intro n hn
      exact (mem_sort _).mpr (List.mem_toFinset.mpr hn)
  apply Rows.ext (by simp [ofParts, hsort, rowsList])
  funext i
  change (sortedParts (parts p)).getD i 0 = p.part i
  rw [hsort]
  by_cases h : i < p.length
  · rw [List.getD_eq_getElem _ _ (by simpa [rowsList] using h)]
    simp [rowsList]
  · rw [List.getD_eq_default _ _ (by simpa [rowsList] using Nat.le_of_not_gt h),
      p.zero i (Nat.le_of_not_gt h)]

private theorem sum_parts (p : Rows) : ∑ x ∈ parts p, x = size p := by
  rw [parts, List.sum_toFinset _ (rowsList_sorted p).nodup]
  simp [rowsList, size, List.sum_ofFn, Fin.sum_univ_eq_sum_range]

private theorem sum_ofParts (s : Finset ℕ) (hz : 0 ∉ s) :
    size (ofParts s) = ∑ x ∈ s, x := by
  rw [← sum_parts, parts_ofParts, erase_eq_of_notMem hz]

private def staircase (k b : ℕ) : Rows where
  length := k
  part i := if i < k then b+1+(k-1-i) else 0
  desc := by intro i hi; simp only [if_pos hi]; split_ifs <;> omega
  zero := by intro i hi; simp [Nat.not_lt.mpr hi]

private theorem staircase_bottom (k b : ℕ) (h : 0 < k) :
    smallest (staircase k b) = b+1 := by
  simp [smallest, staircase, show k-1 < k by omega]

private theorem staircase_slope (k b : ℕ) (h : 0 < k) : slope (staircase k b) = k := by
  have hle := slope_le (staircase k b) h
  change slope (staircase k b) ≤ k at hle
  by_contra! hn
  let t := slope (staircase k b)
  have hlt : t < k := by dsimp [t]; omega
  have hgap := break_at_slope (staircase k b) hlt
  have hpos : 0 < t := slope_pos (staircase k b)
  change (if t < k then b+1+(k-1-t) else 0)+1 <
    (if t-1 < k then b+1+(k-1-(t-1)) else 0) at hgap
  rw [if_pos hlt, if_pos (by omega : t-1 < k)] at hgap
  omega

private theorem rows_eq_staircase (p : Rows) (h : slope p = p.length)
    (hp : 0 < p.length) : p = staircase p.length (smallest p-1) := by
  refine Rows.ext (y := staircase p.length (smallest p-1)) rfl ?_
  funext i
  by_cases hi : i < p.length
  · have hdist (j : ℕ) (i : ℕ) (hij : i+j = p.length-1) :
        p.part i = smallest p + j := by
      induction j generalizing i with
      | zero => simp [smallest, show i=p.length-1 by omega]
      | succ j ih =>
        have hc := consecutive p (show i+1 < slope p by omega)
        rw [hc, ih (i+1) (by omega)]
        omega
    have hx := p.desc (p.length-1) (by omega : p.length-1 < p.length)
    change p.part (p.length-1+1) < smallest p at hx
    rw [hdist (p.length-1-i) i (by omega)]
    simp only [staircase, if_pos hi]
    omega
  · simp [staircase, hi, p.zero i (by omega)]

private theorem twice_staircase_size (k b : ℕ) :
    2 * size (staircase k b) = 2*k*(b+1) + k*(k-1) := by
  have hsum : (∑ i ∈ range k, (k-1-i)) = ∑ i ∈ range k, i := by
    cases k with
    | zero => simp
    | succ k => simpa using Finset.sum_flip (n:=k) (fun i : ℕ => i)
  have hh : size (staircase k b) = k*(b+1) + (∑ i ∈ range k, (k-1-i)) := by
    unfold size
    change (∑ i ∈ range k, if i < k then b+1+(k-1-i) else 0) = _
    have he : (∑ j ∈ range k, if j < k then b+1+(k-1-j) else 0) =
        ∑ j ∈ range k, (b+1+(k-1-j)) :=
      Finset.sum_congr rfl (fun j hj => if_pos (Finset.mem_range.mp hj))
    rw [he, sum_add_distrib]
    simp
  rw [hh, hsum, mul_add, ← sum_range_id_mul_two]
  ring

private def fixedMagnitude (p : Rows) : ℕ :=
  if p.length=0 then 1 else if smallest p = p.length then 6*p.length-1 else 6*p.length+1

private theorem fixed_square (p : Rows) (h : flip p = p) :
    fixedMagnitude p * fixedMagnitude p = 24*size p + 1 := by
  rcases (flip_fixed p).mp h with hzero | ⟨hsl, hb⟩
  · simp [fixedMagnitude, size, hzero]
  · by_cases hzero : p.length=0
    · simp [fixedMagnitude, size, hzero]
    · have hpos : 0 < p.length := by omega
      have hs := twice_staircase_size p.length (smallest p-1)
      rw [← rows_eq_staircase p hsl hpos] at hs
      obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hzero
      rcases hb with he | he
      · simp only [fixedMagnitude, if_neg hzero, if_pos he]
        rw [he, hk] at hs
        simp only [Nat.succ_sub_one] at hs
        rw [hk, Nat.mul_succ, show 6*k+6-1 = 6*k+5 by omega]
        nlinarith
      · have hne : smallest p ≠ p.length := by omega
        simp only [fixedMagnitude, if_neg hzero, if_neg hne]
        rw [he, hk] at hs
        simp only [Nat.succ_sub_one] at hs
        rw [hk]
        nlinarith

private theorem fixed_same_size (p q : Rows) (hp : flip p = p) (hq : flip q = q)
    (hsize : size p = size q) : p = q := by
  have hm : fixedMagnitude p = fixedMagnitude q := by
    rw [← Nat.mul_self_inj, fixed_square p hp, fixed_square q hq, hsize]
  rcases (flip_fixed p).mp hp with pz | ⟨ps, pb⟩ <;>
    rcases (flip_fixed q).mp hq with qz | ⟨qs, qb⟩
  · apply Rows.ext (pz.trans qz.symm)
    funext i
    rw [p.zero i (by omega), q.zero i (by omega)]
  · have q0 : q.length=0 := by unfold fixedMagnitude at hm; split_ifs at hm <;> omega
    apply Rows.ext (pz.trans q0.symm)
    funext i
    rw [p.zero i (by omega), q.zero i (by omega)]
  · have p0 : p.length=0 := by unfold fixedMagnitude at hm; split_ifs at hm <;> omega
    apply Rows.ext (p0.trans qz.symm)
    funext i
    rw [p.zero i (by omega), q.zero i (by omega)]
  · by_cases pz : p.length=0
    · have qz : q.length=0 := by unfold fixedMagnitude at hm; split_ifs at hm <;> omega
      apply Rows.ext (pz.trans qz.symm)
      funext i
      rw [p.zero i (by omega), q.zero i (by omega)]
    · by_cases qz : q.length=0
      · unfold fixedMagnitude at hm; split_ifs at hm <;> omega
      · have hlen : p.length=q.length := by
          unfold fixedMagnitude at hm
          split_ifs at hm <;> omega
        have hbase : smallest p=smallest q := by
          unfold fixedMagnitude at hm
          split_ifs at hm <;> omega
        rw [rows_eq_staircase p ps (by omega), rows_eq_staircase q qs (by omega), hlen, hbase]

private theorem fixed_of_square {d m : ℕ} (hm : m*m = 24*d+1) :
    ∃ p : Rows, flip p = p ∧ size p = d := by
  have hl := (square_lattice m).mp (by rw [hm]; omega)
  rcases hl with hl | hl
  · let k := m/6
    have hmk : m=6*k+1 := by dsimp [k]; omega
    refine ⟨staircase k k, ?_, ?_⟩
    · apply (flip_fixed _).mpr
      by_cases hk : k=0
      · exact Or.inl hk
      · exact Or.inr ⟨staircase_slope k k (by omega), Or.inr (staircase_bottom k k (by omega))⟩
    · have hs := twice_staircase_size k k
      rcases Nat.eq_zero_or_pos k with hk | hk
      · have hm0 : m=1 := by omega
        rw [hm0] at hm
        simpa [hk, size, staircase] using (show (0:ℕ)=d by omega)
      · have he : k-1+1=k := by omega
        have he' : k*(k-1)+k=k*k := by nlinarith [congrArg (k * ·) he]
        rw [hmk] at hm
        nlinarith
  · let b := m/6
    have hmb : m=6*b+5 := by dsimp [b]; omega
    refine ⟨staircase (b+1) b, ?_, ?_⟩
    · exact (flip_fixed _).mpr (Or.inr ⟨staircase_slope _ _ (by omega),
        Or.inl (staircase_bottom _ _ (by omega))⟩)
    · have hs := twice_staircase_size (b+1) b
      rw [Nat.add_sub_cancel] at hs
      rw [hmb] at hm
      nlinarith

private def available (n : ℕ) : Finset ℕ := (range n).image (· + 1)

private theorem mem_available {n a : ℕ} : a ∈ available n ↔ 0 < a ∧ a ≤ n := by
  unfold available
  constructor
  · intro h
    obtain ⟨j, hj, rfl⟩ := mem_image.mp h
    simp only [mem_range] at hj
    omega
  · intro h
    exact mem_image.mpr ⟨a-1, mem_range.mpr (by omega), by omega⟩

private def distinctOfSize (n d : ℕ) : Finset (Finset ℕ) :=
  ((available n).powerset).filter (fun s => ∑ a ∈ s, a = d)

private def flipParts (s : Finset ℕ) : Finset ℕ := parts (flip (ofParts s))

private theorem zero_not_mem {n d : ℕ} {s : Finset ℕ} (hs : s ∈ distinctOfSize n d) : 0 ∉ s := by
  intro h
  have hsub := mem_powerset.mp (mem_filter.mp hs).1
  exact (Nat.lt_irrefl 0) (mem_available.mp (hsub h)).1

private theorem distinct_size {n d : ℕ} {s : Finset ℕ} (hs : s ∈ distinctOfSize n d) :
    size (ofParts s) = d := by
  rw [sum_ofParts s (zero_not_mem hs)]
  exact (mem_filter.mp hs).2

private theorem distinct_parts {n d : ℕ} (p : Rows) (hp : size p = d) (hd : d ≤ n) :
    parts p ∈ distinctOfSize n d := by
  apply mem_filter.mpr
  refine ⟨mem_powerset.mpr ?_, (sum_parts p).trans hp⟩
  intro a ha
  apply mem_available.mpr
  refine ⟨parts_pos p ha, ?_⟩
  have hsum : a ≤ ∑ a ∈ parts p, a := Finset.single_le_sum (fun b _ => Nat.zero_le b) ha
  exact hsum.trans ((sum_parts p).trans hp ▸ hd)

private theorem flipParts_mem {n d : ℕ} (hd : d ≤ n) (s : Finset ℕ) (hs : s ∈ distinctOfSize n d) :
    flipParts s ∈ distinctOfSize n d :=
  distinct_parts _ ((flip_size _).trans (distinct_size hs)) hd

private theorem flipParts_involution {n d : ℕ} (s : Finset ℕ) (hs : s ∈ distinctOfSize n d) :
    flipParts (flipParts s) = s := by
  rw [flipParts, flipParts, ofParts_parts, flip_involution, parts_ofParts,
    erase_eq_of_notMem (zero_not_mem hs)]

private theorem flipParts_fixed_iff {n d : ℕ} {s : Finset ℕ} (hs : s ∈ distinctOfSize n d) :
    flipParts s = s ↔ flip (ofParts s) = ofParts s := by
  constructor
  · intro h
    have hh := congrArg ofParts h
    rwa [flipParts, ofParts_parts] at hh
  · intro h
    rw [flipParts, h, parts_ofParts, erase_eq_of_notMem (zero_not_mem hs)]

private theorem coefficient_card (n d : ℕ) :
    coeff d (eulerProduct n) = ((distinctOfSize n d).card : F) := by
  unfold eulerProduct
  have he : (∏ j ∈ range n, (1+(PowerSeries.X : Series)^(j+1))) =
      ∏ a ∈ available n, (1+(PowerSeries.X : Series)^a) := by
    rw [available, Finset.prod_image]
    intro i _ j _ hh
    change i+1 = j+1 at hh
    omega
  rw [he, Finset.prod_one_add, map_sum]
  have hsum : (∑ s ∈ (available n).powerset, coeff d (∏ a ∈ s, (PowerSeries.X : Series)^a)) =
      ∑ s ∈ (available n).powerset, (if ∑ a ∈ s, a = d then (1:F) else 0) := by
    apply sum_congr rfl
    intro s _
    rw [Finset.prod_pow_eq_pow_sum, coeff_X_pow]
    by_cases hs : (∑ a ∈ s, a) = d
    · simp [hs]
    · simp [hs, Ne.symm hs]
  rw [hsum]
  rw [distinctOfSize, Finset.card_filter]
  push_cast
  apply sum_congr rfl
  intro i _
  split_ifs <;> simp_all

theorem euler_pentagonal_mod_two (n d : ℕ) (hd : d ≤ n) :
    coeff d (eulerProduct n) = pentagonalBit d := by
  classical
  let S := distinctOfSize n d
  let fixed := S.filter (fun s => flipParts s=s)
  let moved := S.filter (fun s => flipParts s≠s)
  have hcard : fixed.card + moved.card = S.card := card_filter_add_card_filter_not (s:=S) _
  have hz : (moved.card : F) = 0 := by
    rw [← show (∑ _ ∈ moved, (1:F)) = (moved.card:F) by simp]
    apply Finset.sum_involution (g := fun s _ => flipParts s)
    · intro s hs
      exact (by decide : (1 : F)+1=0)
    · intro s hs _
      exact (mem_filter.mp hs).2
    · intro s hs
      have hS := (mem_filter.mp hs).1
      exact mem_filter.mpr ⟨flipParts_mem hd s hS, fun h =>
        (mem_filter.mp hs).2 (h.symm.trans (flipParts_involution s hS))⟩
    · intro s hs
      exact flipParts_involution s (mem_filter.mp hs).1
  rw [coefficient_card, ← hcard, Nat.cast_add, hz, add_zero, pentagonalBit]
  by_cases hsq : (24*d+1).sqrt * (24*d+1).sqrt = 24*d+1
  · rw [if_pos hsq]
    obtain ⟨p, hp, hpd⟩ := fixed_of_square hsq
    have hm : parts p ∈ S := distinct_parts p hpd hd
    have hpfix : flipParts (parts p) = parts p := by simp [flipParts, ofParts_parts, hp]
    have he : fixed = {parts p} := by
      ext s
      constructor
      · intro hs
        have hS := (mem_filter.mp hs).1
        have hflip := (flipParts_fixed_iff hS).mp (mem_filter.mp hs).2
        have he := fixed_same_size (ofParts s) p hflip hp ((distinct_size hS).trans hpd.symm)
        rw [mem_singleton, ← he, parts_ofParts, erase_eq_of_notMem (zero_not_mem hS)]
      · intro hs
        rw [mem_singleton.mp hs]
        exact mem_filter.mpr ⟨hm,hpfix⟩
    rw [he, card_singleton, Nat.cast_one]
  · rw [if_neg hsq]
    have he : fixed = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro s hs
      have hS := (mem_filter.mp hs).1
      have hflip := (flipParts_fixed_iff hS).mp (mem_filter.mp hs).2
      obtain eq := fixed_square (ofParts s) hflip
      rw [distinct_size hS] at eq
      apply hsq
      rw [← eq, Nat.sqrt_eq]
    rw [he, card_empty, Nat.cast_zero]

theorem reciprocal_mock_pentagonal (d : ℕ) :
    reciprocalBit (fun i => ((KElimination.MockTheta.mockCoeff i : ℤ) : F)) d =
      pentagonalBit d :=
  (reciprocal_euler d (d+1) (by omega)).trans (euler_pentagonal_mod_two _ _ (by omega))

end
end MockThetaAnalytic.ShadowPentagonal
