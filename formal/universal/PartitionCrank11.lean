import Std

/-! Integer partitions and their ordinary Dyson rank and Andrews–Garvan crank modulo 11. -/

namespace KElimination.PartitionCrank11

/-- Parts are positive, weakly decreasing, and bounded above by `bound`. -/
def orderedBelow : Nat → List Nat → Prop
  | _, [] => True
  | bound, x :: xs => 0 < x ∧ x ≤ bound ∧ orderedBelow x xs

/-- Split on whether the maximum allowed part occurs. -/
def partitionsAtMost (bound size : Nat) : List (List Nat) :=
  match bound with
  | 0 => if size = 0 then [[]] else []
  | k + 1 =>
    if _h : k + 1 ≤ size then
      partitionsAtMost k size ++
        (partitionsAtMost (k+1) (size - (k+1))).map (List.cons (k+1))
    else partitionsAtMost k size
termination_by bound + size
decreasing_by all_goals omega

def partitions (size : Nat) : List (List Nat) := partitionsAtMost size size

/-- The empty partition has rank zero. -/
def rank (p : List Nat) : Int := (p.headD 0 : Int) - p.length

/-- If no ones occur, take the largest part (zero for the empty partition).
Otherwise subtract the number of ones from the number of parts larger than that count.
Thus the ordinary partition `[1]` has crank −1. -/
def crank (p : List Nat) : Int :=
  let ones := p.count 1
  if ones = 0 then p.headD 0 else (p.countP (· > ones) : Int) - ones

/-- Count a residue class using signed Euclidean reduction. -/
def countClass (stat : List Nat → Int) : List (List Nat) → Nat → Nat
  | [], _ => 0
  | p :: ps, r => if (stat p % 11).toNat = r then countClass stat ps r + 1 else countClass stat ps r

def histogram11 (stat : List Nat → Int) (size : Nat) : List Nat :=
  (List.range 11).map (countClass stat (partitions size))

theorem mem_partitionsAtMost (bound size : Nat) (p : List Nat) :
    p ∈ partitionsAtMost bound size ↔ p.sum = size ∧ orderedBelow bound p := by
  cases bound with
  | zero =>
    rw [partitionsAtMost]
    cases p <;> split <;> simp_all [orderedBelow] <;> omega
  | succ k =>
    rw [partitionsAtMost]
    by_cases h : k + 1 ≤ size
    · rw [dif_pos h, List.mem_append, mem_partitionsAtMost k size p]
      cases p with
      | nil => simp [orderedBelow, List.mem_map]
      | cons x xs =>
        simp only [List.mem_map, List.cons.injEq, List.sum_cons, orderedBelow]
        constructor
        · rintro (⟨hs,hx,hb,ht⟩ | ⟨ls, hm, he, rfl⟩)
          · exact ⟨hs, hx, by omega, ht⟩
          · have ⟨hs, ht⟩ := (mem_partitionsAtMost (k+1) (size-(k+1)) ls).mp hm
            subst x
            exact ⟨by omega, by omega, by omega, ht⟩
        · rintro ⟨hs, hx, hb, ht⟩
          by_cases he : x ≤ k
          · exact Or.inl ⟨hs, hx, he, ht⟩
          · have heq : x = k + 1 := by omega
            subst x
            exact Or.inr ⟨xs, (mem_partitionsAtMost (k+1) (size-(k+1)) xs).mpr
              ⟨by omega, ht⟩, rfl, rfl⟩
    · rw [dif_neg h, mem_partitionsAtMost k size p]
      cases p with
      | nil => simp [orderedBelow]
      | cons x xs =>
        simp only [orderedBelow, List.sum_cons]
        constructor <;> rintro ⟨hs,hx,hb,ht⟩ <;> exact ⟨hs,hx,by omega,ht⟩
termination_by bound + size
decreasing_by all_goals omega

/-- Every canonical partition of the given size occurs in the enumeration. -/
theorem mem_partitions (n : Nat) (p : List Nat) :
    p ∈ partitions n ↔ p.sum = n ∧ orderedBelow n p := mem_partitionsAtMost n n p

/-- The two recursion branches are disjoint by their largest part. -/
theorem nodup_partitionsAtMost (bound size : Nat) : (partitionsAtMost bound size).Nodup := by
  cases bound with
  | zero => rw [partitionsAtMost]; split <;> simp
  | succ k =>
    rw [partitionsAtMost]
    split
    next h =>
      apply List.nodup_append.mpr
      refine ⟨nodup_partitionsAtMost k size, ?_, ?_⟩
      · exact (nodup_partitionsAtMost (k+1) (size-(k+1))).map (List.cons (k+1))
          (fun a b hne heq => hne (List.cons.inj heq).2)
      · intro a ha b hb heq
        obtain ⟨xs, _, rfl⟩ := List.mem_map.mp hb
        subst a
        have ordered := ((mem_partitionsAtMost k size _).mp ha).2
        exact (Nat.not_succ_le_self k) ordered.2.1
    next => exact nodup_partitionsAtMost k size
termination_by bound + size
decreasing_by all_goals omega

theorem partitions_nodup (size : Nat) : (partitions size).Nodup := nodup_partitionsAtMost size size

theorem empty_statistics : rank [] = 0 ∧ crank [] = 0 := by decide

theorem singleton_one_statistics : rank [1] = 0 ∧ crank [1] = -1 := by decide

theorem partitions_six_count : (partitions 6).length = 11 := by decide +kernel

theorem rank_histogram_six : histogram11 rank 6 = [1,2,1,1,0,1,1,0,1,1,2] := by decide +kernel

theorem crank_histogram_six : histogram11 crank 6 = List.replicate 11 1 := by decide +kernel

theorem crank_six_uniform : ∀ r : Fin 11, countClass crank (partitions 6) r = 1 := by decide +kernel

theorem rank_six_not_uniform : ¬ ∀ r : Fin 11,
    countClass rank (partitions 6) r = countClass rank (partitions 6) 0 := by decide +kernel

end KElimination.PartitionCrank11

#print axioms KElimination.PartitionCrank11.mem_partitionsAtMost
#print axioms KElimination.PartitionCrank11.mem_partitions
#print axioms KElimination.PartitionCrank11.nodup_partitionsAtMost
#print axioms KElimination.PartitionCrank11.partitions_nodup
#print axioms KElimination.PartitionCrank11.empty_statistics
#print axioms KElimination.PartitionCrank11.singleton_one_statistics
#print axioms KElimination.PartitionCrank11.partitions_six_count
#print axioms KElimination.PartitionCrank11.rank_histogram_six
#print axioms KElimination.PartitionCrank11.crank_histogram_six
#print axioms KElimination.PartitionCrank11.crank_six_uniform
#print axioms KElimination.PartitionCrank11.rank_six_not_uniform
