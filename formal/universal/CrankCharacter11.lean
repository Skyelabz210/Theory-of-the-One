import CrankShadow11
import PartitionCrank11
import MockThetaSeventh

/-! Finite character pairing on the signed statistic of each partition.
The statistic coordinate and the degree indexing the partition size are independent. -/

namespace KElimination.CrankCharacter11

open Lean.Grind ResidueSeries CrankShadow11 PartitionCrank11

universe u
variable {R : Type u} [CommRing R]
attribute [local instance] Semiring.natCast

/-- Pair an eleven-bin histogram with the powers of a supplied ring element. -/
def histPair (h : Nat → Nat) (z : R) : R :=
  sumBelow 11 (fun r => Nat.cast (h r) * z ^ r)

/-- Add one character value for each observed partition class. -/
def classPair (observe : List Nat → Nat) (z : R) : List (List Nat) → R
  | [] => 0
  | p :: ps => classPair observe z ps + z ^ observe p

/-- Direct character sum on the signed statistic class of each entry. -/
def samplePair (stat : List Nat → Int) (z : R) (ps : List (List Nat)) : R :=
  classPair (fun p => statClass (stat p)) z ps

/-- A root of period eleven gives a multiplicative character on signed statistics. -/
theorem statistic_character_add (z : R) (hz : z^11 = 1) (a b : Int) :
    z ^ statClass (a+b) = z ^ statClass a * z ^ statClass b := by
  have hc : statClass (a+b) = (statClass a + statClass b) % 11 := by
    unfold statClass
    omega
  rw [hc, root_power_mod z 11 _ hz, Semiring.pow_add]

/-- Aggregating the classes before the pairing gives exactly the direct sum.
When z^11=1 the powers give a character of the statistic group. -/
theorem histPair_eq_samplePair (stat : List Nat → Int) (z : R) (ps : List (List Nat)) :
    histPair (countClass stat ps) z = samplePair stat z ps := by
  induction ps with
  | nil => simp [histPair, countClass, samplePair, classPair, Semiring.natCast_zero, Semiring.zero_mul, sumBelow_zero]
  | cons p ps ih =>
    let k := statClass (stat p)
    have hkEq : (stat p % 11).toNat = k := rfl
    have hk : k < 11 := statClass_lt _
    unfold histPair at ih ⊢
    calc
      _ = sumBelow 11 (fun r =>
          Nat.cast (countClass stat ps r) * z^r + (if k = r then z^k else 0)) := by
        apply sumBelow_congr
        intro r _
        by_cases h : k = r
        · subst r
          simp [countClass, hkEq,
            Semiring.natCast_succ, Semiring.right_distrib, Semiring.one_mul]
        · simp [countClass, hkEq, h, Semiring.add_zero]
      _ = samplePair stat z ps + z^k := by
        rw [sumBelow_add, sumBelow_single, if_pos hk, ih]
      _ = _ := rfl

/-- Authentic S8 transition observations supply each crank exponent directly. -/
theorem s8_crank_pairing (z : R) (ps : List (List Nat))
    (before after chart shadow : List Nat → Int)
    (hstep : ∀ p ∈ ps, after p = before p + splitPayload * crank p)
    (hchart : ∀ p ∈ ps, chart p = before p % 11)
    (hshadow : ∀ p ∈ ps, shadow p = after p % 11) :
    histPair (countClass crank ps) z =
      classPair (fun p => (s8Readout (chart p) (shadow p)).toNat) z ps := by
  rw [histPair_eq_samplePair]
  unfold samplePair
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    have hp := s8_increment_statClass (crank p) (before p) (after p) (chart p) (shadow p)
      (hstep p (by simp)) (hchart p (by simp)) (hshadow p (by simp))
    simp only [classPair, hp]
    rw [ih (fun x hx => hstep x (List.mem_cons_of_mem _ hx))
      (fun x hx => hchart x (List.mem_cons_of_mem _ hx))
      (fun x hx => hshadow x (List.mem_cons_of_mem _ hx))]

/-- The reduced coefficients of the histogram polynomial modulo
Φ₁₁(X)=1+X+⋯+X¹⁰. The coefficient of degree ten is eliminated. -/
def reducedCoeff (h : Nat → Nat) (r : Nat) : Int := (h r : Int) - h 10

theorem reduced_zero_iff_uniform (h : Nat → Nat) :
    (∀ r, r < 10 → reducedCoeff h r = 0) ↔ ∀ r, r < 11 → h r = h 10 := by
  constructor
  · intro he r hr
    by_cases hlt : r < 10
    · have := he r hlt
      unfold reducedCoeff at this
      omega
    · have : r = 10 := by omega
      rw [this]
  · intro he r hr
    unfold reducedCoeff
    rw [he r (by omega)]
    omega

/-- Evaluating at a root of Φ₁₁ reduces to the ten coefficient differences. -/
theorem histPair_reduced (h : Nat → Nat) (z : R)
    (hz : sumBelow 11 (fun r => z^r) = 0) :
    histPair h z =
      sumBelow 10 (fun r => (Nat.cast (h r) - Nat.cast (h 10)) * z^r) := by
  have he := sumBelow_mul_left 11 (fun r => z^r) (Nat.cast (h 10) : R)
  rw [hz, Semiring.mul_zero] at he
  change sumBelow 10 (fun r => Nat.cast (h 10) * z ^ r) + Nat.cast (h 10) * z^10 = 0 at he
  have split := sumBelow_add 10 (fun r => (Nat.cast (h r) - Nat.cast (h 10)) * z^r)
    (fun r => Nat.cast (h 10) * z^r)
  have heq : sumBelow 10 (fun r => Nat.cast (h r) * z^r) =
      sumBelow 10 (fun r => ((Nat.cast (h r) - Nat.cast (h 10)) * z^r) + Nat.cast (h 10) * z^r) := by
    apply sumBelow_congr
    intro r _
    grind
  change sumBelow 10 (fun r => Nat.cast (h r) * z^r) + Nat.cast (h 10) * z^10 = _
  rw [heq, split]
  grind

/-- Every root of Φ₁₁ annihilates the ordinary crank distribution at size six. -/
theorem crank_six_vanishes (z : R) (hz : sumBelow 11 (fun r => z^r) = 0) :
    samplePair crank z (partitions 6) = 0 := by
  rw [← histPair_eq_samplePair, ← hz]
  apply sumBelow_congr
  intro r hr
  have h := crank_six_uniform ⟨r, hr⟩
  change countClass crank (partitions 6) r = 1 at h
  rw [h, Semiring.natCast_one, Semiring.one_mul]

theorem rank_six_reduced_witness :
    reducedCoeff (countClass rank (partitions 6)) 4 = -2 := by decide +kernel

/-- Weight the statistic bin at each partition size by a degree-dependent scalar. -/
def weightedClass (a : Nat → R) (N r : Nat) (stat : List Nat → Int) : R :=
  sumBelow N (fun n => a n * Nat.cast (countClass stat (partitions n) r))

theorem weighted_pairing (a : Nat → R) (N : Nat) (z : R) (stat : List Nat → Int) :
    sumBelow 11 (fun r => weightedClass a N r stat * z^r) =
      sumBelow N (fun n => a n * samplePair stat z (partitions n)) := by
  calc
    _ = sumBelow 11 (fun r => sumBelow N
        (fun n => (a n * Nat.cast (countClass stat (partitions n) r)) * z^r)) := by
      apply sumBelow_congr
      intro r _
      exact (sumBelow_mul_right N _ (z^r)).symm
    _ = _ := by
      rw [sumBelow_swap]
      apply sumBelow_congr
      intro n _
      rw [← histPair_eq_samplePair, histPair, ← sumBelow_mul_left]
      apply sumBelow_congr
      intro r _
      exact Semiring.mul_assoc _ _ _

/-- Each seventh-order series supplies size weights; the crank coordinate
selects the character exponent independently at each size. -/
theorem seventh_crank_pairing (s : MockThetaSeventh.Family) (N : Nat) (t z : R) :
    sumBelow 11 (fun r => weightedClass (fun n => MockThetaSeventh.coeff s n * t^n) N r crank * z^r) =
      sumBelow N (fun n => (MockThetaSeventh.coeff s n * t^n) * samplePair crank z (partitions n)) :=
  weighted_pairing _ N z crank

/-- Fold authentic paired S8 readings directly into the seventh-order
weighted crank transform, at every retained size. -/
theorem seventh_crank_from_s8 (s : MockThetaSeventh.Family) (N : Nat) (t z : R)
    (before after chart shadow : List Nat → Int)
    (hobs : ∀ n, n < N → ∀ p ∈ partitions n,
      after p = before p + splitPayload * crank p ∧
      chart p = before p % 11 ∧ shadow p = after p % 11) :
    sumBelow 11 (fun r => weightedClass (fun n => MockThetaSeventh.coeff s n * t^n) N r crank * z^r) =
      sumBelow N (fun n => (MockThetaSeventh.coeff s n * t^n) *
        classPair (fun p => (s8Readout (chart p) (shadow p)).toNat) z (partitions n)) := by
  rw [seventh_crank_pairing]
  apply sumBelow_congr
  intro n hn
  rw [← histPair_eq_samplePair, s8_crank_pairing z (partitions n) before after chart shadow
    (fun p hp => (hobs n hn p hp).1) (fun p hp => (hobs n hn p hp).2.1)
    (fun p hp => (hobs n hn p hp).2.2)]

end KElimination.CrankCharacter11

#print axioms KElimination.CrankCharacter11.histPair_eq_samplePair
#print axioms KElimination.CrankCharacter11.reduced_zero_iff_uniform
#print axioms KElimination.CrankCharacter11.histPair_reduced
#print axioms KElimination.CrankCharacter11.weighted_pairing
#print axioms KElimination.CrankCharacter11.seventh_crank_pairing
#print axioms KElimination.CrankCharacter11.statistic_character_add
#print axioms KElimination.CrankCharacter11.s8_crank_pairing
#print axioms KElimination.CrankCharacter11.crank_six_vanishes
#print axioms KElimination.CrankCharacter11.rank_six_reduced_witness
#print axioms KElimination.CrankCharacter11.seventh_crank_from_s8
