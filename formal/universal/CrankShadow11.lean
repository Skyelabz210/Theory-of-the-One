import IntegerSpecialization
import ProfiniteObservations

/-! Residue classes of a signed statistic and two documented uses of residue 11.

In the fixed S6 primary, 11 divides 30030, so the degree-one primary coordinate
projects directly to the statistic class. In the S8 shadow split, the product
of the seven payload moduli is 881790. The shadow reading of an affine source
changes by 881790 times the lift increment modulo 11. NINE65's
`crates/cram-core/src/phase_lock.rs` documents this successor arithmetic.
The affine relation and authentic readings are hypotheses on the producer.
-/

namespace KElimination.CrankShadow11

open KElimination.ProfiniteObservations
open KElimination.IntegerSpecialization

/-- Canonical residue of a signed statistic in the eleven histogram bins. -/
def statClass (s : Int) : Nat := (s % 11).toNat

theorem statClass_lt (s : Int) : statClass s < 11 := by
  exact (intPoint positivePeriods s).bound ⟨11, (by decide : 0 < (11 : Nat))⟩

/-- The direct shadow coordinate observes the signed statistic itself. -/
theorem direct_statistic_coordinate (s : Int) :
    (intPoint positivePeriods s).residue ⟨11, (by decide : 0 < (11 : Nat))⟩ = statClass s := rfl

/-- Exponent one in the actual 30030-power period family. -/
def s6Period : selectedPrimaryPowers.Period :=
  ⟨selectedPrimary, 1, (Nat.pow_one _).symm⟩

/-- The base S6 coordinate of a diagonal statistic already carries its
class modulo eleven. -/
theorem s6_statistic_coordinate (s : Int) :
    (intPoint selectedPrimaryPowers s).residue s6Period % 11 = statClass s := by
  exact (intPoint positivePeriods s).coherent ⟨11, (by decide : 0 < (11 : Nat))⟩
    ⟨selectedPrimary, (by decide : 0 < selectedPrimary)⟩ (by decide)

/-- The payload product in the S8 shadow-split profile. -/
def splitPayload : Int := 881790

theorem splitPayload_factorization :
    splitPayload = 2 * 3 * 5 * 7 * 13 * 17 * 19 := by decide

theorem splitPayload_inverse : (7 * splitPayload) % 11 = 1 % 11 := by decide

/-- The existing positive-quotient query, with the two mod-11 readings in
chart, successor order and the public S8 inverse. -/
def s8Readout (chart shadow : Int) : Int :=
  query chart shadow 11 7

/-- For a statistic encoded as an affine increment, the query yields its
histogram class. Both shadow readings are supplied by the same transition. -/
theorem s8_increment_statClass (stat before after chart shadow : Int)
    (hstep : after = before + splitPayload * stat)
    (hchart : chart = before % 11) (hshadow : shadow = after % 11) :
    (s8Readout chart shadow).toNat = statClass stat :=
  congrArg Int.toNat (query_chart_of_decomposition after before chart shadow splitPayload
    11 7 stat hstep hchart hshadow splitPayload_inverse)

/-- When the input source is itself the statistic, querying its payload
remainder's chart and its shadow gives the Euclidean quotient class. -/
theorem s8_quotient_readout (s chart shadow : Int)
    (hchart : chart = (s % splitPayload) % 11) (hshadow : shadow = s % 11) :
    s8Readout chart shadow = (s / splitPayload) % 11 := by
  apply query_chart_of_decomposition s (s % splitPayload) chart shadow splitPayload 11 7
    (s / splitPayload) _ hchart hshadow splitPayload_inverse
  exact (Int.emod_add_mul_ediv s splitPayload).symm

/-- A public width-11 window turns the quotient class into a signed value. -/
theorem s8_quotient_window (s chart shadow lo : Int)
    (hchart : chart = (s % splitPayload) % 11) (hshadow : shadow = s % 11)
    (hl : lo ≤ s / splitPayload) (hu : s / splitPayload < lo + 11) :
    windowDecode (s8Readout chart shadow) 11 lo = s / splitPayload := by
  rw [s8_quotient_readout s chart shadow hchart hshadow]
  exact window_decode_exact _ _ _ hl hu

/-- The two finite coordinates repeat at the full S8 product. -/
theorem s8_joint_period (s : Int) :
    (s + splitPayload * 11) % splitPayload = s % splitPayload ∧
      statClass (s + splitPayload * 11) = statClass s := by
  unfold splitPayload statClass
  constructor <;> omega

end KElimination.CrankShadow11

#print axioms KElimination.CrankShadow11.statClass_lt
#print axioms KElimination.CrankShadow11.direct_statistic_coordinate
#print axioms KElimination.CrankShadow11.s6_statistic_coordinate
#print axioms KElimination.CrankShadow11.splitPayload_factorization
#print axioms KElimination.CrankShadow11.splitPayload_inverse
#print axioms KElimination.CrankShadow11.s8_increment_statClass
#print axioms KElimination.CrankShadow11.s8_quotient_readout
#print axioms KElimination.CrankShadow11.s8_quotient_window
#print axioms KElimination.CrankShadow11.s8_joint_period
