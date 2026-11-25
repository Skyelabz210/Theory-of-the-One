import MockThetaPhi
import MockThetaPsi
import MockThetaChi
import MockThetaFifthZero
import MockThetaFifthOne
import MockThetaSeventh

/-! Exact tests of fixed-target CRAM resolution against the historical mock-theta orders. -/
namespace OrderTest

open KElimination KElimination.ProfiniteObservations KElimination.ResidueSeries Lean.Grind

inductive Name where
  | f | phi | psi | chi
  | f0 | phi0 | psi0 | chi0 | bigF0
  | f1 | phi1 | psi1 | chi1 | bigF1
  | seventh0 | seventh1 | seventh2
  deriving Repr, DecidableEq

/-- Each case points directly to its named finite coefficient construction. -/
def coeff {R : Type} [CommRing R] : Name → Nat → R
  | .f => MockTheta.mockCoeff
  | .phi => MockThetaPhi.phiCoeff
  | .psi => MockThetaPsi.psiCoeff
  | .chi => MockThetaChi.chiCoeff
  | .f0 => MockThetaFifthZero.coeff .f
  | .phi0 => MockThetaFifthZero.coeff .phi
  | .psi0 => MockThetaFifthZero.coeff .psi
  | .chi0 => MockThetaFifthZero.coeff .chi
  | .bigF0 => MockThetaFifthZero.coeff .bigF
  | .f1 => MockThetaFifthOne.coeff .f
  | .phi1 => MockThetaFifthOne.coeff .phi
  | .psi1 => MockThetaFifthOne.coeff .psi
  | .chi1 => MockThetaFifthOne.coeff .chi
  | .bigF1 => MockThetaFifthOne.coeff .bigF
  | .seventh0 => MockThetaSeventh.coeff .f0
  | .seventh1 => MockThetaSeventh.coeff .f1
  | .seventh2 => MockThetaSeventh.coeff .f2

/-- The given historical labels are the comparison data. -/
def historicalOrder : Name → Nat
  | .f | .phi | .psi | .chi => 3
  | .seventh0 | .seventh1 | .seventh2 => 7
  | _ => 5

/-- The source theorem applies to every named sequence and every coefficient truncation. -/
theorem finite_transform {R : Type} [CommRing R] (s : Name) (t z : R) (N M H b : Nat)
    (hM : 0 < M) (hH : 0 < H) (hb : 0 < b) (h : reducedTargetPeriod M b ∣ H)
    (hz : z ^ b = 1) :
    sumBelow (M * H) (fun u => weightedPacket (coeff s) (fun d => t ^ d) N (M * H) u * z ^ u) =
      sumBelow N (fun d => coeff s d * (t * z) ^ d) :=
  CoefficientObservations.finite_root_evaluation_from_reduced_winding (coeff s) t z N M H b
    hM hH hb h hz

structure LeastPositive (P : Nat → Prop) (H : Nat) : Prop where
  positive : 0 < H
  admits : P H
  least : ∀ J, 0 < J → P J → H ≤ J

theorem least_universal_target (M b : Nat) (r : Int) (hb : 0 < b) :
    LeastPositive (fun H => ExactObservation.FiberConstant (quotientObservation H)
      (affineTarget M b r)) (reducedTargetPeriod M b) := by
  refine ⟨reduced_target_period_pos _ _ hb, ?_, ?_⟩
  · exact (target_constant_on_quotient_fibers_iff _ _ _ _ hb).mpr (Nat.dvd_refl _)
  · intro J hJ hj
    exact Nat.le_of_dvd hJ ((target_constant_on_quotient_fibers_iff _ _ _ _ hb).mp hj)

/-- The complete coefficient packet in the residue selected by the source chart.
Its value is a function of degree, so all equalities below hold at every degree. -/
def packetReading (a : Nat → Int) (M b : Nat) (r k : Int) (d : Nat) : Int :=
  packet a b (affineTarget M b r k).toNat d

def Occupied (a : Nat → Int) (M b : Nat) (r : Int) : Prop :=
  ∃ (d : Nat) (k : Int), a d ≠ 0 ∧ d % b = (affineTarget M b r k).toNat

def Admits (a : Nat → Int) (M b : Nat) (r : Int) (H : Nat) : Prop :=
  ExactObservation.FiberConstant (quotientObservation H) (packetReading a M b r)

private theorem empty_packet {a : Nat → Int} {M b : Nat} {r : Int}
    (h : ¬ Occupied a M b r) (k : Int) (d : Nat) : packetReading a M b r k d = 0 := by
  unfold packetReading packet
  split
  next he =>
    apply Classical.byContradiction
    intro hn
    exact h ⟨d,k,hn,he⟩
  next => rfl

/-- One nonzero coefficient in the visited residue orbit detects the whole
reduced period. If the orbit is empty, its packet vanishes on every source. -/
theorem packet_criterion (a : Nat → Int) (M b : Nat) (r : Int) (H : Nat) (hb : 0 < b) :
    Admits a M b r H ↔ (Occupied a M b r → reducedTargetPeriod M b ∣ H) := by
  constructor
  · intro hg ⟨d,k,hn,hr⟩
    have hsame : quotientObservation H (k + H) = quotientObservation H k :=
      (quotient_observation_eq_iff H _ _).mpr ⟨1, by omega⟩
    have he := congrFun (hg (k + H) k hsame) d
    simp only [packetReading, packet, if_pos hr] at he
    have hres : d % b = (affineTarget M b r (k + H)).toNat := by
      apply Classical.byContradiction
      intro hh
      simp [hh, Ne.symm hn] at he
    have hnon (j : Int) : 0 ≤ affineTarget M b r j :=
      Int.emod_nonneg _ (by omega)
    have haa : affineTarget M b r (k+H) = affineTarget M b r k := by
      have h₁ := hnon (k + H)
      have h₂ := hnon k
      omega
    have hemod := Int.emod_eq_emod_iff_emod_sub_eq_zero.mp haa
    have halg : r + (M : Int) * (k + H) - (r + M * k) = (M : Int) * H := by grind
    rw [halg] at hemod
    apply (reduced_target_dvd_iff _ _ _ hb).mpr
    exact Int.ofNat_dvd.mp (by simpa only [Int.natCast_mul] using Int.dvd_of_emod_eq_zero hemod)
  · intro h k j hobs
    by_cases hv : Occupied a M b r
    · have he := (target_constant_on_quotient_fibers_iff M b H r hb).mpr (h hv) k j hobs
      funext d
      simp only [packetReading, he]
    · funext d
      rw [empty_packet hv, empty_packet hv]

theorem least_occupied (a : Nat → Int) (M b : Nat) (r : Int) (hb : 0 < b)
    (hv : Occupied a M b r) :
    LeastPositive (Admits a M b r) (reducedTargetPeriod M b) := by
  refine ⟨reduced_target_period_pos _ _ hb, (packet_criterion _ _ _ _ _ hb).mpr
    (fun _ => Nat.dvd_refl _), ?_⟩
  intro J hJ hj
  exact Nat.le_of_dvd hJ ((packet_criterion _ _ _ _ _ hb).mp hj hv)

theorem least_unoccupied (a : Nat → Int) (M b : Nat) (r : Int) (hb : 0 < b)
    (hv : ¬ Occupied a M b r) : LeastPositive (Admits a M b r) 1 := by
  exact ⟨by decide, (packet_criterion _ _ _ _ _ hb).mpr (fun h => (hv h).elim),
    fun _ hJ _ => hJ⟩

private theorem least_unique {P : Nat → Prop} {H J : Nat}
    (hH : LeastPositive P H) (hJ : LeastPositive P J) : H = J :=
  Nat.le_antisymm (hH.least J hJ.positive hJ.admits) (hJ.least H hH.positive hH.admits)

theorem packet_minimum_dichotomy (a : Nat → Int) (M b : Nat) (r : Int) (H : Nat)
    (hb : 0 < b) (h : LeastPositive (Admits a M b r) H) : H = 1 ∨ H = reducedTargetPeriod M b := by
  by_cases hv : Occupied a M b r
  · exact Or.inr (least_unique h (least_occupied a M b r hb hv))
  · exact Or.inl (least_unique h (least_unoccupied a M b r hb hv))

/-- At one common target and chart, even a test of actual coefficient-packet
values cannot recover the three historical labels as least resolutions. -/
theorem no_common_target (M b : Nat) (r : Int) (hb : 0 < b) :
    ¬ ∀ s : Name, LeastPositive (Admits (coeff s) M b r) (historicalOrder s) := by
  intro hall
  have h₃ := packet_minimum_dichotomy _ _ _ _ _ hb (hall .f)
  have h₅ := packet_minimum_dichotomy _ _ _ _ _ hb (hall .f0)
  simp only [historicalOrder] at h₃ h₅
  omega

private theorem reached34 (r : Int) (d : Nat) (hd : (d : Int) % 2 = r % 2) :
    ∃ k : Int, d % 34 = (affineTarget selectedPrimary 34 r k).toNat := by
  let j := ((d : Int) - r) / 2
  have hdiff : r + 2*j = (d : Int) := by dsimp [j]; omega
  refine ⟨13*j, ?_⟩
  change d % 34 = ((r + 30030*(13*j)) % 34).toNat
  have he : r + 30030*(13*j) = d + (11482*j)*34 := by omega
  rw [he]
  simp [Int.add_emod]
  omega

private theorem occupied_of_degree34 (a : Nat → Int) (r : Int) (d : Nat)
    (hd : a d ≠ 0) (hp : (d : Int) % 2 = r % 2) : Occupied a selectedPrimary 34 r := by
  obtain ⟨k,hk⟩ := reached34 r d hp
  exact ⟨d,k,hd,hk⟩

set_option maxRecDepth 12000 in
/-- Each actual series has an occupied even degree among 0, 2, 4 and an
occupied odd degree among 1, 3. This covers both affine orbits at target 34. -/
theorem all_seventeen_occupied34 (s : Name) (r : Int) : Occupied (coeff s) selectedPrimary 34 r := by
  have hw : ((coeff s 0 : Int) ≠ 0 ∨ (coeff s 2 : Int) ≠ 0 ∨ (coeff s 4 : Int) ≠ 0) ∧
      ((coeff s 1 : Int) ≠ 0 ∨ (coeff s 3 : Int) ≠ 0) := by
    cases s <;> decide +kernel
  by_cases hp : r % 2 = 0
  · rcases hw.1 with h | h | h
    all_goals exact occupied_of_degree34 _ _ _ h (by omega)
  · rcases hw.2 with h | h
    all_goals exact occupied_of_degree34 _ _ _ h (by omega)

theorem all_seventeen_exact34 (s : Name) (r : Int) (H : Nat) :
    Admits (coeff s) selectedPrimary 34 r H ↔ 17 ∣ H := by
  rw [packet_criterion _ _ _ _ _ (by decide)]
  have h : reducedTargetPeriod selectedPrimary 34 = 17 := by decide
  rw [h]
  exact ⟨fun h' => h' (all_seventeen_occupied34 s r), fun h' _ => h'⟩

theorem all_seventeen_least34 (s : Name) (r : Int) :
    LeastPositive (Admits (coeff s) selectedPrimary 34 r) 17 :=
  least_occupied _ _ _ _ (by decide) (all_seventeen_occupied34 s r)

theorem historical_order_fails34 (s : Name) (r : Int) :
    ¬ Admits (coeff s) selectedPrimary 34 r (historicalOrder s) := by
  rw [all_seventeen_exact34]
  cases s <;> decide

theorem repo_targets :
    reducedTargetPeriod selectedPrimary 3 = 1 ∧ reducedTargetPeriod selectedPrimary 5 = 1 ∧
    reducedTargetPeriod selectedPrimary 7 = 1 ∧ reducedTargetPeriod selectedPrimary 10 = 1 ∧
    reducedTargetPeriod selectedPrimary 34 = 17 := by decide

#print axioms finite_transform
#print axioms least_universal_target
#print axioms packet_criterion
#print axioms least_occupied
#print axioms least_unoccupied
#print axioms packet_minimum_dichotomy
#print axioms no_common_target
#print axioms all_seventeen_occupied34
#print axioms all_seventeen_exact34
#print axioms all_seventeen_least34
#print axioms historical_order_fails34
#print axioms repo_targets

end OrderTest
