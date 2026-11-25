import QuantumTransport34

/-! Character phases and translated endpoint packets from actual signed-source
observations. The two primary lanes have moduli 2 and 5. The auxiliary lane
is a reading of that same source modulo 17. -/

namespace MockThetaAnalytic.Order34Source

open KElimination.ResidueSeries KElimination.QuantumRadial
open KElimination.IntegerSpecialization BoundaryObservation34

/-- The two primary readings and one auxiliary reading consumed by the calculation. -/
structure Lanes where
  parity : ℤ
  mod5 : ℤ
  mod17 : ℤ

/-- The semantic observation of a signed source. No quotient is stored. -/
def observe (X : ℤ) : Lanes := ⟨X % 2, X % 5, X % 17⟩

/-- Add a public offset lane by lane. -/
def translate (s : Lanes) (d : ℤ) : Lanes :=
  ⟨(s.parity + d) % 2, (s.mod5 + d) % 5, (s.mod17 + d) % 17⟩

theorem translate_observe (X d : ℤ) : translate (observe X) d = observe (X + d) := by
  simp [observe, translate, Int.emod_add_emod]

/-- Lift the odd lane to its unique residue of the required parity modulo twice its modulus. -/
private def parityLift (p s oddModulus : ℤ) : ℤ := s + oddModulus * ((p - s) % 2)

def exponent34 (s : Lanes) : ℤ := parityLift s.parity s.mod17 17
def exponent10 (s : Lanes) : ℤ := parityLift s.parity s.mod5 5

/-- Both exponents agree with the signed-source residues. -/
theorem source_readout (X : ℤ) :
    exponent34 (observe X) = X % 34 ∧ exponent10 (observe X) = X % 10 := by
  unfold exponent34 exponent10 parityLift observe
  dsimp
  omega

/-- For each signed source, observe its primary and auxiliary lane together.
The existing query then computes the Euclidean quotient class on demand. -/
theorem quotient17_of_observed_source (X : ℤ) :
    query ((X % 30030) % 17) (observe X).mod17 17 15 = (X / 30030) % 17 := by
  apply quotient_from_anchor17 X (X % 30030) (X / 30030) _ _ _ rfl rfl
  rw [mul_comm (30030 : ℤ), Int.emod_add_ediv_mul]

/-- The two lifts 0 and 30030 rule out a universal primary-only quotient-class query. -/
theorem no_primary_quotient17 :
    ¬ ∃ readK : ℤ → ℤ, ∀ X : ℤ, readK (X % 30030) = (X / 30030) % 17 := by
  rintro ⟨readK, h⟩
  have h0 := h 0
  have h1 := h 30030
  norm_num at h0 h1
  omega

/-- The parity/17 readout agrees with the existing source-bound affine quotient query. -/
theorem source_readout_agrees_with_anchor (X : ℤ) :
    exponent34 (observe X) = targetLaneProjection ((X % 30030) % 34)
      (query ((X % 30030) % 17) (X % 17) 17 15) 8 34 := by
  rw [(source_readout X).1]
  symm
  apply target34_from_anchor17 X (X % 30030) (X / 30030) _ _ _ _ rfl rfl rfl
  rw [mul_comm (30030 : ℤ), Int.emod_add_ediv_mul]

noncomputable section

theorem zpow_residue (X : ℤ) {b : ℕ} (hb : b ≠ 0) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ b) : ζ ^ (X % (b : ℤ)) = ζ ^ X := by
  have hpow : ζ ^ (b : ℤ) = 1 := by simpa only [zpow_natCast] using hζ.pow_eq_one
  calc
    _ = ζ^(X % (b : ℤ)) * (ζ^(b : ℤ))^(X / (b : ℤ)) := by rw [hpow, one_zpow, mul_one]
    _ = ζ^X := by
      rw [← zpow_mul, ← zpow_add₀ (hζ.ne_zero hb), mul_comm (b : ℤ), Int.emod_add_ediv_mul]

/-- At either root the translated observations produce the character for X+d,
including negative offsets and sources. -/
theorem source_phase_shift (X d : ℤ) {ζ η : ℂ}
    (hζ : IsPrimitiveRoot ζ 34) (hη : IsPrimitiveRoot η 10) :
    ζ ^ exponent34 (translate (observe X) d) = ζ^X * ζ^d ∧
    η ^ exponent10 (translate (observe X) d) = η^X * η^d := by
  rw [translate_observe, (source_readout _).1, (source_readout _).2]
  exact ⟨(zpow_residue (X+d) (by decide : (34:ℕ) ≠ 0) hζ).trans (zpow_add₀ (hζ.ne_zero (by decide)) _ _),
    (zpow_residue (X+d) (by decide : (10:ℕ) ≠ 0) hη).trans (zpow_add₀ (hη.ne_zero (by decide)) _ _)⟩

/-- No function of the full primary remainder can return every order-34
character value. Sources zero and 30030 give the same primary input. -/
theorem no_primary_phase34 {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 34) :
    ¬ ∃ f : ℤ → ℂ, ∀ X : ℤ, f (X % 30030) = ζ^X := by
  rintro ⟨f, hf⟩
  have hzero : f 0 = 1 := by simpa using hf 0
  have hother := hf 30030
  have hpow : ζ ^ (30030 : ℕ) = 1 := by
    simpa only [Int.emod_self, hzero, ← zpow_natCast] using hother.symm
  exact (by decide : ¬34 ∣ 30030) (hζ.dvd_of_pow_eq_one _ hpow)

/-- Pair all supplied packets with their lane-generated character phases. -/
def translatedPacketValue (ζ : ℂ) (N L : ℕ) (e : Lanes → ℤ) (s : Lanes) : ℂ :=
  (-4) * sumBelow L (fun r => uPacket ζ N L r * ζ ^ e (translate s r))

private theorem translatedPacketValue_eq (X : ℤ) (ζ : ℂ) (N L : ℕ) (e : Lanes → ℤ)
    (hphase : ∀ r : ℕ, ζ ^ e (translate (observe X) r) = ζ^X * ζ^r) :
    translatedPacketValue ζ N L e (observe X) =
      ζ^X * ((-4) * sumBelow L (fun r => uPacket ζ N L r * ζ^r)) := by
  unfold translatedPacketValue
  have h := sumBelow_congr L (fun r => uPacket ζ N L r * ζ ^ e (translate (observe X) r))
    (fun r => ζ^X * (uPacket ζ N L r * ζ^r)) (fun r _ => by dsimp only; rw [hphase r]; ring)
  rw [h, sumBelow_mul_left]
  ring

/-- Starting with the three actual readings of any signed source, translate by
each packet degree and evaluate the two complete finite endpoint sums. -/
theorem source_packet_endpoints (X : ℤ) (N34 N10 : ℕ) {ζ η : ℂ}
    (hζ : IsPrimitiveRoot ζ 34) (hη : IsPrimitiveRoot η 10)
    (h34 : 17 ≤ N34) (h10 : 5 ≤ N10) :
    translatedPacketValue ζ N34 510510 exponent34 (observe X) = ζ^X * boundaryValue 17 ζ ∧
    translatedPacketValue η N10 30030 exponent10 (observe X) = η^X * boundaryValue 5 η := by
  constructor
  · rw [translatedPacketValue_eq _ _ _ _ _ (fun r => by
      simpa only [zpow_natCast] using (source_phase_shift X r hζ hη).1),
      endpoint34_from_packets N34 ζ hζ h34]
  · rw [translatedPacketValue_eq _ _ _ _ _ (fun r => by
      simpa only [zpow_natCast] using (source_phase_shift X r hζ hη).2),
      endpoint10_from_packets N10 η hη h10]

/-- FKTY's weighted difference at −1/34 and −1/10, computed from the complete
translated packets. Each character is divided out in its own target lane. -/
def normalizedPacketDefect (N34 N10 : ℕ) (s : Lanes) : ℂ :=
  let ζ := integerNome (1/34)
  let η := integerNome (1/10)
  (fktyScale * integerNome (-1/816)) *
      (translatedPacketValue ζ N34 510510 exponent34 s / ζ ^ exponent34 s) -
    (Real.sqrt (17/5) : ℂ) * ((fktyScale * integerNome (-1/240)) *
      (translatedPacketValue η N10 30030 exponent10 s / η ^ exponent10 s))

/-- The unrotated, normalized defect is the same finite boundary expression for
every signed source and every pair of cutoffs past the two terminating indices. -/
theorem normalizedPacketDefect_eq_boundary (X : ℤ) (N34 N10 : ℕ)
    (h34 : 17 ≤ N34) (h10 : 5 ≤ N10) :
    normalizedPacketDefect N34 N10 (observe X) =
      (fktyScale * integerNome (-1/816)) * boundaryValue 17 (integerNome (1/34)) -
        (Real.sqrt (17/5) : ℂ) *
          ((fktyScale * integerNome (-1/240)) * boundaryValue 5 (integerNome (1/10))) := by
  have hζ : IsPrimitiveRoot (integerNome (1/34)) 34 := by
    simpa [integerNome, mul_one_div] using Complex.isPrimitiveRoot_exp 34 (by decide)
  have hη : IsPrimitiveRoot (integerNome (1/10)) 10 := by
    simpa [integerNome, mul_one_div] using Complex.isPrimitiveRoot_exp 10 (by decide)
  obtain ⟨p34, p10⟩ := source_packet_endpoints X N34 N10 hζ hη h34 h10
  have phase34 : integerNome (1/34) ^ exponent34 (observe X) = integerNome (1/34) ^ X := by
    rw [(source_readout X).1]
    exact zpow_residue X (by decide : (34 : ℕ) ≠ 0) hζ
  have phase10 : integerNome (1/10) ^ exponent10 (observe X) = integerNome (1/10) ^ X := by
    rw [(source_readout X).2]
    exact zpow_residue X (by decide : (10 : ℕ) ≠ 0) hη
  dsimp only [normalizedPacketDefect]
  rw [p34, p10, phase34, phase10,
    mul_div_cancel_left₀ _ (zpow_ne_zero X (hζ.ne_zero (by decide))),
    mul_div_cancel_left₀ _ (zpow_ne_zero X (hη.ne_zero (by decide)))]

/-- Agreement with the completion's Eichler integral is equivalent to the
single FKTY transformation equation at the reflected cusp. -/
theorem normalizedPacketDefect_eq_period_iff (X : ℤ) (N34 N10 : ℕ)
    (h34 : 17 ≤ N34) (h10 : 5 ≤ N10) :
    normalizedPacketDefect N34 N10 (observe X) =
        fktyVerticalPeriod (fun u => xiHalf mockCompletion (u/24) / 2) (-1/24) (-1/34) ↔
      fktyPhi (-1/34) - (Real.sqrt (17/5) : ℂ) * fktyPhi (-1/10) =
        fktyVerticalPeriod fktyTheta (-1/24) (-1/34) := by
  rw [normalizedPacketDefect_eq_boundary X N34 N10 h34 h10, ← fktyPeriod34_eq_completionPeriod,
    fktyPhi_neg_one_div_34, fktyPhi_neg_one_div_10]

/-- The full FKTY law implies the particular period identity for these source packets. -/
theorem normalizedPacketDefect_eq_period (hFKTY : FKTYWeightHalfLaw) (X : ℤ) (N34 N10 : ℕ)
    (h34 : 17 ≤ N34) (h10 : 5 ≤ N10) :
    normalizedPacketDefect N34 N10 (observe X) =
      fktyVerticalPeriod (fun u => xiHalf mockCompletion (u/24) / 2) (-1/24) (-1/34) := by
  rw [normalizedPacketDefect_eq_boundary X N34 N10 h34 h10, boundary34_transport10 hFKTY,
    fktyPeriod34_eq_completionPeriod]

end
end MockThetaAnalytic.Order34Source
