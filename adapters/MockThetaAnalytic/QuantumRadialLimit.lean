import QuantumRadial
import MockTheta
import Mathlib.Algebra.Ring.GrindInstances
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Complex.Norm
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-! Transfer of a compensated radial limit to finite coefficient packets.
The two analytic inputs in the specialization are the interior Taylor expansion
and the Folsom–Ono–Rhoades limit at the chosen primitive even cusp. -/

noncomputable section

namespace MockThetaAnalytic
open Filter KElimination KElimination.ResidueSeries
open scoped Topology

/-- The integer coefficients of the original third-order f, in the complex plane. -/
def complexFCoeff (d : ℕ) : ℂ := ((MockTheta.mockCoeff d : ℤ) : ℂ)

/-- Pair the retained finite degree packets with the chosen character. -/
def fPacketAtRadius (N L : ℕ) (t : ℝ) (ζ : ℂ) : ℂ :=
  sumBelow L (fun r => weightedPacket complexFCoeff (fun d => (t : ℂ)^d) N L r * ζ^r)

private theorem sumBelow_complex (u : ℕ → ℂ) (N : ℕ) :
    sumBelow N u = ∑ d ∈ Finset.range N, u d := by
  induction N with
  | zero => simp [sumBelow]
  | succ n ih => simp [sumBelow, Finset.sum_range_succ, ih]

theorem fPacketAtRadius_eq_polynomial (N L b : ℕ) (t : ℝ) (ζ : ℂ)
    (hL : 0 < L) (hd : b ∣ L) (hz : ζ^b = 1) :
    fPacketAtRadius N L t ζ = ∑ d ∈ Finset.range N, complexFCoeff d * ((t : ℂ)*ζ)^d := by
  rw [fPacketAtRadius, finite_root_evaluation_of_dvd complexFCoeff (t : ℂ) ζ N b L hL hd hz,
    sumBelow_complex]

/-- The accuracy threshold can depend on the radius. Every larger finite
truncation still works. This needs only pointwise convergence inside the disk. -/
theorem exists_packet_cutoffs (r : ℕ → ℝ) (f : ℂ → ℂ) (L b : ℕ) (ζ : ℂ)
    (hL : 0 < L) (hd : b ∣ L) (hz : ζ^b = 1)
    (hTaylor : ∀ j, HasSum (fun d => complexFCoeff d * ((r j : ℂ)*ζ)^d) (f ((r j : ℂ)*ζ))) :
    ∃ K : ℕ → ℕ, (∀ j, j ≤ K j) ∧ ∀ j N, K j ≤ N →
      ‖fPacketAtRadius N L (r j) ζ - f ((r j : ℂ)*ζ)‖ ≤ 1 / ((j : ℝ)+1) := by
  classical
  have exists_bound (j : ℕ) : ∃ N₀ : ℕ, ∀ N ≥ N₀,
      dist (∑ d ∈ Finset.range N, complexFCoeff d * ((r j : ℂ)*ζ)^d) (f ((r j : ℂ)*ζ))
        < 1 / ((j : ℝ)+1) :=
    (Metric.tendsto_atTop.1 (hTaylor j).tendsto_sum_nat) _ (by positivity)
  choose bound hb using exists_bound
  refine ⟨fun j => max j (bound j), fun j => le_max_left _ _, ?_⟩
  intro j N hN
  rw [fPacketAtRadius_eq_polynomial N L b (r j) ζ hL hd hz, ← dist_eq_norm]
  exact (hb j N ((le_max_right j _).trans hN)).le

/-- Ramanujan's f from its defining series, evaluated only at interior points in the limit theorem. -/
def radialF (q : ℂ) : ℂ :=
  ∑' n : ℕ, q^(n*n) / (∏ j ∈ Finset.range n, (1 + q^(j+1))^2)

/-- The compensating modular product b(q) = (q;q)∞ / (−q;q)∞². -/
def radialB (q : ℂ) : ℂ :=
  ∏' n : ℕ, (1 - q^(n+1)) / (1 + q^(n+1))^2

/-- With the published compensated limit as input, finite packets converge to
the same terminating boundary value along every radial approach. The choice of
cutoff controls approximation of f before the modular correction is subtracted. -/
theorem for_limit_from_f_packets (ζ : ℂ) (k L : ℕ)
    (hζ : IsPrimitiveRoot ζ (2*k)) (hL : 0 < L) (hperiod : 2*k ∣ L)
    (r : ℕ → ℝ) (hr : ∀ j, 0 < r j ∧ r j < 1) (hlim : Tendsto r atTop (𝓝[<] (1 : ℝ)))
    (hTaylor : ∀ t : ℝ, 0 < t → t < 1 →
      HasSum (fun d => complexFCoeff d * ((t : ℂ)*ζ)^d) (radialF ((t : ℂ)*ζ)))
    (hFOR : Tendsto (fun t : ℝ => radialF ((t : ℂ)*ζ) - (-1 : ℂ)^k * radialB ((t : ℂ)*ζ))
      (𝓝[<] (1 : ℝ)) (𝓝 (QuantumRadial.boundaryValue k ζ))) :
    ∃ K : ℕ → ℕ, (∀ j, j ≤ K j) ∧ ∀ N : ℕ → ℕ, (∀ j, K j ≤ N j) →
      Tendsto (fun j => fPacketAtRadius (N j) L (r j) ζ - (-1 : ℂ)^k * radialB ((r j : ℂ)*ζ))
        atTop (𝓝 (QuantumRadial.boundaryValue k ζ)) := by
  obtain ⟨K, hK, hdist⟩ := exists_packet_cutoffs r radialF L (2*k) ζ hL hperiod hζ.pow_eq_one
    (fun j => hTaylor _ (hr j).1 (hr j).2)
  refine ⟨K, hK, ?_⟩
  intro N hN
  have herr : Tendsto (fun j => fPacketAtRadius (N j) L (r j) ζ - radialF ((r j : ℂ)*ζ))
      atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun j => hdist j (N j) (hN j))
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  have ha := herr.add (hFOR.comp hlim)
  simpa only [Function.comp_apply, Pi.add_apply, sub_add_sub_cancel, zero_add] using ha

end MockThetaAnalytic
