import EichlerCuspLimit
import EichlerProfile
import PeriodicSmoothing

/-! Limits of the actual vertical Eichler integrals at rational cusps.
Both lowering the reflected endpoint and removing a fixed-cusp cutoff recover
the same first moment. At the two selected cusps this is the terminating FKTY value. -/

noncomputable section

namespace MockThetaAnalytic

open Filter Set
open scoped Topology

private theorem tendsto_mesh_at_zero :
    Tendsto (fun b : ℝ => Real.sqrt (Real.pi/12*b)) (𝓝[>] 0) (𝓝[>] 0) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · have h : Continuous (fun b : ℝ => Real.sqrt (Real.pi/12*b)) := by fun_prop
    simpa using (h.continuousAt (x := (0 : ℝ))).tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi 0))
  · filter_upwards [self_mem_nhdsWithin] with b hb
    exact Real.sqrt_pos.2 (mul_pos (by positivity) hb)

private theorem tendsto_profile_moment (k : ℕ) (hk : 0 < k) (u : ℂ)
    (hu : u^(24*k) = 1) (W : ℝ → ℝ) (hz : W 0 = 1) (hc : ContinuousAt W 0)
    (ha : AntitoneOn W (Ici 0)) (hv : ConvexOn ℝ (Ici 0) W)
    (hs : ∀ h : ℝ, 0 < h → Summable (fun m : ℕ => W (m*h))) :
    Tendsto (fun b : ℝ => 2 * fktyScale * ∑' m : ℕ,
      fktyCuspCoefficient u m * (W (m*Real.sqrt (Real.pi/12*b)) : ℂ)) (𝓝[>] 0)
      (𝓝 (2*fktyScale*fktyCuspMoment (24*k) u)) := by
  have h := tendsto_periodic_convex_smoothing (24*k) (by omega) (fktyCuspCoefficient u)
    (fktyCuspCoefficient_period k u hu) (sum_fktyCuspCoefficient_eq_zero k u hu) W hz hc ha hv hs
  exact (h.comp tendsto_mesh_at_zero).const_mul _

/-- Both FKTY vertical cutoff conventions at a root of period 24k have a limit
given by the first moment of its signed coefficient array. -/
theorem fktyEichler_boundaryLimits_of_period (x : ℝ) (k : ℕ) (hk : 0 < k)
    (hu : integerNome ((x : ℂ)/24) ^ (24*k) = 1) :
    let v := 2 * fktyScale * fktyCuspMoment (24*k) (integerNome ((x : ℂ)/24))
    Tendsto (fun b : ℝ => fktyEichlerTrunc x b b) (𝓝[>] 0) (𝓝 v) ∧
    Tendsto (fun b : ℝ => fktyEichlerTrunc x b 0) (𝓝[>] 0) (𝓝 v) := by
  constructor
  · apply (tendsto_profile_moment k hk _ hu eichlerProfile eichlerProfile_zero
      continuous_eichlerProfile.continuousAt antitoneOn_eichlerProfile convexOn_eichlerProfile
      summable_eichlerProfile_mesh).congr'
    filter_upwards [self_mem_nhdsWithin] with b hb
    exact (fktyEichlerTrunc_eq_lower_series x b hb).symm
  · apply (tendsto_profile_moment k hk _ hu erfc erfc_zero continuous_erfc.continuousAt
      antitoneOn_erfc convexOn_erfc summable_erfc_mesh).congr'
    filter_upwards [self_mem_nhdsWithin] with b hb
    exact (fktyEichlerTrunc_eq_boundary_series x b hb).symm

/-- The lower Eichler integral at −1/34 and the truncated fixed-parameter
integral both tend to the normalized terminating quantum value. -/
theorem fktyEichler_boundaryLimits34 :
    Tendsto (fun b : ℝ => fktyEichlerTrunc (-1/34) b b) (𝓝[>] 0) (𝓝 (fktyPhi (-1/34))) ∧
    Tendsto (fun b : ℝ => fktyEichlerTrunc (-1/34) b 0) (𝓝[>] 0) (𝓝 (fktyPhi (-1/34))) := by
  have hx : (((-1/34 : ℝ) : ℂ)/24) = -1/816 := by push_cast; norm_num
  have hr := (Complex.isPrimitiveRoot_exp_rat (-1/816)).pow_eq_one
  rw [show (-1/816 : ℚ).den = 816 by decide +kernel] at hr
  have hu : integerNome (-1/816) ^ (24*34) = 1 := by
    simpa [integerNome] using hr
  rw [fktyPhi_eq_cuspMoment34]
  simpa only [hx] using fktyEichler_boundaryLimits_of_period (-1/34) 34 (by decide) (hx ▸ hu)

/-- The corresponding two limits at the reflected order-ten cusp. -/
theorem fktyEichler_boundaryLimits10 :
    Tendsto (fun b : ℝ => fktyEichlerTrunc (-1/10) b b) (𝓝[>] 0) (𝓝 (fktyPhi (-1/10))) ∧
    Tendsto (fun b : ℝ => fktyEichlerTrunc (-1/10) b 0) (𝓝[>] 0) (𝓝 (fktyPhi (-1/10))) := by
  have hx : (((-1/10 : ℝ) : ℂ)/24) = -1/240 := by push_cast; norm_num
  have hr := (Complex.isPrimitiveRoot_exp_rat (-1/240)).pow_eq_one
  rw [show (-1/240 : ℚ).den = 240 by decide +kernel] at hr
  have hu : integerNome (-1/240) ^ (24*10) = 1 := by
    simpa [integerNome] using hr
  rw [fktyPhi_eq_cuspMoment10]
  simpa only [hx] using fktyEichler_boundaryLimits_of_period (-1/10) 10 (by decide) (hx ▸ hu)

end MockThetaAnalytic
