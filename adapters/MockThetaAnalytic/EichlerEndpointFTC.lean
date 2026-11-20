import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.Complex.Basic

/-! Endpoint values of a primitive on an open vertical ray with integrable derivative. -/

noncomputable section
namespace MockThetaAnalytic
open MeasureTheory Filter Set
open scoped Topology

/-- Removing the bottom of an absolutely integrable ray integral recovers the
whole integral as the positive cutoff tends to zero. -/
theorem tendsto_eichlerTail_zero (g : ℝ → ℂ) (hg : IntegrableOn g (Ioi 0)) :
    Tendsto (fun b : ℝ => ∫ t in Ioi b, g t) (𝓝[>] 0) (𝓝 (∫ t in Ioi (0 : ℝ), g t)) := by
  have cover : AECover (volume.restrict (Ioi (0 : ℝ))) (𝓝[>] (0 : ℝ)) Ioi := by
    constructor
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds ht)
    · exact fun _ => measurableSet_Ioi
  apply (cover.integral_tendsto_of_countably_generated hg).congr'
  filter_upwards [self_mem_nhdsWithin] with b hb
  change (∫ t, g t ∂(volume.restrict (Ioi 0)).restrict (Ioi b)) = _
  rw [Measure.restrict_restrict measurableSet_Ioi, inter_eq_left.mpr (Ioi_subset_Ioi hb.le)]

/-- If a primitive has an absolutely integrable derivative on the positive
ray, both endpoint limits exist and their difference is its derivative's integral. -/
theorem primitive_ray_endpoints (F g : ℝ → ℂ) (hg : IntegrableOn g (Ioi 0))
    (hderiv : ∀ t : ℝ, 0 < t → HasDerivAt F (g t) t) :
    ∃ T : ℂ, Tendsto F atTop (𝓝 T) ∧
      Tendsto F (𝓝[>] 0) (𝓝 (T - ∫ t in Ioi (0 : ℝ), g t)) := by
  have htop := tendsto_limUnder_of_hasDerivAt_of_integrableOn_Ioi hderiv hg
  refine ⟨_, htop, ((tendsto_const_nhds (x := limUnder atTop F)).sub
    (tendsto_eichlerTail_zero g hg)).congr' ?_⟩
  filter_upwards [self_mem_nhdsWithin] with b hb
  have h := integral_Ioi_of_hasDerivAt_of_tendsto' (a := b)
    (fun t ht => hderiv t (lt_of_lt_of_le hb ht)) (hg.mono_set (Ioi_subset_Ioi hb.le)) htop
  simp only [h, sub_sub_cancel]

end MockThetaAnalytic
