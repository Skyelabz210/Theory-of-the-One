import FORWatsonTerms

/-! Boundary convergence of Watson's third-order φ(−q) at primitive roots
of order 2k with odd k. -/

noncomputable section
namespace MockThetaAnalytic

open Complex Finset Filter
open scoped Topology

/-- The nth term of Watson's third-order φ evaluated at −q. -/
def watsonPhiTerm (q : ℂ) (n : ℕ) : ℂ :=
  (-q)^(n^2) / ∏ j ∈ range n, (1 + q^(2*j+2))

/-- Watson's third-order φ(−q), in the same radial coordinate as f(q). -/
def watsonPhi (q : ℂ) : ℂ := ∑' n : ℕ, watsonPhiTerm q n

theorem watsonPhiTerm_succ (q : ℂ) (n : ℕ) :
    watsonPhiTerm q (n+1) = watsonPhiTerm q n * ((-q)^(2*n+1) / (1+q^(2*n+2))) :=
  watsonTerm_succ 2 q n

/-- The radial terms are dominated by their actual boundary magnitudes. -/
theorem norm_watsonPhiTerm_radial_le (ζ : ℂ) (hζ : IsPrimitiveRoot ζ 34)
    (t : ℝ) (ht : 0 < t) (ht' : t ≤ 1) (n : ℕ) :
    ‖watsonPhiTerm ((t:ℂ)*ζ) n‖ ≤ ‖watsonPhiTerm ζ n‖ :=
  norm_watsonTerm_radial_le (k := 17) (by decide) hζ (c := 2) (by decide) (by decide) t ht ht' n

theorem watsonPhiTerm_add_seventeen (ζ : ℂ) (hζ : IsPrimitiveRoot ζ 34) (n : ℕ) :
    watsonPhiTerm ζ (n+17) = watsonPhiTerm ζ n / 2 :=
  watsonTerm_add_halfOrder (k := 17) (by decide) hζ (c := 2) (by decide) n

theorem summable_norm_watsonPhiTerm (ζ : ℂ) (hζ : IsPrimitiveRoot ζ 34) :
    Summable (fun n : ℕ => ‖watsonPhiTerm ζ n‖) :=
  summable_norm_watsonTerm (k := 17) (by decide) hζ (c := 2) (by decide)

theorem watsonPhi_eq_two_mul_head {ζ : ℂ} {k : ℕ} (hk : 0 < k)
    (hζ : IsPrimitiveRoot ζ (2*k)) (hodd : Odd k) :
    watsonPhi ζ = 2 * ∑ n ∈ range k, watsonPhiTerm ζ n := by
  exact watsonTerm_tsum_eq_two_mul_sum hk hζ (c := 2) (hodd.add_even (by decide))

theorem watsonPhi_eq_two_mul_sum (ζ : ℂ) (hζ : IsPrimitiveRoot ζ 34) :
    watsonPhi ζ = 2 * ∑ n ∈ range 17, watsonPhiTerm ζ n :=
  watsonPhi_eq_two_mul_head (k := 17) (by decide) hζ (by decide)

/-- At every primitive even order with odd half-order, φ has its actual
series value as a radial limit. -/
theorem watsonPhi_radial_limit_of_odd {ζ : ℂ} {k : ℕ} (hk : 0 < k)
    (hζ : IsPrimitiveRoot ζ (2*k)) (hodd : Odd k) :
    Tendsto (fun t : ℝ => watsonPhi ((t:ℂ)*ζ)) (𝓝[<] 1) (𝓝 (watsonPhi ζ)) := by
  exact watsonTerm_radial_limit hk hζ (c := 2) (hodd.add_even (by decide)) (by decide) 0

theorem watsonPhi_radial_limit (ζ : ℂ) (hζ : IsPrimitiveRoot ζ 34) :
    Tendsto (fun t : ℝ => watsonPhi ((t:ℂ)*ζ)) (𝓝[<] 1) (𝓝 (watsonPhi ζ)) :=
  watsonPhi_radial_limit_of_odd (k := 17) (by decide) hζ (by decide)

end MockThetaAnalytic
