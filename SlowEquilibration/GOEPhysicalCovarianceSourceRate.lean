-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GOEPhysicalCovarianceQuantitative

/-! The genuine physical GOE inverse-trace error in the manuscript's
ambient-dimension normalization. The stronger matrix-dimension squared rate
is converted to the source's ambient inverse-dimension square bound. -/
@[expose] public section
namespace SlowEquilibration.GOEClippedResolvent
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open SphericalGaussianJet
open scoped Topology
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Actual source square error O(1/N), uniformly over the physical fixed
gap ray and using the literal cutoff a_N*rho and genuine variance-b/N law. -/
theorem physical_covariance_trace_source_L2_rate (j : ℕ) {b g ρ : ℝ}
    (hb : 0 < b) (hg : 0 < g) (hρ : 0 < ρ) (hρg : ρ ≤ (g/Real.sqrt b)/2) :
    ∃ C : ℝ,0 < C ∧ ∀ᶠ n : ℕ in atTop,∀ k : ℝ,2*Real.sqrt b+g≤k →
      (∫ W,(physicalCovarianceTrace n j b k ρ W-b*physicalResolvent b k)^2
        ∂goeLaw (n+1) (n+1+j) b) ≤ C/((n+1+j:ℕ):ℝ) := by
  obtain ⟨C,hC,h⟩:=physical_covariance_trace_uniform_L2_rate j hb hg hρ hρg
  refine ⟨C*(j+1:ℝ),by positivity,?_⟩
  filter_upwards [h] with n hn
  intro k hk
  have hN : 0 < (n+1:ℝ):=by positivity
  have hAmbient : 0 < ((n+1+j:ℕ):ℝ):=by positivity
  have hdim : ((n+1+j:ℕ):ℝ)≤(j+1:ℝ)*(n+1:ℝ)^2 := by
    simp only [Nat.cast_add,Nat.cast_one]
    have hn0 : 0 ≤ (n:ℝ):=by positivity
    have hj0 : 0 ≤ (j:ℝ):=by positivity
    nlinarith [mul_nonneg hn0 hj0,mul_nonneg (sq_nonneg (n:ℝ)) hj0]
  apply (hn k hk).trans
  apply (div_le_div_iff₀ (sq_pos_of_pos hN) hAmbient).mpr
  nlinarith [mul_le_mul_of_nonneg_left hdim hC.le]

end
end SlowEquilibration.GOEClippedResolvent
