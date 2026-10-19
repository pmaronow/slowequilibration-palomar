-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GOEClippedResolventConvergence
public import SlowEquilibration.BoundedQuadraticConvergence

/-! Genuine actual outside-edge clipped GOE trace convergence in L².
Its probability limit and boundedness are derived from the true GOE law. -/
@[expose] public section
namespace SlowEquilibration.GOEClippedResolvent
noncomputable section
open Function MeasureTheory ProbabilityTheory Filter Set
open GOEAsymptotics SphericalGaussianJet OAI.CriticalSK BoundedQuadraticConvergence
open scoped Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

/-- Actual normalized clipped GOE resolvent converges in mean square to
the true outside semicircle value. There is no asymptotic premise. -/
theorem clippedResolvent_converges_in_L2 {s ρ : ℝ} (hs : 0 < s) (hρ : 0 < ρ) (hρs : ρ ≤ s/2) :
    Tendsto (fun n:ℕ=>∫ W,(clippedResolvent n s ρ W-semicircleResolvent s)^2
      ∂goeLaw (n+1) (n+1) 1) atTop (𝓝 0) := by
  apply integral_square_tendsto_zero (μ:=fun n=>goeLaw (n+1) (n+1) 1)
    (X:=fun n W=>clippedResolvent n s ρ W-semicircleResolvent s)
    (fun n=>(clippedResolvent_measurable n s ρ).sub_const _) (C:=1/ρ+|semicircleResolvent s|)
    (by positivity)
  · intro n W
    have hb:=clippedResolvent_bounds n s hρ W
    calc
      _ ≤ |clippedResolvent n s ρ W|+|semicircleResolvent s|:=abs_sub _ _
      _ ≤ 1/ρ+|semicircleResolvent s|:=by rw [abs_of_nonneg hb.1];gcongr;exact hb.2
  · intro ε hε
    exact clippedResolvent_converges_in_probability hs hρs hε

end
end SlowEquilibration.GOEClippedResolvent
