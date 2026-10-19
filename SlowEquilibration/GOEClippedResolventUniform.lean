-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GOEClippedResolventVaryingShift
public import SlowEquilibration.CompactUniformSequence

/-! Actual compact-window uniform outside-edge GOE clipped trace L²
convergence, obtained from genuine varying-shift limits and compactness. -/
@[expose] public section
namespace SlowEquilibration.GOEClippedResolvent
noncomputable section
open Function MeasureTheory ProbabilityTheory Filter Set
open GOEAsymptotics SphericalGaussianJet OAI.CriticalSK CompactUniformSequence
open scoped Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

/-- Uniform genuine mean-square convergence over every fixed compact
outside-edge shift window. No uniform spectral limit is an input. -/
theorem uniform_clippedResolvent_L2 {a b ρ : ℝ} (ha : 0 < a) (hρ : 0 < ρ) (hρa : ρ ≤ a/2)
    {ε : ℝ} (hε : 0 < ε) : ∀ᶠ n:ℕ in atTop,∀ s ∈ Icc a b,
    (∫ W,(clippedResolvent n s ρ W-semicircleResolvent s)^2 ∂goeLaw (n+1) (n+1) 1) ≤ ε := by
  apply uniform_eventually_le_of_varying_limit isCompact_Icc
    (fun n s=>∫ W,(clippedResolvent n s ρ W-semicircleResolvent s)^2 ∂goeLaw (n+1) (n+1) 1) _ hε
  intro φ hφ p s hs hp
  exact clippedResolvent_varying_shift_L2 φ hφ p hp (lt_of_lt_of_le ha hs.1) hρ (by linarith [hs.1])

end
end SlowEquilibration.GOEClippedResolvent
