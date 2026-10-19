-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GOEPhysicalClippedResolventL2

/-! Actual compact-window uniform physical GOE clipped trace L² limit,
with literal variance b/N and the explicitly scaled positive cutoff. -/
@[expose] public section
namespace SlowEquilibration.GOEClippedResolvent
noncomputable section
open Function MeasureTheory ProbabilityTheory Filter Set
open GOEAsymptotics SphericalGaussianJet CompactUniformSequence
open scoped Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

/-- Genuine physical trace convergence uniformly on each fixed compact
outside-edge shift interval; no uniform trace limit is assumed. -/
theorem uniform_physical_clipped_resolvent_L2 (j : ℕ) {b ρ k0 k1 : ℝ} (hb : 0 < b)
    (hρ : 0 < ρ) (hk0 : 2*Real.sqrt b < k0) (hρk0 : ρ ≤ (k0/Real.sqrt b-2)/2)
    {ε : ℝ} (hε : 0 < ε) : ∀ᶠ n:ℕ in atTop,∀ k ∈ Icc k0 k1,
    (∫ W,(physicalClippedResolvent n j b k ρ W-physicalResolvent b k)^2
      ∂goeLaw (n+1) (n+1+j) b) ≤ ε := by
  apply uniform_eventually_le_of_varying_limit isCompact_Icc
    (fun n k=>∫ W,(physicalClippedResolvent n j b k ρ W-physicalResolvent b k)^2
      ∂goeLaw (n+1) (n+1+j) b) _ hε
  intro φ hφ p k hk hp
  apply physical_clipped_resolvent_varying_L2 j hb hρ (lt_of_lt_of_le hk0 hk.1) _ φ hφ p hp
  exact hρk0.trans (div_le_div_of_nonneg_right
    (sub_le_sub_right (div_le_div_of_nonneg_right hk.1 (Real.sqrt_nonneg b)) 2) (by norm_num))

end
end SlowEquilibration.GOEClippedResolvent
