-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SphericalC1LocalAgreement

/-! Initial states already outside the open collar are handled at time zero;
the pre-exit condition is then empty at every positive time. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalC1LocalAgreement
open MeasureTheory ProbabilityTheory SphericalAging
open SphericalAging.HardSphereDynamics
open SlowEquilibration.SphericalC1Dynamics
open scoped NNReal ENNReal
set_option autoImplicit false

variable {N : ℕ}

theorem c1Process_agree_before_open_exit_anyInitial
    (hN : N ≠ 0) (β : ℝ)
    (g g' : State N → State N)
    (hg : ContDiff ℝ 1 g) (hg' : ContDiff ℝ 1 g')
    (z : State N → ℝ) (hz : Continuous z)
    (hgrad : ∀ y, z y < 1 → g y = g' y)
    (x : State N) (hx : OnSphere x) (T : ℝ≥0) :
    ∀ᵐ ω ∂VectorBrownian.law N, ∀ t, t ≤ T →
      (∀ s, s < t → z (process β g hg x s ω) < 1) →
      process β g hg x t ω = process β g' hg' x t ω := by
  by_cases hT : 0 < T
  · by_cases hxz : z x < 1
    · exact c1Process_agree_before_open_exit hN β g g' hg hg' z hz hgrad x hx hxz T hT
    · filter_upwards [process_zero β g hg x, process_zero β g' hg' x] with ω hzero hzero'
      intro t _ hbefore
      by_cases hzeroT : t = 0
      · subst t
        exact hzero.trans hzero'.symm
      · have hpos : 0 < t := lt_of_le_of_ne bot_le (Ne.symm hzeroT)
        have hh := hbefore 0 hpos
        rw [hzero] at hh
        exact False.elim (hxz hh)
  · have hT0 : T = 0 := le_antisymm (le_of_not_gt hT) bot_le
    filter_upwards [process_zero β g hg x,process_zero β g' hg' x] with ω hzero hzero'
    intro t ht _
    have ht0 : t = 0 := le_antisymm (hT0 ▸ ht) bot_le
    subst t
    exact hzero.trans hzero'.symm

end SlowEquilibration.SphericalC1LocalAgreement
