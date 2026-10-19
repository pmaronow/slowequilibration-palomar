-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GOEPhysicalCovarianceTrace

/-! Genuine finite ordinary integrability of the physical covariance-
weighted clipped inverse trace at every real shift. -/
@[expose] public section
namespace SlowEquilibration.GOEClippedResolvent
noncomputable section
open Function MeasureTheory ProbabilityTheory
open GOEAsymptotics SphericalGaussianJet GOEScaling
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

theorem physicalCovarianceTrace_square_integrable (n j : ℕ) {b ρ : ℝ}
    (hb : 0 < b) (hρ : 0 < ρ) (k t : ℝ) :
    Integrable (fun W:Matrix (Fin (n+1)) (Fin (n+1)) ℝ=>
      (physicalCovarianceTrace n j b k ρ W-t)^2) (goeLaw (n+1) (n+1+j) b) := by
  let α:=(scaleFactor n (n+1+j) b)^2
  have hα : α≠0:=(sq_pos_of_pos (scaleFactor_pos n (by omega) hb)).ne'
  have hh:=(physicalClippedResolvent_centered_square_integrable n j hb hρ k (t/α)).const_mul (α^2)
  convert hh using 1
  funext W
  unfold physicalCovarianceTrace
  change (α*physicalClippedResolvent n j b k ρ W-t)^2=
    α^2*(physicalClippedResolvent n j b k ρ W-t/α)^2
  field_simp

lemma physicalCovarianceTrace_measurable (n j : ℕ) (b k ρ : ℝ) :
    Measurable (physicalCovarianceTrace n j b k ρ) :=
  measurable_const.mul (physicalClippedTrace_measurable n k _)

end
end SlowEquilibration.GOEClippedResolvent

