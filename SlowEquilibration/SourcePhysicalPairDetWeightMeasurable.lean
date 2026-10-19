-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourcePhysicalPairWindowDefinitions

/-! A narrow measurable full-field Hessian product bridge, so window
disintegration does not need to unfold the tensor derivative expressions. -/
@[expose] public section
namespace SlowEquilibration.PairConditionalDeterminantMoments
noncomputable section
open MeasureTheory SphericalModel SphericalGaussianJet SphericalMarkedWindows
open scoped ENNReal
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

lemma intrinsicPairDetWeight_measurable {n P:ℕ} (c:Degree P→ℝ) (x y:Vector (n+1))
    (hx:‖x‖^2=(n+1:ℕ)) (hy:‖y‖^2=(n+1:ℕ)) :
    Measurable (intrinsicPairDetWeight c x y):=by
  unfold intrinsicPairDetWeight
  exact (intrinsicDet_measurable c x hx).mul (intrinsicDet_measurable c y hy)

end
end SlowEquilibration.PairConditionalDeterminantMoments
