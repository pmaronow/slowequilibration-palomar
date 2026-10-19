-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourcePhysicalPairMarkFiber

/-! Literal full-field pair window intensity definitions. Both original
intrinsic Hessians and their true coordinate-free zero-gradient posterior
remain in the defining integrals. -/
@[expose] public section
namespace SlowEquilibration.PairConditionalDeterminantMoments
noncomputable section
open MeasureTheory ProbabilityTheory
open SphericalModel SphericalGaussianJet SphericalForm WholeFieldRegression SphereHessian
open IntrinsicGradientRegression SphericalPairIntrinsicCoordinates GaussianRegression
open SphericalMarkedWindows
open scoped ENNReal
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 600000
attribute [local instance] Classical.propDecidable

def intrinsicPairDetWeight {N P:ℕ} (c:Degree P→ℝ) (x y:Vector N)
    (J:Disorder N P):ℝ≥0∞:=
  ENNReal.ofReal |(intrinsicHessian (field c J) x).det| * 
    ENNReal.ofReal |(intrinsicHessian (field c J) y).det|

def intrinsicMixedPairWindowIntensity {N P:ℕ} (c:Degree P→ℝ) (x y:Vector N)
    (K:Set (EuclideanSpace ℝ (Fin 2))) (phi:Disorder N P→ℝ≥0∞):ℝ≥0∞:=
  observationPdf (pairIntrinsicGamma c x y) 0*
    ∫⁻ J,intrinsicPairDetWeight c x y J*
      (if actualScore c J x∈K ∧ actualScore c J y∈K then phi J else 0)
      ∂coefficientKernel (pairIntrinsicGamma c x y) 0

def intrinsicValuePairWindowIntensity {N P:ℕ} (c:Degree P→ℝ) (x y:Vector N)
    (I:Set ℝ) (phi:Disorder N P→ℝ≥0∞):ℝ≥0∞:=
  observationPdf (pairIntrinsicGamma c x y) 0*
    ∫⁻ J,intrinsicPairDetWeight c x y J*
      (if actualValue c J x∈I ∧ actualValue c J y∈I then phi J else 0)
      ∂coefficientKernel (pairIntrinsicGamma c x y) 0

end
end SlowEquilibration.PairConditionalDeterminantMoments
