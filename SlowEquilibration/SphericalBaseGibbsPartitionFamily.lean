-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalLocalizedCoefficientFamily
public import SlowEquilibration.SphericalZeroGibbsLaw
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions

/-! Actual sphere partition continuity from the continuous linear integral
of a compact-localized bounded continuous family. The original finite tensor
model supplies its joint field continuity internally. -/
@[expose] public section
noncomputable section
open MeasureTheory Filter
open scoped BoundedContinuousFunction ENNReal
namespace SlowEquilibration.SphericalModel
open SphericalForm
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
variable {N : ℕ} {Θ : Type*} [TopologicalSpace Θ]

/-- The literal sphere integral on bounded continuous functions, as a
continuous linear map obtained from the actual finite probability measure. -/
def sphereBoundedIntegralCLM (N : ℕ) : (Vector N →ᵇ ℝ) →L[ℝ] ℝ := by
  let _ := sphereLaw_probability N
  exact (L1.integralCLM (α := Vector N) (E := ℝ) (μ := sphereLaw N)).comp
    (BoundedContinuousFunction.toLp 1 (sphereLaw N) ℝ)

theorem sphereBoundedIntegralCLM_apply (f : Vector N →ᵇ ℝ) :
    sphereBoundedIntegralCLM N f=∫ x,f x ∂sphereLaw N := by
  let _ := sphereLaw_probability N
  unfold sphereBoundedIntegralCLM
  rw [ContinuousLinearMap.comp_apply,← L1.integral_eq,L1.integral_eq_integral]
  exact integral_congr_ae (BoundedContinuousFunction.coeFn_toLp 1 (sphereLaw N) ℝ f)

/-- Joint continuity on the actual spatial domain yields true continuity
of the normalizing sphere integral through a fixed compact localization. -/
theorem jointHamiltonianPartition_continuous (hN : 1 ≤ N) (β : ℝ)
    (H : Θ×Vector N→ℝ) (hH : Continuous H) :
    Continuous (fun p => partition N β (fun x => H (p,x))) := by
  let F : Θ×Vector N→ℝ := fun z => Real.exp (β*H z)
  have hF : Continuous F := Real.continuous_exp.comp (hH.const_mul β)
  let B := sphericalLocalizedFamily F hF
  have hB : Continuous B := sphericalLocalizedFamily_continuous F hF
  have hEq (p : Θ) : sphereBoundedIntegralCLM N (B p)=partition N β (fun x => H (p,x)) := by
    rw [sphereBoundedIntegralCLM_apply]
    apply integral_congr_ae
    have hAE := sphericalLocalizedFamily_ae hN 0 (fun _ => 0) F hF p
    rw [gibbsLaw_zeroHamiltonian] at hAE
    exact hAE
  have hc := (sphereBoundedIntegralCLM N).continuous.comp hB
  simpa only [Function.comp_def,hEq] using hc

/-- The actual original Gaussian mixture partition varies continuously
with the genuine finite ordered-tensor disorder. No partition or field
continuity assertion is required as an assumption. -/
theorem mixturePartition_continuous (hN : 1 ≤ N) (μ : FiniteMixture) (β : ℝ) :
    Continuous (mixturePartition (N := N) μ β) := by
  exact jointHamiltonianPartition_continuous hN β
    (fun z : Disorder N μ.maxDegree×Vector N => fieldOfMixture μ z.1 z.2)
    (field_jointContinuous (mixtureCoefficients μ))

theorem mixturePartition_jointContinuous (hN : 1 ≤ N) (μ : FiniteMixture) (β : ℝ) :
    Continuous (fun z : Disorder N μ.maxDegree×Vector N =>
      partition N β (fieldOfMixture μ z.1)) :=
  (mixturePartition_continuous hN μ β).comp continuous_fst

end SlowEquilibration.SphericalModel
