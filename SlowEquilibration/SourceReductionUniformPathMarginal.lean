-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourceReductionPathMarginal
public import SlowEquilibration.SourceReductionTrueCapPathWeight

/-! The real-time uniform-start path marginal is the actual physical
uniform-start Langevin transition measure at every time in its horizon. -/

@[expose] public section
namespace SlowEquilibration.SourceReductionUniformPathMarginal
noncomputable section
open Set MeasureTheory ProbabilityTheory SphericalModel SphericalDynamics
open SphericalRealTimePathKernel SphericalFullFieldPathKernel
open SourceReductionPathMarginal SourceReductionTrueCapPathWeight
open SphericalKacRiceHittingSource SphericalRotationCovariance SphericalFieldKernels
open SphericalFullFieldSphereTV
open SphericalAging.HardSphereDynamics
open scoped NNReal ENNReal RealInnerProductSpace Topology
set_option autoImplicit false
set_option maxHeartbeats 1000000

variable {N : ℕ}

/-- Equality of the literal uniform-start real path evaluation and the
ordinary original-disorder Markov semigroup at any time in `[0,T]`. -/
theorem uniformRealPathKernel_eval_real_eq_evolved (hN : 2 ≤ N)
    (μ : FiniteMixture) (β : ℝ) (T : ℝ≥0)
    (J : Disorder N μ.maxDegree) (t : RealPathTime T)
    {A : Set (Vector N)} (hA : MeasurableSet A) :
    (uniformRealPathKernel hN μ β T (fieldMap μ J)).real
      {p : RealSpherePath N T | (p t).1 ∈ A} =
      (mixedTransitionKernel μ J β (nnrealTime t) ∘ₘ sphereLaw N).real A := by
  let E : RealSpherePath N T → Vector N := fun p => (p t).1
  have hE : Measurable E :=
    measurable_subtype_coe.comp (ContinuousMap.measurable_eval t)
  have hEA : MeasurableSet (E ⁻¹' A) := hA.preimage hE
  have hright : (mixedTransitionKernel μ J β (nnrealTime t) ∘ₘ sphereLaw N).real A =
      ∫ x : Vector N,
        (mixedTransitionKernel μ J β (nnrealTime t) x).real A ∂sphereLaw N := by
    rw [Measure.real, Measure.bind_apply hA (mixedTransitionKernel μ J β (nnrealTime t)).aemeasurable]
    exact (integral_toReal
      ((mixedTransitionKernel μ J β (nnrealTime t)).measurable_coe hA).aemeasurable
      (.of_forall fun x => measure_lt_top _ _)).symm
  rw [hright]
  change (uniformRealPathKernel hN μ β T (fieldMap μ J)).real (E ⁻¹' A) = _
  rw [uniformRealPathKernel_real_eq_integral hN μ β T (fieldMap μ J) hEA]
  apply integral_congr_ae
  filter_upwards [sphereLaw_support (by omega : 1 ≤ N)] with x hx
  let X : PhysicalSphere N := ⟨x,(onSphere_iff_norm_sq x).mpr hx⟩
  have hrec : sphereStateRecovery (sphereBasepoint (by omega : 1 ≤ N)) x = X := by
    exact Subtype.ext (by simp [sphereStateRecovery, X, (onSphere_iff_norm_sq x).mpr hx])
  rw [hrec]
  have hfix := realPathKernel_original_eval_ambient hN μ β T J X t
  have hm := map_measureReal_apply (μ := realPathKernel μ β T (fieldMap μ J,X)) hE hA
  rw [hfix] at hm
  exact hm.symm

end
end SlowEquilibration.SourceReductionUniformPathMarginal
