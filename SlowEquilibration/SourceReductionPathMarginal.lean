-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourceReductionPointCapMass

/-! A one-time evaluation of the literal real-time diffusion path is the
original mixed Langevin transition law, at every time in the horizon. -/

@[expose] public section
namespace SlowEquilibration.SourceReductionPathMarginal
noncomputable section
open Set MeasureTheory ProbabilityTheory SphericalModel SphericalDynamics
open SphericalRealTimePathKernel SphericalFullFieldPathKernel
open SphericalRotationCovariance SphericalFieldKernels
open SphericalAging.HardSphereDynamics
open scoped NNReal ENNReal RealInnerProductSpace Topology
set_option autoImplicit false
set_option maxHeartbeats 1000000

variable {N : ℕ}

def nnrealTime {T : ℝ≥0} (t : RealPathTime T) : ℝ≥0 :=
  ⟨t.1,t.2.1⟩

/-- The physical path kernel evaluated at an arbitrary time has exactly the
original diffusion transition law in ambient spherical coordinates. -/
theorem realPathKernel_original_eval_ambient (hN : 2 ≤ N)
    (μ : FiniteMixture) (β : ℝ) (T : ℝ≥0)
    (J : Disorder N μ.maxDegree) (x : PhysicalSphere N)
    (t : RealPathTime T) :
    (realPathKernel μ β T (fieldMap μ J,x)).map
      (fun p : RealSpherePath N T => (p t).1) =
        mixedTransitionKernel μ J β (nnrealTime t) x.1 := by
  let E : RealSpherePath N T → Vector N := fun p => (p t).1
  let R : SphericalAging.VectorBrownian.Space N → RealSpherePath N T :=
    fun ω => realPathEquiv T (spherePathRepresentative μ J β x T ω)
  have hE : Measurable E :=
    measurable_subtype_coe.comp (ContinuousMap.measurable_eval t)
  have hR : Measurable R :=
    (realPathEquiv T).measurable.comp (spherePathRepresentative_measurable μ J β x T)
  rw [realPathKernel_fieldMap (by omega : 1 ≤ N) μ β T J x]
  rw [Measure.map_map hE hR]
  rw [mixedTransitionKernel_apply,mixedTransitionLaw]
  apply Measure.map_congr
  filter_upwards [realPathRepresentative_ae_actual (by omega : 1 ≤ N)
      μ J β x T] with ω hω
  exact hω t

end
end SlowEquilibration.SourceReductionPathMarginal
