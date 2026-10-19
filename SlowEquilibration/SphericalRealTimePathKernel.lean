-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalFullFieldPathKernel

@[expose] public section

/-! # The source path kernel on the literal real closed time interval

The physical nonnegative time interval is homeomorphic to [0,T] in ℝ.
Precomposition gives an explicit Borel path equivalence, and transports
the faithful complete-polynomial source kernel to its exact real-time
continuous sphere-valued path space.
-/

namespace SlowEquilibration.SphericalRealTimePathKernel
noncomputable section
open Set MeasureTheory ProbabilityTheory
open SphericalModel SphericalDynamics SphericalRotationCovariance SphericalFieldKernels
open SphericalFullFieldPathKernel
open SphericalAging.HardSphereDynamics
open scoped Topology NNReal ENNReal
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
variable {N : ℕ}

abbrev RealPathTime (T : ℝ≥0) := Icc (0 : ℝ) (T : ℝ)
abbrev RealSpherePath (N : ℕ) (T : ℝ≥0) := C(RealPathTime T,PhysicalSphere N)

def timeHomeomorph (T : ℝ≥0) : PathTime T ≃ₜ RealPathTime T where
  toFun t := ⟨t.1.1,⟨t.1.2,t.2.2⟩⟩
  invFun t := ⟨⟨t.1,t.2.1⟩,⟨zero_le,t.2.2⟩⟩
  left_inv t := by apply Subtype.ext; apply Subtype.ext; rfl
  right_inv t := by apply Subtype.ext; rfl
  continuous_toFun := by
    have hc : Continuous (fun t : PathTime T => (t.1 : ℝ)) :=
      continuous_subtype_val.comp continuous_subtype_val
    exact hc.subtype_mk _
  continuous_invFun := by
    have hc : Continuous (fun t : RealPathTime T => (⟨t.1,t.2.1⟩ : ℝ≥0)) :=
      continuous_subtype_val.subtype_mk _
    exact hc.subtype_mk _

def realPathEquiv (T : ℝ≥0) : SpherePath N T ≃ᵐ RealSpherePath N T where
  toFun p := p.comp ⟨(timeHomeomorph T).symm,(timeHomeomorph T).symm.continuous⟩
  invFun p := p.comp ⟨timeHomeomorph T,(timeHomeomorph T).continuous⟩
  left_inv p := by
    apply ContinuousMap.ext
    intro t
    simp
  right_inv p := by
    apply ContinuousMap.ext
    intro t
    simp
  measurable_toFun := by
    rw [ProbabilityTheory.ContinuousMap.measurable_iff_eval]
    intro t
    exact ContinuousMap.measurable_eval ((timeHomeomorph T).symm t)
  measurable_invFun := by
    rw [ProbabilityTheory.ContinuousMap.measurable_iff_eval]
    intro t
    exact ContinuousMap.measurable_eval (timeHomeomorph T t)

/-- The literal source kernel into C([0,T] ⊂ ℝ,S_N). -/
def realPathKernel (μ : FiniteMixture) (β : ℝ) (T : ℝ≥0) :
    Kernel (Field N μ × PhysicalSphere N) (RealSpherePath N T) :=
  (pathKernel μ β T).map (realPathEquiv T)

instance realPathKernel_markov (μ : FiniteMixture) (β : ℝ) (T : ℝ≥0) :
    IsMarkovKernel (realPathKernel (N := N) μ β T) :=
  Kernel.IsMarkovKernel.map _ (realPathEquiv T).measurable

theorem realPathKernel_joint_measurable (μ : FiniteMixture) (β : ℝ) (T : ℝ≥0) :
    Measurable (fun q : Field N μ × PhysicalSphere N => realPathKernel μ β T q) :=
  (realPathKernel μ β T).measurable

theorem realPathKernel_inverse_image (μ : FiniteMixture) (β : ℝ) (T : ℝ≥0)
    (q : Field N μ × PhysicalSphere N) :
    (realPathKernel μ β T q).map (realPathEquiv T).symm = pathKernel μ β T q := by
  rw [realPathKernel,Kernel.map_apply _ (realPathEquiv T).measurable,
    Measure.map_map (realPathEquiv T).symm.measurable (realPathEquiv T).measurable,
    (realPathEquiv T).symm_comp_self,Measure.map_id]

/-- Exact source-field factorization on the literal real-time path space. -/
theorem realPathKernel_fieldMap (hN : 1 ≤ N) (μ : FiniteMixture) (β : ℝ) (T : ℝ≥0)
    (J : Disorder N μ.maxDegree) (x : PhysicalSphere N) :
    realPathKernel μ β T (fieldMap μ J,x) =
      (SphericalAging.VectorBrownian.law N).map
        (fun ω => realPathEquiv T (spherePathRepresentative μ J β x T ω)) := by
  rw [realPathKernel,Kernel.map_apply _ (realPathEquiv T).measurable,
    pathKernel_fieldMap hN μ β T,spherePathLaw_eq_actual_map,
    Measure.map_map (realPathEquiv T).measurable (spherePathRepresentative_measurable μ J β x T)]
  rfl

/-- On one conull event the source representative is the actual physical
SDE at every real time t ∈ [0,T], including both endpoints. -/
theorem realPathRepresentative_ae_actual (hN : 1 ≤ N) (μ : FiniteMixture)
    (J : Disorder N μ.maxDegree) (β : ℝ) (x : PhysicalSphere N) (T : ℝ≥0) :
    ∀ᵐ ω ∂SphericalAging.VectorBrownian.law N, ∀ t : RealPathTime T,
      (realPathEquiv T (spherePathRepresentative μ J β x T ω) t).1 =
        mixedProcess μ J β x.1 ⟨t.1,t.2.1⟩ ω := by
  filter_upwards [spherePathRepresentative_ae_actual hN μ J β x T] with ω hω
  intro t
  exact hω ((timeHomeomorph T).symm t)

def realPathRotation (U : Vector N ≃ₗᵢ[ℝ] Vector N) (T : ℝ≥0)
    (p : RealSpherePath N T) : RealSpherePath N T :=
  (⟨sphereRotation U,sphereRotation_continuous U⟩ :
    C(PhysicalSphere N,PhysicalSphere N)).comp p

lemma realPathRotation_measurable (U : Vector N ≃ₗᵢ[ℝ] Vector N) (T : ℝ≥0) :
    Measurable (realPathRotation U T) := by
  rw [ProbabilityTheory.ContinuousMap.measurable_iff_eval]
  intro t
  exact (sphereRotation_continuous U).measurable.comp (ContinuousMap.measurable_eval t)

/-- Full source finite-horizon rotation covariance on the literal real
continuous spherical path space. -/
theorem realPathKernel_rotation (hN : 1 ≤ N) (μ : FiniteMixture) (β : ℝ) (T : ℝ≥0)
    (U : Vector N ≃ₗᵢ[ℝ] Vector N) (H : Field N μ) (x : PhysicalSphere N) :
    (realPathKernel μ β T (H,x)).map (realPathRotation U T) =
      realPathKernel μ β T (fieldRotation μ U H,sphereRotation U x) := by
  simp only [realPathKernel,Kernel.map_apply _ (realPathEquiv T).measurable]
  rw [Measure.map_map (realPathRotation_measurable U T) (realPathEquiv T).measurable]
  have he : realPathRotation U T ∘ realPathEquiv T =
      realPathEquiv T ∘ spherePathRotation U T := rfl
  rw [he,← Measure.map_map (realPathEquiv T).measurable (spherePathRotation_measurable U T),
    pathKernel_rotation hN μ β T U H x]

end
end SlowEquilibration.SphericalRealTimePathKernel
