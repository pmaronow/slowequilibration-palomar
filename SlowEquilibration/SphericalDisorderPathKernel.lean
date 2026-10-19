module
-- SPDX-License-Identifier: Apache-2.0

public import SlowEquilibration.SphericalPathRotation
public import SlowEquilibration.SphericalDisorderKernelMeasurable
public import SlowEquilibration.ContinuousFieldLaw

@[expose] public section

/-! # The actual joint disorder-and-state continuous-path kernel

The genuine joint Picard process is recovered as a continuous path from
its countably many dense-time evaluations. Recovery is Borel and agrees
with the original physical SDE on each parameter slice. Thus no joint
path-measurability premise is used.
-/
namespace SlowEquilibration.SphericalRotationCovariance
noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 2000000
open Set MeasureTheory ProbabilityTheory Filter TopologicalSpace
open SphericalModel SphericalDynamics
open SphericalAging HardSphereDynamics
open scoped Topology NNReal ENNReal
variable {N : ℕ}

instance pathTime_nonempty (T : ℝ≥0) : Nonempty (PathTime T) :=
  ⟨⟨0,⟨le_rfl,zero_le⟩⟩⟩

/-- A true joint all-time representative of the actual mixed diffusion,
constructed from its coefficient-dependent Picard classes. -/
@[irreducible] def jointMixedProcess (μ : FiniteMixture) (β : ℝ) :
    (Disorder N μ.maxDegree × Vector N) → ℝ≥0 → VectorBrownian.Space N → Vector N :=
  ParameterFamily.globalRepresentative (NullAugmentation.driver (VectorBrownian.driver N))
    (fun J => cutoffDrift β (mixedGradient μ J) (cutoffRadius N) (cutoffRadius_pos N))
    (fun J => cutoffDrift_lipschitz β (mixedGradient μ J) (mixedGradient_contDiff μ J)
      (cutoffRadius N) (cutoffRadius_pos N))
    (fun A => mixed_cutoffDrift_uniform_state_lipschitz μ β (cutoffRadius N) (cutoffRadius_pos N) A)
    (mixed_cutoffDrift_disorder_lipschitz μ β (cutoffRadius N) (cutoffRadius_pos N))
    (CutoffSDE.cutoffNoise_lipschitz N (cutoffRadius N) (cutoffRadius_pos N)).choose_spec

lemma jointMixedProcess_measurable (μ : FiniteMixture) (β : ℝ) :
    Measurable (fun z : ((Disorder N μ.maxDegree × Vector N) × ℝ≥0) × VectorBrownian.Space N =>
      jointMixedProcess μ β z.1.1 z.1.2 z.2) := by
  unfold jointMixedProcess
  exact ParameterFamily.globalRepresentative_measurable
    (NullAugmentation.driver (VectorBrownian.driver N))
    (fun J : Disorder N μ.maxDegree => cutoffDrift β (mixedGradient μ J) (cutoffRadius N) (cutoffRadius_pos N))
    (fun J => cutoffDrift_lipschitz β (mixedGradient μ J) (mixedGradient_contDiff μ J)
      (cutoffRadius N) (cutoffRadius_pos N))
    (fun A => mixed_cutoffDrift_uniform_state_lipschitz μ β (cutoffRadius N) (cutoffRadius_pos N) A)
    (mixed_cutoffDrift_disorder_lipschitz μ β (cutoffRadius N) (cutoffRadius_pos N))
    (CutoffSDE.cutoffNoise_lipschitz N (cutoffRadius N) (cutoffRadius_pos N)).choose_spec

lemma jointMixedProcess_ae_actual (μ : FiniteMixture) (β : ℝ)
    (q : Disorder N μ.maxDegree × Vector N) :
    ∀ᵐ ω ∂VectorBrownian.law N, ∀ t,
      jointMixedProcess μ β q t ω=mixedProcess μ q.1 β q.2 t ω := by
  unfold jointMixedProcess ParameterFamily.globalRepresentative mixedProcess
  exact (ParameterFamily.exists_joint_global_process
    (NullAugmentation.driver (VectorBrownian.driver N))
    (fun J : Disorder N μ.maxDegree => cutoffDrift β (mixedGradient μ J) (cutoffRadius N) (cutoffRadius_pos N))
    (fun J => cutoffDrift_lipschitz β (mixedGradient μ J) (mixedGradient_contDiff μ J)
      (cutoffRadius N) (cutoffRadius_pos N))
    (fun A => mixed_cutoffDrift_uniform_state_lipschitz μ β (cutoffRadius N) (cutoffRadius_pos N) A)
    (mixed_cutoffDrift_disorder_lipschitz μ β (cutoffRadius N) (cutoffRadius_pos N))
    (CutoffSDE.cutoffNoise_lipschitz N (cutoffRadius N) (cutoffRadius_pos N)).choose_spec).choose_spec.2 q

/-- Borel recovery of an actual continuous physical path, including the
degenerate zero-time horizon, from the genuine joint process. -/
def jointContinuousPath (μ : FiniteMixture) (β : ℝ) (T : ℝ≥0)
    (z : (Disorder N μ.maxDegree × Vector N) × VectorBrownian.Space N) : ContinuousPath N T :=
  (ContinuousFieldLaw.denseEvaluation_measurableEmbedding
    (K := PathTime T) (V := Vector N)).invFun
      (fun n => jointMixedProcess μ β z.1 (denseSeq (PathTime T) n).1 z.2)

lemma jointContinuousPath_measurable (μ : FiniteMixture) (β : ℝ) (T : ℝ≥0) :
    Measurable (jointContinuousPath (N := N) μ β T) := by
  apply (ContinuousFieldLaw.denseEvaluation_measurableEmbedding
    (K := PathTime T) (V := Vector N)).measurable_invFun.comp
  apply Measurable.of_eval
  intro n
  exact (jointMixedProcess_measurable μ β).comp
    ((measurable_fst.prodMk measurable_const).prodMk measurable_snd)

lemma jointContinuousPath_ae_actual (μ : FiniteMixture) (β : ℝ) (T : ℝ≥0)
    (q : Disorder N μ.maxDegree × Vector N) :
    ∀ᵐ ω ∂VectorBrownian.law N, ∀ t : PathTime T,
      jointContinuousPath μ β T (q,ω) t=mixedProcess μ q.1 β q.2 t.1 ω := by
  filter_upwards [jointMixedProcess_ae_actual μ β q,
    mixedProcess_continuous μ q.1 β q.2] with ω he hc
  let p : ContinuousPath N T :=
    ⟨fun t => mixedProcess μ q.1 β q.2 t.1 ω,hc.comp continuous_subtype_val⟩
  have hd : (fun n => jointMixedProcess μ β q (denseSeq (PathTime T) n).1 ω)=
      ContinuousFieldLaw.denseEvaluation p := by
    funext n
    exact he _
  have hp : jointContinuousPath μ β T (q,ω)=p := by
    unfold jointContinuousPath
    rw [hd]
    exact (ContinuousFieldLaw.denseEvaluation_measurableEmbedding
      (K := PathTime T) (V := Vector N)).leftInverse_invFun p
  intro t
  rw [hp]
  rfl

/-- A genuine Markov kernel into the Borel continuous-path space, jointly
in the actual mixed tensor field and physical initial state. -/
def disorderPathKernel (μ : FiniteMixture) (β : ℝ) (T : ℝ≥0) :
    Kernel (Disorder N μ.maxDegree × Vector N) (ContinuousPath N T) :=
  (Kernel.id ×ₖ Kernel.const (Disorder N μ.maxDegree × Vector N) (VectorBrownian.law N)).map
    (jointContinuousPath μ β T)

instance disorderPathKernel_markov (μ : FiniteMixture) (β : ℝ) (T : ℝ≥0) :
    IsMarkovKernel (disorderPathKernel (N := N) μ β T) :=
  Kernel.IsMarkovKernel.map _ (jointContinuousPath_measurable μ β T)

/-- Every spherical parameter slice of the joint kernel is exactly the
original physical continuous path law. -/
theorem disorderPathKernel_apply (hN : 1 ≤ N) (μ : FiniteMixture) (β : ℝ) (T : ℝ≥0)
    (q : Disorder N μ.maxDegree × Vector N) (hx : OnSphere q.2) :
    disorderPathKernel μ β T q=pathLaw μ q.1 β q.2 T := by
  rw [disorderPathKernel,Kernel.map_apply _ (jointContinuousPath_measurable μ β T),
    Kernel.prod_apply,Kernel.id_apply,Kernel.const_apply,Measure.dirac_prod,
    Measure.map_map (jointContinuousPath_measurable μ β T) measurable_prodMk_left]
  unfold pathLaw
  apply Measure.map_congr
  filter_upwards [jointContinuousPath_ae_actual μ β T q,
    continuousPathRepresentative_ae_actual hN μ q.1 β q.2 hx T] with ω he hr
  apply ContinuousMap.ext
  intro t
  exact (he t).trans (hr t).symm

abbrev PhysicalSphere (N : ℕ) := {x : Vector N // OnSphere x}

/-- The source path kernel, with its initial state literally on the sphere. -/
def sphereDisorderPathKernel (μ : FiniteMixture) (β : ℝ) (T : ℝ≥0) :
    Kernel (Disorder N μ.maxDegree × PhysicalSphere N) (ContinuousPath N T) :=
  (disorderPathKernel μ β T).comap (fun q => (q.1,q.2.1))
    (measurable_fst.prodMk (measurable_subtype_coe.comp measurable_snd))

instance sphereDisorderPathKernel_markov (μ : FiniteMixture) (β : ℝ) (T : ℝ≥0) :
    IsMarkovKernel (sphereDisorderPathKernel (N := N) μ β T) := by
  unfold sphereDisorderPathKernel
  infer_instance

theorem sphereDisorderPathKernel_apply (hN : 1 ≤ N) (μ : FiniteMixture) (β : ℝ) (T : ℝ≥0)
    (q : Disorder N μ.maxDegree × PhysicalSphere N) :
    sphereDisorderPathKernel μ β T q=pathLaw μ q.1 β q.2.1 T :=
  disorderPathKernel_apply hN μ β T (q.1,q.2.1) q.2.2

/-- Genuine joint Borel measurability of the actual continuous path law. -/
theorem pathLaw_joint_measurable (hN : 1 ≤ N) (μ : FiniteMixture) (β : ℝ) (T : ℝ≥0) :
    Measurable (fun q : Disorder N μ.maxDegree × PhysicalSphere N =>
      pathLaw μ q.1 β q.2.1 T) := by
  have he : (fun q : Disorder N μ.maxDegree × PhysicalSphere N => pathLaw μ q.1 β q.2.1 T)=
      (fun q => sphereDisorderPathKernel μ β T q) :=
    funext (fun q => (sphereDisorderPathKernel_apply hN μ β T q).symm)
  rw [he]
  exact (sphereDisorderPathKernel μ β T).measurable

theorem sphereDisorderPathKernel_sphere_supported (hN : 1 ≤ N)
    (μ : FiniteMixture) (β : ℝ) (T : ℝ≥0)
    (q : Disorder N μ.maxDegree × PhysicalSphere N) :
    ∀ᵐ p ∂sphereDisorderPathKernel μ β T q, ∀ t, OnSphere (p t) := by
  rw [sphereDisorderPathKernel_apply hN μ β T q]
  exact pathLaw_sphere_supported μ q.1 β q.2.1 q.2.2 T

/-- The genuine joint path kernel obeys the derived source rotation law. -/
theorem sphereDisorderPathKernel_rotation (hN : 1 ≤ N)
    (μ : FiniteMixture) (β : ℝ) (T : ℝ≥0)
    (U : Vector N ≃ₗᵢ[ℝ] Vector N)
    (q : Disorder N μ.maxDegree × PhysicalSphere N) :
    (sphereDisorderPathKernel μ β T q).map (continuousPathRotation U T)=
      sphereDisorderPathKernel μ β T
        (rotatedDisorder U q.1,⟨U q.2.1,onSphere_map U q.2.2⟩) := by
  rw [sphereDisorderPathKernel_apply hN μ β T,
    sphereDisorderPathKernel_apply hN μ β T]
  exact pathLaw_rotation hN μ q.1 β U q.2.1 q.2.2 T

end
end SlowEquilibration.SphericalRotationCovariance
