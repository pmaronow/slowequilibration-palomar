-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalDisorderPathKernel
public import SlowEquilibration.SphericalFieldKernels

@[expose] public section

/-! # Genuine spherical path kernels in the complete polynomial field

The faithful finite-dimensional field is used as the parameter. The target
is literally the Borel space of continuous sphere-valued paths, and its
ambient image is the proved physical SDE law. -/

namespace SlowEquilibration.SphericalFullFieldPathKernel
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open SphericalModel SphericalDynamics SphericalRotationCovariance SphericalFieldKernels
open SphericalAging.HardSphereDynamics
open scoped Topology NNReal ENNReal
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
variable {N : ℕ}

theorem mixedProcess_congr_full (μ : FiniteMixture)
    (J K : Disorder N μ.maxDegree)
    (hfield : fieldOfMixture μ J = fieldOfMixture μ K) (β : ℝ) (x : Vector N) :
    mixedProcess μ J β x = mixedProcess μ K β x := by
  let G : {g : Vector N → Vector N // ContDiff ℝ ⊤ g} →
      (ℝ≥0 → SphericalAging.VectorBrownian.Space N → Vector N) := fun g =>
    SphericalAging.GlobalSDE.process
      (SphericalAging.NullAugmentation.driver (SphericalAging.VectorBrownian.driver N))
      (cutoffDrift_lipschitz β g.1 g.2 (cutoffRadius N) (cutoffRadius_pos N)).choose_spec
      (SphericalAging.CutoffSDE.cutoffNoise_lipschitz N
        (cutoffRadius N) (cutoffRadius_pos N)).choose_spec x
  have hg : (⟨mixedGradient μ J, mixedGradient_contDiff μ J⟩ :
      {g : Vector N → Vector N // ContDiff ℝ ⊤ g}) =
      ⟨mixedGradient μ K, mixedGradient_contDiff μ K⟩ := by
    apply Subtype.ext
    exact congrArg gradient hfield
  change G ⟨mixedGradient μ J, mixedGradient_contDiff μ J⟩ =
    G ⟨mixedGradient μ K, mixedGradient_contDiff μ K⟩
  exact congrArg G hg

theorem pathLaw_congr_full (hN : 1 ≤ N) (μ : FiniteMixture)
    (J K : Disorder N μ.maxDegree)
    (hfield : fieldOfMixture μ J = fieldOfMixture μ K) (β : ℝ) (x : Vector N)
    (hx : OnSphere x) (T : ℝ≥0) :
    pathLaw μ J β x T = pathLaw μ K β x T := by
  have he := mixedProcess_congr_full μ J K hfield β x
  unfold pathLaw
  apply Measure.map_congr
  filter_upwards [continuousPathRepresentative_ae_actual hN μ J β x hx T,
    continuousPathRepresentative_ae_actual hN μ K β x hx T] with ω hJ hK
  apply ContinuousMap.ext
  intro t
  rw [hJ t, hK t, he]

/-- Literal source target C([0,T],S_N), with its ordinary Borel structure. -/
abbrev SpherePath (N : ℕ) (T : ℝ≥0) := C(PathTime T, PhysicalSphere N)

def spherePathEmbedding (T : ℝ≥0) (p : SpherePath N T) : ContinuousPath N T :=
  ⟨fun t => (p t).1, continuous_subtype_val.comp p.continuous⟩

lemma spherePathEmbedding_measurable (T : ℝ≥0) :
    Measurable (spherePathEmbedding (N := N) T) := by
  rw [ProbabilityTheory.ContinuousMap.measurable_iff_eval]
  intro t
  exact measurable_subtype_coe.comp (ContinuousMap.measurable_eval t)

lemma spherePathEmbedding_injective (T : ℝ≥0) :
    Function.Injective (spherePathEmbedding (N := N) T) := by
  intro p q hpq
  apply ContinuousMap.ext
  intro t
  apply Subtype.ext
  exact congrArg (fun r : ContinuousPath N T => r t) hpq

def sphericalPaths (N : ℕ) (T : ℝ≥0) : Set (ContinuousPath N T) :=
  {p | ∀ t, OnSphere (p t)}

lemma sphericalPaths_closed (N : ℕ) (T : ℝ≥0) : IsClosed (sphericalPaths N T) := by
  have he : sphericalPaths N T =
      ⋂ t : PathTime T, {p : ContinuousPath N T | inner ℝ (p t) (p t) = (N : ℝ)} := by
    ext p
    simp only [sphericalPaths, mem_ofPred_eq, mem_iInter, OnSphere]
  rw [he]
  exact isClosed_iInter fun t => isClosed_eq
    (by fun_prop : Continuous (fun p : ContinuousPath N T => inner ℝ (p t) (p t)))
    continuous_const

/-- Borel retraction to sphere paths, with the physical initial point as
the harmless default off the supported set. -/
def spherePathRecovery (T : ℝ≥0) (z : PhysicalSphere N × ContinuousPath N T) : SpherePath N T := by
  classical
  exact if hp : z.2 ∈ sphericalPaths N T then
    ⟨fun t => ⟨z.2 t, hp t⟩, z.2.continuous.subtype_mk _⟩
  else ContinuousMap.const _ z.1

lemma spherePathRecovery_measurable (T : ℝ≥0) :
    Measurable (spherePathRecovery (N := N) T) := by
  classical
  rw [ProbabilityTheory.ContinuousMap.measurable_iff_eval]
  intro t
  apply Measurable.subtype_mk
  have hm : Measurable (fun z : PhysicalSphere N × ContinuousPath N T => z.2 t) :=
    (ContinuousMap.measurable_eval t).comp measurable_snd
  have hS : MeasurableSet {z : PhysicalSphere N × ContinuousPath N T |
      z.2 ∈ sphericalPaths N T} :=
    (sphericalPaths_closed N T).measurableSet.preimage measurable_snd
  have he : (fun z : PhysicalSphere N × ContinuousPath N T =>
      ((spherePathRecovery T z) t).1) =
      {z : PhysicalSphere N × ContinuousPath N T | z.2 ∈ sphericalPaths N T}.piecewise
        (fun z => z.2 t) (fun z => z.1.1) := by
    funext z
    by_cases hz : z.2 ∈ sphericalPaths N T <;> simp [spherePathRecovery, hz, Set.piecewise]
  change Measurable (fun z => ((spherePathRecovery T z) t).val)
  rw [he]
  exact hm.piecewise hS (measurable_subtype_coe.comp measurable_fst)

theorem spherePathEmbedding_recovery (T : ℝ≥0) (x : PhysicalSphere N)
    (p : ContinuousPath N T) (hp : p ∈ sphericalPaths N T) :
    spherePathEmbedding T (spherePathRecovery T (x,p)) = p := by
  classical
  apply ContinuousMap.ext
  intro t
  simp [spherePathEmbedding, spherePathRecovery, hp]

theorem spherePathRecovery_embedding (T : ℝ≥0) (x : PhysicalSphere N)
    (p : SpherePath N T) :
    spherePathRecovery T (x,spherePathEmbedding T p) = p := by
  apply spherePathEmbedding_injective T
  rw [spherePathEmbedding_recovery]
  exact fun t => (p t).2

theorem spherePathEmbedding_range (T : ℝ≥0) :
    Set.range (spherePathEmbedding (N := N) T) = sphericalPaths N T := by
  ext p
  constructor
  · rintro ⟨q,rfl⟩ t
    exact (q t).2
  · intro hp
    exact ⟨⟨fun t => ⟨p t,hp t⟩,p.continuous.subtype_mk _⟩,rfl⟩

theorem spherePathEmbedding_measurableEmbedding (T : ℝ≥0) (x : PhysicalSphere N) :
    MeasurableEmbedding (spherePathEmbedding (N := N) T) := by
  apply MeasurableEmbedding.of_measurable_inverse
    (g := fun p => spherePathRecovery T (x,p)) (spherePathEmbedding_measurable T)
  · rw [spherePathEmbedding_range]
    exact (sphericalPaths_closed N T).measurableSet
  · exact (spherePathRecovery_measurable T).comp
      ((measurable_const (a := x)).prodMk measurable_id)
  · exact spherePathRecovery_embedding T x

/-- Physical path law on the literal continuous spherical path space. -/
def spherePathLaw (μ : FiniteMixture) (J : Disorder N μ.maxDegree)
    (β : ℝ) (x : PhysicalSphere N) (T : ℝ≥0) : Measure (SpherePath N T) :=
  (pathLaw μ J β x.1 T).map (fun p => spherePathRecovery T (x,p))

instance spherePathLaw_probability (μ : FiniteMixture) (J : Disorder N μ.maxDegree)
    (β : ℝ) (x : PhysicalSphere N) (T : ℝ≥0) :
    IsProbabilityMeasure (spherePathLaw μ J β x T) := by
  unfold spherePathLaw
  have hm : Measurable (fun p => spherePathRecovery T (x,p)) :=
    (spherePathRecovery_measurable T).comp ((measurable_const (a := x)).prodMk measurable_id)
  infer_instance

/-- The spherical path law has exactly the actual ambient SDE path law
as its Borel image, so every physical path event is preserved. -/
theorem spherePathLaw_ambient_image (μ : FiniteMixture) (J : Disorder N μ.maxDegree)
    (β : ℝ) (x : PhysicalSphere N) (T : ℝ≥0) :
    (spherePathLaw μ J β x T).map (spherePathEmbedding T) = pathLaw μ J β x.1 T := by
  have hm : Measurable (fun p : ContinuousPath N T => spherePathRecovery T (x,p)) :=
    (spherePathRecovery_measurable T).comp ((measurable_const (a := x)).prodMk measurable_id)
  rw [spherePathLaw,Measure.map_map (spherePathEmbedding_measurable T) hm]
  conv_rhs => rw [← Measure.map_id (μ := pathLaw μ J β x.1 T)]
  apply Measure.map_congr
  filter_upwards [pathLaw_sphere_supported μ J β x.1 x.2 T] with p hp
  exact spherePathEmbedding_recovery T x p hp

def spherePathRepresentative (μ : FiniteMixture) (J : Disorder N μ.maxDegree)
    (β : ℝ) (x : PhysicalSphere N) (T : ℝ≥0)
    (ω : SphericalAging.VectorBrownian.Space N) : SpherePath N T :=
  spherePathRecovery T (x,continuousPathRepresentative μ J β x.1 T ω)

theorem spherePathRepresentative_measurable (μ : FiniteMixture) (J : Disorder N μ.maxDegree)
    (β : ℝ) (x : PhysicalSphere N) (T : ℝ≥0) :
    Measurable (spherePathRepresentative μ J β x T) :=
  (spherePathRecovery_measurable T).comp
    ((measurable_const (a := x)).prodMk (continuousPathRepresentative_measurable μ J β x.1 T))

/-- The sphere-valued representative agrees with the physical diffusion
at every time on a single event of full Wiener probability. -/
theorem spherePathRepresentative_ae_actual (hN : 1 ≤ N) (μ : FiniteMixture)
    (J : Disorder N μ.maxDegree) (β : ℝ) (x : PhysicalSphere N) (T : ℝ≥0) :
    ∀ᵐ ω ∂SphericalAging.VectorBrownian.law N, ∀ t : PathTime T,
      (spherePathRepresentative μ J β x T ω t).1 = mixedProcess μ J β x.1 t.1 ω := by
  filter_upwards [continuousPathRepresentative_ae_actual hN μ J β x.1 x.2 T,
    mixedProcess_onSphere (by omega) μ J β x.1 x.2] with ω he hs
  have hp : continuousPathRepresentative μ J β x.1 T ω ∈ sphericalPaths N T := by
    intro t
    rw [he t]
    exact hs t.1
  have hrec := spherePathEmbedding_recovery T x
    (continuousPathRepresentative μ J β x.1 T ω) hp
  intro t
  exact (congrArg (fun p : ContinuousPath N T => p t) hrec).trans (he t)

theorem spherePathLaw_eq_actual_map (μ : FiniteMixture) (J : Disorder N μ.maxDegree)
    (β : ℝ) (x : PhysicalSphere N) (T : ℝ≥0) :
    spherePathLaw μ J β x T =
      (SphericalAging.VectorBrownian.law N).map (spherePathRepresentative μ J β x T) := by
  have hm : Measurable (fun p : ContinuousPath N T => spherePathRecovery T (x,p)) :=
    (spherePathRecovery_measurable T).comp ((measurable_const (a := x)).prodMk measurable_id)
  rw [spherePathLaw,pathLaw,Measure.map_map hm
    (continuousPathRepresentative_measurable μ J β x.1 T)]
  rfl

/-- The exact joint Borel path law in the complete polynomial parameter,
before transporting to the sphere-valued path space. -/
def ambientPathKernel (μ : FiniteMixture) (β : ℝ) (T : ℝ≥0) :
    Kernel (Field N μ × PhysicalSphere N) (ContinuousPath N T) :=
  (sphereDisorderPathKernel μ β T).comap
    (fun q => (coefficientLift μ q.1,q.2))
    (((coefficientLift (N := N) μ).measurable.comp measurable_fst).prodMk measurable_snd)

instance ambientPathKernel_markov (μ : FiniteMixture) (β : ℝ) (T : ℝ≥0) :
    IsMarkovKernel (ambientPathKernel (N := N) μ β T) := by
  unfold ambientPathKernel
  infer_instance

theorem ambientPathKernel_apply (hN : 1 ≤ N) (μ : FiniteMixture) (β : ℝ) (T : ℝ≥0)
    (H : Field N μ) (x : PhysicalSphere N) :
    ambientPathKernel μ β T (H,x) = pathLaw μ (coefficientLift μ H) β x.1 T := by
  rw [ambientPathKernel,Kernel.comap_apply]
  exact sphereDisorderPathKernel_apply hN μ β T (coefficientLift μ H,x)

theorem ambientPathKernel_fieldMap (hN : 1 ≤ N) (μ : FiniteMixture) (β : ℝ) (T : ℝ≥0)
    (J : Disorder N μ.maxDegree) (x : PhysicalSphere N) :
    ambientPathKernel μ β T (fieldMap μ J,x) = pathLaw μ J β x.1 T := by
  rw [ambientPathKernel_apply hN μ β T]
  exact pathLaw_congr_full hN μ _ J (lifted_field_eq μ J) β x.1 x.2 T

/-- Source lem:red-kernels(a): a genuine Borel probability kernel from
the actual whole-polynomial field and sphere point to C([0,T],S_N). -/
def pathKernel (μ : FiniteMixture) (β : ℝ) (T : ℝ≥0) :
    Kernel (Field N μ × PhysicalSphere N) (SpherePath N T) :=
  (Kernel.id ×ₖ ambientPathKernel μ β T).map
    (fun z => spherePathRecovery T (z.1.2,z.2))

lemma pathKernel_map_measurable (T : ℝ≥0) (μ : FiniteMixture) :
    Measurable (fun z : (Field N μ × PhysicalSphere N) × ContinuousPath N T =>
      spherePathRecovery T (z.1.2,z.2)) :=
  (spherePathRecovery_measurable T).comp
    ((measurable_snd.comp measurable_fst).prodMk measurable_snd)

instance pathKernel_markov (μ : FiniteMixture) (β : ℝ) (T : ℝ≥0) :
    IsMarkovKernel (pathKernel (N := N) μ β T) :=
  Kernel.IsMarkovKernel.map _ (pathKernel_map_measurable T μ)

theorem pathKernel_apply (hN : 1 ≤ N) (μ : FiniteMixture) (β : ℝ) (T : ℝ≥0)
    (H : Field N μ) (x : PhysicalSphere N) :
    pathKernel μ β T (H,x) = spherePathLaw μ (coefficientLift μ H) β x T := by
  rw [pathKernel,Kernel.map_apply _ (pathKernel_map_measurable T μ),
    Kernel.prod_apply,Kernel.id_apply,ambientPathKernel_apply hN μ β T,
    Measure.dirac_prod,Measure.map_map (pathKernel_map_measurable T μ) measurable_prodMk_left]
  rfl

/-- Exact source-field factorization of the original physical SDE law,
without observing any redundant raw tensor coefficients. -/
theorem pathKernel_fieldMap (hN : 1 ≤ N) (μ : FiniteMixture) (β : ℝ) (T : ℝ≥0)
    (J : Disorder N μ.maxDegree) (x : PhysicalSphere N) :
    pathKernel μ β T (fieldMap μ J,x) = spherePathLaw μ J β x T := by
  rw [pathKernel_apply hN μ β T]
  unfold spherePathLaw
  rw [pathLaw_congr_full hN μ _ J (lifted_field_eq μ J) β x.1 x.2 T]

theorem pathKernel_joint_measurable (μ : FiniteMixture) (β : ℝ) (T : ℝ≥0) :
    Measurable (fun q : Field N μ × PhysicalSphere N => pathKernel μ β T q) :=
  (pathKernel μ β T).measurable

theorem pathKernel_ambient_image (hN : 1 ≤ N) (μ : FiniteMixture) (β : ℝ) (T : ℝ≥0)
    (H : Field N μ) (x : PhysicalSphere N) :
    (pathKernel μ β T (H,x)).map (spherePathEmbedding T) =
      pathLaw μ (coefficientLift μ H) β x.1 T := by
  rw [pathKernel_apply hN μ β T]
  exact spherePathLaw_ambient_image μ _ β x T

/-- The actual source action H ↦ H ∘ U⁻¹ on the faithful full field. -/
def fieldRotation (μ : FiniteMixture) (U : Vector N ≃ₗᵢ[ℝ] Vector N)
    (H : Field N μ) : Field N μ :=
  fieldMap μ (rotatedDisorder U (coefficientLift μ H))

theorem fieldRotation_measurable (μ : FiniteMixture)
    (U : Vector N ≃ₗᵢ[ℝ] Vector N) : Measurable (fieldRotation (N := N) μ U) :=
  (fieldMap (N := N) μ).measurable.comp
    ((rotatedDisorder_measurable U).comp (coefficientLift (N := N) μ).measurable)

/-- This action is equality of the entire ambient polynomial, including
radial information used by later source reductions. -/
theorem fieldRotation_full (μ : FiniteMixture) (U : Vector N ≃ₗᵢ[ℝ] Vector N)
    (H : Field N μ) :
    fieldOfMixture μ (coefficientLift μ (fieldRotation μ U H)) =
      fun x => fieldOfMixture μ (coefficientLift μ H) (U.symm x) := by
  calc
    _ = fieldOfMixture μ (rotatedDisorder U (coefficientLift μ H)) :=
      lifted_field_eq μ _
    _ = _ := funext (field_precomp_rotation (mixtureCoefficients μ) U _)

theorem fieldRotation_fieldMap (μ : FiniteMixture)
    (U : Vector N ≃ₗᵢ[ℝ] Vector N) (J : Disorder N μ.maxDegree) :
    fieldRotation μ U (fieldMap μ J) = fieldMap μ (rotatedDisorder U J) := by
  apply (SphericalEffectiveField.full_project_eq_iff (mixtureCoefficients μ) _ _).mpr
  change fieldOfMixture μ (rotatedDisorder U (coefficientLift μ (fieldMap μ J))) =
    fieldOfMixture μ (rotatedDisorder U J)
  funext x
  simp only [fieldOfMixture,field_precomp_rotation]
  exact congrFun (lifted_field_eq μ J) (U.symm x)

/-- The law of the complete source polynomial is invariant under its
actual polynomial rotation action. -/
theorem fieldRotation_hasLaw (μ : FiniteMixture) (U : Vector N ≃ₗᵢ[ℝ] Vector N) :
    HasLaw (fieldRotation (N := N) μ U) (fieldLaw N μ) (fieldLaw N μ) := by
  refine ⟨(fieldRotation_measurable μ U).aemeasurable,?_⟩
  change ((disorderLaw N μ.maxDegree).map (fieldMap μ)).map (fieldRotation μ U) =
    (disorderLaw N μ.maxDegree).map (fieldMap μ)
  rw [Measure.map_map (fieldRotation_measurable μ U) (fieldMap (N := N) μ).measurable]
  have he : fieldRotation μ U ∘ fieldMap μ = fieldMap μ ∘ rotatedDisorder U :=
    funext (fieldRotation_fieldMap μ U)
  rw [he,← Measure.map_map (fieldMap (N := N) μ).measurable (rotatedDisorder_measurable U),
    (rotatedDisorder_hasLaw U).map_eq]

def sphereRotation (U : Vector N ≃ₗᵢ[ℝ] Vector N) (x : PhysicalSphere N) : PhysicalSphere N :=
  ⟨U x.1,onSphere_map U x.2⟩

lemma sphereRotation_continuous (U : Vector N ≃ₗᵢ[ℝ] Vector N) :
    Continuous (sphereRotation U) :=
  (U.continuous.comp continuous_subtype_val).subtype_mk _

def spherePathRotation (U : Vector N ≃ₗᵢ[ℝ] Vector N) (T : ℝ≥0)
    (p : SpherePath N T) : SpherePath N T :=
  (⟨sphereRotation U,sphereRotation_continuous U⟩ :
    C(PhysicalSphere N,PhysicalSphere N)).comp p

lemma spherePathRotation_measurable (U : Vector N ≃ₗᵢ[ℝ] Vector N) (T : ℝ≥0) :
    Measurable (spherePathRotation U T) := by
  rw [ProbabilityTheory.ContinuousMap.measurable_iff_eval]
  intro t
  exact (sphereRotation_continuous U).measurable.comp (ContinuousMap.measurable_eval t)

theorem spherePathEmbedding_rotation (U : Vector N ≃ₗᵢ[ℝ] Vector N) (T : ℝ≥0) :
    spherePathEmbedding T ∘ spherePathRotation U T =
      continuousPathRotation U T ∘ spherePathEmbedding T := rfl

theorem spherePathLaw_rotation (hN : 1 ≤ N) (μ : FiniteMixture)
    (J : Disorder N μ.maxDegree) (β : ℝ)
    (U : Vector N ≃ₗᵢ[ℝ] Vector N) (x : PhysicalSphere N) (T : ℝ≥0) :
    (spherePathLaw μ J β x T).map (spherePathRotation U T) =
      spherePathLaw μ (rotatedDisorder U J) β (sphereRotation U x) T := by
  apply (spherePathEmbedding_measurableEmbedding T x).map_injective
  rw [Measure.map_map (spherePathEmbedding_measurable T) (spherePathRotation_measurable U T),
    spherePathEmbedding_rotation,
    ← Measure.map_map (continuousPathRotation_measurable U T) (spherePathEmbedding_measurable T),
    spherePathLaw_ambient_image,spherePathLaw_ambient_image]
  exact pathLaw_rotation hN μ J β U x.1 x.2 T

/-- The finite-horizon source kernel satisfies true simultaneous rotation
covariance in the full polynomial and physical state. -/
theorem pathKernel_rotation (hN : 1 ≤ N) (μ : FiniteMixture) (β : ℝ) (T : ℝ≥0)
    (U : Vector N ≃ₗᵢ[ℝ] Vector N) (H : Field N μ) (x : PhysicalSphere N) :
    (pathKernel μ β T (H,x)).map (spherePathRotation U T) =
      pathKernel μ β T (fieldRotation μ U H,sphereRotation U x) := by
  rw [pathKernel_apply hN μ β T,pathKernel_apply hN μ β T,
    spherePathLaw_rotation hN μ _ β U x T]
  unfold spherePathLaw
  rw [pathLaw_congr_full hN μ _ _
    (lifted_field_eq μ (rotatedDisorder U (coefficientLift μ H))).symm
    β (sphereRotation U x).1 (sphereRotation U x).2 T]
  rfl

/-- Source Gibbs covariance in the exact same full-field parameter. -/
theorem gibbsKernel_rotation (hN : 1 ≤ N) (μ : FiniteMixture) (β : ℝ)
    (U : Vector N ≃ₗᵢ[ℝ] Vector N) (H : Field N μ) :
    (gibbsKernel μ β H).map U = gibbsKernel μ β (fieldRotation μ U H) := by
  rw [gibbsKernel_apply,gibbsKernel_apply,
    mixtureGibbsLaw_rotation hN μ _ β U]
  change gibbsLaw N β (fieldOfMixture μ (rotatedDisorder U (coefficientLift μ H))) =
    gibbsLaw N β (fieldOfMixture μ (coefficientLift μ (fieldRotation μ U H)))
  rw [show fieldOfMixture μ (coefficientLift μ (fieldRotation μ U H)) =
    fieldOfMixture μ (rotatedDisorder U (coefficientLift μ H)) from lifted_field_eq μ _]

theorem pathLaw_evaluation (hN : 1 ≤ N) (μ : FiniteMixture)
    (J : Disorder N μ.maxDegree) (β : ℝ) (x : PhysicalSphere N)
    (T : ℝ≥0) (t : PathTime T) :
    (pathLaw μ J β x.1 T).map (fun p => p t) = mixedTransitionKernel μ J β t.1 x.1 := by
  rw [pathLaw,Measure.map_map (ContinuousMap.measurable_eval t)
    (continuousPathRepresentative_measurable μ J β x.1 T),
    mixedTransitionKernel_apply,mixedTransitionLaw]
  apply Measure.map_congr
  filter_upwards [continuousPathRepresentative_ae_actual hN μ J β x.1 x.2 T] with ω hω
  exact hω t

/-- Literal sphere-state conditional transition kernel, obtained by
evaluating the source continuous path kernel at the horizon. -/
def sphereTransitionKernel (μ : FiniteMixture) (β : ℝ) (t : ℝ≥0) :
    Kernel (Field N μ × PhysicalSphere N) (PhysicalSphere N) :=
  (pathKernel μ β t).map (fun p => p ⟨t,⟨zero_le,le_rfl⟩⟩)

instance sphereTransitionKernel_markov (μ : FiniteMixture) (β : ℝ) (t : ℝ≥0) :
    IsMarkovKernel (sphereTransitionKernel (N := N) μ β t) :=
  Kernel.IsMarkovKernel.map _ (ContinuousMap.measurable_eval _)

theorem sphereTransitionKernel_ambient_image (hN : 1 ≤ N) (μ : FiniteMixture)
    (β : ℝ) (t : ℝ≥0) (H : Field N μ) (x : PhysicalSphere N) :
    (sphereTransitionKernel μ β t (H,x)).map Subtype.val = transitionKernel μ β t (H,x.1) := by
  let s : PathTime t := ⟨t,⟨zero_le,le_rfl⟩⟩
  rw [sphereTransitionKernel,Kernel.map_apply _ (ContinuousMap.measurable_eval _),
    Measure.map_map measurable_subtype_coe (ContinuousMap.measurable_eval _)]
  have he : (fun p : SpherePath N t => (p s).1) =
      (fun p : ContinuousPath N t => p s) ∘ spherePathEmbedding t := rfl
  change (pathKernel μ β t (H,x)).map (fun p => (p s).1) = _
  rw [he,← Measure.map_map (ContinuousMap.measurable_eval s) (spherePathEmbedding_measurable t),
    pathKernel_ambient_image hN μ β t,pathLaw_evaluation hN μ _ β x t s,
    transitionKernel_apply]

/-- In particular every sphere-Borel transition event is jointly Borel
in the exact full field and physical initial point. -/
theorem sphereTransitionKernel_event_measurable (μ : FiniteMixture) (β : ℝ) (t : ℝ≥0)
    (A : Set (PhysicalSphere N)) (hA : MeasurableSet A) :
    Measurable (fun q : Field N μ × PhysicalSphere N => sphereTransitionKernel μ β t q A) :=
  (sphereTransitionKernel μ β t).measurable_coe hA

theorem sphereTransitionKernel_rotation (hN : 1 ≤ N) (μ : FiniteMixture) (β : ℝ) (t : ℝ≥0)
    (U : Vector N ≃ₗᵢ[ℝ] Vector N) (H : Field N μ) (x : PhysicalSphere N) :
    (sphereTransitionKernel μ β t (H,x)).map (sphereRotation U) =
      sphereTransitionKernel μ β t (fieldRotation μ U H,sphereRotation U x) := by
  let s : PathTime t := ⟨t,⟨zero_le,le_rfl⟩⟩
  have he := congrArg (fun M : Measure (SpherePath N t) => M.map (fun p => p s))
    (pathKernel_rotation hN μ β t U H x)
  rw [Measure.map_map (ContinuousMap.measurable_eval s) (spherePathRotation_measurable U t)] at he
  rw [sphereTransitionKernel,Kernel.map_apply _ (ContinuousMap.measurable_eval _),
    Measure.map_map (sphereRotation_continuous U).measurable (ContinuousMap.measurable_eval _),
    Kernel.map_apply _ (ContinuousMap.measurable_eval _)]
  exact he

def sphereRotationEquiv (U : Vector N ≃ₗᵢ[ℝ] Vector N) : PhysicalSphere N ≃ᵐ PhysicalSphere N where
  toFun := sphereRotation U
  invFun := sphereRotation U.symm
  left_inv x := by apply Subtype.ext; exact U.symm_apply_apply x.1
  right_inv x := by apply Subtype.ext; exact U.apply_symm_apply x.1
  measurable_toFun := (sphereRotation_continuous U).measurable
  measurable_invFun := (sphereRotation_continuous U.symm).measurable

/-- Source lem:red-kernels(b), with literal Borel subsets of S_N. -/
theorem sphereTransitionKernel_rotation_event (hN : 1 ≤ N) (μ : FiniteMixture)
    (β : ℝ) (t : ℝ≥0) (U : Vector N ≃ₗᵢ[ℝ] Vector N)
    (H : Field N μ) (x : PhysicalSphere N)
    (A : Set (PhysicalSphere N)) (hA : MeasurableSet A) :
    sphereTransitionKernel μ β t (fieldRotation μ U H,sphereRotation U x)
      (sphereRotation U '' A) = sphereTransitionKernel μ β t (H,x) A := by
  have hImg : MeasurableSet (sphereRotation U '' A) :=
    (sphereRotationEquiv U).measurableEmbedding.measurableSet_image.mpr hA
  rw [← sphereTransitionKernel_rotation hN μ β t U H x,
    Measure.map_apply (sphereRotation_continuous U).measurable hImg]
  change sphereTransitionKernel μ β t (H,x)
      ((sphereRotationEquiv U) ⁻¹' ((sphereRotationEquiv U) '' A)) = _
  rw [(sphereRotationEquiv U).injective.preimage_image]

end
end SlowEquilibration.SphericalFullFieldPathKernel
