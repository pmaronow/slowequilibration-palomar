-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SourceReductionFinitePathUnionBound
public import SlowEquilibration.SourceMixedCenteredTrueEntranceTransfer
public import SlowEquilibration.SphericalPosteriorGradientShortCells

/-! Identifies the original diffusion path-kernel hit probability with the
true-field cap-hit observable used as a whole-disorder Kac--Rice mark. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.SourceReductionTrueCapPathWeight
open Set MeasureTheory ProbabilityTheory SphericalModel SphericalDynamics
open SphericalKacRiceHittingSource SphericalRealTimePathKernel
open SphericalFullFieldPathKernel SphericalFieldKernels
open SphericalFullFieldSphereTV
open SphericalSmoothParameter ConditionedEntrance
open SphericalRotationCovariance SphericalForm
open SphericalAging
open SphericalPosteriorGradientIndependence
open SphericalAging.HardSphereDynamics
open scoped NNReal ENNReal RealInnerProductSpace
set_option autoImplicit false
set_option maxHeartbeats 1000000

variable {N : ℕ}

theorem realPathKernel_original_true_cap_probability
    (hN : 2 ≤ N) (μ : FiniteMixture) (β : ℝ) (T : ℝ≥0)
    (a : ℝ) (J : Disorder N μ.maxDegree)
    (u x : PhysicalSphere N) :
    (realPathKernel μ β T (fieldMap μ J,x)).real
      {p | (p,u) ∈ overlapSupEvent T a} =
      capHitProbability β
        (jointSpatialGradient (originalTrueJointHamiltonian μ))
        (jointSpatialGradient_contDiff _ (originalTrueJointHamiltonian_contDiff μ))
        T a (u.1,(J,x.1)) := by
  let g := jointSpatialGradient (originalTrueJointHamiltonian (N := N) μ)
  let hg := jointSpatialGradient_contDiff _ (originalTrueJointHamiltonian_contDiff (N := N) μ)
  let R : VectorBrownian.Space N → RealSpherePath N T :=
    fun ω => realPathEquiv T (spherePathRepresentative μ J β x T ω)
  have hR : Measurable R :=
    (realPathEquiv T).measurable.comp (spherePathRepresentative_measurable μ J β x T)
  have hA : MeasurableSet {p : RealSpherePath N T |
      (p,u) ∈ overlapSupEvent T a} :=
    (overlapSupEvent_measurable T a).preimage
      (measurable_id.prodMk measurable_const)
  rw [realPathKernel_fieldMap (by omega : 1 ≤ N) μ β T J x]
  rw [Measure.real, Measure.map_apply hR hA]
  rw [capHitProbability_eq_actual]
  apply congrArg ENNReal.toReal
  apply measure_congr
  filter_upwards [realPathRepresentative_ae_actual (by omega : 1 ≤ N)
      μ J β x T,
    mixedProcess_ae_C1Process (by omega : 1 ≤ N) μ J β x.1 x.2] with ω hpath hproc
  apply propext
  rw [overlapSupEvent_eq_hitting]
  constructor
  · rintro ⟨t,ht⟩
    refine ⟨⟨t.1,t.2.1⟩,t.2.2,?_⟩
    rw [hpath t] at ht
    rw [hproc ⟨t.1,t.2.1⟩] at ht
    simpa only [g,hg,originalTrueJointHamiltonian,jointSpatialGradient,
      mixedGradient,overlap,real_inner_comm] using ht
  · rintro ⟨t,ht,hh⟩
    let τ : RealPathTime T := ⟨(t:ℝ),⟨NNReal.coe_nonneg t,by exact_mod_cast ht⟩⟩
    refine ⟨τ,?_⟩
    have hτ : (⟨τ.1,τ.2.1⟩ : ℝ≥0) = t := by apply Subtype.ext; rfl
    rw [hpath τ,hτ,hproc t]
    simpa only [g,hg,originalTrueJointHamiltonian,jointSpatialGradient,
      mixedGradient,overlap,real_inner_comm] using hh

/-- The actual uniform-start path kernel is the sphere-law average of its
fixed-initial-state path probabilities. -/
theorem uniformRealPathKernel_real_eq_integral
    (hN : 2 ≤ N) (μ : FiniteMixture) (β : ℝ) (T : ℝ≥0)
    (H : Field N μ) {A : Set (RealSpherePath N T)}
    (hA : MeasurableSet A) :
    (uniformRealPathKernel hN μ β T H).real A =
      ∫ x : Vector N,
        (realPathKernel μ β T
          (H,sphereStateRecovery (sphereBasepoint (by omega : 1 ≤ N)) x)).real A
        ∂sphereLaw N := by
  let κ := ambientStartPathKernel hN μ β T
  let ρ := (Kernel.id : Kernel (Field N μ) (Field N μ)) ×ₖ
    Kernel.const (Field N μ) (sphereLaw N)
  have hκm : Measurable (fun q : Field N μ × Vector N => (κ q).real A) :=
    (κ.measurable_coe hA).ennreal_toReal
  have hfinite (q : Field N μ × Vector N) : (κ q) A < ⊤ := by
    exact measure_lt_top _ _
  have hcomp : ((κ ∘ₖ ρ) H).real A =
      ∫ q, (κ q).real A ∂ρ H := by
    rw [Kernel.comp_apply]
    rw [Measure.real, Measure.bind_apply hA κ.aemeasurable]
    exact (integral_toReal (κ.measurable_coe hA).aemeasurable
      (.of_forall hfinite)).symm
  change ((κ ∘ₖ ρ) H).real A = _
  rw [hcomp]
  rw [show ρ H = (sphereLaw N).map (Prod.mk H) by
    simp only [ρ,Kernel.prod_apply,Kernel.id_apply,Kernel.const_apply,
      Measure.dirac_prod]]
  rw [integral_map (μ := sphereLaw N) (φ := Prod.mk H)
    (measurable_const.prodMk measurable_id).aemeasurable
    hκm.aestronglyMeasurable]
  apply integral_congr_ae
  exact .of_forall fun x => by
    change (κ (H,x)).real A = _
    rfl

/-- A fixed physical center's path-kernel cap probability is precisely the
jointly Borel true-field mark in the original tensor coefficients. -/
theorem uniformRealPathKernel_original_true_cap_probability
    (hN : 2 ≤ N) (μ : FiniteMixture) (β : ℝ) (T : ℝ≥0)
    (a : ℝ) (J : Disorder N μ.maxDegree) (u : PhysicalSphere N) :
    (uniformRealPathKernel hN μ β T (fieldMap μ J)).real
      {p | (p,u) ∈ overlapSupEvent T a} =
      originalTrueCapHitProbability μ β T a u.1 J := by
  have hA : MeasurableSet {p : RealSpherePath N T |
      (p,u) ∈ overlapSupEvent T a} :=
    (overlapSupEvent_measurable T a).preimage
      (measurable_id.prodMk measurable_const)
  rw [uniformRealPathKernel_real_eq_integral hN μ β T (fieldMap μ J) hA]
  unfold originalTrueCapHitProbability uniformCapHitProbability
  apply integral_congr_ae
  filter_upwards [sphereLaw_support (by omega : 1 ≤ N)] with x hx
  let X : PhysicalSphere N := ⟨x,(onSphere_iff_norm_sq x).mpr hx⟩
  have hrec : sphereStateRecovery (sphereBasepoint (by omega : 1 ≤ N)) x = X := by
    exact Subtype.ext (by simp [sphereStateRecovery, X, (onSphere_iff_norm_sq x).mpr hx])
  rw [hrec]
  exact realPathKernel_original_true_cap_probability hN μ β T a J u X

end SlowEquilibration.SourceReductionTrueCapPathWeight
