-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntranceSourceJointCapHitExposure

/-! Uniform-axis and uniform-start integration of the physical source cap
exposure, bounded by the same measurable physical resolvent as the weighted
energy argument. -/
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open SlowEquilibration.SphericalModel SlowEquilibration.SphericalForm
open SlowEquilibration.SphericalOverlapExponential
open scoped NNReal
namespace SlowEquilibration.ConditionedEntrance
open SphericalAging HardSphereDynamics SmoothKilled PhysicalHitting FeynmanKac
set_option autoImplicit false
set_option maxHeartbeats 1200000

theorem source_joint_uniform_cap_hit_le_physical_resolvent
    {N : ℕ} (hN : 1≤N) (μ : FiniteMixture)
    (hnp : μ.minDegree<μ.maxDegree) (Q : ℝ) (hQ : 0<Q) (hQ1 : Q≤1)
    (α : ℝ) (hα : 0<α) (χ : ℝ→ℝ) (hχ : ContDiff ℝ 2 χ)
    (β : ℝ) (hβ : 0≤β) (θ : ℝ≥0) (hθ : 0<θ)
    (J : Disorder N μ.maxDegree) (hJ : J ∈ regularDisorder)
    (e k : ℝ) (U : SourceParameters N μ×Vector N→ℝ)
    (hUsm : StronglyMeasurable U)
    (hPhysical : ∀ u : Vector N,∀ hu : OnSphere u,
      let D := SourceData.atSourceParameters hN μ hnp Q hQ hQ1 α hα χ hχ
        (J,(u,(e,k))) hu
      (fun x => U ((J,(u,(e,k))),x))=ᵐ[gibbsLaw N β D.hamiltonian]
        rateLaplace D β (capKilling α u)
          (capKilling_contDiff α u).continuous
          (capKilling_nonneg α u) θ
          (killingVector D β (capKilling α u)
            (capKilling_contDiff α u).continuous))
    (u₀ : Vector N) (hu₀ : OnSphere u₀) (H T : ℝ≥0) (hT : 0<T)
    (hsmall : 4 * (1 + β * sourceGradientConstant μ Q e k α χ hχ) *
      (T : ℝ) ≤ α / 12) :
    exposureFactor (θ : ℝ) H T *
      ((∫ u,∫ x,sourceAxisCapHitProbability μ hQ hnp J β α χ hχ e k H u x
        ∂sphereLaw N ∂sphereLaw N) -
        (gridSize H T : ℝ) *
          (2 * Real.exp (-(N : ℝ) * (α / 12)^2 / (16 * (T : ℝ))))) ≤
      ∫ u,∫ x,U ((J,(u,(e,k))),x) ∂sphereLaw N ∂sphereLaw N := by
  let σ := sphereLaw N
  let P := VectorBrownian.law N
  let D₀ := SourceData.atSourceParameters hN μ hnp Q hQ hQ1 α hα χ hχ
    (J,(u₀,(e,k))) hu₀
  let κ : Vector N×Vector N→ℝ := fun z => capKilling α z.1 z.2
  let Y := sourceData_axisJointProcess D₀ β
  let p : Vector N×Vector N→ℝ := fun z =>
    sourceAxisCapHitProbability μ hQ hnp J β α χ hχ e k H z.1 z.2
  let F : (Vector N×Vector N)×VectorBrownian.Space N→ℝ := fun z =>
    finiteDiscountedMass κ Y (θ : ℝ) (H+T) z
  let G : Vector N×Vector N→ℝ := fun z => ∫ omega,F (z,omega) ∂P
  let gridError : ℝ := (gridSize H T : ℝ) *
    (2 * Real.exp (-(N : ℝ) * (α / 12)^2 / (16 * (T : ℝ))))
  let c := exposureFactor (θ : ℝ) H T
  let : IsProbabilityMeasure σ := sphereLaw_probability N
  have hκ : Continuous κ := by
    have hrc : Continuous (fun z : Vector N×Vector N => overlapValue z.1 z.2) := by
      simpa only [overlapValue_eq] using
        (continuous_inner (𝕜 := ℝ) (E := Vector N)).div_const (N : ℝ)
    exact ((SphericalCapCutoff.cutoff_contDiff _ _).continuous.comp hrc).add
      ((SphericalCapCutoff.cutoff_contDiff _ _).continuous.comp hrc.neg)
  let g := jointSpatialGradient (fun z : Vector N×Vector N =>
    sourceSmoothCutoffField μ Q hQ hnp J z.1 e k α χ z.2)
  let hg := mixedSourceAxisGradient_contDiff μ hQ hnp J α χ hχ e k
  have hY : Y = (fun t q => (q.1.1,
      SphericalSmoothParameter.jointProcess β g hg q.1 t q.2)) := rfl
  have hFsm : StronglyMeasurable F := by
    change StronglyMeasurable (finiteDiscountedMass κ Y (θ : ℝ) (H+T))
    rw [hY]
    exact jointAxis_finiteDiscountedMass_stronglyMeasurable β g hg κ hκ.measurable
      (θ : ℝ) (H+T)
  have hFnorm : ∀ z,‖F z‖ ≤ ((H+T : ℝ≥0) : ℝ) := by
    intro z
    exact finiteDiscountedMass_norm_le κ
      (fun z => capKilling_nonneg α z.1 z.2)
      (fun z => capKilling_le_one hα z.1 z.2) Y θ.coe_nonneg (H+T) z
  have hFi : Integrable F ((σ.prod σ).prod P) :=
    Integrable.of_bound hFsm.aestronglyMeasurable ((H+T : ℝ≥0) : ℝ)
      (.of_forall hFnorm)
  have hGsm : StronglyMeasurable G := hFsm.integral_prod_right'
  have hGi : Integrable G (σ.prod σ) := hFi.integral_prod_left
  have hpsm : StronglyMeasurable p :=
    (sourceAxisCapHitProbability_measurable μ hQ hnp J β α χ hχ e k H).stronglyMeasurable
  have hpnorm : ∀ z,‖p z‖ ≤ 1 := by
    intro z
    rw [Real.norm_eq_abs,abs_of_nonneg
      (sourceAxisCapHitProbability_mem_unit μ hQ hnp J β α χ hχ e k H z.1 z.2).1]
    exact (sourceAxisCapHitProbability_mem_unit μ hQ hnp J β α χ hχ e k H z.1 z.2).2
  have hpi : Integrable p (σ.prod σ) :=
    Integrable.of_bound hpsm.aestronglyMeasurable 1 (.of_forall hpnorm)
  have hLefti : Integrable (fun z => c * (p z - gridError)) (σ.prod σ) :=
    (hpi.sub (integrable_const gridError)).const_mul c
  have hPoint : ∀ᵐ z ∂σ.prod σ,c * (p z-gridError) ≤ G z := by
    have hm : MeasurableSet {z : Vector N×Vector N | c*(p z-gridError)≤G z} :=
      measurableSet_le (measurable_const.mul (hpsm.measurable.sub measurable_const))
        hGsm.measurable
    apply (Measure.ae_prod_iff_ae_ae hm).mpr
    filter_upwards [sphereLaw_support hN] with u hu
    filter_upwards [sphereLaw_support hN] with x hx
    have h := source_axis_cap_hit_exposure_le_joint_firing hN μ hnp Q hQ hQ1
      α hα χ hχ β hβ θ J hJ e k u₀ hu₀ u x
      ((onSphere_iff_norm_sq u).mpr hu) ((onSphere_iff_norm_sq x).mpr hx)
      H T hT hsmall
    change c*(p (u,x)-gridError) ≤ G (u,x) at h
    exact h
  have hMean := integral_mono_ae hLefti hGi hPoint
  have hPprod := integral_prod p hpi
  have hGprod := integral_prod G hGi
  have hLeft : (∫ z,c*(p z-gridError) ∂σ.prod σ) =
      c*((∫ u,∫ x,p (u,x) ∂σ ∂σ)-gridError) := by
    rw [integral_const_mul,integral_sub hpi (integrable_const gridError)]
    rw [hPprod]
    simp
  have hU := source_joint_uniform_finiteDiscountedMass_le_physical_resolvent
    hN μ hnp Q hQ hQ1 α hα χ hχ β θ hθ J e k U hUsm hPhysical
    u₀ hu₀ (H+T)
  change (∫ u,∫ x,G (u,x) ∂σ ∂σ) ≤
    ∫ u,∫ x,U ((J,(u,(e,k))),x) ∂σ ∂σ at hU
  calc
    _ = ∫ z,c*(p z-gridError) ∂σ.prod σ := hLeft.symm
    _ ≤ ∫ z,G z ∂σ.prod σ := hMean
    _ = ∫ u,∫ x,G (u,x) ∂σ ∂σ := hGprod
    _ ≤ _ := hU

end SlowEquilibration.ConditionedEntrance
