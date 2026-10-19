-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntranceSourcePairTransformFull
public import SlowEquilibration.ConditionedEntranceQuenchedSourceReferenceHazard

/-! A frozen, jointly measurable physical reference resolvent agrees under
the global source tilt with the canonical positive reference representative. -/
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory
open SlowEquilibration.SphericalModel SlowEquilibration.SphericalForm
open scoped NNReal
namespace SlowEquilibration.ConditionedEntrance
open SphericalAging.HardSphereDynamics SmoothKilled
set_option autoImplicit false
set_option maxHeartbeats 800000

theorem source_joint_frozen_reference_ae_canonical
    {N : ℕ} (hN : 1≤N) (μ : FiniteMixture)
    (hnp : μ.minDegree<μ.maxDegree) (Q : ℝ) (hQ : 0<Q) (hQ1 : Q≤1)
    (α : ℝ) (hα : 0<α) (χ : ℝ→ℝ) (hχ : ContDiff ℝ 2 χ)
    (β : ℝ) (θ : ℝ≥0)
    (J : Disorder N μ.maxDegree) (e k M : ℝ)
    (F : SourceParameters N μ×Vector N→ℝ)
    (hFsm : StronglyMeasurable F)
    (hFrozen : ∀ u v x,
      F ((J,(u,(e,k))),x)=F ((J,(v,(e,k))),x))
    (hPhysical : ∀ v : Vector N,∀ hv : OnSphere v,
      let p : SourceParameters N μ := (J,(v,(e,k)))
      let D := SourceData.atSourceParameters hN μ hnp Q hQ hQ1
        α hα χ hχ p hv
      (fun x => F (p,x))=ᵐ[gibbsLaw N β D.hamiltonian]
        referenceRate D.baseData β θ (referenceInitialVector D.baseData β))
    (u₀ : Vector N) (hu₀ : OnSphere u₀) :
    let D₀ := SourceData.atSourceParameters hN μ hnp Q hQ hQ1 α hα χ hχ
      (J,(u₀,(e,k))) hu₀
    let H₀ := fieldOfMixture μ J
    let w : Vector N×Vector N→ℝ := fun z =>
      β*(sourceSmoothCutoffField μ Q hQ hnp J z.1 e k α χ z.2-H₀ z.2)
    let ν := normalizedTilt ((sphereLaw N).prod (gibbsLaw N β H₀)) w M
    (fun z : Vector N×Vector N => F ((J,(z.1,(e,k))),z.2)) =ᵐ[ν]
      (fun z => sourceReferencePositivePart D₀ β θ z.2) := by
  dsimp only
  let D₀ := SourceData.atSourceParameters hN μ hnp Q hQ hQ1 α hα χ hχ
    (J,(u₀,(e,k))) hu₀
  let H₀ := fieldOfMixture μ J
  let π := gibbsLaw N β H₀
  let σ := sphereLaw N
  let w : Vector N×Vector N→ℝ := fun z =>
    β*(sourceSmoothCutoffField μ Q hQ hnp J z.1 e k α χ z.2-H₀ z.2)
  let ν := normalizedTilt (σ.prod π) w M
  let Fa : Vector N×Vector N→ℝ := fun z => F ((J,(z.1,(e,k))),z.2)
  have hH₀ : Continuous H₀ := (fieldOfMixture_contDiff μ J).continuous
  let : IsProbabilityMeasure π := gibbsLaw_probability hN β hH₀
  have hD₀base : D₀.baseData.hamiltonian=H₀ :=
    SourceData.baseData_hamiltonian D₀
  have hπsource : π ≪ gibbsLaw N β D₀.hamiltonian :=
    gibbsLaw_absolutelyContinuous_gibbsLaw hN β β D₀.hamiltonian H₀
      D₀.hamiltonian_contDiff.continuous
  have hF₀ : (fun x => Fa (u₀,x))=ᵐ[π]
      referenceRate D₀.baseData β θ (referenceInitialVector D₀.baseData β) := by
    simpa only [Fa,D₀] using
      (hPhysical u₀ hu₀).filter_mono hπsource.ae_le
  have hCanon : (fun x => sourceReferencePositivePart D₀ β θ x)=ᵐ[π]
      referenceRate D₀.baseData β θ (referenceInitialVector D₀.baseData β) := by
    simpa only [π,hD₀base] using sourceReferencePositivePart_ae D₀ β θ
  have hFcan : (fun x => Fa (u₀,x))=ᵐ[π]
      sourceReferencePositivePart D₀ β θ := hF₀.trans hCanon.symm
  have hCanSm : StronglyMeasurable (sourceReferencePositivePart D₀ β θ) := by
    unfold sourceReferencePositivePart
    exact stronglyMeasurable_const.sup
      (Lp.stronglyMeasurable
        (referenceRate D₀.baseData β θ (referenceInitialVector D₀.baseData β)))
  have hFaSm : StronglyMeasurable Fa := hFsm.comp_measurable (by fun_prop)
  have hset : MeasurableSet {z : Vector N×Vector N |
      Fa z=sourceReferencePositivePart D₀ β θ z.2} :=
    measurableSet_eq_fun hFaSm.measurable (hCanSm.measurable.comp measurable_snd)
  have hprod : Fa =ᵐ[σ.prod π]
      (fun z => sourceReferencePositivePart D₀ β θ z.2) := by
    apply (Measure.ae_prod_iff_ae_ae hset).mpr
    exact .of_forall (fun u => hFcan.mono (fun x hx => by
      change Fa (u,x)=sourceReferencePositivePart D₀ β θ x
      exact (hFrozen u u₀ x).trans hx))
  have hν : ν ≪ σ.prod π := withDensity_absolutelyContinuous _ _
  exact hprod.filter_mono hν.ae_le

end SlowEquilibration.ConditionedEntrance
