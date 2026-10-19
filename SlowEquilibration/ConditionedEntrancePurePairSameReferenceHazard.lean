-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntrancePurePairTransformFull
public import SlowEquilibration.ConditionedEntrancePureQuenchedReferenceHazard

/-! A frozen, jointly measurable physical reference resolvent agrees under
the global source tilt with the canonical positive reference representative. -/
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory
open SlowEquilibration.SphericalModel SlowEquilibration.SphericalForm
open scoped NNReal
namespace SlowEquilibration.ConditionedEntrance
open SphericalAging.HardSphereDynamics SmoothKilledGeneral
set_option autoImplicit false
set_option maxHeartbeats 800000

set_option linter.unusedVariables false in
theorem pure_joint_frozen_reference_ae_canonical
    {N : ℕ} (hN : 1≤N) (d : ℕ) (hd : 2 ≤ d) (c : ℝ) (hc : 0 < c) (Q : ℝ)
    (α : ℝ) (hα : 0<α) (χ : ℝ→ℝ) (hχ : ContDiff ℝ 2 χ)
    (β : ℝ) (θ : ℝ≥0)
    (J : Disorder N (FiniteMixture.pure d hd c hc).maxDegree) (e M : ℝ)
    (F : SourceParameters N (FiniteMixture.pure d hd c hc)×Vector N→ℝ)
    (hFsm : StronglyMeasurable F)
    (hFrozen : ∀ u v x,
      F ((J,(u,(e,0))),x)=F ((J,(v,(e,0))),x))
    (hPhysical : ∀ v : Vector N,∀ hv : OnSphere v,
      let p : SourceParameters N (FiniteMixture.pure d hd c hc) := (J,(v,(e,0)))
      let D := FieldData.ofPure hN d hd c hc Q p.1 p.2.1 p.2.2.1 α χ hχ
      let Dbase := FieldData.ofOriginal hN (FiniteMixture.pure d hd c hc) p.1
      (fun x => F (p,x))=ᵐ[gibbsLaw N β D.hamiltonian]
        referenceRate Dbase β θ (referenceInitialVector Dbase β))
    (u₀ : Vector N) (hu₀ : OnSphere u₀) :
    let D₀ := FieldData.ofOriginal hN (FiniteMixture.pure d hd c hc) J
    let H₀ := fieldOfMixture (FiniteMixture.pure d hd c hc) J
    let w : Vector N×Vector N→ℝ := fun z =>
      β*(pureSourceSmoothCutoffField d hd c hc Q J z.1 e α χ z.2-H₀ z.2)
    let ν := normalizedTilt ((sphereLaw N).prod (gibbsLaw N β H₀)) w M
    (fun z : Vector N×Vector N => F ((J,(z.1,(e,0))),z.2)) =ᵐ[ν]
      (fun z => fieldReferencePositivePart D₀ β θ z.2) := by
  dsimp only
  let D₀ := FieldData.ofOriginal hN (FiniteMixture.pure d hd c hc) J
  let D := FieldData.ofPure hN d hd c hc Q J u₀ e α χ hχ
  let H₀ := fieldOfMixture (FiniteMixture.pure d hd c hc) J
  let π := gibbsLaw N β H₀
  let σ := sphereLaw N
  let w : Vector N×Vector N→ℝ := fun z =>
    β*(pureSourceSmoothCutoffField d hd c hc Q J z.1 e α χ z.2-H₀ z.2)
  let ν := normalizedTilt (σ.prod π) w M
  let Fa : Vector N×Vector N→ℝ := fun z => F ((J,(z.1,(e,0))),z.2)
  have hH₀ : Continuous H₀ := (fieldOfMixture_contDiff (FiniteMixture.pure d hd c hc) J).continuous
  let : IsProbabilityMeasure π := gibbsLaw_probability hN β hH₀
  have hD₀base : D₀.hamiltonian=H₀ :=
    rfl
  have hπsource : π ≪ gibbsLaw N β D.hamiltonian :=
    gibbsLaw_absolutelyContinuous_gibbsLaw hN β β D.hamiltonian H₀
      D.hamiltonian_contDiff.continuous
  have hF₀ : (fun x => Fa (u₀,x))=ᵐ[π]
      referenceRate D₀ β θ (referenceInitialVector D₀ β) := by
    simpa only [Fa,D₀,D] using
      (hPhysical u₀ hu₀).filter_mono hπsource.ae_le
  have hCanon : (fun x => fieldReferencePositivePart D₀ β θ x)=ᵐ[π]
      referenceRate D₀ β θ (referenceInitialVector D₀ β) := by
    simpa only [π,hD₀base] using fieldReferencePositivePart_ae D₀ β θ
  have hFcan : (fun x => Fa (u₀,x))=ᵐ[π]
      fieldReferencePositivePart D₀ β θ := hF₀.trans hCanon.symm
  have hCanSm : StronglyMeasurable (fieldReferencePositivePart D₀ β θ) := by
    unfold fieldReferencePositivePart
    exact stronglyMeasurable_const.sup
      (Lp.stronglyMeasurable
        (referenceRate D₀ β θ (referenceInitialVector D₀ β)))
  have hFaSm : StronglyMeasurable Fa := hFsm.comp_measurable (by fun_prop)
  have hset : MeasurableSet {z : Vector N×Vector N |
      Fa z=fieldReferencePositivePart D₀ β θ z.2} :=
    measurableSet_eq_fun hFaSm.measurable (hCanSm.measurable.comp measurable_snd)
  have hprod : Fa =ᵐ[σ.prod π]
      (fun z => fieldReferencePositivePart D₀ β θ z.2) := by
    apply (Measure.ae_prod_iff_ae_ae hset).mpr
    exact .of_forall (fun u => hFcan.mono (fun x hx => by
      change Fa (u,x)=fieldReferencePositivePart D₀ β θ x
      exact (hFrozen u u₀ x).trans hx))
  have hν : ν ≪ σ.prod π := withDensity_absolutelyContinuous _ _
  exact hprod.filter_mono hν.ae_le

end SlowEquilibration.ConditionedEntrance
