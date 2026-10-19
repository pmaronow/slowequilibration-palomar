-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntranceMixedSourceAxisFiring
public import SlowEquilibration.ConditionedEntrancePhysicalHittingSourceLaplace
public import SlowEquilibration.ConditionedEntrancePhysicalUniformResolventTransferAny

/-! Finite physical firing of the joint source process is bounded by any
jointly measurable physical killed resolvent under the uniform start. -/
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open SlowEquilibration.SphericalModel SlowEquilibration.SphericalForm
open scoped NNReal
namespace SlowEquilibration.ConditionedEntrance
open SphericalAging HardSphereDynamics SmoothKilled PhysicalHitting FeynmanKac
set_option autoImplicit false
set_option maxHeartbeats 900000

theorem source_joint_uniform_finiteDiscountedMass_le_physical_resolvent
    {N : ℕ} (hN : 1≤N) (μ : FiniteMixture)
    (hnp : μ.minDegree<μ.maxDegree) (Q : ℝ) (hQ : 0<Q) (hQ1 : Q≤1)
    (α : ℝ) (hα : 0<α) (χ : ℝ→ℝ) (hχ : ContDiff ℝ 2 χ)
    (β : ℝ) (θ : ℝ≥0) (hθ : 0<θ)
    (J : Disorder N μ.maxDegree) (e k : ℝ)
    (U : SourceParameters N μ×Vector N→ℝ) (hUsm : StronglyMeasurable U)
    (hPhysical : ∀ u : Vector N,∀ hu : OnSphere u,
      let D := SourceData.atSourceParameters hN μ hnp Q hQ hQ1 α hα χ hχ
        (J,(u,(e,k))) hu
      (fun x => U ((J,(u,(e,k))),x))=ᵐ[gibbsLaw N β D.hamiltonian]
        rateLaplace D β (capKilling α u)
          (capKilling_contDiff α u).continuous
          (capKilling_nonneg α u) θ
          (killingVector D β (capKilling α u)
            (capKilling_contDiff α u).continuous))
    (u₀ : Vector N) (hu₀ : OnSphere u₀) (L : ℝ≥0) :
    let D₀ := SourceData.atSourceParameters hN μ hnp Q hQ hQ1 α hα χ hχ
      (J,(u₀,(e,k))) hu₀
    let κ : Vector N×Vector N→ℝ := fun z => capKilling α z.1 z.2
    let Y := sourceData_axisJointProcess D₀ β
    let Ua : Vector N×Vector N→ℝ := fun z => U ((J,(z.1,(e,k))),z.2)
    (∫ u,∫ x,∫ omega,finiteDiscountedMass κ Y (θ : ℝ) L ((u,x),omega)
      ∂VectorBrownian.law N ∂sphereLaw N ∂sphereLaw N)≤
      ∫ u,∫ x,Ua (u,x) ∂sphereLaw N ∂sphereLaw N := by
  dsimp only
  let σ := sphereLaw N
  let D₀ := SourceData.atSourceParameters hN μ hnp Q hQ hQ1 α hα χ hχ
    (J,(u₀,(e,k))) hu₀
  let κ : Vector N×Vector N→ℝ := fun z => capKilling α z.1 z.2
  let Y := sourceData_axisJointProcess D₀ β
  let Ua : Vector N×Vector N→ℝ := fun z => U ((J,(z.1,(e,k))),z.2)
  let P : Vector N→ℝ := fun u =>
    ∫ x,∫ omega,finiteDiscountedMass κ Y (θ : ℝ) L ((u,x),omega)
      ∂VectorBrownian.law N ∂σ
  let V : Vector N→ℝ := fun u => ∫ x,Ua (u,x) ∂σ
  let : IsProbabilityMeasure σ := sphereLaw_probability N
  have hUaSm : StronglyMeasurable Ua := hUsm.comp_measurable (by fun_prop)
  have hUbound (u : Vector N) (hu : OnSphere u) :
      ∀ᵐ x ∂σ,0≤Ua (u,x) ∧ Ua (u,x)≤1 := by
    let D := SourceData.atSourceParameters hN μ hnp Q hQ hQ1 α hα χ hχ
      (J,(u,(e,k))) hu
    let κu := capKilling α u
    have hκu := (capKilling_contDiff α u).continuous
    have hκ0 := capKilling_nonneg α u
    have hκ1 : ∀ x,‖κu x‖≤(1 : ℝ≥0) := by
      intro x
      rw [Real.norm_eq_abs,abs_of_nonneg (hκ0 x)]
      exact capKilling_le_one hα u x
    have hσD : σ ≪ gibbsLaw N β D.hamiltonian :=
      sphereLaw_absolutelyContinuous_gibbsLaw hN β D.hamiltonian
        D.hamiltonian_contDiff.continuous
    have hu' := hPhysical u hu
    have hb := rateLaplace_killing_unit_interval D β κu hκu hκ0 1 hκ1 θ hθ
    filter_upwards [hu'.filter_mono hσD.ae_le,hb.filter_mono hσD.ae_le]
      with x hx hb
    change Ua (u,x)=_ at hx
    rw [hx]
    exact hb
  have hUb : ∀ᵐ z ∂σ.prod σ,0≤Ua z ∧ Ua z≤1 := by
    apply (Measure.ae_prod_iff_ae_ae (by
      exact (measurableSet_le measurable_const hUaSm.measurable).inter
        (measurableSet_le hUaSm.measurable measurable_const))).mpr
    filter_upwards [sphereLaw_support hN] with u hu
    exact hUbound u ((onSphere_iff_norm_sq u).mpr hu)
  have hUnorm : ∀ᵐ z ∂σ.prod σ,‖Ua z‖≤1 :=
    hUb.mono (fun z hz => by
      rw [Real.norm_eq_abs,abs_of_nonneg hz.1]
      exact hz.2)
  have hUi : Integrable Ua (σ.prod σ) :=
    Integrable.of_bound hUaSm.aestronglyMeasurable 1 hUnorm
  have hVi : Integrable V σ := hUi.integral_prod_left
  have hP0 : ∀ᵐ u ∂σ,0≤P u := .of_forall (fun u => by
    dsimp only [P]
    apply integral_nonneg
    intro x
    apply integral_nonneg
    intro omega
    exact finiteDiscountedMass_nonneg κ
      (fun z => capKilling_nonneg α z.1 z.2) Y (θ : ℝ) L ((u,x),omega))
  have hpoint : ∀ᵐ u ∂σ,P u≤V u := by
    filter_upwards [sphereLaw_support hN] with u hu
    let hu' : OnSphere u := (onSphere_iff_norm_sq u).mpr hu
    let D := SourceData.atSourceParameters hN μ hnp Q hQ hQ1 α hα χ hχ
      (J,(u,(e,k))) hu'
    have hfire (x : Vector N) :
        (∫ omega,finiteDiscountedMass κ Y (θ : ℝ) L ((u,x),omega)
          ∂VectorBrownian.law N)=
        (∫ omega,finiteDiscountedMass (capKilling α u)
          (process D β x) (θ : ℝ) L omega ∂VectorBrownian.law N) := by
      apply integral_congr_ae
      change (fun omega => finiteDiscountedMass
        (fun z : Vector N × Vector N => capKilling D.cutoffScale z.1 z.2)
        (sourceData_axisJointProcess D β) (θ : ℝ) L ((D.axis,x),omega))
        =ᵐ[VectorBrownian.law N]
        fun omega => finiteDiscountedMass (capKilling D.cutoffScale D.axis)
          (process D β x) (θ : ℝ) L omega
      exact sourceData_axisJoint_finiteDiscountedMass_ae_actual D β (θ : ℝ) L x
    have hσD : σ ≪ gibbsLaw N β D.hamiltonian :=
      sphereLaw_absolutelyContinuous_gibbsLaw hN β D.hamiltonian
        D.hamiltonian_contDiff.continuous
    have hUae := (hPhysical u hu').filter_mono hσD.ae_le
    have hUeq : (∫ x,Ua (u,x) ∂σ)=
        ∫ x,rateLaplace D β (capKilling α u)
          (capKilling_contDiff α u).continuous (capKilling_nonneg α u) θ
          (killingVector D β (capKilling α u)
            (capKilling_contDiff α u).continuous) x ∂σ := by
      exact integral_congr_ae hUae
    have hFireEq : P u=
        ∫ x,∫ omega,finiteDiscountedMass (capKilling α u)
          (process D β x) (θ : ℝ) L omega
          ∂VectorBrownian.law N ∂σ := by
      exact integral_congr_ae (.of_forall hfire)
    have hBound := source_uniform_finiteDiscountedMass_le_rateLaplace D β
      (capKilling α u) (capKilling_contDiff α u).continuous
      (capKilling_nonneg α u) (capKilling_le_one hα u) θ hθ L
    rw [← hFireEq,← hUeq] at hBound
    exact hBound
  exact integral_mono_of_nonneg hP0 hVi hpoint

end SlowEquilibration.ConditionedEntrance
