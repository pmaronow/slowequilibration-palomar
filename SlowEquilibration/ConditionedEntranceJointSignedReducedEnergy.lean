-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntranceSquareCommutatorSignedReduction
public import SlowEquilibration.ConditionedEntranceJointEnergyPhysical
public import SlowEquilibration.ConditionedEntranceSourceReferenceBounds
public import SlowEquilibration.ConditionedEntranceSquareCommutatorReduction
public import SlowEquilibration.SphericalBoundedSquareIntegrability
public import SlowEquilibration.SphericalJointZeroDefectIntegral

/-! The actual joint source weighted energy with both commutator signs
retained through the fibre step. It uses the same physical representatives
and scalar bounds as the unsigned reduction. -/
@[expose] public section
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal InnerProductSpace
namespace SlowEquilibration.ConditionedEntrance
open SphericalModel SphericalForm SmoothKilled
open SphericalAging.HardSphereDynamics
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
variable {N : ℕ}

theorem sourceJointReferenceSignedReducedEnergy (hN : 1≤N) (μ : FiniteMixture)
    (hnp : μ.minDegree<μ.maxDegree) (Q : ℝ) (hQ : 0<Q) (hQ1 : Q≤1)
    (α : ℝ) (hα : 0<α) (χ : ℝ→ℝ) (hχ : ContDiff ℝ 2 χ)
    (β : ℝ) (hβ : 0≤β) (θ : ℝ≥0) (hθ : 0<θ) :
    let H := sourceJointHamiltonian (N:=N) μ Q hQ hnp α χ
    let H₀ := fun z : SourceParameters N μ×Vector N => fieldOfMixture μ z.1.1 z.2
    let κ := sourceJointCapKilling (N:=N) μ α
    let w := fun z => β*H z-β*H₀ z
    ∃ F : SourceParameters N μ×Vector N→ℝ,
      ∃ GF : (Fin N×Fin N)→SourceParameters N μ×Vector N→ℝ,
      ∃ U : SourceParameters N μ×Vector N→ℝ,
      ∃ G : (Fin N×Fin N)→SourceParameters N μ×Vector N→ℝ,
        StronglyMeasurable F ∧ (∀ ij,StronglyMeasurable (GF ij)) ∧
        StronglyMeasurable U ∧ (∀ ij,StronglyMeasurable (G ij)) ∧
        (∀ p q x,p.1=q.1 → F (p,x)=F (q,x)) ∧
        (∀ ij p q x,p.1=q.1 → GF ij (p,x)=GF ij (q,x)) ∧
        Measurable (jointGibbsWeightedGradientSquare β H F G) ∧
        Measurable (jointGibbsWeightedSquare β H F U) ∧
        Measurable (jointGibbsZeroDefectSquare β H w F U) ∧
        Measurable (jointGibbsKilledReference β H κ F) ∧
        Measurable (jointGibbsTiltGradientCross β H w U GF G) ∧
        Measurable (jointGibbsFisher β H₀ F GF) ∧
        ∀ p : SourceParameters N μ,∀ hp : OnSphere p.2.1,∀ _hJ : p.1∈regularDisorder,
          let D := SourceData.atSourceParameters hN μ hnp Q hQ hQ1 α hα χ hχ p hp
          let hκ := (PhysicalHitting.capKilling_contDiff α p.2.1).continuous
          let hκ0 := PhysicalHitting.capKilling_nonneg α p.2.1
          let h := rateLaplace D β (PhysicalHitting.capKilling α p.2.1) hκ hκ0 θ
            (killingVector D β (PhysicalHitting.capKilling α p.2.1) hκ)
          ((fun x => F (p,x))=ᵐ[gibbsLaw N β D.hamiltonian]
            referenceRate D.baseData β θ (referenceInitialVector D.baseData β)) ∧
          ((fun x => U (p,x))=ᵐ[gibbsLaw N β D.hamiltonian] h) ∧
          (∀ᵐ x ∂gibbsLaw N β D.hamiltonian,
            1≤F (p,x) ∧ ‖F (p,x)‖≤1+Real.exp (2*β*derivativeConstant (mixtureCoefficients μ)*(N : ℝ))) ∧
          (∀ᵐ x ∂gibbsLaw N β D.hamiltonian,0≤U (p,x) ∧ U (p,x)≤1) ∧
          jointGibbsFisher β H₀ F GF p≤
            (θ : ℝ)*(2*Real.log 2+4*β*derivativeConstant (mixtureCoefficients μ)*(N : ℝ)) ∧
          jointGibbsWeightedGradientSquare β H F G p+
            (θ : ℝ)/2*jointGibbsWeightedSquare β H F U p≤
              jointGibbsKilledReference β H κ F p-
              (θ : ℝ)/2*jointGibbsZeroDefectSquare β H w F U p-
              jointGibbsTiltGradientCross β H w U GF G p ∧
          ∃ F₀ : sphericalSobolevGraph hN β D.baseData.hamiltonian D.baseData.hamiltonian_contDiff.continuous,
            ∃ F₁ u : sphericalSobolevGraph hN β D.hamiltonian D.hamiltonian_contDiff.continuous,
              sphericalEnergyL2Map hN β D.baseData.hamiltonian D.baseData.hamiltonian_contDiff.continuous F₀=
                referenceRate D.baseData β θ (referenceInitialVector D.baseData β) ∧
              sphericalEnergyL2Map hN β D.hamiltonian D.hamiltonian_contDiff.continuous u=h ∧
              ((fun x => F (p,x))=ᵐ[gibbsLaw N β D.baseData.hamiltonian] F₀.val.fst) ∧
              (∀ ij : Fin N×Fin N,(fun x => GF ij (p,x))=ᵐ[gibbsLaw N β D.baseData.hamiltonian] F₀.val.snd ij) ∧
              ((fun x => F (p,x))=ᵐ[gibbsLaw N β D.hamiltonian] F₁.val.fst) ∧
              (∀ ij : Fin N×Fin N,(fun x => GF ij (p,x))=ᵐ[gibbsLaw N β D.hamiltonian] F₁.val.snd ij) ∧
              ((fun x => U (p,x))=ᵐ[gibbsLaw N β D.hamiltonian] u.val.fst) ∧
              ∀ ij : Fin N×Fin N,(fun x => G ij (p,x))=ᵐ[gibbsLaw N β D.hamiltonian] u.val.snd ij := by
  dsimp only
  let H := sourceJointHamiltonian (N:=N) μ Q hQ hnp α χ
  let H₀ := fun z : SourceParameters N μ×Vector N => fieldOfMixture μ z.1.1 z.2
  let κ := sourceJointCapKilling (N:=N) μ α
  let w := fun z => β*H z-β*H₀ z
  have hH := sourceJointHamiltonian_continuous (N:=N) μ Q hQ hnp α χ hχ.continuous
  have hH₀ : Continuous H₀ := (field_jointContinuous (mixtureCoefficients μ)).comp
    (continuous_fst.fst.prodMk continuous_snd)
  have hw : Continuous w := (hH.const_mul β).sub (hH₀.const_mul β)
  obtain ⟨F,GF,U,G,hF,hGF,hU,hG,hFf,hGFf,hB,hA,_,hR,_,hC,hJF,hE⟩ :=
    sourceJointReferenceEnergy_physical hN μ hnp Q hQ hQ1 α hα χ hχ β hβ θ hθ
  have hK₀ := jointGibbsZeroDefectSquare_measurable hN β H w F U hH hw.stronglyMeasurable hF hU
  refine ⟨F,GF,U,G,hF,hGF,hU,hG,hFf,hGFf,hB,hA,hK₀,hR,hC,hJF,?_⟩
  intro p hp hJ
  let D := SourceData.atSourceParameters hN μ hnp Q hQ hQ1 α hα χ hχ p hp
  let kp := PhysicalHitting.capKilling α p.2.1
  have hkp := (PhysicalHitting.capKilling_contDiff α p.2.1).continuous
  have hkp0 := PhysicalHitting.capKilling_nonneg α p.2.1
  have hKp : ∀ x,‖kp x‖≤(1 : ℝ≥0) := by
    intro x
    rw [Real.norm_eq_abs,abs_of_nonneg (hkp0 x)]
    exact PhysicalHitting.capKilling_le_one hα p.2.1 x
  obtain ⟨hFs,hUs,hFisher,he,hPhys⟩ := hE p hp hJ
  let π := gibbsLaw N β D.hamiltonian
  let : IsProbabilityMeasure π := gibbsLaw_probability hN β D.hamiltonian_contDiff.continuous
  let C := 1+Real.exp (2*β*derivativeConstant (mixtureCoefficients μ)*(N : ℝ))
  have hC0 : 0≤C := by positivity
  let Fp := fun x => F (p,x)
  let Up := fun x => U (p,x)
  let ip := fun x => baseInitialJoint μ β (p.1,x)
  let wp := fun x => w (p,x)
  have hFm : AEStronglyMeasurable Fp π :=
    (hF.comp_measurable (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  have hUm : AEStronglyMeasurable Up π :=
    (hU.comp_measurable (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  have hic : Continuous ip := (baseInitialJoint_continuous hN μ β).comp
    (continuous_const.prodMk continuous_id)
  have hwc : Continuous wp := hw.comp (continuous_const.prodMk continuous_id)
  have hib : ∀ᵐ x ∂π,1 ≤ ip x ∧ ip x ≤ C := by
    simpa only [ip,C,π,baseInitialJoint,SourceData.baseData_hamiltonian,D,SourceData.atSourceParameters]
      using referenceInitial_source_regular_bounds D β hβ hJ
  have hFb : ∀ᵐ x ∂π,1≤Fp x ∧ ‖Fp x‖≤C := by
    filter_upwards [hFs,referenceRate_source_regular_bounds D β hβ θ hθ hJ] with x hx hb
    change Fp x=_ at hx
    rw [hx]
    refine ⟨hb.1,?_⟩
    rw [Real.norm_eq_abs,abs_of_nonneg (by linarith [hb.1])]
    exact hb.2
  have hUb : ∀ᵐ x ∂π,0≤Up x ∧ Up x≤1 := by
    filter_upwards [hUs,rateLaplace_killing_unit_interval D β kp hkp hkp0 1 hKp θ hθ] with x hx hb
    change Up x=_ at hx
    rw [hx]
    exact hb
  have hUn : ∀ᵐ x ∂π,‖Up x‖≤1 := hUb.mono (fun x hx => by
    rw [Real.norm_eq_abs,abs_of_nonneg hx.1];exact hx.2)
  have hAf := integrable_bounded_weight_square π Fp Up C hC0 hFm hUm
    (hFb.mono (fun _ hx => hx.2)) hUn
  have hfm1 : ∀ᵐ x ∂π,‖Fp x-1‖≤C+1 := hFb.mono (fun x hx => by
    have hn : ‖Fp x-1‖≤‖Fp x‖+1 := by simpa only [norm_one] using norm_sub_le (Fp x) 1
    linarith [hx.2])
  have hKf := integrable_continuous_bounded_weight_square hN β D.hamiltonian
    (tiltDefect wp) (fun x => Fp x-1) Up D.hamiltonian_contDiff.continuous
    (continuous_const.sub (Real.continuous_exp.comp hwc.neg)) (C+1) (by positivity)
    (hFm.sub aestronglyMeasurable_const) hUm hfm1 hUn
  have hzim : AEStronglyMeasurable (fun x => (θ : ℝ)*(ip x-Fp x)) π :=
    (hic.aestronglyMeasurable.sub hFm).const_mul (θ : ℝ)
  have hzin : ∀ᵐ x ∂π,‖(θ : ℝ)*(ip x-Fp x)‖≤(θ : ℝ)*(2*C) := by
    filter_upwards [hib,hFb] with x hi hf
    have hin : ‖ip x‖≤C := by rw [Real.norm_eq_abs,abs_of_nonneg (by linarith [hi.1])];exact hi.2
    rw [norm_mul,Real.norm_eq_abs,abs_of_nonneg θ.coe_nonneg]
    exact mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans (by linarith [hin,hf.2])) θ.coe_nonneg
  have hZf := integrable_continuous_bounded_weight_square hN β D.hamiltonian
    (fun x => Real.exp (-wp x)) (fun x => (θ : ℝ)*(ip x-Fp x)) Up
    D.hamiltonian_contDiff.continuous (Real.continuous_exp.comp hwc.neg) ((θ : ℝ)*(2*C))
    (by positivity) hzim hUm hzin hUn
  have hKpos : 0≤jointGibbsKilledWeightedSquare β H κ F U p := by
    unfold jointGibbsKilledWeightedSquare
    apply integral_nonneg_of_ae
    exact hFb.mono (fun x hx => mul_nonneg
      (mul_nonneg (hkp0 x) (by linarith [hx.1])) (sq_nonneg _))
  have hr := squareCommutator_energy_reduction_signed π (θ : ℝ) θ.coe_nonneg ip Fp Up wp
    (hib.mono (fun _ hx => hx.1)) hZf hAf hKf
    (jointGibbsWeightedGradientSquare β H F G p) (jointGibbsTiltGradientCross β H w U GF G p)
    (jointGibbsKilledWeightedSquare β H κ F U p) (jointGibbsKilledReference β H κ F p) hKpos he
  exact ⟨hFs,hUs,hFb,hUb,hFisher,hr,hPhys⟩

end SlowEquilibration.ConditionedEntrance
