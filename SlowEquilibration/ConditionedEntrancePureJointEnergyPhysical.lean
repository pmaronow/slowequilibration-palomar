-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntrancePureBaseJointReference
public import SlowEquilibration.ConditionedEntrancePureJointKilledRepresentatives
public import SlowEquilibration.SphericalJointEnergyIntegrals

/-! Proper-pure jointly measurable energy and square-commutator terms for the
original-base entropy reference and actual source physical inverse.
The physical equations, reference Fisher estimate and all representatives
are derived before the joint integral consumers. Actual completed graphs
and each gradient coordinate are retained for subsequent integration. -/
@[expose] public section
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal InnerProductSpace BigOperators
namespace SlowEquilibration.ConditionedEntrance
open SphericalModel SphericalForm SmoothKilledGeneral
open SphericalAging.HardSphereDynamics
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
variable {N : ℕ}

set_option linter.unusedVariables false in
theorem pureJointReferenceEnergy_physical (hN : 1≤N)
    (d : ℕ) (hd : 2 ≤ d) (c : ℝ) (hc : 0 < c) (Q : ℝ)
    (α : ℝ) (hα : 0<α) (χ : ℝ→ℝ) (hχ : ContDiff ℝ 2 χ)
    (β : ℝ) (hβ : 0≤β) (θ : ℝ≥0) (hθ : 0<θ) :
    let μ := FiniteMixture.pure d hd c hc
    let H := pureSourceJointHamiltonian (N:=N) d hd c hc Q α χ
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
        let L := fun z => (θ : ℝ)*(baseInitialJoint μ β (z.1.1,z.2)-F z)
        Measurable (jointGibbsWeightedGradientSquare β H F G) ∧
        Measurable (jointGibbsWeightedSquare β H F U) ∧
        Measurable (jointGibbsKilledWeightedSquare β H κ F U) ∧
        Measurable (jointGibbsKilledReference β H κ F) ∧
        Measurable (jointGibbsGeneratorSquare β H w L U) ∧
        Measurable (jointGibbsTiltGradientCross β H w U GF G) ∧
        Measurable (jointGibbsFisher β H₀ F GF) ∧
        ∀ p : SourceParameters N μ,∀ hp : OnSphere p.2.1,∀ _hJ : p.1∈regularDisorder,
          let D := FieldData.ofPure hN d hd c hc Q p.1 p.2.1 p.2.2.1 α χ hχ
          let D₀ := FieldData.ofOriginal hN μ p.1
          let hκ := (PhysicalHitting.capKilling_contDiff α p.2.1).continuous
          let hκ0 := PhysicalHitting.capKilling_nonneg α p.2.1
          let h := rateLaplace D β (PhysicalHitting.capKilling α p.2.1) hκ hκ0 θ
            (killingVector D β (PhysicalHitting.capKilling α p.2.1) hκ)
          ((fun x => F (p,x))=ᵐ[gibbsLaw N β D.hamiltonian]
            referenceRate D₀ β θ (referenceInitialVector D₀ β)) ∧
          ((fun x => U (p,x))=ᵐ[gibbsLaw N β D.hamiltonian] h) ∧
          jointGibbsFisher β H₀ F GF p≤
            (θ : ℝ)*(2*Real.log 2+4*β*derivativeConstant (mixtureCoefficients μ)*(N : ℝ)) ∧
          jointGibbsWeightedGradientSquare β H F G p+
            (1/2 : ℝ)*jointGibbsGeneratorSquare β H w L U p+
            jointGibbsTiltGradientCross β H w U GF G p+
            jointGibbsKilledWeightedSquare β H κ F U p+
            (θ : ℝ)*jointGibbsWeightedSquare β H F U p≤jointGibbsKilledReference β H κ F p ∧
          ∃ F₀ : sphericalSobolevGraph hN β D₀.hamiltonian D₀.hamiltonian_contDiff.continuous,
            ∃ F₁ u : sphericalSobolevGraph hN β D.hamiltonian D.hamiltonian_contDiff.continuous,
              sphericalEnergyL2Map hN β D₀.hamiltonian D₀.hamiltonian_contDiff.continuous F₀=
                referenceRate D₀ β θ (referenceInitialVector D₀ β) ∧
              sphericalEnergyL2Map hN β D.hamiltonian D.hamiltonian_contDiff.continuous u=h ∧
              ((fun x => F (p,x))=ᵐ[gibbsLaw N β D₀.hamiltonian] F₀.val.fst) ∧
              (∀ ij : Fin N×Fin N,(fun x => GF ij (p,x))=ᵐ[gibbsLaw N β D₀.hamiltonian] F₀.val.snd ij) ∧
              ((fun x => F (p,x))=ᵐ[gibbsLaw N β D.hamiltonian] F₁.val.fst) ∧
              (∀ ij : Fin N×Fin N,(fun x => GF ij (p,x))=ᵐ[gibbsLaw N β D.hamiltonian] F₁.val.snd ij) ∧
              ((fun x => U (p,x))=ᵐ[gibbsLaw N β D.hamiltonian] u.val.fst) ∧
              ∀ ij : Fin N×Fin N,(fun x => G ij (p,x))=ᵐ[gibbsLaw N β D.hamiltonian] u.val.snd ij := by
  dsimp only
  let μ := FiniteMixture.pure d hd c hc
  let H := pureSourceJointHamiltonian (N:=N) d hd c hc Q α χ
  let H₀ := fun z : SourceParameters N μ×Vector N => fieldOfMixture μ z.1.1 z.2
  let κ := sourceJointCapKilling (N:=N) μ α
  let w := fun z => β*H z-β*H₀ z
  have hH := (pureSourceJointHamiltonian_contDiff (N:=N) d hd c hc Q α χ hχ).continuous
  have hH₀ : Continuous H₀ := (field_jointContinuous (mixtureCoefficients μ)).comp
    (continuous_fst.fst.prodMk continuous_snd)
  obtain ⟨F,GF,hF,hGF,hFf,hGFf,hFa⟩ := originalBaseReference_joint_physical_representatives hN μ β θ hθ
  obtain ⟨U,G,hU,hG,hUa⟩ := pureJointKilledSolution_joint_physical_representatives hN d hd c hc Q α hα χ hχ β θ hθ
  let L := fun z => (θ : ℝ)*(baseInitialJoint μ β (z.1.1,z.2)-F z)
  have hL : StronglyMeasurable L := ((baseInitialJoint_continuous hN μ β).stronglyMeasurable.comp_measurable
    (measurable_fst.fst.prodMk measurable_snd)).sub hF |>.const_mul (θ : ℝ)
  have hw : StronglyMeasurable w := ((hH.const_mul β).sub (hH₀.const_mul β)).stronglyMeasurable
  obtain ⟨hB,hA,hK,hR,hZ,hC,_⟩ := jointGibbsEnergyIntegrals_measurable hN β H κ w L F U hH
    (sourceJointCapKilling_continuous μ α).stronglyMeasurable hw hL hF hU GF G hGF hG
  have hJF := (jointGibbsEnergyIntegrals_measurable hN β H₀ κ w L F U hH₀
    (sourceJointCapKilling_continuous μ α).stronglyMeasurable hw hL hF hU GF G hGF hG).2.2.2.2.2.2
  refine ⟨F,GF,U,G,hF,hGF,hU,hG,hFf,hGFf,hB,hA,hK,hR,hZ,hC,hJF,?_⟩
  intro p hp hJ
  let D := FieldData.ofPure hN d hd c hc Q p.1 p.2.1 p.2.2.1 α χ hχ
  let D₀ := FieldData.ofOriginal hN μ p.1
  let kp := PhysicalHitting.capKilling α p.2.1
  have hkp := (PhysicalHitting.capKilling_contDiff α p.2.1).continuous
  have hkp0 := PhysicalHitting.capKilling_nonneg α p.2.1
  have hKp : ∀ x,‖kp x‖≤(1 : ℝ≥0) := by
    intro x
    rw [Real.norm_eq_abs,abs_of_nonneg (hkp0 x)]
    exact PhysicalHitting.capKilling_le_one hα p.2.1 x
  obtain ⟨F₀,F₁,u,hF₀,hF₁,hGF₁,hu,hbound,hFisher,he⟩ :=
    rateLaplace_reference_commutator_energy D D₀ β hβ kp hkp hkp0 1 hKp θ hθ
      (derivativeConstant (mixtureCoefficients μ)*(N : ℝ))
      (mul_nonneg (derivativeConstant_pos _).le (Nat.cast_nonneg N))
      (original_regular_hamiltonian_bound hN μ p.1 hJ)
  obtain ⟨v,hv,hFv,hGFv⟩ := hFa p
  obtain ⟨u',hu',hUu,hGu⟩ := hUa p
  have hev : v=F₀ := sphericalEnergyL2Map_injective hN β D₀.hamiltonian
    (D₀.hamiltonian_contDiff.of_le (by norm_num)) (hv.trans hF₀.symm)
  have heu : u'=u := sphericalEnergyL2Map_injective hN β D.hamiltonian
    (D.hamiltonian_contDiff.of_le (by norm_num)) (hu'.trans hu.symm)
  rw [hev] at hGFv
  rw [heu] at hGu
  have hπ := (gibbsLaw_absolutelyContinuous β D.hamiltonian).ae_le
  have hπ₀ := (gibbsLaw_absolutelyContinuous β D₀.hamiltonian).ae_le
  have hAC := (gibbsLaw_absolutelyContinuous_gibbsLaw hN β β D₀.hamiltonian
    D.hamiltonian D₀.hamiltonian_contDiff.continuous).ae_le
  have hFs := hFv.filter_mono hπ
  have hUs := hUu.filter_mono hπ
  have hGF₀ (ij : Fin N×Fin N) := (hGFv ij).filter_mono hπ₀
  have hGFs (ij : Fin N×Fin N) := (hGFv ij).filter_mono hπ
  have hGs (ij : Fin N×Fin N) := (hGu ij).filter_mono hπ
  have hFF : (fun x => F (p,x))=ᵐ[gibbsLaw N β D.hamiltonian] F₁.val.fst := hFs.trans hF₁.symm
  have hFF₀ : (fun x => F (p,x))=ᵐ[gibbsLaw N β D₀.hamiltonian] F₀.val.fst := by
    have hfv : F₀.val.fst=referenceRate D₀ β θ (referenceInitialVector D₀ β) := hF₀
    simpa only [hfv] using hFv.filter_mono hπ₀
  have hHpx (x : Vector N) : H (p,x)=D.hamiltonian x := by
    rw [FieldData.ofPure_hamiltonian]
    rfl
  have hH₀px (x : Vector N) : H₀ (p,x)=D₀.hamiltonian x :=
    rfl
  have hwpx (x : Vector N) : w (p,x)=gibbsEnergyDifference β β D₀.hamiltonian D.hamiltonian x := by
    change β*H (p,x)-β*H₀ (p,x)=_
    rw [hHpx,hH₀px]
    rfl
  have hJFp : jointGibbsFisher β H₀ F GF p=
      sphericalFisher hN β D₀.hamiltonian D₀.hamiltonian_contDiff.continuous F₀ := by
    unfold jointGibbsFisher sphericalFisher
    simp only [hH₀px]
    apply Finset.sum_congr rfl
    intro ij _
    apply integral_congr_ae
    filter_upwards [hFF₀,hGF₀ ij] with x hx hg
    rw [hx,hg,div_eq_mul_inv]
  have hBp : jointGibbsWeightedGradientSquare β H F G p=
      sphericalWeightedGradientSquare hN β D.hamiltonian D.hamiltonian_contDiff.continuous u F₁ := by
    unfold jointGibbsWeightedGradientSquare sphericalWeightedGradientSquare
    simp only [hHpx]
    apply Finset.sum_congr rfl
    intro ij _
    apply integral_congr_ae
    filter_upwards [hFF,hGs ij] with x hx hg
    rw [hx,hg]
  have hCp : jointGibbsTiltGradientCross β H w U GF G p=
      sphericalTiltGradientCross hN β β D₀.hamiltonian D.hamiltonian
        D₀.hamiltonian_contDiff.continuous D.hamiltonian_contDiff.continuous F₀ u := by
    unfold jointGibbsTiltGradientCross sphericalTiltGradientCross tiltDefect
    simp only [hHpx,hwpx]
    apply integral_congr_ae
    filter_upwards [hUs,ae_all_iff.mpr hGFs,ae_all_iff.mpr hGs] with x hx hf hg
    have huv : u.val.fst=rateLaplace D β kp hkp hkp0 θ (killingVector D β kp hkp) := hu
    rw [← huv] at hx
    rw [hx]
    congr 1
    apply Finset.sum_congr rfl
    intro ij _
    rw [hf ij,hg ij]
  have hAp : jointGibbsWeightedSquare β H F U p=
      ∫ x,F₁.val.fst x*(rateLaplace D β kp hkp hkp0 θ (killingVector D β kp hkp) x)^2
        ∂gibbsLaw N β D.hamiltonian := by
    unfold jointGibbsWeightedSquare
    simp only [hHpx]
    apply integral_congr_ae
    filter_upwards [hFF,hUs] with x hx hy
    rw [hx,hy]
  have hKp' : jointGibbsKilledWeightedSquare β H κ F U p=
      ∫ x,kp x*F₁.val.fst x*(rateLaplace D β kp hkp hkp0 θ (killingVector D β kp hkp) x)^2
        ∂gibbsLaw N β D.hamiltonian := by
    unfold jointGibbsKilledWeightedSquare
    simp only [hHpx]
    apply integral_congr_ae
    filter_upwards [hFF,hUs] with x hx hy
    change kp x*F (p,x)*(U (p,x))^2=_
    rw [hx,hy]
  have hRp : jointGibbsKilledReference β H κ F p=
      ∫ x,kp x*F₁.val.fst x ∂gibbsLaw N β D.hamiltonian := by
    unfold jointGibbsKilledReference
    simp only [hHpx]
    apply integral_congr_ae
    exact hFF.mono (fun x hx => by
      change F (p,x)=F₁.val.fst x at hx
      change kp x*F (p,x)=kp x*F₁.val.fst x
      rw [hx])
  let Fv := referenceRate D₀ β θ (referenceInitialVector D₀ β)
  let V : (sphericalGenerator hN β D₀.hamiltonian D₀.hamiltonian_contDiff.continuous).domain :=
    ⟨Fv,(referenceRate_generator D₀ β θ hθ (referenceInitialVector D₀ β)).choose⟩
  have hgen : sphericalGenerator hN β D₀.hamiltonian D₀.hamiltonian_contDiff.continuous V=
      (θ : ℝ) • (referenceInitialVector D₀ β-Fv) :=
    (referenceRate_generator D₀ β θ hθ (referenceInitialVector D₀ β)).choose_spec
  have hLp : (fun x => L (p,x))=ᵐ[gibbsLaw N β D.hamiltonian]
      sphericalGenerator hN β D₀.hamiltonian D₀.hamiltonian_contDiff.continuous V := by
    rw [hgen]
    filter_upwards [hFs,(Lp.coeFn_smul (θ : ℝ) (referenceInitialVector D₀ β-Fv)).filter_mono hAC,
      (Lp.coeFn_sub (referenceInitialVector D₀ β) Fv).filter_mono hAC,
      (referenceInitialVector_ae D₀ β).filter_mono hAC] with x hx hs hd hi
    change (θ : ℝ)*(baseInitialJoint μ β (p.1,x)-F (p,x))=_
    change F (p,x)=Fv x at hx
    rw [hs,Pi.smul_apply,smul_eq_mul,hd]
    simp only [Pi.sub_apply]
    rw [hi,hx]
    simp only [baseInitialJoint,D₀,FieldData.ofOriginal_hamiltonian,Fv]
  have hZp : jointGibbsGeneratorSquare β H w L U p=
      ∫ x,Real.exp (-gibbsEnergyDifference β β D₀.hamiltonian D.hamiltonian x)*
        (sphericalGenerator hN β D₀.hamiltonian D₀.hamiltonian_contDiff.continuous V x)*
          (rateLaplace D β kp hkp hkp0 θ (killingVector D β kp hkp) x)^2 ∂gibbsLaw N β D.hamiltonian := by
    unfold jointGibbsGeneratorSquare
    simp only [hHpx,hwpx]
    apply integral_congr_ae
    filter_upwards [hLp,hUs] with x hx hy
    rw [hx,hy]
  refine ⟨hFs,hUs,?_,?_,?_⟩
  · rw [hJFp]
    simpa only [mul_assoc] using hFisher
  · rw [hBp,hZp,hCp,hKp',hAp,hRp]
    exact he
  · refine ⟨F₀,F₁,u,hF₀,hu,hFF₀,hGF₀,hFF,?_,?_,hGs⟩
    · intro ij
      exact (hGFs ij).trans (hGF₁ ij).symm
    · have huval : u.val.fst=rateLaplace D β kp hkp hkp0 θ (killingVector D β kp hkp) := hu
      simpa only [huval] using hUs

end SlowEquilibration.ConditionedEntrance
