-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntranceAxisSignedEnergyGlobal
public import SlowEquilibration.ConditionedEntranceSourceGradientFibreIntegral
public import SlowEquilibration.ConditionedEntranceSignedGlobalAllEnergy

/-! The actual source signed fibre energy becomes the global raw energy
inequality under the one physical axis–spin tilt. The gradient fibre
identity and all five L¹ inputs are stated explicitly for consumers. -/
@[expose] public section
noncomputable section
open MeasureTheory
open SlowEquilibration.SphericalModel SlowEquilibration.SphericalForm
open SphericalAging.HardSphereDynamics
open scoped NNReal BigOperators
namespace SlowEquilibration.ConditionedEntrance
set_option autoImplicit false
set_option maxHeartbeats 500000

theorem source_joint_signed_global_raw_energy_of_fibres
    {N : ℕ} (hN : 1 ≤ N) (μ : FiniteMixture)
    (hnp : μ.minDegree < μ.maxDegree) (Q : ℝ) (hQ : 0 < Q)
    (α : ℝ) (χ : ℝ → ℝ) (hχ : Continuous χ)
    (β : ℝ) (θ : ℝ≥0) (J : Disorder N μ.maxDegree) (e k : ℝ)
    (F U : SourceParameters N μ × Vector N → ℝ)
    (GF G : (Fin N × Fin N) → SourceParameters N μ × Vector N → ℝ)
    (M : ℝ) (hM : 0 < M)
    (hMphys : M = ∫ z : Vector N×Vector N,
      Real.exp (β*(sourceSmoothCutoffField μ Q hQ hnp J z.1 e k α χ z.2-
        fieldOfMixture μ J z.2))
      ∂((sphereLaw N).prod (gibbsLaw N β (fieldOfMixture μ J))))
    (hBint : Integrable (fun z : Vector N×Vector N =>
      F ((J,(z.1,(e,k))),z.2)*
        (∑ ij : Fin N×Fin N,(G ij ((J,(z.1,(e,k))),z.2))^2))
      (normalizedTilt ((sphereLaw N).prod (gibbsLaw N β (fieldOfMixture μ J)))
        (fun z => β*(sourceSmoothCutoffField μ Q hQ hnp J z.1 e k α χ z.2-
          fieldOfMixture μ J z.2)) M))
    (hAint : Integrable (fun z : Vector N×Vector N =>
      F ((J,(z.1,(e,k))),z.2)*U ((J,(z.1,(e,k))),z.2)^2)
      (normalizedTilt ((sphereLaw N).prod (gibbsLaw N β (fieldOfMixture μ J)))
        (fun z => β*(sourceSmoothCutoffField μ Q hQ hnp J z.1 e k α χ z.2-
          fieldOfMixture μ J z.2)) M))
    (hRint : Integrable (fun z : Vector N×Vector N =>
      PhysicalHitting.capKilling α z.1 z.2*F ((J,(z.1,(e,k))),z.2))
      (normalizedTilt ((sphereLaw N).prod (gibbsLaw N β (fieldOfMixture μ J)))
        (fun z => β*(sourceSmoothCutoffField μ Q hQ hnp J z.1 e k α χ z.2-
          fieldOfMixture μ J z.2)) M))
    (hKint : Integrable (fun z : Vector N×Vector N =>
      tiltDefect (fun y : Vector N×Vector N =>
        β*(sourceSmoothCutoffField μ Q hQ hnp J y.1 e k α χ y.2-
          fieldOfMixture μ J y.2)) z *
      (F ((J,(z.1,(e,k))),z.2)-1)*U ((J,(z.1,(e,k))),z.2)^2)
      (normalizedTilt ((sphereLaw N).prod (gibbsLaw N β (fieldOfMixture μ J)))
        (fun z => β*(sourceSmoothCutoffField μ Q hQ hnp J z.1 e k α χ z.2-
          fieldOfMixture μ J z.2)) M))
    (hCint : Integrable (fun z : Vector N×Vector N =>
      tiltDefect (fun y : Vector N×Vector N =>
        β*(sourceSmoothCutoffField μ Q hQ hnp J y.1 e k α χ y.2-
          fieldOfMixture μ J y.2)) z *
      U ((J,(z.1,(e,k))),z.2)*
        (∑ ij : Fin N×Fin N,
          GF ij ((J,(z.1,(e,k))),z.2)*G ij ((J,(z.1,(e,k))),z.2)))
      (normalizedTilt ((sphereLaw N).prod (gibbsLaw N β (fieldOfMixture μ J)))
        (fun z => β*(sourceSmoothCutoffField μ Q hQ hnp J z.1 e k α χ z.2-
          fieldOfMixture μ J z.2)) M))
    (hBfibre : ∀ v : Vector N, OnSphere v →
      let p : SourceParameters N μ := (J,(v,(e,k)))
      jointGibbsWeightedGradientSquare β
        (sourceJointHamiltonian μ Q hQ hnp α χ) F G p =
        ∫ x, F (p,x)*(∑ ij : Fin N×Fin N,(G ij (p,x))^2)
          ∂gibbsLaw N β
            (sourceSmoothCutoffField μ Q hQ hnp J v e k α χ))
    (hpoint : ∀ v : Vector N, OnSphere v →
      let p : SourceParameters N μ := (J,(v,(e,k)))
      let H := sourceJointHamiltonian μ Q hQ hnp α χ
      let H₀ := fun z : SourceParameters N μ×Vector N => fieldOfMixture μ z.1.1 z.2
      let w := fun z => β*H z-β*H₀ z
      let κ := sourceJointCapKilling μ α
      jointGibbsWeightedGradientSquare β H F G p+
        (θ : ℝ)/2*jointGibbsWeightedSquare β H F U p ≤
          jointGibbsKilledReference β H κ F p-
          (θ : ℝ)/2*jointGibbsZeroDefectSquare β H w F U p-
          jointGibbsTiltGradientCross β H w U GF G p) :
    let H₀ := fieldOfMixture μ J
    let H : Vector N → Vector N → ℝ := fun v x =>
      sourceSmoothCutoffField μ Q hQ hnp J v e k α χ x
    let w : Vector N×Vector N → ℝ := fun z => β*(H z.1 z.2-H₀ z.2)
    let ν := normalizedTilt ((sphereLaw N).prod (gibbsLaw N β H₀)) w M
    let Fa : Vector N×Vector N → ℝ := fun z => F ((J,(z.1,(e,k))),z.2)
    let Ua : Vector N×Vector N → ℝ := fun z => U ((J,(z.1,(e,k))),z.2)
    let GFa : (Fin N×Fin N) → Vector N×Vector N → ℝ := fun ij z =>
      GF ij ((J,(z.1,(e,k))),z.2)
    let Ga : (Fin N×Fin N) → Vector N×Vector N → ℝ := fun ij z =>
      G ij ((J,(z.1,(e,k))),z.2)
    (∫ z, Fa z*(∑ ij : Fin N×Fin N,(Ga ij z)^2) ∂ν)+
      (θ : ℝ)/2*(∫ z, Fa z*Ua z^2 ∂ν) ≤
        (∫ z, PhysicalHitting.capKilling α z.1 z.2*Fa z ∂ν)+
        (θ : ℝ)/2*|∫ z, tiltDefect w z*(Fa z-1)*Ua z^2 ∂ν|+
        |∫ z, tiltDefect w z*Ua z*
          (∑ ij : Fin N×Fin N,GFa ij z*Ga ij z) ∂ν| := by
  dsimp only
  subst M
  let H₀ := fieldOfMixture μ J
  let H : Vector N → Vector N → ℝ := fun v x =>
    sourceSmoothCutoffField μ Q hQ hnp J v e k α χ x
  let w : Vector N×Vector N → ℝ := fun z => β*(H z.1 z.2-H₀ z.2)
  let fB : Vector N×Vector N → ℝ := fun z =>
    F ((J,(z.1,(e,k))),z.2)*
      (∑ ij : Fin N×Fin N,(G ij ((J,(z.1,(e,k))),z.2))^2)
  let fA : Vector N×Vector N → ℝ := fun z =>
    F ((J,(z.1,(e,k))),z.2)*U ((J,(z.1,(e,k))),z.2)^2
  let fR : Vector N×Vector N → ℝ := fun z =>
    PhysicalHitting.capKilling α z.1 z.2*F ((J,(z.1,(e,k))),z.2)
  let fK : Vector N×Vector N → ℝ := fun z =>
    tiltDefect w z*(F ((J,(z.1,(e,k))),z.2)-1)*U ((J,(z.1,(e,k))),z.2)^2
  let fC : Vector N×Vector N → ℝ := fun z =>
    tiltDefect w z*U ((J,(z.1,(e,k))),z.2)*
      (∑ ij : Fin N×Fin N,
        GF ij ((J,(z.1,(e,k))),z.2)*G ij ((J,(z.1,(e,k))),z.2))
  have hH₀ : Continuous H₀ := (fieldOfMixture_contDiff μ J).continuous
  have hH : Continuous (fun z : Vector N×Vector N => H z.1 z.2) :=
    (sourceSmoothCutoffField_jointContinuous μ Q hQ hnp α χ hχ).comp
      (show Continuous (fun z : Vector N×Vector N =>
        (((J,(z.1,(e,k))),z.2) : SourceParameters N μ × Vector N)) by fun_prop)
  have hM' : 0 < ∫ z : Vector N×Vector N, Real.exp (w z)
      ∂((sphereLaw N).prod (gibbsLaw N β H₀)) := by
    exact hM
  have hpoint' (v : Vector N) (hv : OnSphere v) :
      (∫ x, fB (v,x) ∂gibbsLaw N β (H v))+
        (θ : ℝ)/2*(∫ x, fA (v,x) ∂gibbsLaw N β (H v)) ≤
      (∫ x, fR (v,x) ∂gibbsLaw N β (H v))-
        (θ : ℝ)/2*(∫ x, fK (v,x) ∂gibbsLaw N β (H v))-
        (∫ x, fC (v,x) ∂gibbsLaw N β (H v)) := by
    let p : SourceParameters N μ := (J,(v,(e,k)))
    have he := hpoint v hv
    have hbe := hBfibre v hv
    -- The four remaining joint energies are fibre integrals by definition.
    have hweq (x : Vector N) :
        (β*sourceJointHamiltonian μ Q hQ hnp α χ (p,x)-
          β*fieldOfMixture μ J x) = w (v,x) := by
      dsimp only [w,H,H₀,sourceJointHamiltonian,p]
      ring
    have hAeq : jointGibbsWeightedSquare β
        (sourceJointHamiltonian μ Q hQ hnp α χ) F U p =
        ∫ x, fA (v,x) ∂gibbsLaw N β (H v) := rfl
    have hReq : jointGibbsKilledReference β
        (sourceJointHamiltonian μ Q hQ hnp α χ)
        (sourceJointCapKilling μ α) F p =
        ∫ x, fR (v,x) ∂gibbsLaw N β (H v) := rfl
    have hKeq : jointGibbsZeroDefectSquare β
        (sourceJointHamiltonian μ Q hQ hnp α χ)
        (fun z => β*sourceJointHamiltonian μ Q hQ hnp α χ z-
          β*fieldOfMixture μ z.1.1 z.2) F U p =
        ∫ x, fK (v,x) ∂gibbsLaw N β (H v) := by
      unfold jointGibbsZeroDefectSquare
      apply integral_congr_ae
      exact .of_forall fun x => by
        dsimp only [fK,tiltDefect]
        rw [← hweq x]
    have hCeq : jointGibbsTiltGradientCross β
        (sourceJointHamiltonian μ Q hQ hnp α χ)
        (fun z => β*sourceJointHamiltonian μ Q hQ hnp α χ z-
          β*fieldOfMixture μ z.1.1 z.2) U GF G p =
        ∫ x, fC (v,x) ∂gibbsLaw N β (H v) := by
      unfold jointGibbsTiltGradientCross
      apply integral_congr_ae
      exact .of_forall fun x => by
        dsimp only [fC,tiltDefect]
        rw [← hweq x]
        have hsum :
            (∑ ij : Fin N×Fin N,
              U (p,x)*GF ij (p,x)*G ij (p,x)) =
            U (p,x)*(∑ ij : Fin N×Fin N,GF ij (p,x)*G ij (p,x)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro ij hij
          ring
        rw [hsum]
        ring
    dsimp only at he
    rw [hbe,hAeq,hReq,hKeq,hCeq] at he
    exact he
  have hraw := axisGibbs_signed_energy_global hN β H₀ hH₀ H hH
    fB fA fR fK fC (θ : ℝ) θ.coe_nonneg hM' hBint hAint hRint hKint hCint hpoint'
  exact hraw

end SlowEquilibration.ConditionedEntrance
