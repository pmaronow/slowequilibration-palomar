-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntranceAxisSignedEnergyGlobal
public import SlowEquilibration.ConditionedEntrancePureGradientFibreIntegral
public import SlowEquilibration.ConditionedEntrancePureSignedGlobalAllEnergy

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

theorem pure_joint_signed_global_raw_energy_of_fibres
    {N : ℕ} (hN : 1 ≤ N) (d : ℕ) (hd : 2 ≤ d) (c : ℝ) (hc : 0 < c) (Q : ℝ)
    (α : ℝ) (χ : ℝ → ℝ) (hχ : ContDiff ℝ 2 χ)
    (β : ℝ) (θ : ℝ≥0) (J : Disorder N (FiniteMixture.pure d hd c hc).maxDegree) (e : ℝ)
    (F U : SourceParameters N (FiniteMixture.pure d hd c hc) × Vector N → ℝ)
    (GF G : (Fin N × Fin N) → SourceParameters N (FiniteMixture.pure d hd c hc) × Vector N → ℝ)
    (M : ℝ) (hM : 0 < M)
    (hMphys : M = ∫ z : Vector N×Vector N,
      Real.exp (β*(pureSourceSmoothCutoffField d hd c hc Q J z.1 e α χ z.2-
        fieldOfMixture (FiniteMixture.pure d hd c hc) J z.2))
      ∂((sphereLaw N).prod (gibbsLaw N β (fieldOfMixture (FiniteMixture.pure d hd c hc) J))))
    (hBint : Integrable (fun z : Vector N×Vector N =>
      F ((J,(z.1,(e,0))),z.2)*
        (∑ ij : Fin N×Fin N,(G ij ((J,(z.1,(e,0))),z.2))^2))
      (normalizedTilt ((sphereLaw N).prod (gibbsLaw N β (fieldOfMixture (FiniteMixture.pure d hd c hc) J)))
        (fun z => β*(pureSourceSmoothCutoffField d hd c hc Q J z.1 e α χ z.2-
          fieldOfMixture (FiniteMixture.pure d hd c hc) J z.2)) M))
    (hAint : Integrable (fun z : Vector N×Vector N =>
      F ((J,(z.1,(e,0))),z.2)*U ((J,(z.1,(e,0))),z.2)^2)
      (normalizedTilt ((sphereLaw N).prod (gibbsLaw N β (fieldOfMixture (FiniteMixture.pure d hd c hc) J)))
        (fun z => β*(pureSourceSmoothCutoffField d hd c hc Q J z.1 e α χ z.2-
          fieldOfMixture (FiniteMixture.pure d hd c hc) J z.2)) M))
    (hRint : Integrable (fun z : Vector N×Vector N =>
      PhysicalHitting.capKilling α z.1 z.2*F ((J,(z.1,(e,0))),z.2))
      (normalizedTilt ((sphereLaw N).prod (gibbsLaw N β (fieldOfMixture (FiniteMixture.pure d hd c hc) J)))
        (fun z => β*(pureSourceSmoothCutoffField d hd c hc Q J z.1 e α χ z.2-
          fieldOfMixture (FiniteMixture.pure d hd c hc) J z.2)) M))
    (hKint : Integrable (fun z : Vector N×Vector N =>
      tiltDefect (fun y : Vector N×Vector N =>
        β*(pureSourceSmoothCutoffField d hd c hc Q J y.1 e α χ y.2-
          fieldOfMixture (FiniteMixture.pure d hd c hc) J y.2)) z *
      (F ((J,(z.1,(e,0))),z.2)-1)*U ((J,(z.1,(e,0))),z.2)^2)
      (normalizedTilt ((sphereLaw N).prod (gibbsLaw N β (fieldOfMixture (FiniteMixture.pure d hd c hc) J)))
        (fun z => β*(pureSourceSmoothCutoffField d hd c hc Q J z.1 e α χ z.2-
          fieldOfMixture (FiniteMixture.pure d hd c hc) J z.2)) M))
    (hCint : Integrable (fun z : Vector N×Vector N =>
      tiltDefect (fun y : Vector N×Vector N =>
        β*(pureSourceSmoothCutoffField d hd c hc Q J y.1 e α χ y.2-
          fieldOfMixture (FiniteMixture.pure d hd c hc) J y.2)) z *
      U ((J,(z.1,(e,0))),z.2)*
        (∑ ij : Fin N×Fin N,
          GF ij ((J,(z.1,(e,0))),z.2)*G ij ((J,(z.1,(e,0))),z.2)))
      (normalizedTilt ((sphereLaw N).prod (gibbsLaw N β (fieldOfMixture (FiniteMixture.pure d hd c hc) J)))
        (fun z => β*(pureSourceSmoothCutoffField d hd c hc Q J z.1 e α χ z.2-
          fieldOfMixture (FiniteMixture.pure d hd c hc) J z.2)) M))
    (hBfibre : ∀ v : Vector N, OnSphere v →
      let p : SourceParameters N (FiniteMixture.pure d hd c hc) := (J,(v,(e,0)))
      jointGibbsWeightedGradientSquare β
        (pureSourceJointHamiltonian d hd c hc Q α χ) F G p =
        ∫ x, F (p,x)*(∑ ij : Fin N×Fin N,(G ij (p,x))^2)
          ∂gibbsLaw N β
            (pureSourceSmoothCutoffField d hd c hc Q J v e α χ))
    (hpoint : ∀ v : Vector N, OnSphere v →
      let p : SourceParameters N (FiniteMixture.pure d hd c hc) := (J,(v,(e,0)))
      let H := pureSourceJointHamiltonian d hd c hc Q α χ
      let H₀ := fun z : SourceParameters N (FiniteMixture.pure d hd c hc)×Vector N => fieldOfMixture (FiniteMixture.pure d hd c hc) z.1.1 z.2
      let w := fun z => β*H z-β*H₀ z
      let κ := sourceJointCapKilling (FiniteMixture.pure d hd c hc) α
      jointGibbsWeightedGradientSquare β H F G p+
        (θ : ℝ)/2*jointGibbsWeightedSquare β H F U p ≤
          jointGibbsKilledReference β H κ F p-
          (θ : ℝ)/2*jointGibbsZeroDefectSquare β H w F U p-
          jointGibbsTiltGradientCross β H w U GF G p) :
    let H₀ := fieldOfMixture (FiniteMixture.pure d hd c hc) J
    let H : Vector N → Vector N → ℝ := fun v x =>
      pureSourceSmoothCutoffField d hd c hc Q J v e α χ x
    let w : Vector N×Vector N → ℝ := fun z => β*(H z.1 z.2-H₀ z.2)
    let ν := normalizedTilt ((sphereLaw N).prod (gibbsLaw N β H₀)) w M
    let Fa : Vector N×Vector N → ℝ := fun z => F ((J,(z.1,(e,0))),z.2)
    let Ua : Vector N×Vector N → ℝ := fun z => U ((J,(z.1,(e,0))),z.2)
    let GFa : (Fin N×Fin N) → Vector N×Vector N → ℝ := fun ij z =>
      GF ij ((J,(z.1,(e,0))),z.2)
    let Ga : (Fin N×Fin N) → Vector N×Vector N → ℝ := fun ij z =>
      G ij ((J,(z.1,(e,0))),z.2)
    (∫ z, Fa z*(∑ ij : Fin N×Fin N,(Ga ij z)^2) ∂ν)+
      (θ : ℝ)/2*(∫ z, Fa z*Ua z^2 ∂ν) ≤
        (∫ z, PhysicalHitting.capKilling α z.1 z.2*Fa z ∂ν)+
        (θ : ℝ)/2*|∫ z, tiltDefect w z*(Fa z-1)*Ua z^2 ∂ν|+
        |∫ z, tiltDefect w z*Ua z*
          (∑ ij : Fin N×Fin N,GFa ij z*Ga ij z) ∂ν| := by
  dsimp only
  subst M
  let H₀ := fieldOfMixture (FiniteMixture.pure d hd c hc) J
  let H : Vector N → Vector N → ℝ := fun v x =>
    pureSourceSmoothCutoffField d hd c hc Q J v e α χ x
  let w : Vector N×Vector N → ℝ := fun z => β*(H z.1 z.2-H₀ z.2)
  let fB : Vector N×Vector N → ℝ := fun z =>
    F ((J,(z.1,(e,0))),z.2)*
      (∑ ij : Fin N×Fin N,(G ij ((J,(z.1,(e,0))),z.2))^2)
  let fA : Vector N×Vector N → ℝ := fun z =>
    F ((J,(z.1,(e,0))),z.2)*U ((J,(z.1,(e,0))),z.2)^2
  let fR : Vector N×Vector N → ℝ := fun z =>
    PhysicalHitting.capKilling α z.1 z.2*F ((J,(z.1,(e,0))),z.2)
  let fK : Vector N×Vector N → ℝ := fun z =>
    tiltDefect w z*(F ((J,(z.1,(e,0))),z.2)-1)*U ((J,(z.1,(e,0))),z.2)^2
  let fC : Vector N×Vector N → ℝ := fun z =>
    tiltDefect w z*U ((J,(z.1,(e,0))),z.2)*
      (∑ ij : Fin N×Fin N,
        GF ij ((J,(z.1,(e,0))),z.2)*G ij ((J,(z.1,(e,0))),z.2))
  have hH₀ : Continuous H₀ := (fieldOfMixture_contDiff (FiniteMixture.pure d hd c hc) J).continuous
  have hH : Continuous (fun z : Vector N×Vector N => H z.1 z.2) :=
    (pure_axisJointHamiltonian_contDiff d hd c hc Q α χ hχ J e).continuous
  have hM' : 0 < ∫ z : Vector N×Vector N, Real.exp (w z)
      ∂((sphereLaw N).prod (gibbsLaw N β H₀)) := by
    exact hM
  have hpoint' (v : Vector N) (hv : OnSphere v) :
      (∫ x, fB (v,x) ∂gibbsLaw N β (H v))+
        (θ : ℝ)/2*(∫ x, fA (v,x) ∂gibbsLaw N β (H v)) ≤
      (∫ x, fR (v,x) ∂gibbsLaw N β (H v))-
        (θ : ℝ)/2*(∫ x, fK (v,x) ∂gibbsLaw N β (H v))-
        (∫ x, fC (v,x) ∂gibbsLaw N β (H v)) := by
    let p : SourceParameters N (FiniteMixture.pure d hd c hc) := (J,(v,(e,0)))
    have he := hpoint v hv
    have hbe := hBfibre v hv
    -- The four remaining joint energies are fibre integrals by definition.
    have hweq (x : Vector N) :
        (β*pureSourceJointHamiltonian d hd c hc Q α χ (p,x)-
          β*fieldOfMixture (FiniteMixture.pure d hd c hc) J x) = w (v,x) := by
      dsimp only [w,H,H₀,pureSourceJointHamiltonian,p]
      ring
    have hAeq : jointGibbsWeightedSquare β
        (pureSourceJointHamiltonian d hd c hc Q α χ) F U p =
        ∫ x, fA (v,x) ∂gibbsLaw N β (H v) := rfl
    have hReq : jointGibbsKilledReference β
        (pureSourceJointHamiltonian d hd c hc Q α χ)
        (sourceJointCapKilling (FiniteMixture.pure d hd c hc) α) F p =
        ∫ x, fR (v,x) ∂gibbsLaw N β (H v) := rfl
    have hKeq : jointGibbsZeroDefectSquare β
        (pureSourceJointHamiltonian d hd c hc Q α χ)
        (fun z => β*pureSourceJointHamiltonian d hd c hc Q α χ z-
          β*fieldOfMixture (FiniteMixture.pure d hd c hc) z.1.1 z.2) F U p =
        ∫ x, fK (v,x) ∂gibbsLaw N β (H v) := by
      unfold jointGibbsZeroDefectSquare
      apply integral_congr_ae
      exact .of_forall fun x => by
        dsimp only [fK,tiltDefect]
        rw [← hweq x]
    have hCeq : jointGibbsTiltGradientCross β
        (pureSourceJointHamiltonian d hd c hc Q α χ)
        (fun z => β*pureSourceJointHamiltonian d hd c hc Q α χ z-
          β*fieldOfMixture (FiniteMixture.pure d hd c hc) z.1.1 z.2) U GF G p =
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
