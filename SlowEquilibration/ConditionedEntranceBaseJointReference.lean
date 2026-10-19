-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntranceBaseJointForcing
public import SlowEquilibration.ConditionedEntranceBaseReference
public import SlowEquilibration.ConditionedEntranceJointPhysicalResolvent

/-! The actual original-base entropy reference is a continuous common
completed-graph family, with its exact physical resolvent identification. -/
@[expose] public section
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal InnerProductSpace
namespace SlowEquilibration.ConditionedEntrance
open SphericalModel SphericalForm SmoothKilled
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
variable {N : ℕ}

def baseJointReferenceSolution (hN : 1≤N) (μ : FiniteMixture) (β θ : ℝ)
    (J : Disorder N μ.maxDegree) : sphericalSobolevGraph hN 0 (fun _ => 0) continuous_const :=
  jointResolventSolution hN β θ (fun z : Disorder N μ.maxDegree×Vector N => fieldOfMixture μ z.1 z.2)
    (fun _ => 0) (baseForcingJoint μ β θ) (field_jointContinuous (mixtureCoefficients μ))
    continuous_const (baseForcingJoint_continuous hN μ β θ) J

theorem baseJointReferenceSolution_continuous (hN : 1≤N) (μ : FiniteMixture) (β θ : ℝ) (hθ : 0<θ) :
    Continuous (baseJointReferenceSolution hN μ β θ) :=
  jointResolventSolution_continuous hN β θ hθ _ _ _ (field_jointContinuous (mixtureCoefficients μ))
    continuous_const (baseForcingJoint_continuous hN μ β θ) (fun _ => le_rfl)

theorem baseJointReferenceSolution_actual (D : SourceData N) (β : ℝ) (θ : ℝ≥0) (hθ : 0<θ) :
    let F := referenceRate D.baseData β θ (referenceInitialVector D.baseData β)
    ∃ u : sphericalSobolevGraph D.dimension_ge_one β D.baseData.hamiltonian D.baseData.hamiltonian_contDiff.continuous,
      sphericalEnergyL2Map D.dimension_ge_one β D.baseData.hamiltonian D.baseData.hamiltonian_contDiff.continuous u=F ∧
      ((baseJointReferenceSolution D.dimension_ge_one D.mixture β (θ : ℝ) D.disorder).val.fst=ᵐ[sphereLaw N] F) ∧
      ∀ ij : Fin N×Fin N,
        (baseJointReferenceSolution D.dimension_ge_one D.mixture β (θ : ℝ) D.disorder).val.snd ij=ᵐ[sphereLaw N] u.val.snd ij := by
  let H := fun z : Disorder N D.mixture.maxDegree×Vector N => fieldOfMixture D.mixture z.1 z.2
  let g := baseForcingJoint (N:=N) D.mixture β (θ : ℝ)
  have hH := field_jointContinuous (N:=N) (mixtureCoefficients D.mixture)
  have hg := baseForcingJoint_continuous D.dimension_ge_one D.mixture β (θ : ℝ)
  have hHp (x : Vector N) : H (D.disorder,x)=D.baseData.hamiltonian x :=
    (congrFun (SourceData.baseData_hamiltonian D) x).symm
  have hK : ∀ x : Vector N,‖(0 : ℝ)‖≤(0 : ℝ≥0) := fun _ => by simp only [norm_zero,NNReal.coe_zero,le_refl]
  obtain ⟨u,hu,hval,hgrad⟩ := jointResolventSolution_actual_source D.baseData β θ hθ H (fun _ => 0) g
    hH continuous_const hg (fun _ => le_rfl) D.disorder hHp 0 hK
  let gp := fun x => g (D.disorder,x)
  have hgp : Continuous gp := hg.comp (continuous_const.prodMk continuous_id)
  have hforcing : gibbsToL2 D.dimension_ge_one β D.baseData.hamiltonian D.baseData.hamiltonian_contDiff.continuous gp hgp=
      (θ : ℝ) • referenceInitialVector D.baseData β := by
    apply Lp.ext
    filter_upwards [gibbsToL2_coe D.dimension_ge_one β D.baseData.hamiltonian D.baseData.hamiltonian_contDiff.continuous gp hgp,
      Lp.coeFn_smul (θ : ℝ) (referenceInitialVector D.baseData β),referenceInitialVector_ae D.baseData β]
      with x hx hs hf
    rw [hx,hs,Pi.smul_apply,smul_eq_mul,hf]
    change baseForcingJoint D.mixture β (θ : ℝ) (D.disorder,x)=
      (θ : ℝ)*(1+uniformInitialDensity N β D.baseData.hamiltonian x)
    simp only [baseForcingJoint,baseInitialJoint,SourceData.baseData_hamiltonian]
  have hr : rateLaplace D.baseData β (fun _ => 0) continuous_const (fun _ => le_rfl) θ
      (gibbsToL2 D.dimension_ge_one β D.baseData.hamiltonian D.baseData.hamiltonian_contDiff.continuous gp hgp)=
      referenceRate D.baseData β θ (referenceInitialVector D.baseData β) := by
    rw [hforcing,map_smul]
    rfl
  have hμ : ae (sphereLaw N) ≤ ae (gibbsLaw N 0 (fun _ => 0)) := by rw [gibbsLaw_zeroHamiltonian]
  refine ⟨u,hu.trans hr,?_,?_⟩
  · have hv := (hval.filter_mono hμ).trans (.of_forall (fun x => congrArg (fun f => f x) hr))
    simpa only [baseJointReferenceSolution,H,g] using hv
  · intro ij
    simpa only [baseJointReferenceSolution,H,g] using (hgrad ij).filter_mono hμ

end SlowEquilibration.ConditionedEntrance
