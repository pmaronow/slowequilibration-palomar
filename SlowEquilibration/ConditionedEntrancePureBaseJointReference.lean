-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.ConditionedEntranceBaseJointForcing
public import SlowEquilibration.ConditionedEntranceJointHamiltonian
public import SlowEquilibration.ConditionedEntrancePureBaseField
public import SlowEquilibration.ConditionedEntranceSmoothKilledGeneralJointPhysicalResolvent

/-! The actual original-base entropy reference is a continuous common
completed-graph family, with its exact physical resolvent identification. -/
@[expose] public section
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal InnerProductSpace
namespace SlowEquilibration.ConditionedEntrance
open SphericalModel SphericalForm SmoothKilledGeneral
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
variable {N : ℕ}

def originalJointReferenceSolution (hN : 1≤N) (μ : FiniteMixture) (β θ : ℝ)
    (J : Disorder N μ.maxDegree) : sphericalSobolevGraph hN 0 (fun _ => 0) continuous_const :=
  jointResolventSolution hN β θ (fun z : Disorder N μ.maxDegree×Vector N => fieldOfMixture μ z.1 z.2)
    (fun _ => 0) (baseForcingJoint μ β θ) (field_jointContinuous (mixtureCoefficients μ))
    continuous_const (baseForcingJoint_continuous hN μ β θ) J

theorem originalJointReferenceSolution_continuous (hN : 1≤N) (μ : FiniteMixture) (β θ : ℝ) (hθ : 0<θ) :
    Continuous (originalJointReferenceSolution hN μ β θ) :=
  jointResolventSolution_continuous hN β θ hθ _ _ _ (field_jointContinuous (mixtureCoefficients μ))
    continuous_const (baseForcingJoint_continuous hN μ β θ) (fun _ => le_rfl)

theorem originalJointReferenceSolution_actual (hN : 1 ≤ N) (μ : FiniteMixture) (J : Disorder N μ.maxDegree) (β : ℝ) (θ : ℝ≥0) (hθ : 0<θ) :
    let D₀ := FieldData.ofOriginal hN μ J
    let F := referenceRate D₀ β θ (referenceInitialVector D₀ β)
    ∃ u : sphericalSobolevGraph hN β D₀.hamiltonian D₀.hamiltonian_contDiff.continuous,
      sphericalEnergyL2Map hN β D₀.hamiltonian D₀.hamiltonian_contDiff.continuous u=F ∧
      ((originalJointReferenceSolution hN μ β (θ : ℝ) J).val.fst=ᵐ[sphereLaw N] F) ∧
      ∀ ij : Fin N×Fin N,
        (originalJointReferenceSolution hN μ β (θ : ℝ) J).val.snd ij=ᵐ[sphereLaw N] u.val.snd ij := by
  dsimp only
  let D₀ := FieldData.ofOriginal hN μ J
  let H := fun z : Disorder N μ.maxDegree×Vector N => fieldOfMixture μ z.1 z.2
  let g := baseForcingJoint (N:=N) μ β (θ : ℝ)
  have hH := field_jointContinuous (N:=N) (mixtureCoefficients μ)
  have hg := baseForcingJoint_continuous hN μ β (θ : ℝ)
  have hHp (x : Vector N) : H (J,x)=D₀.hamiltonian x :=
    rfl
  have hK : ∀ x : Vector N,‖(0 : ℝ)‖≤(0 : ℝ≥0) := fun _ => by simp only [norm_zero,NNReal.coe_zero,le_refl]
  obtain ⟨u,hu,hval,hgrad⟩ := jointResolventSolution_actual_source D₀ β θ hθ H (fun _ => 0) g
    hH continuous_const hg (fun _ => le_rfl) J hHp 0 hK
  let gp := fun x => g (J,x)
  have hgp : Continuous gp := hg.comp (continuous_const.prodMk continuous_id)
  have hforcing : gibbsToL2 hN β D₀.hamiltonian D₀.hamiltonian_contDiff.continuous gp hgp=
      (θ : ℝ) • referenceInitialVector D₀ β := by
    apply Lp.ext
    filter_upwards [gibbsToL2_coe hN β D₀.hamiltonian D₀.hamiltonian_contDiff.continuous gp hgp,
      Lp.coeFn_smul (θ : ℝ) (referenceInitialVector D₀ β),referenceInitialVector_ae D₀ β]
      with x hx hs hf
    rw [hx,hs,Pi.smul_apply,smul_eq_mul,hf]
    change baseForcingJoint μ β (θ : ℝ) (J,x)=
      (θ : ℝ)*(1+uniformInitialDensity N β D₀.hamiltonian x)
    simp only [baseForcingJoint,baseInitialJoint,D₀,FieldData.ofOriginal_hamiltonian]
  have hr : rateLaplace D₀ β (fun _ => 0) continuous_const (fun _ => le_rfl) θ
      (gibbsToL2 hN β D₀.hamiltonian D₀.hamiltonian_contDiff.continuous gp hgp)=
      referenceRate D₀ β θ (referenceInitialVector D₀ β) := by
    rw [hforcing,map_smul]
    rfl
  have hμ : ae (sphereLaw N) ≤ ae (gibbsLaw N 0 (fun _ => 0)) := by rw [gibbsLaw_zeroHamiltonian]
  refine ⟨u,hu.trans hr,?_,?_⟩
  · have hv := (hval.filter_mono hμ).trans (.of_forall (fun x => congrArg (fun f => f x) hr))
    simpa only [originalJointReferenceSolution,H,g] using hv
  · intro ij
    simpa only [originalJointReferenceSolution,H,g] using (hgrad ij).filter_mono hμ



/-- The reference is jointly measurable in the original disorder, and its
representatives are literally constant in the axis and conditioning marks. -/
theorem originalBaseReference_joint_physical_representatives (hN : 1 ≤ N)
    (μ : FiniteMixture) (β : ℝ) (θ : ℝ≥0) (hθ : 0 < θ) :
    ∃ U : SourceParameters N μ × Vector N → ℝ,
      ∃ G : (Fin N × Fin N) → SourceParameters N μ × Vector N → ℝ,
        StronglyMeasurable U ∧ (∀ ij, StronglyMeasurable (G ij)) ∧
        (∀ p q x, p.1 = q.1 → U (p,x) = U (q,x)) ∧
        (∀ ij p q x, p.1 = q.1 → G ij (p,x) = G ij (q,x)) ∧
        ∀ p : SourceParameters N μ,
          let D₀ := FieldData.ofOriginal hN μ p.1
          let F := referenceRate D₀ β θ (referenceInitialVector D₀ β)
          ∃ u : sphericalSobolevGraph hN β D₀.hamiltonian D₀.hamiltonian_contDiff.continuous,
            sphericalEnergyL2Map hN β D₀.hamiltonian D₀.hamiltonian_contDiff.continuous u = F ∧
            ((fun x => U (p,x)) =ᵐ[sphereLaw N] F) ∧
            ∀ ij : Fin N × Fin N,
              (fun x => G ij (p,x)) =ᵐ[sphereLaw N] u.val.snd ij := by
  have hθr : 0 < (θ : ℝ) := by exact_mod_cast hθ
  obtain ⟨U,G,hU,hG,hUa,hGa⟩ := jointResolventSolution_joint_representatives hN β (θ : ℝ) hθr
    (fun z : Disorder N μ.maxDegree × Vector N => fieldOfMixture μ z.1 z.2)
    (fun _ => 0) (baseForcingJoint μ β (θ : ℝ))
    (field_jointContinuous (mixtureCoefficients μ)) continuous_const
    (baseForcingJoint_continuous hN μ β (θ : ℝ)) (fun _ => le_rfl)
  have hm : Measurable (fun z : SourceParameters N μ × Vector N => (z.1.1,z.2)) :=
    measurable_fst.fst.prodMk measurable_snd
  have hμ : ae (sphereLaw N) ≤ ae (gibbsLaw N 0 (fun _ => 0)) := by
    rw [gibbsLaw_zeroHamiltonian]
  refine ⟨fun z => U (z.1.1,z.2), fun ij z => G ij (z.1.1,z.2),
    hU.comp_measurable hm,fun ij => (hG ij).comp_measurable hm,
    fun p q x hpq => by change U (p.1,x) = U (q.1,x); rw [hpq],
    fun ij p q x hpq => by change G ij (p.1,x) = G ij (q.1,x); rw [hpq],?_⟩
  intro p
  obtain ⟨u,hu,hval,hgrad⟩ := originalJointReferenceSolution_actual hN μ p.1 β θ hθ
  refine ⟨u,hu,?_,?_⟩
  · exact ((hUa p.1).filter_mono hμ).trans hval
  · intro ij
    exact ((hGa ij p.1).filter_mono hμ).trans (hgrad ij)

end SlowEquilibration.ConditionedEntrance
