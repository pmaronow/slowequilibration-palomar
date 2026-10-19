-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntranceSourceJointRepresentatives
public import SlowEquilibration.ConditionedEntranceBaseJointRepresentatives

/-! A single joint original-base reference family, frozen in axis and
marks, identified with the literal physical reference at every source
parameter. No physical representative or measurability is supplied. -/
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

theorem sourceBaseReference_joint_physical_representatives (hN : 1≤N) (μ : FiniteMixture)
    (hnp : μ.minDegree<μ.maxDegree) (Q : ℝ) (hQ : 0<Q) (hQ1 : Q≤1)
    (α : ℝ) (hα : 0<α) (χ : ℝ→ℝ) (hχ : ContDiff ℝ 2 χ)
    (β : ℝ) (θ : ℝ≥0) (hθ : 0<θ) :
    ∃ U : SourceParameters N μ×Vector N→ℝ,
      ∃ G : (Fin N×Fin N)→SourceParameters N μ×Vector N→ℝ,
        StronglyMeasurable U ∧ (∀ ij,StronglyMeasurable (G ij)) ∧
        (∀ p q x,p.1=q.1 → U (p,x)=U (q,x)) ∧
        (∀ ij p q x,p.1=q.1 → G ij (p,x)=G ij (q,x)) ∧
        ∀ p : SourceParameters N μ,∀ hp : OnSphere p.2.1,
          let D := SourceData.atSourceParameters hN μ hnp Q hQ hQ1 α hα χ hχ p hp
          let F := referenceRate D.baseData β θ (referenceInitialVector D.baseData β)
          ∃ u : sphericalSobolevGraph hN β D.baseData.hamiltonian D.baseData.hamiltonian_contDiff.continuous,
            sphericalEnergyL2Map hN β D.baseData.hamiltonian D.baseData.hamiltonian_contDiff.continuous u=F ∧
            ((fun x => U (p,x))=ᵐ[sphereLaw N] F) ∧
            ∀ ij : Fin N×Fin N,(fun x => G ij (p,x))=ᵐ[sphereLaw N] u.val.snd ij := by
  have hθr : 0<(θ : ℝ) := by exact_mod_cast hθ
  obtain ⟨U,G,hU,hG,hUa,hGa⟩ := jointResolventSolution_joint_representatives hN β (θ : ℝ) hθr
    (fun z : Disorder N μ.maxDegree×Vector N => fieldOfMixture μ z.1 z.2)
    (fun _ => 0) (baseForcingJoint μ β (θ : ℝ))
    (field_jointContinuous (mixtureCoefficients μ)) continuous_const
    (baseForcingJoint_continuous hN μ β (θ : ℝ)) (fun _ => le_rfl)
  have hm : Measurable (fun z : SourceParameters N μ×Vector N => (z.1.1,z.2)) :=
    measurable_fst.fst.prodMk measurable_snd
  have hμ : ae (sphereLaw N) ≤ ae (gibbsLaw N 0 (fun _ => 0)) := by
    rw [gibbsLaw_zeroHamiltonian]
  refine ⟨fun z => U (z.1.1,z.2),fun ij z => G ij (z.1.1,z.2),
    hU.comp_measurable hm,fun ij => (hG ij).comp_measurable hm,
    fun p q x hpq => by change U (p.1,x)=U (q.1,x);rw [hpq],
    fun ij p q x hpq => by change G ij (p.1,x)=G ij (q.1,x);rw [hpq],?_⟩
  intro p hp
  let D := SourceData.atSourceParameters hN μ hnp Q hQ hQ1 α hα χ hχ p hp
  obtain ⟨u,hu,hval,hgrad⟩ := baseJointReferenceSolution_actual D β θ hθ
  refine ⟨u,hu,?_,?_⟩
  · exact ((hUa p.1).filter_mono hμ).trans hval
  · intro ij
    exact ((hGa ij p.1).filter_mono hμ).trans (hgrad ij)

end SlowEquilibration.ConditionedEntrance
