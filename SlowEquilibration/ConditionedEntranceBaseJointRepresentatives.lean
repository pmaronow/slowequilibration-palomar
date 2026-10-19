-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntranceBaseJointReference

/-! The original-base entropy reference has actual joint value and
normalized-gradient representatives, frozen in the independent axis. -/
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

def SmoothKilled.SourceData.withDisorder (D : SourceData N) (J : Disorder N D.mixture.maxDegree) : SourceData N :=
  {D with disorder:=J}

theorem baseJointReferenceSolution_joint_physical_representatives (D : SourceData N)
    (β : ℝ) (θ : ℝ≥0) (hθ : 0<θ) :
    ∃ U : Disorder N D.mixture.maxDegree×Vector N→ℝ,
      ∃ G : (Fin N×Fin N)→Disorder N D.mixture.maxDegree×Vector N→ℝ,
        StronglyMeasurable U ∧ (∀ ij,StronglyMeasurable (G ij)) ∧
        ∀ J : Disorder N D.mixture.maxDegree,
          let D₀ := (D.withDisorder J).baseData
          let F := referenceRate D₀ β θ (referenceInitialVector D₀ β)
          ∃ u : sphericalSobolevGraph D.dimension_ge_one β D₀.hamiltonian D₀.hamiltonian_contDiff.continuous,
            sphericalEnergyL2Map D.dimension_ge_one β D₀.hamiltonian D₀.hamiltonian_contDiff.continuous u=F ∧
            ((fun x => U (J,x))=ᵐ[sphereLaw N] F) ∧
            ∀ ij : Fin N×Fin N,(fun x => G ij (J,x))=ᵐ[sphereLaw N] u.val.snd ij := by
  have hθr : 0<(θ : ℝ) := by exact_mod_cast hθ
  obtain ⟨U,G,hU,hG,hUa,hGa⟩ := jointResolventSolution_joint_representatives D.dimension_ge_one β (θ : ℝ) hθr
    (fun z : Disorder N D.mixture.maxDegree×Vector N => fieldOfMixture D.mixture z.1 z.2)
    (fun _ => 0) (baseForcingJoint D.mixture β (θ : ℝ))
    (field_jointContinuous (mixtureCoefficients D.mixture)) continuous_const
    (baseForcingJoint_continuous D.dimension_ge_one D.mixture β (θ : ℝ)) (fun _ => le_rfl)
  have hμ : ae (sphereLaw N) ≤ ae (gibbsLaw N 0 (fun _ => 0)) := by rw [gibbsLaw_zeroHamiltonian]
  refine ⟨U,G,hU,hG,?_⟩
  intro J
  obtain ⟨u,hu,hval,hgrad⟩ := baseJointReferenceSolution_actual (D.withDisorder J) β θ hθ
  exact ⟨u,hu,((hUa J).filter_mono hμ).trans hval,
    fun ij => ((hGa ij J).filter_mono hμ).trans (hgrad ij)⟩

theorem baseJointReference_frozen_axis_representatives (D : SourceData N)
    (β : ℝ) (θ : ℝ≥0) (hθ : 0<θ) :
    ∃ U : Vector N×(Disorder N D.mixture.maxDegree×Vector N)→ℝ,
      ∃ G : (Fin N×Fin N)→Vector N×(Disorder N D.mixture.maxDegree×Vector N)→ℝ,
        StronglyMeasurable U ∧ (∀ ij,StronglyMeasurable (G ij)) ∧
        (∀ a b J x,U (a,(J,x))=U (b,(J,x))) ∧
        (∀ ij a b J x,G ij (a,(J,x))=G ij (b,(J,x))) ∧
        ∀ a J,
          let D₀ := (D.withDisorder J).baseData
          let F := referenceRate D₀ β θ (referenceInitialVector D₀ β)
          ∃ u : sphericalSobolevGraph D.dimension_ge_one β D₀.hamiltonian D₀.hamiltonian_contDiff.continuous,
            sphericalEnergyL2Map D.dimension_ge_one β D₀.hamiltonian D₀.hamiltonian_contDiff.continuous u=F ∧
            ((fun x => U (a,(J,x)))=ᵐ[sphereLaw N] F) ∧
            ∀ ij : Fin N×Fin N,(fun x => G ij (a,(J,x)))=ᵐ[sphereLaw N] u.val.snd ij := by
  obtain ⟨U,G,hU,hG,hUa⟩ := baseJointReferenceSolution_joint_physical_representatives D β θ hθ
  exact ⟨fun z => U z.2,fun ij z => G ij z.2,hU.comp_measurable measurable_snd,
    fun ij => (hG ij).comp_measurable measurable_snd,fun _ _ _ _ => rfl,
    fun _ _ _ _ _ => rfl,fun _ J => hUa J⟩

end SlowEquilibration.ConditionedEntrance
