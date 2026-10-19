-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntranceSourceJointKilling
public import SlowEquilibration.ConditionedEntranceJointPhysicalResolvent

/-! Actual jointly measurable source killed-resolvent values and completed
normalized gradients, at every physical axis and all disorder/marks. -/
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

theorem sourceJointKilledSolution_actual (hN : 1≤N) (μ : FiniteMixture)
    (hnp : μ.minDegree<μ.maxDegree) (Q : ℝ) (hQ : 0<Q) (hQ1 : Q≤1)
    (α : ℝ) (hα : 0<α) (χ : ℝ→ℝ) (hχ : ContDiff ℝ 2 χ)
    (β : ℝ) (θ : ℝ≥0) (hθ : 0<θ) (p : SourceParameters N μ) (hp : OnSphere p.2.1) :
    let D := SourceData.atSourceParameters hN μ hnp Q hQ hQ1 α hα χ hχ p hp
    let κ := PhysicalHitting.capKilling α p.2.1
    let hκ := (PhysicalHitting.capKilling_contDiff α p.2.1).continuous
    let hκ0 := PhysicalHitting.capKilling_nonneg α p.2.1
    let h := rateLaplace D β κ hκ hκ0 θ (killingVector D β κ hκ)
    ∃ u : sphericalSobolevGraph hN β D.hamiltonian D.hamiltonian_contDiff.continuous,
      sphericalEnergyL2Map hN β D.hamiltonian D.hamiltonian_contDiff.continuous u=h ∧
      ((sourceJointKilledSolution hN μ Q hQ hnp α χ hχ.continuous β (θ : ℝ) p).val.fst=ᵐ[sphereLaw N] h) ∧
      ∀ ij : Fin N×Fin N,
        (sourceJointKilledSolution hN μ Q hQ hnp α χ hχ.continuous β (θ : ℝ) p).val.snd ij=ᵐ[sphereLaw N] u.val.snd ij := by
  let D := SourceData.atSourceParameters hN μ hnp Q hQ hQ1 α hα χ hχ p hp
  let H := sourceJointHamiltonian (N:=N) μ Q hQ hnp α χ
  let κ := sourceJointCapKilling (N:=N) μ α
  have hH := sourceJointHamiltonian_continuous (N:=N) μ Q hQ hnp α χ hχ.continuous
  have hκ := sourceJointCapKilling_continuous (N:=N) μ α
  have hK : ∀ x,‖κ (p,x)‖≤(1 : ℝ≥0) := by
    intro x
    change ‖PhysicalHitting.capKilling α p.2.1 x‖≤(1 : ℝ≥0)
    rw [Real.norm_eq_abs,abs_of_nonneg (PhysicalHitting.capKilling_nonneg α p.2.1 x)]
    exact PhysicalHitting.capKilling_le_one hα p.2.1 x
  have he := jointResolventSolution_actual_source D β θ hθ H κ κ hH hκ hκ
    (sourceJointCapKilling_nonnegative μ α) p (fun x => rfl) 1 hK
  obtain ⟨u,hu,hval,hgrad⟩ := he
  have hμ : ae (sphereLaw N) ≤ ae (gibbsLaw N 0 (fun _ => 0)) := by
    rw [gibbsLaw_zeroHamiltonian]
  refine ⟨u,hu,?_,?_⟩
  · simpa only [sourceJointKilledSolution,jointKilledSolution,jointResolventSolution,
      killingVector,sourceJointCapKilling,D,H,κ] using hval.filter_mono hμ
  · intro ij
    simpa only [sourceJointKilledSolution,jointKilledSolution,jointResolventSolution] using (hgrad ij).filter_mono hμ

/-- Genuine joint representatives of the literal physical source inverse,
including every normalized-gradient coordinate. The full weak equation,
domain transport, and all measurability are proved before this consumer. -/
theorem sourceJointKilledSolution_joint_physical_representatives (hN : 1≤N) (μ : FiniteMixture)
    (hnp : μ.minDegree<μ.maxDegree) (Q : ℝ) (hQ : 0<Q) (hQ1 : Q≤1)
    (α : ℝ) (hα : 0<α) (χ : ℝ→ℝ) (hχ : ContDiff ℝ 2 χ)
    (β : ℝ) (θ : ℝ≥0) (hθ : 0<θ) :
    ∃ U : SourceParameters N μ×Vector N→ℝ,
      ∃ G : (Fin N×Fin N)→SourceParameters N μ×Vector N→ℝ,
        StronglyMeasurable U ∧ (∀ ij,StronglyMeasurable (G ij)) ∧
        ∀ p : SourceParameters N μ,∀ hp : OnSphere p.2.1,
          let D := SourceData.atSourceParameters hN μ hnp Q hQ hQ1 α hα χ hχ p hp
          let κ := PhysicalHitting.capKilling α p.2.1
          let hκ := (PhysicalHitting.capKilling_contDiff α p.2.1).continuous
          let hκ0 := PhysicalHitting.capKilling_nonneg α p.2.1
          let h := rateLaplace D β κ hκ hκ0 θ (killingVector D β κ hκ)
          ∃ u : sphericalSobolevGraph hN β D.hamiltonian D.hamiltonian_contDiff.continuous,
            sphericalEnergyL2Map hN β D.hamiltonian D.hamiltonian_contDiff.continuous u=h ∧
            ((fun x => U (p,x))=ᵐ[sphereLaw N] h) ∧
            ∀ ij : Fin N×Fin N,(fun x => G ij (p,x))=ᵐ[sphereLaw N] u.val.snd ij := by
  have hθr : 0<(θ : ℝ) := by exact_mod_cast hθ
  obtain ⟨U,G,hU,hG,hUa,hGa⟩ := jointKilledSolution_joint_representatives hN β (θ : ℝ) hθr
    (sourceJointHamiltonian (N:=N) μ Q hQ hnp α χ) (sourceJointCapKilling (N:=N) μ α)
    (sourceJointHamiltonian_continuous μ Q hQ hnp α χ hχ.continuous)
    (sourceJointCapKilling_continuous μ α) (sourceJointCapKilling_nonnegative μ α)
  have hμ : ae (sphereLaw N) ≤ ae (gibbsLaw N 0 (fun _ => 0)) := by
    rw [gibbsLaw_zeroHamiltonian]
  refine ⟨U,G,hU,hG,?_⟩
  intro p hp
  obtain ⟨u,hu,hval,hgrad⟩ := sourceJointKilledSolution_actual hN μ hnp Q hQ hQ1 α hα χ hχ β θ hθ p hp
  exact ⟨u,hu,((hUa p).filter_mono hμ).trans hval,
    fun ij => ((hGa ij p).filter_mono hμ).trans (hgrad ij)⟩

end SlowEquilibration.ConditionedEntrance
