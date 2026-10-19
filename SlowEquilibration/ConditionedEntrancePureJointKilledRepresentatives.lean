-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntrancePureJointHamiltonian
public import SlowEquilibration.ConditionedEntranceSourceJointKilling
public import SlowEquilibration.ConditionedEntranceSmoothKilledGeneralJointPhysicalResolvent
public import SlowEquilibration.ConditionedEntranceSmoothKilledGeneralMassBalance

/-! Joint measurable representatives of the actual proper-pure killed
resolvent and every completed spherical-gradient coordinate. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.ConditionedEntrance
open MeasureTheory Filter SphericalModel SphericalForm
open SphericalAging HardSphereDynamics SmoothKilledGeneral
open scoped NNReal ENNReal RealInnerProductSpace
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

theorem pureJointKilledSolution_joint_physical_representatives {N : ℕ} (hN : 1 ≤ N)
    (p : ℕ) (hp : 2 ≤ p) (c : ℝ) (hc : 0 < c) (Q α : ℝ) (hα : 0 < α)
    (χ : ℝ → ℝ) (hχ : ContDiff ℝ 2 χ)
    (β : ℝ) (θ : ℝ≥0) (hθ : 0 < θ) :
    let μ := FiniteMixture.pure p hp c hc
    ∃ U : SourceParameters N μ × Vector N → ℝ,
      ∃ G : (Fin N × Fin N) → SourceParameters N μ × Vector N → ℝ,
        StronglyMeasurable U ∧ (∀ ij, StronglyMeasurable (G ij)) ∧
        ∀ q : SourceParameters N μ,
          let D := FieldData.ofPure hN p hp c hc Q q.1 q.2.1 q.2.2.1 α χ hχ
          let κ := PhysicalHitting.capKilling α q.2.1
          let hκ := (PhysicalHitting.capKilling_contDiff α q.2.1).continuous
          let hκ0 := PhysicalHitting.capKilling_nonneg α q.2.1
          let h := rateLaplace D β κ hκ hκ0 θ (killingVector D β κ hκ)
          ∃ u : sphericalSobolevGraph hN β D.hamiltonian D.hamiltonian_contDiff.continuous,
            sphericalEnergyL2Map hN β D.hamiltonian D.hamiltonian_contDiff.continuous u = h ∧
            ((fun x => U (q,x)) =ᵐ[sphereLaw N] h) ∧
            ∀ ij : Fin N × Fin N,
              (fun x => G ij (q,x)) =ᵐ[sphereLaw N] u.val.snd ij := by
  dsimp only
  let μ := FiniteMixture.pure p hp c hc
  let H := pureSourceJointHamiltonian (N := N) p hp c hc Q α χ
  let κ := sourceJointCapKilling (N := N) μ α
  have hH : Continuous H := (pureSourceJointHamiltonian_contDiff p hp c hc Q α χ hχ).continuous
  have hκ : Continuous κ := sourceJointCapKilling_continuous μ α
  have hκ0 : ∀ z, 0 ≤ κ z := sourceJointCapKilling_nonnegative μ α
  have hθr : 0 < (θ : ℝ) := by exact_mod_cast hθ
  obtain ⟨U,G,hU,hG,hUa,hGa⟩ :=
    jointKilledSolution_joint_representatives hN β (θ : ℝ) hθr H κ hH hκ hκ0
  have hzero : ae (sphereLaw N) ≤ ae (gibbsLaw N 0 (fun _ => 0)) := by
    rw [gibbsLaw_zeroHamiltonian]
  refine ⟨U,G,hU,hG,?_⟩
  intro q
  let D := FieldData.ofPure hN p hp c hc Q q.1 q.2.1 q.2.2.1 α χ hχ
  have hHp : ∀ x, H (q,x) = D.hamiltonian x := by
    intro x
    rw [FieldData.ofPure_hamiltonian]
    rfl
  have hK : ∀ x, ‖κ (q,x)‖ ≤ (1 : ℝ≥0) := by
    intro x
    change ‖PhysicalHitting.capKilling α q.2.1 x‖ ≤ (1 : ℝ≥0)
    rw [Real.norm_eq_abs,abs_of_nonneg (PhysicalHitting.capKilling_nonneg α q.2.1 x)]
    exact PhysicalHitting.capKilling_le_one hα q.2.1 x
  obtain ⟨u,hu,hval,hgrad⟩ := jointResolventSolution_actual_source D β θ hθ
    H κ κ hH hκ hκ hκ0 q hHp 1 hK
  refine ⟨u,hu,?_,?_⟩
  · exact ((hUa q).filter_mono hzero).trans (hval.filter_mono hzero)
  · intro ij
    exact ((hGa ij q).filter_mono hzero).trans ((hgrad ij).filter_mono hzero)

end SlowEquilibration.ConditionedEntrance
