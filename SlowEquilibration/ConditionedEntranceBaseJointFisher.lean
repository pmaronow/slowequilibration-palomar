-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntranceBaseJointRepresentatives

/-! Actual original regular-bank Fisher bounds for the identified joint
entropy-reference graph, with the true linear-in-N original field bound. -/
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

theorem baseJointReferenceSolution_regular_fisher (D : SourceData N) (β : ℝ) (hβ : 0≤β)
    (θ : ℝ≥0) (hθ : 0<θ) (hJ : D.disorder∈regularDisorder) :
    let F := referenceRate D.baseData β θ (referenceInitialVector D.baseData β)
    ∃ u : sphericalSobolevGraph D.dimension_ge_one β D.baseData.hamiltonian D.baseData.hamiltonian_contDiff.continuous,
      sphericalEnergyL2Map D.dimension_ge_one β D.baseData.hamiltonian D.baseData.hamiltonian_contDiff.continuous u=F ∧
      ((baseJointReferenceSolution D.dimension_ge_one D.mixture β (θ : ℝ) D.disorder).val.fst=ᵐ[sphereLaw N] F) ∧
      (∀ ij : Fin N×Fin N,
        (baseJointReferenceSolution D.dimension_ge_one D.mixture β (θ : ℝ) D.disorder).val.snd ij=ᵐ[sphereLaw N] u.val.snd ij) ∧
      0 ≤ sphericalFisher D.dimension_ge_one β D.baseData.hamiltonian D.baseData.hamiltonian_contDiff.continuous u ∧
      sphericalFisher D.dimension_ge_one β D.baseData.hamiltonian D.baseData.hamiltonian_contDiff.continuous u≤
        (θ : ℝ)*(2*Real.log 2+4*β*derivativeConstant (mixtureCoefficients D.mixture)*(N : ℝ)) := by
  let B := derivativeConstant (mixtureCoefficients D.mixture)*(N : ℝ)
  have hB0 : 0≤B := mul_nonneg (derivativeConstant_pos _).le (Nat.cast_nonneg _)
  have hB : ∀ x,OnSphere x → |fieldOfMixture D.mixture D.disorder x|≤B := by
    intro x hx
    have hn := SphericalAging.LandscapeDerivatives.sphere_norm x ((onSphere_iff_norm_sq x).mp hx)
    exact (field_regularDisorder_ball_bounds D.dimension_ge_one (mixtureCoefficients D.mixture)
      D.disorder hJ x (by rw [hn])).1
  obtain ⟨u,hu,hval,hgrad⟩ := baseJointReferenceSolution_actual D β θ hθ
  obtain ⟨v,hv,hJ0,hJb⟩ := source_base_reference_fisher D β hβ B hB0 hB θ hθ
  have he : u=v := sphericalEnergyL2Map_injective D.dimension_ge_one β D.baseData.hamiltonian
    (D.baseData.hamiltonian_contDiff.of_le (by norm_num)) (hu.trans hv.symm)
  refine ⟨u,hu,hval,hgrad,?_,?_⟩
  · simpa only [he] using hJ0
  · have hb : 2*Real.log 2+4*β*B=2*Real.log 2+4*β*derivativeConstant (mixtureCoefficients D.mixture)*(N : ℝ) := by
      dsimp [B]
      ring
    simpa only [he,hb] using hJb

end SlowEquilibration.ConditionedEntrance
