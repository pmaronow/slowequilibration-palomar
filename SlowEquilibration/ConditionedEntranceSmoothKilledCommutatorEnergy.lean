-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SphericalGeneratorSquareCommutator
public import SlowEquilibration.ConditionedEntranceBaseJointFisher
public import SlowEquilibration.ConditionedEntranceSmoothKilledWeightedEnergy

/-! The actual original-base entropy reference and literal physical
killed source solve the square-test weighted commutator energy identity.
Neither a tested equation nor a cross-term/Fisher estimate is supplied. -/
@[expose] public section
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal InnerProductSpace
namespace SlowEquilibration.ConditionedEntrance.SmoothKilled
open SphericalModel SphericalForm KilledOperator
open SphericalAging.HardSphereDynamics
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
variable {N : ℕ}

theorem rateLaplace_reference_commutator_energy (D : SourceData N) (β : ℝ) (hβ : 0≤β)
    (κ : Vector N→ℝ) (hκ : Continuous κ) (hκ0 : ∀ x,0≤κ x) (K : ℝ≥0) (hK : ∀ x,‖κ x‖≤K)
    (θ : ℝ≥0) (hθ : 0<θ) (hJ : D.disorder∈regularDisorder) :
    let F := referenceRate D.baseData β θ (referenceInitialVector D.baseData β)
    let h := rateLaplace D β κ hκ hκ0 θ (killingVector D β κ hκ)
    let U : (sphericalGenerator D.dimension_ge_one β D.baseData.hamiltonian D.baseData.hamiltonian_contDiff.continuous).domain :=
      ⟨F,(referenceRate_generator D.baseData β θ hθ (referenceInitialVector D.baseData β)).choose⟩
    ∃ F₀ : sphericalSobolevGraph D.dimension_ge_one β D.baseData.hamiltonian D.baseData.hamiltonian_contDiff.continuous,
      ∃ F₁ u : sphericalSobolevGraph D.dimension_ge_one β D.hamiltonian D.hamiltonian_contDiff.continuous,
        sphericalEnergyL2Map D.dimension_ge_one β D.baseData.hamiltonian D.baseData.hamiltonian_contDiff.continuous F₀=F ∧
        (F₁.val.fst=ᵐ[gibbsLaw N β D.hamiltonian] F) ∧
        (∀ ij : Fin N×Fin N,F₁.val.snd ij=ᵐ[gibbsLaw N β D.hamiltonian] F₀.val.snd ij) ∧
        sphericalEnergyL2Map D.dimension_ge_one β D.hamiltonian D.hamiltonian_contDiff.continuous u=h ∧
        (∀ᵐ x ∂gibbsLaw N β D.hamiltonian,1≤F₁.val.fst x ∧
          ‖F₁.val.fst x‖≤1+Real.exp (2*β*derivativeConstant (mixtureCoefficients D.mixture)*(N : ℝ))) ∧
        sphericalFisher D.dimension_ge_one β D.baseData.hamiltonian D.baseData.hamiltonian_contDiff.continuous F₀≤
          (θ : ℝ)*(2*Real.log 2+4*β*derivativeConstant (mixtureCoefficients D.mixture)*(N : ℝ)) ∧
        sphericalWeightedGradientSquare D.dimension_ge_one β D.hamiltonian D.hamiltonian_contDiff.continuous u F₁+
          (1/2 : ℝ)*(∫ x,Real.exp (-gibbsEnergyDifference β β D.baseData.hamiltonian D.hamiltonian x)*
            (sphericalGenerator D.dimension_ge_one β D.baseData.hamiltonian D.baseData.hamiltonian_contDiff.continuous U x)*
              (h x)^2 ∂gibbsLaw N β D.hamiltonian)+
          sphericalTiltGradientCross D.dimension_ge_one β β D.baseData.hamiltonian D.hamiltonian
            D.baseData.hamiltonian_contDiff.continuous D.hamiltonian_contDiff.continuous F₀ u+
          (∫ x,κ x*F₁.val.fst x*(h x)^2 ∂gibbsLaw N β D.hamiltonian)+
          (θ : ℝ)*(∫ x,F₁.val.fst x*(h x)^2 ∂gibbsLaw N β D.hamiltonian)≤
            ∫ x,κ x*F₁.val.fst x ∂gibbsLaw N β D.hamiltonian := by
  let F := referenceRate D.baseData β θ (referenceInitialVector D.baseData β)
  let h := rateLaplace D β κ hκ hκ0 θ (killingVector D β κ hκ)
  let U : (sphericalGenerator D.dimension_ge_one β D.baseData.hamiltonian D.baseData.hamiltonian_contDiff.continuous).domain :=
    ⟨F,(referenceRate_generator D.baseData β θ hθ (referenceInitialVector D.baseData β)).choose⟩
  obtain ⟨u,hu,_⟩ := rateLaplace_killing_formEquation D β κ hκ hκ0 K hK θ hθ
  have hvalU : u.val.fst=h := hu
  have hub : ∀ᵐ x ∂gibbsLaw N β D.hamiltonian,‖u.val.fst x‖≤(1 : ℝ≥0) := by
    rw [hvalU]
    exact (rateLaplace_killing_unit_interval D β κ hκ hκ0 K hK θ hθ).mono
      (fun _ hx => by rw [Real.norm_eq_abs,abs_of_nonneg hx.1];exact hx.2)
  obtain ⟨F₀,F₁,hF₀,hF₁,hGF₁,hcross⟩ := sphericalGenerator_square_commutator D.dimension_ge_one β β
    D.baseData.hamiltonian D.hamiltonian (D.baseData.hamiltonian_contDiff.of_le (by norm_num))
    (D.hamiltonian_contDiff.of_le (by norm_num)) U u 1 hub
  let B := derivativeConstant (mixtureCoefficients D.mixture)*(N : ℝ)
  have hB : ∀ x,OnSphere x → |fieldOfMixture D.mixture D.disorder x|≤B := by
    intro x hx
    have hn := SphericalAging.LandscapeDerivatives.sphere_norm x ((onSphere_iff_norm_sq x).mp hx)
    exact (field_regularDisorder_ball_bounds D.dimension_ge_one (mixtureCoefficients D.mixture)
      D.disorder hJ x (by rw [hn])).1
  have hb := referenceRate_bounds D.baseData β θ hθ (referenceInitialVector D.baseData β) 1
    (1+Real.exp (2*β*B)) (referenceInitialVector_bounds D.baseData β hβ B
      (by simpa only [SourceData.baseData_hamiltonian] using hB))
  have hAC := gibbsLaw_absolutelyContinuous_gibbsLaw D.dimension_ge_one β β
    D.baseData.hamiltonian D.hamiltonian D.baseData.hamiltonian_contDiff.continuous
  have hbounds : ∀ᵐ x ∂gibbsLaw N β D.hamiltonian,1≤F₁.val.fst x ∧ ‖F₁.val.fst x‖≤1+Real.exp (2*β*B) := by
    filter_upwards [hF₁,hb.filter_mono hAC.ae_le] with x hx hbx
    rw [hx]
    refine ⟨hbx.1,?_⟩
    rw [Real.norm_eq_abs,abs_of_nonneg (by linarith [hbx.1])]
    exact hbx.2
  let CF : ℝ≥0 := ⟨1+Real.exp (2*β*B),by positivity⟩
  obtain ⟨u',hu',he⟩ := rateLaplace_killing_weighted_energy D β κ hκ hκ0 K hK θ hθ F₁ CF
    (hbounds.mono (fun _ hx => hx.2)) (hbounds.mono (fun _ hx => by linarith [hx.1]))
  have heu : u'=u := sphericalEnergyL2Map_injective D.dimension_ge_one β D.hamiltonian
    (D.hamiltonian_contDiff.of_le (by norm_num)) (hu'.trans hu.symm)
  rw [heu,hcross,hvalU] at he
  obtain ⟨F₀',hF₀',_,_,_,hJF⟩ := baseJointReferenceSolution_regular_fisher D β hβ θ hθ hJ
  have heF : F₀=F₀' := sphericalEnergyL2Map_injective D.dimension_ge_one β D.baseData.hamiltonian
    (D.baseData.hamiltonian_contDiff.of_le (by norm_num)) (hF₀.trans hF₀'.symm)
  refine ⟨F₀,F₁,u,hF₀,hF₁,hGF₁,hu,?_,?_,?_⟩
  · have hC : 2*β*B=2*β*derivativeConstant (mixtureCoefficients D.mixture)*(N : ℝ) := by
      dsimp [B]
      ring
    simpa only [hC] using hbounds
  · simpa only [heF] using hJF
  · simpa only [add_assoc] using he

end SlowEquilibration.ConditionedEntrance.SmoothKilled
