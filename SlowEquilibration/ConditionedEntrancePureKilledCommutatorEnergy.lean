-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SphericalGeneratorSquareCommutator
public import SlowEquilibration.ConditionedEntranceSmoothKilledGeneralReferenceFisher
public import SlowEquilibration.ConditionedEntrancePureKilledWeightedEnergy

/-! The actual original-base entropy reference and literal physical
killed C² field, including every proper-pure cutoff solve the square-test weighted commutator energy identity.
Neither a tested equation nor a cross-term/Fisher estimate is supplied. -/
@[expose] public section
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal InnerProductSpace
namespace SlowEquilibration.ConditionedEntrance.SmoothKilledGeneral
open SphericalModel SphericalForm KilledOperator
open SphericalAging.HardSphereDynamics
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
variable {N : ℕ}

theorem rateLaplace_reference_commutator_energy (D D₀ : FieldData N) (β : ℝ) (hβ : 0≤β)
    (κ : Vector N→ℝ) (hκ : Continuous κ) (hκ0 : ∀ x,0≤κ x) (K : ℝ≥0) (hK : ∀ x,‖κ x‖≤K)
    (θ : ℝ≥0) (hθ : 0<θ) (B : ℝ) (hB0 : 0 ≤ B)
    (hB : ∀ x, OnSphere x → |D₀.hamiltonian x| ≤ B) :
    let F := referenceRate D₀ β θ (referenceInitialVector D₀ β)
    let h := rateLaplace D β κ hκ hκ0 θ (killingVector D β κ hκ)
    let U : (sphericalGenerator D.dimension_ge_one β D₀.hamiltonian D₀.hamiltonian_contDiff.continuous).domain :=
      ⟨F,(referenceRate_generator D₀ β θ hθ (referenceInitialVector D₀ β)).choose⟩
    ∃ F₀ : sphericalSobolevGraph D.dimension_ge_one β D₀.hamiltonian D₀.hamiltonian_contDiff.continuous,
      ∃ F₁ u : sphericalSobolevGraph D.dimension_ge_one β D.hamiltonian D.hamiltonian_contDiff.continuous,
        sphericalEnergyL2Map D.dimension_ge_one β D₀.hamiltonian D₀.hamiltonian_contDiff.continuous F₀=F ∧
        (F₁.val.fst=ᵐ[gibbsLaw N β D.hamiltonian] F) ∧
        (∀ ij : Fin N×Fin N,F₁.val.snd ij=ᵐ[gibbsLaw N β D.hamiltonian] F₀.val.snd ij) ∧
        sphericalEnergyL2Map D.dimension_ge_one β D.hamiltonian D.hamiltonian_contDiff.continuous u=h ∧
        (∀ᵐ x ∂gibbsLaw N β D.hamiltonian,1≤F₁.val.fst x ∧
          ‖F₁.val.fst x‖≤1+Real.exp (2*β*B)) ∧
        sphericalFisher D.dimension_ge_one β D₀.hamiltonian D₀.hamiltonian_contDiff.continuous F₀≤
          (θ : ℝ)*(2*Real.log 2+4*β*B) ∧
        sphericalWeightedGradientSquare D.dimension_ge_one β D.hamiltonian D.hamiltonian_contDiff.continuous u F₁+
          (1/2 : ℝ)*(∫ x,Real.exp (-gibbsEnergyDifference β β D₀.hamiltonian D.hamiltonian x)*
            (sphericalGenerator D.dimension_ge_one β D₀.hamiltonian D₀.hamiltonian_contDiff.continuous U x)*
              (h x)^2 ∂gibbsLaw N β D.hamiltonian)+
          sphericalTiltGradientCross D.dimension_ge_one β β D₀.hamiltonian D.hamiltonian
            D₀.hamiltonian_contDiff.continuous D.hamiltonian_contDiff.continuous F₀ u+
          (∫ x,κ x*F₁.val.fst x*(h x)^2 ∂gibbsLaw N β D.hamiltonian)+
          (θ : ℝ)*(∫ x,F₁.val.fst x*(h x)^2 ∂gibbsLaw N β D.hamiltonian)≤
            ∫ x,κ x*F₁.val.fst x ∂gibbsLaw N β D.hamiltonian := by
  let F := referenceRate D₀ β θ (referenceInitialVector D₀ β)
  let h := rateLaplace D β κ hκ hκ0 θ (killingVector D β κ hκ)
  let U : (sphericalGenerator D.dimension_ge_one β D₀.hamiltonian D₀.hamiltonian_contDiff.continuous).domain :=
    ⟨F,(referenceRate_generator D₀ β θ hθ (referenceInitialVector D₀ β)).choose⟩
  obtain ⟨u,hu,_⟩ := rateLaplace_killing_formEquation D β κ hκ hκ0 K hK θ hθ
  have hvalU : u.val.fst=h := hu
  have hub : ∀ᵐ x ∂gibbsLaw N β D.hamiltonian,‖u.val.fst x‖≤(1 : ℝ≥0) := by
    rw [hvalU]
    exact (rateLaplace_killing_unit_interval D β κ hκ hκ0 K hK θ hθ).mono
      (fun _ hx => by rw [Real.norm_eq_abs,abs_of_nonneg hx.1];exact hx.2)
  obtain ⟨F₀,F₁,hF₀,hF₁,hGF₁,hcross⟩ := sphericalGenerator_square_commutator D.dimension_ge_one β β
    D₀.hamiltonian D.hamiltonian (D₀.hamiltonian_contDiff.of_le (by norm_num))
    (D.hamiltonian_contDiff.of_le (by norm_num)) U u 1 hub
  have hb := referenceRate_bounds D₀ β θ hθ (referenceInitialVector D₀ β) 1
    (1+Real.exp (2*β*B)) (referenceInitialVector_bounds D₀ β hβ B
      hB)
  have hAC := gibbsLaw_absolutelyContinuous_gibbsLaw D.dimension_ge_one β β
    D₀.hamiltonian D.hamiltonian D₀.hamiltonian_contDiff.continuous
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
  obtain ⟨F₀',hF₀',_,hJF⟩ := referenceRate_initial_fisher_bound D₀ β hβ B hB0 hB θ hθ
  have heF : F₀=F₀' := sphericalEnergyL2Map_injective D.dimension_ge_one β D₀.hamiltonian
    (D₀.hamiltonian_contDiff.of_le (by norm_num)) (hF₀.trans hF₀'.symm)
  refine ⟨F₀,F₁,u,hF₀,hF₁,hGF₁,hu,?_,?_,?_⟩
  · exact hbounds
  · simpa only [heF] using hJF
  · simpa only [add_assoc] using he

end SlowEquilibration.ConditionedEntrance.SmoothKilledGeneral
