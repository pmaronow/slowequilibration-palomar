-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntranceSmoothKilledGeneralIntegralForm
public import SlowEquilibration.ConditionedEntranceSmoothKilledGeneralReferenceFisher
public import SlowEquilibration.SphericalGeneratorFirstCommutator

/-! The first (linear) reference test of any actual C² killed field,
including the proper pure source cutoff. The original reference is independent
of the field and needs no nonpure-mixture witness. The physical
resolvent: its completed Dirichlet term is replaced by the exact
Gibbs-change commutator. The reference generator source is retained
as an L² identity for the subsequent scalar source-pairing formula. -/
@[expose] public section
noncomputable section
open MeasureTheory
open scoped NNReal ENNReal InnerProductSpace
namespace SlowEquilibration.ConditionedEntrance.SmoothKilledGeneral
open SphericalAging.HardSphereDynamics SphericalModel SphericalForm KilledOperator
set_option autoImplicit false
set_option maxHeartbeats 500000
variable {N : ℕ}

theorem rateLaplace_reference_first_test_identity
    (D D₀ : FieldData N) (β : ℝ)
    (κ : Vector N→ℝ) (hκ : Continuous κ) (hκ0 : ∀ x, 0≤κ x)
    (K : ℝ≥0) (hK : ∀ x, ‖κ x‖≤K)
    (θ : ℝ≥0) (hθ : 0<θ) :
    let F := referenceRate D₀ β θ (referenceInitialVector D₀ β)
    let h := rateLaplace D β κ hκ hκ0 θ (killingVector D β κ hκ)
    let H₀ := D₀.hamiltonian
    let H := D.hamiltonian
    let π := gibbsLaw N β H
    ∃ U : (sphericalGenerator D.dimension_ge_one β H₀
      D₀.hamiltonian_contDiff.continuous).domain,
    ∃ F₀ : sphericalSobolevGraph D.dimension_ge_one β H₀
      D₀.hamiltonian_contDiff.continuous,
    ∃ F₁ u : sphericalSobolevGraph D.dimension_ge_one β H
      D.hamiltonian_contDiff.continuous,
      U.val=F ∧
      sphericalGenerator D.dimension_ge_one β H₀
        D₀.hamiltonian_contDiff.continuous U=
          (θ : ℝ) • (referenceInitialVector D₀ β-F) ∧
      sphericalEnergyL2Map D.dimension_ge_one β H₀
        D₀.hamiltonian_contDiff.continuous F₀=F ∧
      F₁.val.fst=ᵐ[π] F ∧
      sphericalEnergyL2Map D.dimension_ge_one β H
        D.hamiltonian_contDiff.continuous u=h ∧
      (∫ x, Real.exp (-gibbsEnergyDifference β β H₀ H x)*
          (sphericalGenerator D.dimension_ge_one β H₀
            D₀.hamiltonian_contDiff.continuous U x)*u.val.fst x ∂π)+
        sphericalTiltGradientPairing D.dimension_ge_one β β H₀ H
          D₀.hamiltonian_contDiff.continuous
          D.hamiltonian_contDiff.continuous F₀ u+
        (∫ x, ((θ : ℝ)+κ x)*u.val.fst x*F₁.val.fst x ∂π)=
        ∫ x, κ x*F₁.val.fst x ∂π := by
  dsimp only
  let F := referenceRate D₀ β θ (referenceInitialVector D₀ β)
  let h := rateLaplace D β κ hκ hκ0 θ (killingVector D β κ hκ)
  let H₀ := D₀.hamiltonian
  let H := D.hamiltonian
  let π := gibbsLaw N β H
  obtain ⟨hd,hgen⟩ :=
    referenceRate_generator D₀ β θ hθ
      (referenceInitialVector D₀ β)
  let U : (sphericalGenerator D.dimension_ge_one β H₀
    D₀.hamiltonian_contDiff.continuous).domain := ⟨F,hd⟩
  obtain ⟨u,hu,hform⟩ :=
    rateLaplace_continuousForcing_integral_form D β κ hκ hκ0 K hK θ hθ κ hκ
  obtain ⟨F₀,F₁,hF₀,hF₁,_hGF₁,hcomm⟩ :=
    sphericalGenerator_first_commutator D.dimension_ge_one β β H₀ H
      (D₀.hamiltonian_contDiff.of_le (by norm_num))
      (D.hamiltonian_contDiff.of_le (by norm_num)) U u
  have hDir : sphericalCompletedDirichlet D.dimension_ge_one β H
      D.hamiltonian_contDiff.continuous u F₁ =
      sphericalCompletedDirichlet D.dimension_ge_one β H
        D.hamiltonian_contDiff.continuous F₁ u := by
    unfold sphericalCompletedDirichlet
    exact real_inner_comm _ _
  have htest := hform F₁
  rw [hDir,hcomm] at htest
  have hgen' : sphericalGenerator D.dimension_ge_one β H₀
      D₀.hamiltonian_contDiff.continuous U=
      (θ : ℝ) • (referenceInitialVector D₀ β-F) := hgen
  refine ⟨U,F₀,F₁,u,rfl,hgen',hF₀,hF₁,hu,?_⟩
  linarith only [htest]

end SlowEquilibration.ConditionedEntrance.SmoothKilledGeneral
