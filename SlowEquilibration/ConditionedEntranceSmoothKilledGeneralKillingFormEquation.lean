-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntranceSmoothKilledGeneralFormEquation
public import SlowEquilibration.ConditionedEntranceSmoothKilledGeneralBounds
public import SlowEquilibration.SphericalPerturbedFormEquation

/-! The actual source smooth killed physical resolvent solves the full
completed spherical Gibbs weak equation, at every positive Laplace rate. -/
@[expose] public section
noncomputable section
open MeasureTheory
open scoped NNReal ENNReal InnerProductSpace
namespace SlowEquilibration.ConditionedEntrance.SmoothKilledGeneral
open SphericalAging.HardSphereDynamics SphericalModel SphericalForm
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
variable {N : ℕ}

/-- No form equation is supplied: it follows from the actual physical
resolvent and the actual full-domain spherical generator theorem. -/
theorem rateLaplace_killing_formEquation (D : FieldData N) (β : ℝ) (κ : Vector N → ℝ)
    (hκ : Continuous κ) (hκ0 : ∀ x,0 ≤ κ x) (K : ℝ≥0) (hK : ∀ x,‖κ x‖ ≤ K)
    (θ : ℝ≥0) (hθ : 0 < θ) :
    let h := rateLaplace D β κ hκ hκ0 θ (killingVector D β κ hκ)
    ∃ u : sphericalSobolevGraph D.dimension_ge_one β D.hamiltonian D.hamiltonian_contDiff.continuous,
      sphericalEnergyL2Map D.dimension_ge_one β D.hamiltonian D.hamiltonian_contDiff.continuous u=h ∧
      ∀ v : sphericalSobolevGraph D.dimension_ge_one β D.hamiltonian D.hamiltonian_contDiff.continuous,
        sphericalCompletedDirichlet D.dimension_ge_one β D.hamiltonian D.hamiltonian_contDiff.continuous u v+
          inner ℝ (killingMultiplication D β κ hκ K hK h)
            (sphericalEnergyL2Map D.dimension_ge_one β D.hamiltonian D.hamiltonian_contDiff.continuous v)+
          (θ : ℝ)*inner ℝ h
            (sphericalEnergyL2Map D.dimension_ge_one β D.hamiltonian D.hamiltonian_contDiff.continuous v)=
          inner ℝ (killingVector D β κ hκ)
            (sphericalEnergyL2Map D.dimension_ge_one β D.hamiltonian D.hamiltonian_contDiff.continuous v) :=
  sphericalGenerator_boundedPerturbation_form D.dimension_ge_one β D.hamiltonian
    D.hamiltonian_contDiff.continuous (killingMultiplication D β κ hκ K hK)
    ⟨rateLaplace D β κ hκ hκ0 θ (killingVector D β κ hκ),
      rateLaplace_mem_domain D β κ hκ hκ0 K hK θ hθ (killingVector D β κ hκ)⟩
    (θ : ℝ) (killingVector D β κ hκ)
    (rateLaplace_resolvent D β κ hκ hκ0 K hK θ hθ (killingVector D β κ hκ))

end SlowEquilibration.ConditionedEntrance.SmoothKilledGeneral
