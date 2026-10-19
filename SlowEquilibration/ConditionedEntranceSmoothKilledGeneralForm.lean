-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntranceSmoothKilledFormEquation

/-! Full actual physical killed-resolvent form equation for every L2
forcing, derived from the actual source operator inverse. -/
@[expose] public section
noncomputable section
open MeasureTheory
open scoped NNReal ENNReal InnerProductSpace
namespace SlowEquilibration.ConditionedEntrance.SmoothKilled
open SphericalModel SphericalForm
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
variable {N : ℕ}

theorem rateLaplace_formEquation (D : SourceData N) (β : ℝ) (κ : Vector N→ℝ)
    (hκ : Continuous κ) (hκ0 : ∀ x,0≤κ x) (K : ℝ≥0) (hK : ∀ x,‖κ x‖≤K)
    (θ : ℝ≥0) (hθ : 0<θ) (f : Lp ℝ 2 (gibbsLaw N β D.hamiltonian)) :
    let h := rateLaplace D β κ hκ hκ0 θ f
    ∃ u : sphericalSobolevGraph D.dimension_ge_one β D.hamiltonian D.hamiltonian_contDiff.continuous,
      sphericalEnergyL2Map D.dimension_ge_one β D.hamiltonian D.hamiltonian_contDiff.continuous u=h ∧
      ∀ v : sphericalSobolevGraph D.dimension_ge_one β D.hamiltonian D.hamiltonian_contDiff.continuous,
        sphericalCompletedDirichlet D.dimension_ge_one β D.hamiltonian D.hamiltonian_contDiff.continuous u v+
          inner ℝ (killingMultiplication D β κ hκ K hK h) v.val.fst+
          (θ : ℝ)*inner ℝ h v.val.fst=inner ℝ f v.val.fst :=
  sphericalGenerator_boundedPerturbation_form D.dimension_ge_one β D.hamiltonian
    D.hamiltonian_contDiff.continuous (killingMultiplication D β κ hκ K hK)
    ⟨rateLaplace D β κ hκ hκ0 θ f,rateLaplace_mem_domain D β κ hκ hκ0 K hK θ hθ f⟩
    (θ : ℝ) f (rateLaplace_resolvent D β κ hκ hκ0 K hK θ hθ f)

end SlowEquilibration.ConditionedEntrance.SmoothKilled
