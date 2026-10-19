-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntranceSmoothKilledFisherEnergy

/-! A true finite bound on the physical source weighted gradient square,
for subsequent disorder/axis integration. -/
@[expose] public section
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal InnerProductSpace
namespace SlowEquilibration.ConditionedEntrance.SmoothKilled
open SphericalModel SphericalForm
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
variable {N : ℕ}

theorem rateLaplace_killing_gradient_bound (D : SourceData N) (β : ℝ) (κ : Vector N→ℝ)
    (hκ : Continuous κ) (hκ0 : ∀ x,0 ≤ κ x) (K : ℝ≥0) (hK : ∀ x,‖κ x‖ ≤ K)
    (θ : ℝ≥0) (hθ : 0<θ)
    (F : sphericalSobolevGraph D.dimension_ge_one β D.hamiltonian D.hamiltonian_contDiff.continuous)
    (CF : ℝ≥0) (hF : ∀ᵐ x ∂gibbsLaw N β D.hamiltonian,‖F.val.fst x‖ ≤ CF)
    (hFlo : ∀ᵐ x ∂gibbsLaw N β D.hamiltonian,1 ≤ F.val.fst x) :
    let h := rateLaplace D β κ hκ hκ0 θ (killingVector D β κ hκ)
    ∃ u : sphericalSobolevGraph D.dimension_ge_one β D.hamiltonian D.hamiltonian_contDiff.continuous,
      sphericalEnergyL2Map D.dimension_ge_one β D.hamiltonian D.hamiltonian_contDiff.continuous u=h ∧
      0 ≤ sphericalWeightedGradientSquare D.dimension_ge_one β D.hamiltonian D.hamiltonian_contDiff.continuous u F ∧
      sphericalWeightedGradientSquare D.dimension_ge_one β D.hamiltonian D.hamiltonian_contDiff.continuous u F ≤
        2*(∫ x,κ x*F.val.fst x ∂gibbsLaw N β D.hamiltonian)+
          sphericalFisher D.dimension_ge_one β D.hamiltonian D.hamiltonian_contDiff.continuous F := by
  obtain ⟨u,hu,he⟩ := rateLaplace_killing_fisher_energy D β κ hκ hκ0 K hK θ hθ F CF hF hFlo
  have hF0 : ∀ᵐ x ∂gibbsLaw N β D.hamiltonian,0 ≤ F.val.fst x := hFlo.mono (fun _ hx => by linarith)
  have hk : 0 ≤ ∫ x,κ x*F.val.fst x*
      (rateLaplace D β κ hκ hκ0 θ (killingVector D β κ hκ) x)^2 ∂gibbsLaw N β D.hamiltonian :=
    integral_nonneg_of_ae (hF0.mono (fun x hx => mul_nonneg (mul_nonneg (hκ0 x) hx) (sq_nonneg _)))
  have ha : 0 ≤ (θ : ℝ)*(∫ x,F.val.fst x*
      (rateLaplace D β κ hκ hκ0 θ (killingVector D β κ hκ) x)^2 ∂gibbsLaw N β D.hamiltonian) :=
    mul_nonneg θ.coe_nonneg (integral_nonneg_of_ae (hF0.mono (fun x hx => mul_nonneg hx (sq_nonneg _))))
  refine ⟨u,hu,sphericalWeightedGradientSquare_nonnegative D.dimension_ge_one β D.hamiltonian
    D.hamiltonian_contDiff.continuous u F hF0,?_⟩
  linarith

end SlowEquilibration.ConditionedEntrance.SmoothKilled
