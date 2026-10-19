-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntranceSmoothKilledWeightedEnergy
public import SlowEquilibration.SphericalWeightedCrossAbsorption

/-! Actual killed-resolvent energy after direct Fisher absorption of the
literal completed-gradient cross term. -/
@[expose] public section
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal InnerProductSpace
namespace SlowEquilibration.ConditionedEntrance.SmoothKilled
open SphericalModel SphericalForm KilledOperator
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
variable {N : ℕ}

theorem rateLaplace_killing_fisher_energy (D : SourceData N) (β : ℝ) (κ : Vector N→ℝ)
    (hκ : Continuous κ) (hκ0 : ∀ x,0≤κ x) (K : ℝ≥0) (hK : ∀ x,‖κ x‖≤K)
    (θ : ℝ≥0) (hθ : 0<θ)
    (F : sphericalSobolevGraph D.dimension_ge_one β D.hamiltonian D.hamiltonian_contDiff.continuous)
    (CF : ℝ≥0) (hF : ∀ᵐ x ∂gibbsLaw N β D.hamiltonian,‖F.val.fst x‖≤CF)
    (hFlo : ∀ᵐ x ∂gibbsLaw N β D.hamiltonian,1≤F.val.fst x) :
    let h := rateLaplace D β κ hκ hκ0 θ (killingVector D β κ hκ)
    ∃ u : sphericalSobolevGraph D.dimension_ge_one β D.hamiltonian D.hamiltonian_contDiff.continuous,
      sphericalEnergyL2Map D.dimension_ge_one β D.hamiltonian D.hamiltonian_contDiff.continuous u=h ∧
      sphericalWeightedGradientSquare D.dimension_ge_one β D.hamiltonian D.hamiltonian_contDiff.continuous u F/2+
        (∫ x,κ x*F.val.fst x*(h x)^2 ∂gibbsLaw N β D.hamiltonian)+
        (θ : ℝ)*(∫ x,F.val.fst x*(h x)^2 ∂gibbsLaw N β D.hamiltonian) ≤
        (∫ x,κ x*F.val.fst x ∂gibbsLaw N β D.hamiltonian)+
        sphericalFisher D.dimension_ge_one β D.hamiltonian D.hamiltonian_contDiff.continuous F/2 := by
  let h := rateLaplace D β κ hκ hκ0 θ (killingVector D β κ hκ)
  have hF0 : ∀ᵐ x ∂gibbsLaw N β D.hamiltonian,0≤F.val.fst x :=
    hFlo.mono (fun _ hx => by linarith)
  obtain ⟨u,hu,he⟩ := rateLaplace_killing_weighted_energy D β κ hκ hκ0 K hK θ hθ F CF hF hF0
  have hu' : u.val.fst=h := hu
  have hub : ∀ᵐ x ∂gibbsLaw N β D.hamiltonian,‖u.val.fst x‖≤(1 : ℝ≥0) := by
    rw [hu']
    exact (rateLaplace_killing_unit_interval D β κ hκ hκ0 K hK θ hθ).mono
      (fun _ hx => by rw [Real.norm_eq_abs,abs_of_nonneg hx.1];exact hx.2)
  have hc := sphericalWeightedGradientCross_absorption D.dimension_ge_one β D.hamiltonian
    D.hamiltonian_contDiff.continuous u F CF hub hF hFlo
  refine ⟨u,hu,?_⟩
  have hl := (abs_le.mp hc).1
  linarith

end SlowEquilibration.ConditionedEntrance.SmoothKilled
