-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntranceJointEnergyIntegralSum
public import SlowEquilibration.ConditionedEntranceJointSignedReducedEnergy

/-! The source weighted-gradient energy defined as a sum of coordinate
Gibbs integrals is the fibre integral of the literal joint density.
This is the final identification needed by global tilt disintegration. -/
@[expose] public section
noncomputable section
open MeasureTheory
open SlowEquilibration.SphericalModel SlowEquilibration.SphericalForm
open SphericalAging.HardSphereDynamics
open scoped NNReal BigOperators
namespace SlowEquilibration.ConditionedEntrance
open SmoothKilled
set_option autoImplicit false
set_option maxHeartbeats 400000

theorem source_joint_weighted_gradient_fibre_integral
    {N : ℕ} (hN : 1 ≤ N) (μ : FiniteMixture)
    (hnp : μ.minDegree < μ.maxDegree) (Q : ℝ) (hQ : 0 < Q) (hQ1 : Q ≤ 1)
    (α : ℝ) (hα : 0 < α) (χ : ℝ → ℝ) (hχ : ContDiff ℝ 2 χ)
    (β : ℝ) (p : SourceParameters N μ) (hp : OnSphere p.2.1)
    (F : SourceParameters N μ × Vector N → ℝ)
    (G : (Fin N × Fin N) → SourceParameters N μ × Vector N → ℝ)
    (hFsm : StronglyMeasurable F) (hGsm : ∀ ij, StronglyMeasurable (G ij))
    (F₁ u : sphericalSobolevGraph hN β
      (SourceData.atSourceParameters hN μ hnp Q hQ hQ1 α hα χ hχ p hp).hamiltonian
      (SourceData.atSourceParameters hN μ hnp Q hQ hQ1 α hα χ hχ p hp).hamiltonian_contDiff.continuous)
    (CF : ℝ≥0)
    (hFb : ∀ᵐ x ∂gibbsLaw N β
      (SourceData.atSourceParameters hN μ hnp Q hQ hQ1 α hα χ hχ p hp).hamiltonian,
      1 ≤ F₁.val.fst x ∧ ‖F₁.val.fst x‖ ≤ CF)
    (hFrep : (fun x => F (p,x)) =ᵐ[gibbsLaw N β
      (SourceData.atSourceParameters hN μ hnp Q hQ hQ1 α hα χ hχ p hp).hamiltonian]
      F₁.val.fst)
    (hGrep : ∀ ij, (fun x => G ij (p,x)) =ᵐ[gibbsLaw N β
      (SourceData.atSourceParameters hN μ hnp Q hQ hQ1 α hα χ hχ p hp).hamiltonian]
      u.val.snd ij) :
    jointGibbsWeightedGradientSquare β
      (sourceJointHamiltonian μ Q hQ hnp α χ) F G p =
      ∫ x, F (p,x)*(∑ ij : Fin N × Fin N, (G ij (p,x))^2)
        ∂gibbsLaw N β
          (SourceData.atSourceParameters hN μ hnp Q hQ hQ1 α hα χ hχ p hp).hamiltonian := by
  let D := SourceData.atSourceParameters hN μ hnp Q hQ hQ1 α hα χ hχ p hp
  let π := gibbsLaw N β D.hamiltonian
  have hi : Integrable (fun x => F (p,x)*
      (∑ ij : Fin N×Fin N, (G ij (p,x))^2)) π :=
    weighted_gradient_density_integrable_of_graph_representatives hN β
      D.hamiltonian D.hamiltonian_contDiff.continuous u F₁ CF
      (hFb.mono (fun _ hx => hx.2)) (fun x => F (p,x))
      (fun ij x => G ij (p,x)) hFrep hGrep
  have hF0 : ∀ᵐ x ∂π, 0 ≤ F (p,x) := by
    filter_upwards [hFrep,hFb] with x hf hb
    rw [hf]
    linarith [hb.1]
  have hFm : Measurable (fun x => F (p,x)) :=
    (hFsm.comp_measurable (by fun_prop)).measurable
  have hGm (ij : Fin N × Fin N) : Measurable (fun x => G ij (p,x)) :=
    ((hGsm ij).comp_measurable (by fun_prop)).measurable
  have hsum := weighted_gradient_density_integral_eq_sum π
    (fun x => F (p,x)) (fun ij x => G ij (p,x)) hFm hGm hF0 hi
  change (∑ ij : Fin N×Fin N, ∫ x,
    F (p,x)*(G ij (p,x))^2 ∂π) = _
  exact hsum.symm

end SlowEquilibration.ConditionedEntrance
