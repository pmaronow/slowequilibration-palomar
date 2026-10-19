-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntranceJointEnergyIntegralSum
public import SlowEquilibration.ConditionedEntrancePureJointSignedReducedEnergy

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
open SmoothKilledGeneral
set_option autoImplicit false
set_option maxHeartbeats 400000

set_option linter.unusedVariables false in
theorem pure_joint_weighted_gradient_fibre_integral
    {N : ℕ} (hN : 1 ≤ N) (d : ℕ) (hd : 2 ≤ d) (c : ℝ) (hc : 0 < c) (Q : ℝ)
    (α : ℝ) (hα : 0 < α) (χ : ℝ → ℝ) (hχ : ContDiff ℝ 2 χ)
    (β : ℝ) (p : SourceParameters N (FiniteMixture.pure d hd c hc)) (hp : OnSphere p.2.1)
    (F : SourceParameters N (FiniteMixture.pure d hd c hc) × Vector N → ℝ)
    (G : (Fin N × Fin N) → SourceParameters N (FiniteMixture.pure d hd c hc) × Vector N → ℝ)
    (hFsm : StronglyMeasurable F) (hGsm : ∀ ij, StronglyMeasurable (G ij))
    (F₁ u : sphericalSobolevGraph hN β
      (FieldData.ofPure hN d hd c hc Q p.1 p.2.1 p.2.2.1 α χ hχ).hamiltonian
      (FieldData.ofPure hN d hd c hc Q p.1 p.2.1 p.2.2.1 α χ hχ).hamiltonian_contDiff.continuous)
    (CF : ℝ≥0)
    (hFb : ∀ᵐ x ∂gibbsLaw N β
      (FieldData.ofPure hN d hd c hc Q p.1 p.2.1 p.2.2.1 α χ hχ).hamiltonian,
      1 ≤ F₁.val.fst x ∧ ‖F₁.val.fst x‖ ≤ CF)
    (hFrep : (fun x => F (p,x)) =ᵐ[gibbsLaw N β
      (FieldData.ofPure hN d hd c hc Q p.1 p.2.1 p.2.2.1 α χ hχ).hamiltonian]
      F₁.val.fst)
    (hGrep : ∀ ij, (fun x => G ij (p,x)) =ᵐ[gibbsLaw N β
      (FieldData.ofPure hN d hd c hc Q p.1 p.2.1 p.2.2.1 α χ hχ).hamiltonian]
      u.val.snd ij) :
    jointGibbsWeightedGradientSquare β
      (pureSourceJointHamiltonian d hd c hc Q α χ) F G p =
      ∫ x, F (p,x)*(∑ ij : Fin N × Fin N, (G ij (p,x))^2)
        ∂gibbsLaw N β
          (FieldData.ofPure hN d hd c hc Q p.1 p.2.1 p.2.2.1 α χ hχ).hamiltonian := by
  let D := FieldData.ofPure hN d hd c hc Q p.1 p.2.1 p.2.2.1 α χ hχ
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
  have hHp : (fun x => pureSourceJointHamiltonian d hd c hc Q α χ (p,x)) =
      D.hamiltonian := by
    rw [FieldData.ofPure_hamiltonian]
    rfl
  unfold jointGibbsWeightedGradientSquare
  simp only [hHp]
  exact hsum.symm

end SlowEquilibration.ConditionedEntrance
