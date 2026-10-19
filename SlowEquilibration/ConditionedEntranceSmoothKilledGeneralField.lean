-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.ConditionedEntranceSmoothKilledPhysical
public import SlowEquilibration.ConditionedEntrancePureSmoothCutoff

/-! A source-independent smooth Hamiltonian for the physical killed diffusion.
The approximation data concerns the actual Hamiltonian and finite tensor fields;
Gibbs stationarity is a theorem, not part of the data. The proper-pure constructor
uses the explicit two-atom posterior correction and its proved approximants. -/
@[expose] public section
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace
namespace SlowEquilibration.ConditionedEntrance.SmoothKilledGeneral
open SphericalModel SphericalForm SphericalGaussianJet SphericalDynamics SphericalReversibility
open SphericalAging HardSphereDynamics SphericalSmoothTensorStationarity
open SphericalAtomSmoothCutoffApproximation
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

structure FieldData (N : ℕ) where
  dimension_ge_one : 1 ≤ N
  hamiltonian : Vector N → ℝ
  hamiltonian_contDiff : ContDiff ℝ 2 hamiltonian
  approximants :
    ∃ (ν : ℕ → FiniteMixture) (K : (j : ℕ) → Disorder N (ν j).maxDegree)
      (M : ℝ) (δ : ℕ → ℝ),
      (∀ j x, OnSphere x → |fieldOfMixture (ν j) (K j) x| ≤ M) ∧
      (∀ x, OnSphere x → Tendsto (fun j => fieldOfMixture (ν j) (K j) x) atTop
        (𝓝 (hamiltonian x))) ∧
      (∀ j, 0 ≤ δ j) ∧
      (∀ j x, OnSphere x →
        ‖gradient (fieldOfMixture (ν j) (K j)) x-gradient hamiltonian x‖ ≤ δ j) ∧
      Tendsto δ atTop (𝓝 0)

variable {N : ℕ}

def FieldData.transitionKernel (D : FieldData N) (β : ℝ) (t : ℝ≥0) :
    Kernel (Vector N) (Vector N) :=
  smoothTransitionKernel D.hamiltonian D.hamiltonian_contDiff β t

instance FieldData.transitionKernel_markov (D : FieldData N) (β : ℝ) (t : ℝ≥0) :
    IsMarkovKernel (D.transitionKernel β t) := by
  unfold FieldData.transitionKernel
  infer_instance

theorem FieldData.stationary (D : FieldData N) (β : ℝ) (t : ℝ≥0) :
    D.transitionKernel β t ∘ₘ gibbsLaw N β D.hamiltonian =
      gibbsLaw N β D.hamiltonian := by
  obtain ⟨ν,K,M,δ,hM,hfield,hδ,hgrad,hlim⟩ := D.approximants
  exact smoothTransitionKernel_gibbs_invariant D.dimension_ge_one _ _ ν K M
    hM hfield δ hδ hgrad hlim β t

/-- The actual proper-pure source cutoff is represented by the finite
two-atom correction of the original sampled field. -/
def FieldData.ofPure (hN : 1 ≤ N) (p : ℕ) (hp : 2 ≤ p)
    (c : ℝ) (hc : 0 < c) (Q : ℝ)
    (J : Disorder N (FiniteMixture.pure p hp c hc).maxDegree)
    (u : Vector N) (e α : ℝ) (χ : ℝ → ℝ) (hχ : ContDiff ℝ 2 χ) : FieldData N := by
  let μ := FiniteMixture.pure p hp c hc
  let G := surfaceGradient (field (centerCoefficients (mixtureCoefficients μ) Q) J) u
  let a := pureSourceCorrectionAtom p hp c hc Q J u e
  let v₁ : Vector N := (((N : ℝ)*α)⁻¹) • u
  let v₂ : Vector N := (((N : ℝ)*α)⁻¹) • G
  let H := atomSmoothCutoffField μ J a v₁ v₂ χ
  let hH := atomSmoothCutoffField_contDiff hN hp μ J a v₁ v₂ χ hχ
  refine { dimension_ge_one := hN, hamiltonian := H,
           hamiltonian_contDiff := hH, approximants := ?_ }
  exact exists_actual_tensor_approximants hN hp μ J
    (pureMixture_maxDegree p hp c hc).le a v₁ v₂ χ hχ

theorem FieldData.ofPure_hamiltonian (hN : 1 ≤ N) (p : ℕ) (hp : 2 ≤ p)
    (c : ℝ) (hc : 0 < c) (Q : ℝ)
    (J : Disorder N (FiniteMixture.pure p hp c hc).maxDegree)
    (u : Vector N) (e α : ℝ) (χ : ℝ → ℝ) (hχ : ContDiff ℝ 2 χ) :
    (FieldData.ofPure hN p hp c hc Q J u e α χ hχ).hamiltonian =
      pureSourceSmoothCutoffField p hp c hc Q J u e α χ := by
  symm
  exact pureSourceSmoothCutoffField_eq_atom p hp c hc Q J u e α χ

end SlowEquilibration.ConditionedEntrance.SmoothKilledGeneral
