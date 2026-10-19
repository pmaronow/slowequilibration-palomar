module
-- SPDX-License-Identifier: Apache-2.0

public import SlowEquilibration.SphericalOperator
public import SlowEquilibration.CompactEigenbasis

@[expose] public section

namespace SlowEquilibration.SphericalForm

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 500000

open MeasureTheory Filter Set
open SphericalModel
open SphericalAging.HardSphereDynamics
open SphericalAging.SphericalIntegrationByParts
open scoped BigOperators InnerProductSpace Topology ContDiff

@[simp] theorem lieDerivative_const {N : ℕ} (A : Operator N) (c : ℝ) :
    lieDerivative A (fun _ : Vector N => c) = fun _ => 0 := by
  funext x
  simp [lieDerivative]

@[simp] theorem rotationGenerator_const (N : ℕ) (β : ℝ) (H : Vector N → ℝ) (c : ℝ) :
    rotationGenerator N β H (fun _ => c) = fun _ => 0 := by
  funext x
  simp [rotationGenerator, rotationLaplacian]

/-- Actual constants in the actual spherical Gibbs L² space. -/
def gibbsConstant {N : ℕ} (hN : 1 ≤ N) (β : ℝ) (H : Vector N → ℝ)
    (hH : Continuous H) (c : ℝ) : Lp ℝ 2 (gibbsLaw N β H) :=
  gibbsToL2 hN β H hH (fun _ => c) continuous_const

theorem gibbsConstant_norm_sq {N : ℕ} (hN : 1 ≤ N) (β : ℝ)
    (H : Vector N → ℝ) (hH : Continuous H) (c : ℝ) :
    ‖gibbsConstant hN β H hH c‖ ^ 2 = c ^ 2 := by
  let := gibbsLaw_probability hN β hH
  rw [← real_inner_self_eq_norm_sq, gibbsConstant, gibbsToL2_inner]
  simp only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one,
    smul_eq_mul, one_mul, pow_two]

theorem gibbsConstant_one_norm {N : ℕ} (hN : 1 ≤ N) (β : ℝ)
    (H : Vector N → ℝ) (hH : Continuous H) : ‖gibbsConstant hN β H hH 1‖ = 1 := by
  have hs := gibbsConstant_norm_sq hN β H hH 1
  nlinarith [norm_nonneg (gibbsConstant hN β H hH 1)]

/-- Constants are genuine resolvent eigenvectors of eigenvalue one. -/
theorem sphericalL2Resolvent_constant {N : ℕ} (hN : 1 ≤ N) (β : ℝ)
    (H : Vector N → ℝ) (hH : ContDiff ℝ 1 H) (c : ℝ) :
    sphericalL2Resolvent hN β H hH.continuous (gibbsConstant hN β H hH.continuous c) =
      gibbsConstant hN β H hH.continuous c := by
  let g : smoothCore N := ⟨fun _ => c, by change ContDiff ℝ ∞ (fun _ : Vector N => c); exact contDiff_const⟩
  have hf : smoothResolventForcing hN β H hH g = gibbsConstant hN β H hH.continuous c := by
    unfold smoothResolventForcing gibbsConstant
    apply gibbsToL2_congr
    apply ae_of_all
    intro x
    change c - rotationGenerator N β H (fun _ => c) x = c
    rw [rotationGenerator_const]
    simp
  have hr := sphericalL2Resolvent_smoothForcing hN β H hH g
  rw [hf] at hr
  exact hr

/-- Every true nonzero resolvent eigenvector has eigenvalue in `(0,1]`. -/
theorem sphericalResolvent_eigenvalue_bounds {N : ℕ} (hN : 1 ≤ N) (β : ℝ)
    (H : Vector N → ℝ) (hH : Continuous H) (μ : ℝ) (f : Lp ℝ 2 (gibbsLaw N β H))
    (hf : f ≠ 0) (he : sphericalL2Resolvent hN β H hH f = μ • f) : 0 < μ ∧ μ ≤ 1 :=
  CompactEigenbasis.eigenvalue_bounds (sphericalL2Resolvent hN β H hH)
    (sphericalL2Resolvent_positive hN β H hH) (sphericalL2Resolvent_norm_le hN β H hH) μ f hf he

/-- An actual resolvent eigenvector is in the actual unbounded generator
domain and has the correct actual generator eigenvalue `μ⁻¹−1`. -/
theorem sphericalGenerator_of_resolvent_eigenvector {N : ℕ} (hN : 1 ≤ N) (β : ℝ)
    (H : Vector N → ℝ) (hH : Continuous H) (μ : ℝ) (f : Lp ℝ 2 (gibbsLaw N β H))
    (hf : f ≠ 0) (he : sphericalL2Resolvent hN β H hH f = μ • f) :
    ∃ hdom : f ∈ (sphericalGenerator hN β H hH).domain,
      sphericalGenerator hN β H hH ⟨f, hdom⟩ = (μ⁻¹ - 1) • f := by
  have hμ : μ ≠ 0 := (sphericalResolvent_eigenvalue_bounds hN β H hH μ f hf he).1.ne'
  let k := μ⁻¹ • f
  have hr : sphericalL2Resolvent hN β H hH k = f := by
    rw [map_smul, he, smul_smul, inv_mul_cancel₀ hμ, one_smul]
  refine ⟨⟨k, hr⟩, ?_⟩
  have hz : (⟨f, ⟨k, hr⟩⟩ : (sphericalGenerator hN β H hH).domain) =
      ⟨sphericalL2Resolvent hN β H hH k, ⟨k, rfl⟩⟩ := Subtype.ext hr.symm
  rw [hz, sphericalGenerator_apply_resolvent, hr]
  dsimp [k]
  module

/-- Every true resolvent eigenvector is an actual energy function satisfying
the weak eigenvalue equation for the literal spherical gradient form. -/
theorem sphericalForm_of_resolvent_eigenvector {N : ℕ} (hN : 1 ≤ N) (β : ℝ)
    (H : Vector N → ℝ) (hH : Continuous H) (μ : ℝ) (f : Lp ℝ 2 (gibbsLaw N β H))
    (hf : f ≠ 0) (he : sphericalL2Resolvent hN β H hH f = μ • f) :
    ∃ u : sphericalSobolevGraph hN β H hH, sphericalEnergyL2Map hN β H hH u = f ∧
      ∀ v, sphericalCompletedDirichlet hN β H hH u v =
        (μ⁻¹ - 1) * inner ℝ f (sphericalEnergyL2Map hN β H hH v) := by
  have hμ : μ ≠ 0 := (sphericalResolvent_eigenvalue_bounds hN β H hH μ f hf he).1.ne'
  let k := μ⁻¹ • f
  have hr : sphericalL2Resolvent hN β H hH k = f := by
    rw [map_smul, he, smul_smul, inv_mul_cancel₀ hμ, one_smul]
  refine ⟨sphericalWeakSolution hN β H hH k, hr, ?_⟩
  intro v
  have hs := sphericalGenerator_resolvent_form hN β H hH k v
  rw [sphericalGenerator_apply_resolvent, hr] at hs
  have hk : k - f = (μ⁻¹ - 1) • f := by dsimp [k]; module
  rw [hk, real_inner_smul_left] at hs
  exact hs

end
end SlowEquilibration.SphericalForm
