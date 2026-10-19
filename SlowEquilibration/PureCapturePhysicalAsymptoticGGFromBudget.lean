-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.PureCapturePhysicalFiniteGGTransfer

/-! The finite physical Gaussian integration-by-parts estimate gives
asymptotic covariance Ghirlanda--Guerra identities when the actual
thermal and quenched energy deviations are sublinear. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.PureCapturePhysicalAsymptoticGGFromBudget

open Set Filter MeasureTheory ProbabilityTheory
open SphericalModel SphericalForm
open GaussianPerturbationSelfAveraging GaussianPerturbationDeviation
open GaussianPerturbationIntegrated
open PureCapturePhysicalShellGG
open PureCapturePhysicalFiniteGGDefinitions
open PureCapturePhysicalFiniteGGTransfer
open scoped Topology

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

/-- A sublinear physical energy fluctuation budget makes every bounded
measurable finite-volume covariance GG defect vanish. The tests may depend
on the volume, so this applies to overlap observables on changing spheres. -/
theorem physicalCovarianceGGDefect_tendsto_zero_of_sublinear_budget
    (μ : FiniteMixture) {β : ℝ} (hβ : 0 < β) (m : ℕ)
    (f : (n : ℕ) → (Fin (m+1) → Vector (n+2)) → ℝ)
    (hf : ∀ n, Measurable (f n))
    (hfb : ∀ n σ, |f n σ| ≤ 1)
    (hbudget : Tendsto (fun n : ℕ =>
      (meanThermalDeviation (shellLaw (n+2))
          (shellLinear (mixtureCoefficients μ)) (fun _ => true) β +
        energyFluctuation (shellLaw (n+2))
          (shellLinear (mixtureCoefficients μ)) (fun _ => true) β) /
        ((n+2 : ℕ) : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => physicalCovarianceGGDefect μ β n m (f n))
      atTop (𝓝 0) := by
  let D : ℝ := ((m : ℝ)+1)*β
  have hD : D ≠ 0 := ne_of_gt (mul_pos (by positivity) hβ)
  have hright : Tendsto (fun n : ℕ =>
      (meanThermalDeviation (shellLaw (n+2))
          (shellLinear (mixtureCoefficients μ)) (fun _ => true) β +
        energyFluctuation (shellLaw (n+2))
          (shellLinear (mixtureCoefficients μ)) (fun _ => true) β) /
        (D * ((n+2 : ℕ) : ℝ))) atTop (𝓝 0) := by
    convert hbudget.div_const D using 1
    · ext n
      have hN : ((n+2 : ℕ) : ℝ) ≠ 0 := by positivity
      dsimp [D]
      field_simp
    · simp
  have habs : Tendsto (fun n : ℕ =>
      |physicalCovarianceGGDefect μ β n m (f n)|) atTop (𝓝 0) := by
    apply squeeze_zero (fun n => abs_nonneg _)
      (fun n => physicalCovarianceGGDefect_abs_le μ hβ n m (f n) (hf n) (hfb n))
    exact hright
  rw [tendsto_zero_iff_abs_tendsto_zero]
  exact habs

end SlowEquilibration.PureCapturePhysicalAsymptoticGGFromBudget
