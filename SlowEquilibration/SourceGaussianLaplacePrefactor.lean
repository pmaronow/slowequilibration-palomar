-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SourceGaussianLaplacePhysicalWindow

/-! Exact cancellation of the coarea square-root density and Gaussian width. -/
@[expose] public section
namespace SlowEquilibration.SourceGaussianLaplacePrefactor
noncomputable section

/-- The exact coefficient needed after combining the latitude density
`1/√(2π)` with the Gaussian Laplace mass. -/
theorem coarea_gaussian_prefactor {κ : ℝ} (hκ : 0 < κ) :
    (1/Real.sqrt (2*Real.pi))*Real.sqrt (Real.pi/(κ/2)) =
      1/Real.sqrt κ := by
  have hq : κ/2 ≠ 0 := by positivity
  have heq : Real.pi/(κ/2)=2*Real.pi/κ := by field_simp
  rw [heq, Real.sqrt_div (by positivity : 0 ≤ 2*Real.pi)]
  have hs : Real.sqrt (2*Real.pi) ≠ 0 := by positivity
  field_simp

end
end SlowEquilibration.SourceGaussianLaplacePrefactor
