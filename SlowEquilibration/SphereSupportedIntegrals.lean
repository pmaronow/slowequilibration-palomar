module
-- SPDX-License-Identifier: Apache-2.0

public import SlowEquilibration.SphericalForm
public import Mathlib.MeasureTheory.Function.L2Space

@[expose] public section

/-! # Genuine integrability on finite measures supported on the actual sphere -/
namespace SlowEquilibration.SphericalForm
noncomputable section
open Set MeasureTheory Filter Metric
open SphericalModel
open scoped ENNReal
variable {N : ℕ} {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Every continuous vector-valued function has every finite-measure Lᵖ
moment on the actual compact sphere. -/
theorem memLp_sphereSupported_continuous (μ : Measure (Vector N)) [IsFiniteMeasure μ]
    (hs : ∀ᵐ u ∂μ, ‖u‖^2 = (N:ℝ)) {f : Vector N → G} (hf : Continuous f)
    (p : ℝ≥0∞) : MemLp f p μ := by
  obtain ⟨C,hC⟩ := (isCompact_closedBall (0 : Vector N) (Real.sqrt N)).exists_bound_of_continuousOn hf.continuousOn
  apply MemLp.of_bound hf.aestronglyMeasurable C
  filter_upwards [hs] with u hu
  apply hC
  simp only [mem_closedBall, dist_zero_right]
  rw [← hu, Real.sqrt_sq (norm_nonneg u)]

theorem integrable_sphereSupported_continuous (μ : Measure (Vector N)) [IsFiniteMeasure μ]
    (hs : ∀ᵐ u ∂μ, ‖u‖^2 = (N:ℝ)) {f : Vector N → G} (hf : Continuous f) :
    Integrable f μ :=
  (memLp_sphereSupported_continuous μ hs hf 1).integrable le_rfl

end
end SlowEquilibration.SphericalForm
