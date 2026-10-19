-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntranceGlobalInitialL1
public import SlowEquilibration.ConditionedEntranceActualSourceGlobalTilt

/-! The global-tilt initial-density estimate for a literal spherical Gibbs
reference. Continuity and compact sphere support discharge the abstract
product-integrability assumptions of the preceding theorem. -/
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Metric
open SlowEquilibration.SphericalModel SlowEquilibration.SphericalForm
namespace SlowEquilibration.ConditionedEntrance
set_option autoImplicit false
set_option maxHeartbeats 500000

private theorem physical_pair_integrable {N : ℕ} (hN : 1 ≤ N)
    (β : ℝ) (H : Vector N → ℝ) (hH : Continuous H)
    {f : Vector N × Vector N → ℝ} (hf : Continuous f) :
    Integrable f ((sphereLaw N).prod (gibbsLaw N β H)) := by
  let : IsProbabilityMeasure (sphereLaw N) := sphereLaw_probability N
  let : IsProbabilityMeasure (gibbsLaw N β H) := gibbsLaw_probability hN β hH
  have hs : ∀ᵐ z : Vector N × Vector N
      ∂(sphereLaw N).prod (gibbsLaw N β H),
      ‖z.1‖^2 = (N : ℝ) ∧ ‖z.2‖^2 = (N : ℝ) := by
    apply (Measure.ae_prod_iff_ae_ae (by measurability)).mpr
    filter_upwards [sphereLaw_support hN] with u hu
    filter_upwards [gibbsLaw_support hN β H] with x hx
    exact ⟨hu,hx⟩
  obtain ⟨C,hC⟩ := ((isCompact_closedBall (0 : Vector N) (Real.sqrt N)).prod
    (isCompact_closedBall (0 : Vector N) (Real.sqrt N))).exists_bound_of_continuousOn hf.continuousOn
  apply Integrable.of_bound hf.aestronglyMeasurable C
  filter_upwards [hs] with z hz
  apply hC
  constructor
  · simp only [mem_closedBall,dist_zero_right]
    rw [← hz.1,Real.sqrt_sq (norm_nonneg z.1)]
  · simp only [mem_closedBall,dist_zero_right]
    rw [← hz.2,Real.sqrt_sq (norm_nonneg z.2)]

/-- Under the literal Gibbs reference, the global source normalizer gives
an initial density within `4η` of the reference density in its own tilted
law. The reference density is the inverse of the actual Gibbs density. -/
theorem gibbsGlobalTilt_initialDensity_l1_le_four_eta {N : ℕ} (hN : 1 ≤ N)
    (β : ℝ) (H : Vector N → ℝ) (hH : Continuous H)
    (w : Vector N × Vector N → ℝ) (hw : Continuous w)
    {η : ℝ} (hη : 0 ≤ η) (hηhalf : η ≤ 1/2)
    (haxis : ∀ᵐ x ∂gibbsLaw N β H,
      (∫ u, |Real.exp (w (u,x))-1| ∂sphereLaw N) ≤ η) :
    let π := gibbsLaw N β H
    let f₀ := fun x => (gibbsDensity N β H x)⁻¹
    let M := ∫ z, Real.exp (w z) ∂(sphereLaw N).prod π
    (∫ z, |M * Real.exp (-w z) * f₀ z.2 - f₀ z.2|
      ∂normalizedTilt ((sphereLaw N).prod π) w M) ≤ 4*η := by
  dsimp only
  let π := gibbsLaw N β H
  let f₀ : Vector N → ℝ := fun x => (gibbsDensity N β H x)⁻¹
  let : IsProbabilityMeasure (sphereLaw N) := sphereLaw_probability N
  let : IsProbabilityMeasure π := gibbsLaw_probability hN β hH
  have hf₀c : Continuous f₀ :=
    (gibbsDensity_continuous β hH).inv₀
      (fun x => (gibbsDensity_pos hN β hH x).ne')
  have hf₀ : Integrable f₀ π := integrable_gibbs_of_continuous hN β hH hf₀c
  have hf₀pos : ∀ x, 0 ≤ f₀ x := fun x =>
    inv_nonneg.mpr (gibbsDensity_pos hN β hH x).le
  have hf₀mass : (∫ x, f₀ x ∂π) = 1 := by
    rw [integral_gibbsLaw hN β hH f₀]
    have heq : (fun x => gibbsDensity N β H x * f₀ x) = fun _ => 1 := by
      funext x
      exact mul_inv_cancel₀ (gibbsDensity_pos hN β hH x).ne'
    rw [heq]
    simp
  have he : Integrable (fun z => Real.exp (w z)) ((sphereLaw N).prod π) :=
    physical_pair_integrable hN β H hH hw.rexp
  have hfprod : Integrable (fun z : Vector N × Vector N => f₀ z.2)
      ((sphereLaw N).prod π) :=
    physical_pair_integrable hN β H hH (hf₀c.comp continuous_snd)
  have hewprod : Integrable (fun z : Vector N × Vector N => Real.exp (w z) * f₀ z.2)
      ((sphereLaw N).prod π) :=
    physical_pair_integrable hN β H hH (hw.rexp.mul (hf₀c.comp continuous_snd))
  exact normalizedTilt_initialDensity_l1_le_four_eta (sphereLaw N) π w hw.measurable
    he f₀ hf₀ hf₀pos hf₀mass hfprod hewprod hη hηhalf haxis

end SlowEquilibration.ConditionedEntrance
