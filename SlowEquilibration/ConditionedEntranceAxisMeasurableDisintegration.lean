-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntranceMixedSourceAxisDisintegration

/-! Exact disintegration of the physical source tilt for integrable jointly
measurable observables. The completed Sobolev representatives in the
weighted-energy argument need not be continuous in the frozen axis. -/
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Metric Topology
open SlowEquilibration.SphericalModel SlowEquilibration.SphericalForm
namespace SlowEquilibration.ConditionedEntrance
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

/-- The exact axis weight is the physical fibre partition ratio even for
integrable, merely measurable representatives. This is the measure-level
identity needed for the joint resolvent and gradient energies. -/
theorem axisGibbs_globalTilt_integral_disintegration_integrable
    {N : ℕ} (hN : 1 ≤ N) (β : ℝ)
    (H₀ : Vector N → ℝ) (hH₀ : Continuous H₀)
    (H : Vector N → Vector N → ℝ)
    (hH : Continuous (fun z : Vector N × Vector N => H z.1 z.2))
    (f : Vector N × Vector N → ℝ)
    (hif : Integrable (fun z : Vector N × Vector N =>
      Real.exp (β * (H z.1 z.2 - H₀ z.2)) * f z)
      ((sphereLaw N).prod (gibbsLaw N β H₀))) :
    let w : Vector N × Vector N → ℝ := fun z => β * (H z.1 z.2 - H₀ z.2)
    let m : Vector N → ℝ := fun u => partition N β (H u) / partition N β H₀
    let M := ∫ z, Real.exp (w z)
      ∂((sphereLaw N).prod (gibbsLaw N β H₀))
    (∫ u, (m u / M) * (∫ x, f (u,x) ∂gibbsLaw N β (H u))
      ∂sphereLaw N) =
      ∫ z, f z ∂normalizedTilt
        ((sphereLaw N).prod (gibbsLaw N β H₀)) w M := by
  dsimp only
  let w : Vector N × Vector N → ℝ := fun z => β * (H z.1 z.2 - H₀ z.2)
  let m : Vector N → ℝ := fun u => partition N β (H u) / partition N β H₀
  let θ := sphereLaw N
  let π := gibbsLaw N β H₀
  let M := ∫ z, Real.exp (w z) ∂θ.prod π
  let : IsProbabilityMeasure θ := sphereLaw_probability N
  let : IsProbabilityMeasure π := gibbsLaw_probability hN β hH₀
  have hHu (u : Vector N) : Continuous (H u) :=
    hH.comp (continuous_const.prodMk continuous_id)
  have hw : Continuous w :=
    (hH.sub (hH₀.comp continuous_snd)).const_mul β
  have hiw : Integrable (fun z => Real.exp (w z)) (θ.prod π) := by
    -- The tilt is bounded on the two compact spherical supports.
    have hs : ∀ᵐ z : Vector N × Vector N ∂θ.prod π,
        ‖z.1‖^2 = (N : ℝ) ∧ ‖z.2‖^2 = (N : ℝ) := by
      apply (Measure.ae_prod_iff_ae_ae (by measurability)).mpr
      filter_upwards [sphereLaw_support hN] with u hu
      filter_upwards [gibbsLaw_support hN β H₀] with x hx
      exact ⟨hu,hx⟩
    obtain ⟨C,hC⟩ := ((isCompact_closedBall (0 : Vector N) (Real.sqrt N)).prod
      (isCompact_closedBall (0 : Vector N) (Real.sqrt N))).exists_bound_of_continuousOn
        hw.rexp.continuousOn
    apply Integrable.of_bound hw.rexp.aestronglyMeasurable C
    filter_upwards [hs] with z hz
    apply hC
    constructor
    · simp only [mem_closedBall,dist_zero_right]
      rw [← hz.1,Real.sqrt_sq (norm_nonneg z.1)]
    · simp only [mem_closedBall,dist_zero_right]
      rw [← hz.2,Real.sqrt_sq (norm_nonneg z.2)]
  have hM : 0 < M := integral_exp_pos hiw
  have hm (u : Vector N) : 0 < m u :=
    div_pos (partition_pos hN β (hHu u)) (partition_pos hN β hH₀)
  have htw (u : Vector N) : Measurable (fun x => w (u,x)) :=
    (hw.comp (continuous_const.prodMk continuous_id)).measurable
  have hsource (u : Vector N) :
      gibbsLaw N β (H u) = normalizedTilt π (fun x => w (u,x)) (m u) := by
    calc
      gibbsLaw N β (H u) = normalizedTilt π
          (gibbsEnergyDifference β β H₀ (H u)) (m u) :=
        gibbsLaw_normalizedTilt hN β β H₀ (H u) hH₀ (hHu u)
      _ = normalizedTilt π (fun x => w (u,x)) (m u) := by
        congr 1
        funext x
        dsimp only [w,gibbsEnergyDifference]
        ring
  have hfibre (u : Vector N) :
      m u * (∫ x, f (u,x) ∂gibbsLaw N β (H u)) =
        ∫ x, Real.exp (w (u,x)) * f (u,x) ∂π := by
    rw [hsource u, integral_normalizedTilt π _ (htw u) (hm u)]
    field_simp [(hm u).ne']
  calc
    (∫ u, (m u / M) * (∫ x, f (u,x) ∂gibbsLaw N β (H u)) ∂θ) =
      ∫ u, (∫ x, Real.exp (w (u,x)) * f (u,x) ∂π) / M ∂θ := by
        apply integral_congr_ae
        exact .of_forall fun u => by
          dsimp only
          rw [← hfibre u]
          ring
    _ = (∫ u, ∫ x, Real.exp (w (u,x)) * f (u,x) ∂π ∂θ) / M := by
      rw [integral_div]
    _ = (∫ z, Real.exp (w z) * f z ∂θ.prod π) / M := by
      rw [integral_prod _ (by simpa only [w,θ,π] using hif)]
    _ = ∫ z, f z ∂normalizedTilt (θ.prod π) w M :=
      (integral_normalizedTilt _ w hw.measurable hM f).symm

end SlowEquilibration.ConditionedEntrance
