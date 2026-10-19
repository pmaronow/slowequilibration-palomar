-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntranceAxisMeasurableDisintegration

/-! The exact partition-ratio weighted Gibbs-fibre integral is itself
L¹ in the axis whenever the corresponding joint density is L¹ under
the globally normalized source tilt. -/
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory
open SlowEquilibration.SphericalModel SlowEquilibration.SphericalForm
namespace SlowEquilibration.ConditionedEntrance
set_option autoImplicit false
set_option maxHeartbeats 400000

theorem axisGibbs_partitionWeighted_fibre_integrable
    {N : ℕ} (hN : 1 ≤ N) (β : ℝ)
    (H₀ : Vector N → ℝ) (hH₀ : Continuous H₀)
    (H : Vector N → Vector N → ℝ)
    (hH : Continuous (fun z : Vector N × Vector N => H z.1 z.2))
    (f : Vector N × Vector N → ℝ)
    (M : ℝ) (hM : 0 < M)
    (hif : Integrable (fun z : Vector N × Vector N =>
      Real.exp (β*(H z.1 z.2-H₀ z.2))*f z)
      ((sphereLaw N).prod (gibbsLaw N β H₀))) :
    Integrable (fun u =>
      ((partition N β (H u)/partition N β H₀)/M) *
        (∫ x, f (u,x) ∂gibbsLaw N β (H u))) (sphereLaw N) := by
  let π := gibbsLaw N β H₀
  let : IsProbabilityMeasure π := gibbsLaw_probability hN β hH₀
  let m : Vector N → ℝ := fun u => partition N β (H u)/partition N β H₀
  let w : Vector N × Vector N → ℝ := fun z => β*(H z.1 z.2-H₀ z.2)
  have hHu (u : Vector N) : Continuous (H u) :=
    hH.comp (continuous_const.prodMk continuous_id)
  have hw : Continuous w := (hH.sub (hH₀.comp continuous_snd)).const_mul β
  have hm (u : Vector N) : 0 < m u :=
    div_pos (partition_pos hN β (hHu u)) (partition_pos hN β hH₀)
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
  have htw (u : Vector N) : Measurable (fun x => w (u,x)) :=
    (hw.comp (continuous_const.prodMk continuous_id)).measurable
  have hfibre (u : Vector N) :
      (m u/M)*(∫ x, f (u,x) ∂gibbsLaw N β (H u)) =
      (∫ x, Real.exp (w (u,x))*f (u,x) ∂π)/M := by
    rw [hsource u, integral_normalizedTilt π _ (htw u) (hm u)]
    field_simp [(hm u).ne',hM.ne']
  have hinner : Integrable (fun u =>
      ∫ x, Real.exp (w (u,x))*f (u,x) ∂π) (sphereLaw N) :=
    hif.integral_prod_left
  exact (hinner.div_const M).congr
    (Filter.Eventually.of_forall (fun u => (hfibre u).symm))

end SlowEquilibration.ConditionedEntrance
