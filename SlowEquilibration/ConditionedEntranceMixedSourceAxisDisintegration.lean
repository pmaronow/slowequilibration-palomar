-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntranceQuenchedNormalizedSourceCap
public import SlowEquilibration.SphericalGibbsTiltIdentity

/-! The actual globally tilted mixed-source cap mass disintegrates over
the physical axis with the exact source partition-ratio weight. -/
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Metric Topology
open SlowEquilibration.SphericalModel SlowEquilibration.SphericalForm
open SlowEquilibration.SphericalOverlapExponential
namespace SlowEquilibration.ConditionedEntrance
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

private theorem axisGibbs_pair_integrable {N : ℕ} (hN : 1 ≤ N)
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
    (isCompact_closedBall (0 : Vector N) (Real.sqrt N))).exists_bound_of_continuousOn
      hf.continuousOn
  apply Integrable.of_bound hf.aestronglyMeasurable C
  filter_upwards [hs] with z hz
  apply hC
  constructor
  · simp only [mem_closedBall,dist_zero_right]
    rw [← hz.1,Real.sqrt_sq (norm_nonneg z.1)]
  · simp only [mem_closedBall,dist_zero_right]
    rw [← hz.2,Real.sqrt_sq (norm_nonneg z.2)]

/-- A jointly continuous family of physical Hamiltonians disintegrates
its single global exponential tilt into Gibbs fibres with their exact
partition ratios. -/
theorem axisGibbs_globalTilt_integral_disintegration
    {N : ℕ} (hN : 1 ≤ N) (β : ℝ)
    (H₀ : Vector N → ℝ) (hH₀ : Continuous H₀)
    (H : Vector N → Vector N → ℝ)
    (hH : Continuous (fun z : Vector N × Vector N => H z.1 z.2))
    (f : Vector N × Vector N → ℝ) (hf : Continuous f) :
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
  have hiw : Integrable (fun z => Real.exp (w z)) (θ.prod π) :=
    axisGibbs_pair_integrable hN β H₀ hH₀ hw.rexp
  have hiwf : Integrable (fun z => Real.exp (w z) * f z) (θ.prod π) :=
    axisGibbs_pair_integrable hN β H₀ hH₀ (hw.rexp.mul hf)
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
      rw [integral_prod _ hiwf]
    _ = ∫ z, f z ∂normalizedTilt (θ.prod π) w M :=
      (integral_normalizedTilt _ w hw.measurable hM f).symm

/-- For the literal mixed source cutoff and physical two-sided cap, the
axis mixture of genuine source Gibbs laws equals the single globally
normalized tilt. Its axis weight is the exact physical fibre partition
ratio, with no separate pointwise lower bound. -/
theorem mixedSource_globalTilt_capKilling_axis_disintegration
    {N : ℕ} (hN : 1 ≤ N) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 < Q) (hnp : μ.minDegree < μ.maxDegree)
    (J : Disorder N μ.maxDegree) (β α : ℝ) (χ : ℝ → ℝ)
    (hχ : Continuous χ) (e k : ℝ) :
    let H₀ := fieldOfMixture μ J
    let H : Vector N → Vector N → ℝ := fun u x =>
      sourceSmoothCutoffField μ Q hQ hnp J u e k α χ x
    let w : Vector N × Vector N → ℝ := fun z =>
      β * (H z.1 z.2 - H₀ z.2)
    let m : Vector N → ℝ := fun u => partition N β (H u) / partition N β H₀
    let M := ∫ z, Real.exp (w z)
      ∂((sphereLaw N).prod (gibbsLaw N β H₀))
    (∫ u, (m u / M) *
      (∫ x, PhysicalHitting.capKilling α u x ∂gibbsLaw N β (H u))
        ∂sphereLaw N) =
      ∫ z, PhysicalHitting.capKilling α z.1 z.2
        ∂normalizedTilt ((sphereLaw N).prod (gibbsLaw N β H₀)) w M := by
  dsimp only
  let H₀ := fieldOfMixture μ J
  let H : Vector N → Vector N → ℝ := fun u x =>
    sourceSmoothCutoffField μ Q hQ hnp J u e k α χ x
  let κ : Vector N × Vector N → ℝ := fun z =>
    PhysicalHitting.capKilling α z.1 z.2
  have hH₀ : Continuous H₀ := (fieldOfMixture_contDiff μ J).continuous
  have hH : Continuous (fun z : Vector N × Vector N => H z.1 z.2) :=
    (sourceSmoothCutoffField_jointContinuous μ Q hQ hnp α χ hχ).comp
      (show Continuous (fun z : Vector N × Vector N =>
        ((J,(z.1,(e,k))),z.2)) by fun_prop)
  have hrc : Continuous (fun z : Vector N × Vector N => overlapValue z.1 z.2) := by
    simpa only [overlapValue_eq] using
      (continuous_inner (𝕜 := ℝ) (E := Vector N)).div_const (N : ℝ)
  have hκ : Continuous κ := by
    exact ((SphericalCapCutoff.cutoff_contDiff _ _).continuous.comp hrc).add
      ((SphericalCapCutoff.cutoff_contDiff _ _).continuous.comp hrc.neg)
  exact axisGibbs_globalTilt_integral_disintegration hN β H₀ hH₀ H hH κ hκ

end SlowEquilibration.ConditionedEntrance
