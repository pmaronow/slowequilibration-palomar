-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.EntranceActualSourceCutoffTiltMoments
public import SlowEquilibration.ConditionedEntranceTiltCommutator
public import SlowEquilibration.ConditionedEntranceJointHamiltonian

/-! Physical global normalization for the original mixed source cutoff.
The first axis moment is taken at every Gibbs-typical spin, then integrated
over the original disorder-specific Gibbs law. The global tilt is not
replaced by a fibrewise Gibbs normalization. -/
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Metric Topology
open SlowEquilibration.SphericalModel SlowEquilibration.SphericalForm
namespace SlowEquilibration.ConditionedEntrance
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem sphere_gibbs_pair_integrable {N : ℕ} (hN : 1 ≤ N)
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

/-- In the manuscript's degree range, the first-moment error eventually
falls below the threshold needed to normalize the global tilt. -/
theorem sourceTilt_eta_eventually_half (d : ℕ) (hd : 4 ≤ d) (C : ℝ) :
    ∀ᶠ n : ℕ in atTop,
      C*((n+1 : ℕ) : ℝ)^(1-(d : ℝ)/2) ≤ 1/2 := by
  have hpow : 0 < (d : ℝ)/2-1 := by
    have hreal : (4 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hN : Tendsto (fun n : ℕ => ((n+1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hlim : Tendsto (fun n : ℕ => C*((n+1 : ℕ) : ℝ)^(1-(d : ℝ)/2))
      atTop (𝓝 0) := by
    convert ((tendsto_rpow_neg_atTop hpow).comp hN).const_mul C using 1
    · funext n
      congr 2
      ring
    · simp
  exact (hlim.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1/2))).mono
    (fun _ hn => hn.le)

/-- Averaging the pointwise source normalization over any genuine
conditioned disorder probability law preserves its same error constant. -/
theorem globalTilt_disorder_average_close_one
    {Θ : Type*} [MeasurableSpace Θ] (ξ : Measure Θ) [IsProbabilityMeasure ξ]
    (M : Θ → ℝ) (hM : Integrable M ξ) {η : ℝ}
    (hpoint : ∀ᵐ J ∂ξ, |M J-1| ≤ η) :
    |(∫ J, M J ∂ξ)-1| ≤ η := by
  have hi : Integrable (fun J => M J-1) ξ := hM.sub (integrable_const _)
  have hb : (∫ J, |M J-1| ∂ξ) ≤ η := by
    simpa only [integral_const,probReal_univ,one_smul] using
      integral_mono_ae hi.abs (integrable_const η) hpoint
  calc
    |(∫ J, M J ∂ξ)-1| = |∫ J, M J-1 ∂ξ| := by
      rw [integral_sub hM (integrable_const (1 : ℝ))]
      simp
    _ ≤ ∫ J, |M J-1| ∂ξ := abs_integral_le_integral_abs
    _ ≤ η := hb

/-- The genuine global mass of the mixed physical source tilt is within
`O(N^(1-d/2))` of one on the original latitude-mean event. The constant is
chosen before dimension, original disorder, axis, cutoff and marks. -/
theorem actual_mixedSource_globalTilt_mass_close_one (μ : FiniteMixture)
    (hd : 4 ≤ μ.minDegree) {Q B β : ℝ} (hQ : 0 < Q)
    (hnp : μ.minDegree < μ.maxDegree) (hB : 0 ≤ B) (hβ : 0 ≤ β) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (J : Disorder (n+1) μ.maxDegree), J ∈
        EntranceLatitudeTangentObservable.originalLatitudeMeanGood n μ →
      ∀ (α : ℝ), 0 < α →
        α ≤ EntranceLatitudeTangentObservable.sourceCutoffMomentScale μ Q B (2*β) →
      ∀ (χ : ℝ → ℝ), ContDiff ℝ 2 χ → (∀ s, |χ s| ≤ 1) →
        (∀ s, 2 < |s| → χ s = 0) →
      ∀ (e k : ℝ), |e| ≤ B → |k| ≤ B →
      let H₀ := fieldOfMixture μ J
      let w : Vector (n+1) × Vector (n+1) → ℝ := fun z =>
        β * (sourceSmoothCutoffField μ Q hQ hnp J z.1 e k α χ z.2 - H₀ z.2)
      let M := ∫ z, Real.exp (w z)
        ∂((sphereLaw (n+1)).prod (gibbsLaw (n+1) β H₀))
      |M-1| ≤ C*((n+1 : ℕ) : ℝ)^(1-(μ.minDegree : ℝ)/2) ∧
      (C*((n+1 : ℕ) : ℝ)^(1-(μ.minDegree : ℝ)/2) ≤ 1/2 →
        IsProbabilityMeasure
          (normalizedTilt ((sphereLaw (n+1)).prod (gibbsLaw (n+1) β H₀)) w M)) := by
  obtain ⟨C,hC,hMom⟩ :=
    EntranceLatitudeTangentObservable.actual_sourceSmoothCutoffField_tilt_moments
      μ hd hQ hnp hB hβ
  refine ⟨C,hC,?_⟩
  filter_upwards [hMom] with n hn
  intro J hJ α hα hαsmall χ hχ hχb hχ0 e k he hk
  dsimp only
  let H₀ := fieldOfMixture μ J
  let w : Vector (n+1) × Vector (n+1) → ℝ := fun z =>
    β * (sourceSmoothCutoffField μ Q hQ hnp J z.1 e k α χ z.2 - H₀ z.2)
  let π := gibbsLaw (n+1) β H₀
  let : IsProbabilityMeasure (sphereLaw (n+1)) := sphereLaw_probability (n+1)
  have hN : 1 ≤ n+1 := by omega
  have hH₀ : Continuous H₀ := (fieldOfMixture_contDiff μ J).continuous
  let : IsProbabilityMeasure (gibbsLaw (n+1) β H₀) := gibbsLaw_probability hN β hH₀
  have hH : Continuous (fun z : Vector (n+1) × Vector (n+1) =>
      sourceSmoothCutoffField μ Q hQ hnp J z.1 e k α χ z.2) :=
    (sourceSmoothCutoffField_jointContinuous μ Q hQ hnp α χ hχ.continuous).comp
      (show Continuous (fun z : Vector (n+1) × Vector (n+1) =>
        ((J,(z.1,(e,k))),z.2)) by fun_prop)
  have hw : Continuous w :=
    (hH.sub (hH₀.comp continuous_snd)).const_mul β
  have hexp : Integrable (fun z => Real.exp (w z)) ((sphereLaw (n+1)).prod π) :=
    sphere_gibbs_pair_integrable hN β H₀ hH₀ hw.rexp
  have haxis : ∀ᵐ x ∂π,
      (∫ u, |Real.exp (w (u,x))-1| ∂sphereLaw (n+1)) ≤
        C*((n+1 : ℕ) : ℝ)^(1-(μ.minDegree : ℝ)/2) := by
    filter_upwards [gibbsLaw_support hN β H₀] with x hx
    exact (hn J hJ x hx α hα hαsmall χ hχ hχb hχ0 e k he hk).1
  have hc := exponential_mass_close_one (sphereLaw (n+1)) π w hexp rfl haxis
  refine ⟨hc,?_⟩
  intro hsmall
  have hM : 0 < (∫ z, Real.exp (w z) ∂((sphereLaw (n+1)).prod π)) := by
    have hl := (abs_le.mp hc).1
    linarith
  exact normalizedTilt_probability _ w hM hexp rfl

/-- The same genuine global normalization rate for the proper pure source.
The pure correction is its exact homogeneous two-atom expression; it does
not pass through the inverse covariance formula for a mixed field. -/
theorem actual_pureSource_globalTilt_mass_close_one
    (p : ℕ) (hp : 4 ≤ p) (c : ℝ) (hc : 0 < c)
    {Q B β : ℝ} (hQ : 0 < Q) (hB : 0 ≤ B) (hβ : 0 ≤ β) :
    let μ := FiniteMixture.pure p (by omega) c hc
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (J : Disorder (n+1) μ.maxDegree), J ∈
        EntranceLatitudeTangentObservable.originalLatitudeMeanGood n μ →
      ∀ (α : ℝ), 0 < α →
        α ≤ EntranceLatitudeTangentObservable.sourceCutoffMomentScale μ Q B (2*β) →
      ∀ (χ : ℝ → ℝ), ContDiff ℝ 2 χ → (∀ s, |χ s| ≤ 1) →
        (∀ s, 2 < |s| → χ s = 0) →
      ∀ (e : ℝ), |e| ≤ B →
      let H₀ := fieldOfMixture μ J
      let w : Vector (n+1) × Vector (n+1) → ℝ := fun z =>
        β * (pureSourceSmoothCutoffField
          p (by omega) c hc Q J z.1 e α χ z.2 - H₀ z.2)
      let M := ∫ z, Real.exp (w z)
        ∂((sphereLaw (n+1)).prod (gibbsLaw (n+1) β H₀))
      |M-1| ≤ C*((n+1 : ℕ) : ℝ)^(1-(μ.minDegree : ℝ)/2) ∧
      (C*((n+1 : ℕ) : ℝ)^(1-(μ.minDegree : ℝ)/2) ≤ 1/2 →
        IsProbabilityMeasure
          (normalizedTilt ((sphereLaw (n+1)).prod (gibbsLaw (n+1) β H₀)) w M)) := by
  dsimp only
  let μ := FiniteMixture.pure p (by omega) c hc
  obtain ⟨C,hC,hMom⟩ :=
    EntranceLatitudeTangentObservable.actual_pureSourceSmoothCutoffField_tilt_moments
      p hp c hc hQ hB hβ
  refine ⟨C,hC,?_⟩
  filter_upwards [hMom] with n hn
  intro J hJ α hα hαsmall χ hχ hχb hχ0 e he
  let H₀ := fieldOfMixture μ J
  let w : Vector (n+1) × Vector (n+1) → ℝ := fun z =>
    β * (pureSourceSmoothCutoffField
      p (by omega) c hc Q J z.1 e α χ z.2 - H₀ z.2)
  let π := gibbsLaw (n+1) β H₀
  let : IsProbabilityMeasure (sphereLaw (n+1)) := sphereLaw_probability (n+1)
  have hN : 1 ≤ n+1 := by omega
  have hH₀ : Continuous H₀ := (fieldOfMixture_contDiff μ J).continuous
  let : IsProbabilityMeasure (gibbsLaw (n+1) β H₀) := gibbsLaw_probability hN β hH₀
  have hH : Continuous (fun z : Vector (n+1) × Vector (n+1) =>
      pureSourceSmoothCutoffField
        p (by omega) c hc Q J z.1 e α χ z.2) :=
    (pureSourceJointHamiltonian_contDiff
      p (by omega) c hc Q α χ hχ).continuous.comp
      (show Continuous (fun z : Vector (n+1) × Vector (n+1) =>
        ((J,(z.1,(e,(0 : ℝ)))),z.2)) by fun_prop)
  have hw : Continuous w :=
    (hH.sub (hH₀.comp continuous_snd)).const_mul β
  have hexp : Integrable (fun z => Real.exp (w z)) ((sphereLaw (n+1)).prod π) :=
    sphere_gibbs_pair_integrable hN β H₀ hH₀ hw.rexp
  have haxis : ∀ᵐ x ∂π,
      (∫ u, |Real.exp (w (u,x))-1| ∂sphereLaw (n+1)) ≤
        C*((n+1 : ℕ) : ℝ)^(1-(μ.minDegree : ℝ)/2) := by
    filter_upwards [gibbsLaw_support hN β H₀] with x hx
    exact (hn J hJ x hx α hα hαsmall χ hχ hχb hχ0 e he).1
  have hc := exponential_mass_close_one (sphereLaw (n+1)) π w hexp rfl haxis
  refine ⟨hc,?_⟩
  intro hsmall
  have hM : 0 < (∫ z, Real.exp (w z) ∂((sphereLaw (n+1)).prod π)) := by
    have hl := (abs_le.mp hc).1
    linarith
  exact normalizedTilt_probability _ w hM hexp rfl

end SlowEquilibration.ConditionedEntrance
