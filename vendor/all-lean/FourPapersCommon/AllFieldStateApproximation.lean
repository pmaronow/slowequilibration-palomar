module
public import Paper.ParisiSelectedState
public import FRSB.OptimalDiffusion
public import FRSB.IntegralGronwall
public import Paper.ParisiCDFIntegral
public import FRSB.GlobalMeasureStability

@[expose] public section

/-! Actual all-field same-Brownian state stability. The common initial h and
common Brownian driver cancel in the difference of the genuine integral
equations. The deterministic estimate is uniform in the sample path and the
initial field; no law-convergence or drift-regularity premise is supplied. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal BoundedContinuousFunction
namespace FourPapersCommon
open Paper FRSB

/-- The actual selected gradient evaluated along the all-field Brownian state. -/
abbrev fieldMagnetization (β h : ℝ) (hβ : β ≠ 0) (μ : Paper.ParisiMeasure)
    (s : ℝ) (ω : Paper.BrownianSample) : ℝ :=
  parisiGradient β μ (s, selectedParisiStateReal β h hβ μ ω s)

 theorem continuous_fieldMagnetization_path (β h : ℝ) (hβ : β ≠ 0) (μ : Paper.ParisiMeasure) (ω : Paper.BrownianSample) :
    Continuous (fun s => fieldMagnetization β h hβ μ s ω) := by
  simp only [fieldMagnetization]
  exact (Paper.continuous_parisiGradient β μ).comp
    (continuous_id.prodMk (continuous_selectedParisiStateReal β h hβ μ ω))

 theorem selectedDrift_intervalIntegrable (β h : ℝ) (hβ : β ≠ 0) (μ : Paper.ParisiMeasure)
    (ω : Paper.BrownianSample) (a b : ℝ) :
    IntervalIntegrable (fun s => β ^ 2 * alpha μ s * fieldMagnetization β h hβ μ s ω) volume a b :=
  ((Paper.parisiCDF_intervalIntegrable μ a b).const_mul (β ^ 2)).mul_continuousOn
    (continuous_fieldMagnetization_path β h hβ μ ω).continuousOn

 theorem selectedState_drift_difference_le (β h : ℝ) (hβ : β ≠ 0) (μ ν : Paper.ParisiMeasure)
    (d : ℝ) (_hd : 0 ≤ d)
    (hgrad : ∀ s x, ‖Paper.parisiGradient β μ (s,x) -
      Paper.parisiGradient β ν (s,x)‖ ≤ d) (ω : Paper.BrownianSample) (s : ℝ) :
    ‖alpha μ s * fieldMagnetization β h hβ μ s ω - alpha ν s * fieldMagnetization β h hβ ν s ω‖ ≤
      ‖alpha μ s - alpha ν s‖ + d +
        ‖selectedParisiStateReal β h hβ μ ω s - selectedParisiStateReal β h hβ ν ω s‖ := by
  have hm : ‖fieldMagnetization β h hβ μ s ω‖ ≤ 1 := by
    simpa only [fieldMagnetization] using
      Paper.norm_parisiGradient_le_one β μ (s, selectedParisiStateReal β h hβ μ ω s)
  have han : ‖alpha ν s‖ ≤ 1 := by
    change ‖Paper.parisiCDF ν s‖ ≤ 1
    rw [Real.norm_of_nonneg (Paper.parisiCDF_nonneg ν s)]
    exact Paper.parisiCDF_le_one ν s
  have hM : ‖fieldMagnetization β h hβ μ s ω - fieldMagnetization β h hβ ν s ω‖ ≤ d +
      ‖selectedParisiStateReal β h hβ μ ω s - selectedParisiStateReal β h hβ ν ω s‖ := by
    simp only [fieldMagnetization]
    calc
      ‖Paper.parisiGradient β μ (s, selectedParisiStateReal β h hβ μ ω s) -
          Paper.parisiGradient β ν (s, selectedParisiStateReal β h hβ ν ω s)‖ ≤
          ‖Paper.parisiGradient β μ (s, selectedParisiStateReal β h hβ μ ω s) -
            Paper.parisiGradient β ν (s, selectedParisiStateReal β h hβ μ ω s)‖ +
          ‖Paper.parisiGradient β ν (s, selectedParisiStateReal β h hβ μ ω s) -
            Paper.parisiGradient β ν (s, selectedParisiStateReal β h hβ ν ω s)‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ d + ‖selectedParisiStateReal β h hβ μ ω s - selectedParisiStateReal β h hβ ν ω s‖ := by
        apply add_le_add (hgrad s _)
        simpa only [dist_eq_norm, NNReal.coe_one, one_mul] using
          (Paper.lipschitzWith_parisiGradient_all β ν s).dist_le_mul
            (selectedParisiStateReal β h hβ μ ω s) (selectedParisiStateReal β h hβ ν ω s)
  have he : alpha μ s * fieldMagnetization β h hβ μ s ω - alpha ν s * fieldMagnetization β h hβ ν s ω =
      (alpha μ s - alpha ν s) * fieldMagnetization β h hβ μ s ω +
        alpha ν s * (fieldMagnetization β h hβ μ s ω - fieldMagnetization β h hβ ν s ω) := by ring
  rw [he]
  apply (norm_add_le _ _).trans
  simp only [norm_mul]
  have h1 := mul_le_mul_of_nonneg_left hm (norm_nonneg (alpha μ s - alpha ν s))
  have h2 := mul_le_mul han hM (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  simp only [mul_one, one_mul] at h1 h2
  exact (add_le_add h1 h2).trans_eq (by ring)

 theorem selectedState_L1_dist_le (β h : ℝ) (hβ : β ≠ 0) (μ ν : Paper.ParisiMeasure)
    (d : ℝ) (hd : 0 ≤ d)
    (hgrad : ∀ s x, ‖Paper.parisiGradient β μ (s,x) -
      Paper.parisiGradient β ν (s,x)‖ ≤ d)
    (ω : Paper.BrownianSample) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖selectedParisiStateReal β h hβ μ ω t - selectedParisiStateReal β h hβ ν ω t‖ ≤
      β ^ 2 * Real.exp (β ^ 2) * (d + Paper.parisiCDFDistance μ ν) := by
  let e : ℝ → ℝ := fun s => ‖selectedParisiStateReal β h hβ μ ω s - selectedParisiStateReal β h hβ ν ω s‖
  have he : Continuous e := ((continuous_selectedParisiStateReal β h hβ μ ω).sub
    (continuous_selectedParisiStateReal β h hβ ν ω)).norm
  have hCDFint (a b : ℝ) : IntervalIntegrable (fun s => ‖alpha μ s - alpha ν s‖) volume a b :=
    ((Paper.parisiCDF_intervalIntegrable μ a b).sub
      (Paper.parisiCDF_intervalIntegrable ν a b)).norm
  have hbudget : 0 ≤ Paper.parisiCDFDistance μ ν := Paper.parisiCDFDistance_nonneg μ ν
  have hbound : ∀ r ∈ Icc (0 : ℝ) 1,
      e r ≤ β ^ 2 * (d + Paper.parisiCDFDistance μ ν) + β ^ 2 * ∫ s in 0..r, e s := by
    intro r hr
    have hiμ := selectedDrift_intervalIntegrable β h hβ μ ω 0 r
    have hiν := selectedDrift_intervalIntegrable β h hβ ν ω 0 r
    have hCDFle : (∫ s in 0..r, ‖alpha μ s - alpha ν s‖) ≤ Paper.parisiCDFDistance μ ν :=
      intervalIntegral.integral_mono_interval le_rfl hr.1 hr.2
        (ae_of_all _ (fun s => norm_nonneg _)) (hCDFint 0 1)
    have hdint : IntervalIntegrable (fun _ : ℝ => d) volume 0 r := intervalIntegrable_const
    have hisum : IntervalIntegrable
        (fun s => β ^ 2 * (‖alpha μ s - alpha ν s‖ + d + e s)) volume 0 r :=
      (((hCDFint 0 r).add hdint).add (he.intervalIntegrable 0 r)).const_mul _
    have hm := intervalIntegral.integral_mono_on hr.1 ((hiμ.sub hiν).norm) hisum
      (fun s _ => by
        rw [mul_assoc (β ^ 2), mul_assoc (β ^ 2), ← mul_sub, norm_mul,
          Real.norm_of_nonneg (sq_nonneg β)]
        exact mul_le_mul_of_nonneg_left (selectedState_drift_difference_le β h hβ μ ν d hd hgrad ω s)
          (sq_nonneg β))
    have heq : e r = ‖∫ s in 0..r,
        (β ^ 2 * alpha μ s * fieldMagnetization β h hβ μ s ω - β ^ 2 * alpha ν s * fieldMagnetization β h hβ ν s ω)‖ := by
      dsimp only [e]
      rw [selectedParisiState_integral_equation β h hβ μ ω hr, selectedParisiState_integral_equation β h hβ ν ω hr,
        add_sub_add_left_eq_sub, intervalIntegral.integral_sub hiμ hiν]
      rfl
    rw [heq]
    apply ((intervalIntegral.norm_integral_le_integral_norm hr.1).trans hm).trans
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add
      ((hCDFint 0 r).add hdint) (he.intervalIntegrable 0 r),
      intervalIntegral.integral_add (hCDFint 0 r) hdint, intervalIntegral.integral_const]
    simp only [sub_zero, smul_eq_mul]
    nlinarith [mul_le_mul_of_nonneg_left hCDFle (sq_nonneg β),
      mul_le_mul_of_nonneg_left hr.2 hd]
  have hg := integral_gronwall_exp_bound e he (β ^ 2 * (d + Paper.parisiCDFDistance μ ν))
    (β ^ 2) (mul_nonneg (sq_nonneg β) (add_nonneg hd hbudget)) (sq_nonneg β)
    (fun s _ => norm_nonneg _) hbound t ht
  exact hg.trans_eq (by ring)

/-- The paper's exact deterministic bound with the actual global gradient norm. -/
theorem selectedState_dist_le (β h : ℝ) (hβ : β ≠ 0) (μ ν : Paper.ParisiMeasure) (ω : Paper.BrownianSample)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖selectedParisiStateReal β h hβ μ ω t - selectedParisiStateReal β h hβ ν ω t‖ ≤
      β ^ 2 * Real.exp (β ^ 2) *
        (‖Paper.parisiGradientBCF β μ - Paper.parisiGradientBCF β ν‖ +
          Paper.parisiCDFDistance μ ν) :=
  selectedState_L1_dist_le β h hβ μ ν _ (norm_nonneg _) (fun s x =>
    Paper.norm_parisiSlabExtend_sub_le (by norm_num) _ _ (s,x)) ω ht

/-- Actual weak-measure convergence gives uniform same-Brownian path convergence.
The deterministic bound holds simultaneously for every sample path. -/
theorem selectedState_uniform_convergence_of_weak {ι : Type*} {L : Filter ι}
    [L.IsCountablyGenerated] (β h : ℝ) (hβ : β ≠ 0) (μs : ι → Paper.ParisiMeasure) (μ : Paper.ParisiMeasure)
    (hμ : Tendsto μs L (nhds μ)) :
    ∀ ε > 0, ∀ᶠ i in L, ∀ ω : Paper.BrownianSample, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖selectedParisiStateReal β h hβ (μs i) ω t - selectedParisiStateReal β h hβ μ ω t‖ < ε := by
  have hgrad := ((continuous_gradientBCF β).tendsto μ).comp hμ
  have hn : Tendsto (fun i => ‖Paper.parisiGradientBCF β (μs i) -
      Paper.parisiGradientBCF β μ‖) L (nhds 0) := by
    simpa using (hgrad.sub (tendsto_const_nhds (x := Paper.parisiGradientBCF β μ))).norm
  have hc := tendsto_parisiCDFDistance_of_tendsto hμ
  have hbudget : Tendsto (fun i => β ^ 2 * Real.exp (β ^ 2) *
      (‖Paper.parisiGradientBCF β (μs i) - Paper.parisiGradientBCF β μ‖ +
        Paper.parisiCDFDistance (μs i) μ)) L (nhds 0) := by
    simpa using tendsto_const_nhds.mul (hn.add hc)
  intro ε hε
  filter_upwards [hbudget.eventually (eventually_lt_nhds hε)] with i hi ω t ht
  exact (selectedState_dist_le β h hβ (μs i) μ ω ht).trans_lt hi

/-- Weak overlap convergence implies pointwise convergence of the actual
same-Brownian selected state, with an arbitrary fixed initial field. -/
theorem tendsto_selectedStateReal_of_weak {ι : Type*} {L : Filter ι}
    [L.IsCountablyGenerated] (β h : ℝ) (hβ : β ≠ 0)
    (μs : ι → Paper.ParisiMeasure) (μ : Paper.ParisiMeasure)
    (hμ : Tendsto μs L (nhds μ)) (ω : Paper.BrownianSample) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    Tendsto (fun i => selectedParisiStateReal β h hβ (μs i) ω t) L
      (nhds (selectedParisiStateReal β h hβ μ ω t)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [selectedState_uniform_convergence_of_weak β h hβ μs μ hμ ε hε]
    with i hi
  simpa only [dist_eq_norm] using hi ω t ht

theorem measurable_selectedStateIto_time (β h : ℝ) (hβ : β ≠ 0)
    (μ : Paper.ParisiMeasure) (t : ℝ≥0) :
    Measurable (selectedParisiItoState β h hβ μ t) :=
  ((boundedDriftItoCharacteristics_selectedParisiState β h hβ μ).adapted_state t).measurable
    |>.mono (canonicalBrownianFiltration.le t) le_rfl

theorem measurable_selectedStateReal_time (β h : ℝ) (hβ : β ≠ 0)
    (μ : Paper.ParisiMeasure) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    Measurable (fun ω => selectedParisiStateReal β h hβ μ ω t) := by
  have hm := measurable_selectedStateIto_time β h hβ μ t.toNNReal
  have he : selectedParisiItoState β h hβ μ t.toNNReal =
      fun ω => selectedParisiStateReal β h hβ μ ω t := by
    funext ω
    rw [selectedParisiItoState_eq β h hβ μ
      (by simpa only [Real.coe_toNNReal _ ht.1] using ht.2),
      Real.coe_toNNReal _ ht.1]
  rw [he] at hm
  exact hm

/-- Actual bounded-continuous observable expectations converge. This is an
application of genuine dominated convergence to the constructed states. -/
theorem tendsto_integral_selectedStateReal_of_weak {ι : Type*} {L : Filter ι}
    [L.IsCountablyGenerated] (β h : ℝ) (hβ : β ≠ 0)
    (μs : ι → Paper.ParisiMeasure) (μ : Paper.ParisiMeasure)
    (hμ : Tendsto μs L (nhds μ)) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (ψ : ℝ → ℝ) (hψ : Continuous ψ) (C : ℝ) (hC : ∀ x, ‖ψ x‖ ≤ C) :
    Tendsto (fun i => ∫ ω, ψ (selectedParisiStateReal β h hβ (μs i) ω t)
        ∂canonicalBrownianMeasure) L
      (nhds (∫ ω, ψ (selectedParisiStateReal β h hβ μ ω t)
        ∂canonicalBrownianMeasure)) := by
  apply tendsto_integral_filter_of_dominated_convergence (bound := fun _ => C)
  · exact .of_forall fun i =>
      (hψ.measurable.comp (measurable_selectedStateReal_time β h hβ (μs i) ht)).aestronglyMeasurable
  · exact .of_forall fun _ => .of_forall fun ω => hC _
  · exact integrable_const C
  · exact .of_forall fun ω => hψ.continuousAt.tendsto.comp
      (tendsto_selectedStateReal_of_weak β h hβ μs μ hμ ω ht)

/-- The all-field weak endpoint law passage on the physical time strip.
No density, transition law, or state convergence is an extra assumption. -/
theorem tendsto_integral_selectedState_of_weak {ι : Type*} {L : Filter ι}
    [L.IsCountablyGenerated] (β h : ℝ) (hβ : β ≠ 0)
    (μs : ι → Paper.ParisiMeasure) (μ : Paper.ParisiMeasure)
    (hμ : Tendsto μs L (nhds μ)) (t : ℝ≥0) (ht : (t : ℝ) ≤ 1)
    (ψ : ℝ → ℝ) (hψ : Continuous ψ) (C : ℝ) (hC : ∀ x, ‖ψ x‖ ≤ C) :
    Tendsto (fun i => ∫ ω, ψ (selectedParisiItoState β h hβ (μs i) t ω)
        ∂canonicalBrownianMeasure) L
      (nhds (∫ ω, ψ (selectedParisiItoState β h hβ μ t ω)
        ∂canonicalBrownianMeasure)) := by
  have he (ν : Paper.ParisiMeasure) : selectedParisiItoState β h hβ ν t =
      fun ω => selectedParisiStateReal β h hβ ν ω t := by
    funext ω
    exact selectedParisiItoState_eq β h hβ ν ht ω
  simp_rw [he]
  exact tendsto_integral_selectedStateReal_of_weak β h hβ μs μ hμ
    ⟨t.coe_nonneg, ht⟩ ψ hψ C hC

end FourPapersCommon
