module
public import FRSB.ItoExpectationSource
public import FRSB.ItoSquareTest
public import Paper.ParisiGradientCells

@[expose] public section

/-! Finite-cell squared-gradient expectations on the actual optimal state. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter StochasticCalculus Paper
open scoped NNReal Topology
namespace FRSB
open SpinGlass.Targets

set_option maxHeartbeats 1000000 in
theorem canonicalParisiState_gradient_square_cell_bound
    (β h : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure) (v : ℝ → ℝ → ℝ)
    (hv : Continuous (Function.uncurry v)) (hvb : ∀ t x, ‖v t x‖ ≤ 1)
    (hvl : ∀ t, LipschitzWith 1 (v t))
    (a b : ℝ≥0) (hab : a < b) (hb1 : (b : ℝ) ≤ 1)
    {k : ℕ} (s : RSBScheme k) (j : ℕ) {m : ℝ} (hm : m ∈ Icc (0 : ℝ) 1)
    {eps : ℝ} (heps : 0 ≤ eps)
    (hclose : ∀ ω, ∀ t ∈ Icc (a : ℝ) (b : ℝ),
      ‖v t (canonicalParisiItoState β h μ v hv hvb hvl t.toNNReal ω) -
        parisiSlabGradient s β j m b t (canonicalParisiItoState β h μ v hv hvb hvl t.toNNReal ω)‖ ≤ eps) :
    ‖(∫ ω, parisiSlabGradient s β j m b b
          (canonicalParisiItoState β h μ v hv hvb hvl b ω)^2 ∂canonicalBrownianMeasure) -
        (∫ ω, parisiSlabGradient s β j m b a
          (canonicalParisiItoState β h μ v hv hvb hvl a ω)^2 ∂canonicalBrownianMeasure) -
        ∫ t in (a : ℝ)..(b : ℝ), ∫ ω, β^2 * parisiSlabHessian s β j m b t
          (canonicalParisiItoState β h μ v hv hvb hvl t.toNNReal ω)^2 ∂canonicalBrownianMeasure‖ ≤
      2 * β^2 * (∫ t in (a : ℝ)..(b : ℝ), |parisiCDF μ t - m|) +
        2 * β^2 * eps * ((b : ℝ)-a) := by
  let X := canonicalParisiItoState β h μ v hv hvb hvl
  let d := canonicalParisiItoDrift β h μ v hv hvb hvl
  let source : ℝ → BrownianSample → ℝ := fun t ω =>
    β^2 * parisiSlabHessian s β j m b t (X t.toNNReal ω)^2
  let err : ℝ → ℝ := fun t => 2*β^2*(|parisiCDF μ t-m|+eps)
  have hXm (t : ℝ≥0) : Measurable (X t) :=
    ((stronglyAdapted_canonicalParisiItoState β h μ v hv hvb hvl t).mono
      (canonicalBrownianFiltration.le t)).measurable
  have hsource : Measurable (Function.uncurry source) := by
    apply measurable_const.mul
    apply Measurable.pow_const
    have hmap := measurable_fst.prodMk
      ((measurable_canonicalParisiItoState β h μ v hv hvb hvl).comp
        (measurable_real_toNNReal.prodMap measurable_id))
    exact (continuous_parisiSlab s β j hm.1 b).2.2.measurable.comp hmap
  have hsourceb : ∀ t ω, ‖source t ω‖ ≤ β^2 := by
    intro t ω
    dsimp only [source]
    rw [norm_mul, Real.norm_of_nonneg (sq_nonneg β), norm_pow]
    exact (mul_le_mul_of_nonneg_left
      (pow_le_one₀ (norm_nonneg _) (norm_parisiSlabHessian_le_one s β j hm b t _))
      (sq_nonneg β)).trans_eq (by ring)
  have herr : IntervalIntegrable err volume a b :=
    ((((parisiCDF_monotone μ).intervalIntegrable (a := a) (b := b)).sub
      intervalIntegrable_const).norm.add intervalIntegrable_const).const_mul _
  have hpoint (c : ℝ) (hc : c ∈ Ioo (a : ℝ) (b : ℝ)) :
      ‖(∫ ω, parisiSlabGradient s β j m b
          (hjbTimeCap c (((b : ℝ)-c)/2) b) (X b ω)^2 ∂canonicalBrownianMeasure) -
        (∫ ω, parisiSlabGradient s β j m b a (X a ω)^2 ∂canonicalBrownianMeasure) -
        ∫ t in (a : ℝ)..(b : ℝ), ∫ ω, source t ω ∂canonicalBrownianMeasure‖ ≤
      (∫ t in (a : ℝ)..(b : ℝ), err t) + 34*β^2*((b : ℝ)-c) := by
    let δ := ((b : ℝ)-c)/2
    have hδ : 0 < δ := by dsimp [δ]; linarith [hc.2]
    have hcb : c+δ ≤ (b : ℝ) := by dsimp [δ]; linarith [hc.2]
    let g := hjbSlabGradientTest s β j m b c δ
    let f := itoSquareTest g
    have hg := continuous_hjbSlabGradientTest s β j hm.1 b c δ
    have hgt : ∀ x, Differentiable ℝ (fun t => g t x) := fun x t =>
      (hasDerivAt_hjbSlabGradientTest_time s β hβ j hm b c hδ hcb t x).differentiableAt
    have hgs := contDiff_hjbSlabGradientTest_spatial s β j hm b c δ
    have hgd : ∀ t, Differentiable ℝ (g t) := fun t => (hgs t).differentiable (by norm_num)
    have hgx := continuous_hjbSlabGradientTest_spaceDerivative s β j hm.1 b c δ
    have hgxx := continuous_hjbSlabGradientTest_spaceSecondDerivative s β j hm b c δ
    have hgdt := continuous_hjbSlabGradientTest_timeDerivative s β hβ j hm b c hδ hcb
    let E : ℝ → ℝ := fun t => err t + parisiGradientTailError (34*β^2) c t
    have hE : IntervalIntegrable E volume a b := herr.add
      ((parisiGradientTailError_monotone (by positivity : 0 ≤ 34*β^2) c).intervalIntegrable)
    have hgen : ∀ ω, ∀ t ∈ Icc (a : ℝ) (b : ℝ),
        ‖hjbGenerator X d β f t ω - source t ω‖ ≤ E t := by
      intro ω t ht
      have ht1 : t ∈ Icc (0 : ℝ) 1 := ⟨a.coe_nonneg.trans ht.1,ht.2.trans hb1⟩
      have hdr : d t.toNNReal ω = β^2 * parisiCDF μ t * v t (X t.toNNReal ω) := by
        simp only [d,canonicalParisiItoDrift,Real.coe_toNNReal t ht1.1,ite_eq_left ht1.2,X]
      have hgabs : ‖g t (X t.toNNReal ω)‖ ≤ 1 :=
        norm_hjbSlabGradientTest_le_one s β j hm b c δ t _
      rw [itoSquareTest_generator X d β g hgt hgs]
      by_cases htc : t ≤ c
      · have hge : ‖hjbGenerator X d β g t ω‖ ≤ β^2*(|parisiCDF μ t-m|+eps) := by
          unfold hjbGenerator
          rw [hdr]
          exact hjbSlabGradientTest_generator_norm_le s β hβ j hm b c hδ hcb t _
            (parisiCDF μ t) (v t _) eps htc (hvb _ _) (hclose ω t ht)
        have hsp : itoSpaceDerivative g t (X t.toNNReal ω) =
            parisiSlabHessian s β j m b t (X t.toNNReal ω) := by
          simp only [g,itoSpaceDerivative,deriv_hjbSlabGradientTest_spatial,
            hjbTimeCap_of_le c δ t htc]
        rw [hsp]
        change ‖2*g t (X t.toNNReal ω)*hjbGenerator X d β g t ω +
          β^2*parisiSlabHessian s β j m b t (X t.toNNReal ω)^2 -
          β^2*parisiSlabHessian s β j m b t (X t.toNNReal ω)^2‖ ≤ E t
        rw [add_sub_cancel_right,norm_mul,norm_mul,show ‖(2:ℝ)‖=2 by norm_num]
        have hh := mul_le_mul (mul_le_mul_of_nonneg_left hgabs (by norm_num : (0:ℝ)≤2)) hge
          (norm_nonneg _) (by norm_num)
        simpa only [E,err,parisiGradientTailError,ite_eq_left htc,add_zero,mul_one,
          mul_assoc] using hh
      · have hge : ‖hjbGenerator X d β g t ω‖ ≤ 16*β^2 := by
          unfold hjbGenerator
          rw [hdr]
          exact hjbSlabGradientTest_generator_norm_le_sixteen s β hβ j hm b c hδ hcb
            t _ (parisiCDF μ t) (v t _) ⟨parisiCDF_nonneg μ t,parisiCDF_le_one μ t⟩ (hvb _ _)
        have hfirst : ‖2*g t (X t.toNNReal ω)*hjbGenerator X d β g t ω‖ ≤ 32*β^2 := by
          rw [norm_mul,norm_mul,show ‖(2:ℝ)‖=2 by norm_num]
          exact (mul_le_mul (mul_le_mul_of_nonneg_left hgabs (by norm_num : (0:ℝ)≤2)) hge
            (norm_nonneg _) (by norm_num)).trans_eq (by ring)
        have hquad : ‖β^2*itoSpaceDerivative g t (X t.toNNReal ω)^2‖ ≤ β^2 := by
          rw [norm_mul,Real.norm_of_nonneg (sq_nonneg β),norm_pow]
          exact (mul_le_mul_of_nonneg_left (pow_le_one₀ (norm_nonneg _)
            (norm_hjbSlabGradientTest_spaceDerivative_le_one s β j hm b c δ t _))
            (sq_nonneg β)).trans_eq (by ring)
        have htotal := (norm_sub_le _ _).trans (add_le_add
          ((norm_add_le _ _).trans (add_le_add hfirst hquad)) (hsourceb t ω))
        exact htotal.trans (by
          dsimp [E,parisiGradientTailError,err]
          rw [ite_eq_right htc]
          have he0 : 0 ≤ 2*β^2*(|parisiCDF μ t-m|+eps) := by positivity
          linarith)
    have hfi (r : ℝ≥0) : Integrable (fun ω => f r (X r ω)) canonicalBrownianMeasure := by
      apply (integrable_const (1:ℝ)).mono'
        ((hg.pow 2).measurable.comp (measurable_const.prodMk (hXm r))).aestronglyMeasurable
      exact .of_forall fun ω => by
        change ‖g r (X r ω)^2‖ ≤ 1
        rw [norm_pow]
        exact pow_le_one₀ (norm_nonneg _) (norm_hjbSlabGradientTest_le_one s β j hm b c δ r _)
    have hh := ito_expectation_source_error
      (boundedDriftItoCharacteristics_canonicalParisiState β h μ v hv hvb hvl)
      f (continuous_itoSquareTest g hg) (differentiable_itoSquareTest_time g hgt)
      (contDiff_itoSquareTest_spatial g hgs)
      (continuous_itoSquareTest_timeDerivative g hg hgt hgdt)
      (continuous_itoSquareTest_spaceDerivative g hg hgd hgx)
      (continuous_itoSquareTest_spaceSecondDerivative g hg hgs hgx hgxx)
      a b hab.le 2 (fun t _ x => by
        simpa using norm_itoSquareTest_spaceDerivative_le g hgd
          (fun t x => norm_hjbSlabGradientTest_le_one s β j hm b c δ t x)
          (fun t x => norm_hjbSlabGradientTest_spaceDerivative_le_one s β j hm b c δ t x) t x)
      source hsource (β^2) hsourceb E hE hgen (hfi a) (hfi b)
    have htail : IntervalIntegrable (parisiGradientTailError (34*β^2) c) volume a b :=
      (parisiGradientTailError_monotone (by positivity) c).intervalIntegrable
    dsimp only [E] at hh
    rw [intervalIntegral.integral_add herr htail,
      integral_parisiGradientTailError (by positivity : 0≤34*β^2) hc.1.le hc.2.le] at hh
    simpa only [f,itoSquareTest,g,hjbSlabGradientTest,δ,
      hjbTimeCap_of_le c (((b:ℝ)-c)/2) a hc.1.le] using hh
  have hlim : Tendsto (fun c : ℝ => ∫ ω, parisiSlabGradient s β j m b
      (hjbTimeCap c (((b:ℝ)-c)/2) b) (X b ω)^2 ∂canonicalBrownianMeasure)
      (nhdsWithin (b:ℝ) (Iio (b:ℝ)))
      (nhds (∫ ω, parisiSlabGradient s β j m b b (X b ω)^2 ∂canonicalBrownianMeasure)) := by
    have hmeas : ∀ᶠ c in nhdsWithin (b:ℝ) (Iio (b:ℝ)), AEStronglyMeasurable
        (fun ω => parisiSlabGradient s β j m b (hjbTimeCap c (((b:ℝ)-c)/2) b) (X b ω)^2)
        canonicalBrownianMeasure := .of_forall fun c =>
      (((continuous_parisiSlab s β j hm.1 b).2.1.pow 2).measurable.comp
        (measurable_const.prodMk (hXm b))).aestronglyMeasurable
    apply tendsto_integral_filter_of_dominated_convergence (fun _ => (1:ℝ)) hmeas
    · exact .of_forall fun c => .of_forall fun ω => by
        rw [norm_pow]
        exact pow_le_one₀ (norm_nonneg _) (by
          simpa only [Real.norm_eq_abs] using
            (abs_parisiSlabGradient_le_one s β j hm b (hjbTimeCap c (((b:ℝ)-c)/2) b) (X b ω)))
    · exact integrable_const 1
    · exact .of_forall fun ω => (((continuous_parisiSlab s β j hm.1 b).2.1.continuousAt.tendsto.comp
        ((tendsto_hjbTerminalCap b).prodMk_nhds tendsto_const_nhds))).pow 2
  have hright : Tendsto (fun c : ℝ => (∫ t in (a:ℝ)..(b:ℝ),err t)+34*β^2*((b:ℝ)-c))
      (nhdsWithin (b:ℝ) (Iio (b:ℝ))) (nhds (∫ t in (a:ℝ)..(b:ℝ),err t)) := by
    have hi : Tendsto (fun c:ℝ=>c) (nhdsWithin (b:ℝ) (Iio (b:ℝ))) (nhds (b:ℝ)) := nhdsWithin_le_nhds
    simpa using (tendsto_const_nhds (x := ∫ t in (a:ℝ)..(b:ℝ),err t)).add
      (((tendsto_const_nhds (x := (b:ℝ))).sub hi).const_mul (34*β^2))
  have hh := le_of_tendsto_of_tendsto
    ((hlim.sub tendsto_const_nhds).sub tendsto_const_nhds).norm hright (by
      filter_upwards [Ioo_mem_nhdsLT (NNReal.coe_lt_coe.mpr hab)] with c hc
      exact hpoint c hc)
  have herror : (∫ t in (a:ℝ)..(b:ℝ),err t) = 2*β^2*
      (∫ t in (a:ℝ)..(b:ℝ),|parisiCDF μ t-m|)+2*β^2*eps*((b:ℝ)-a) := by
    dsimp [err]
    rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_add]
    · simp only [intervalIntegral.integral_const,smul_eq_mul]
      ring
    · exact (((parisiCDF_monotone μ).intervalIntegrable).sub intervalIntegrable_const).norm
    · exact intervalIntegrable_const
  simpa only [X,source,herror] using hh

end FRSB
