module
public import FourPapersCommon.AllFieldGrid
public import FRSB.GammaIdentity
public import FRSB.UniformSpatialRegularity
public import FRSB.ParisiGridTopology

@[expose] public section

/-! The actual first Gamma derivative, obtained from finite-cell centered Itô
identities and genuine grid approximation. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter StochasticCalculus Paper
open scoped NNReal Topology
namespace FourPapersCommon
open FRSB
set_option maxHeartbeats 1000000

abbrev fieldGamma (β h : ℝ) (hβ : β ≠ 0) (μ : Paper.ParisiMeasure) : ℝ → ℝ :=
  selectedParisiSecondMoment β h hβ μ

theorem fieldGamma_eq_selectedSecondMoment (β h : ℝ) (hβ : β ≠ 0)
    (μ : Paper.ParisiMeasure) (s : ℝ) :
    fieldGamma β h hβ μ s = selectedParisiSecondMoment β h hβ μ s := rfl


 theorem gridGamma_sub_Gamma_norm_le (β h : ℝ) (hβ : β ≠ 0) (μ : Paper.ParisiMeasure)
    (n : ℕ) {t : ℝ} (ht : t∈Icc (0:ℝ) 1) :
    ‖gridGamma β h hβ μ n t-fieldGamma β h hβ μ t‖ ≤ 2*parisiHJBGradientError β μ n := by
  have hm : Measurable (selectedParisiItoState β h hβ μ t.toNNReal) :=
    (boundedDriftItoCharacteristics_selectedParisiState β h hβ μ).adapted_state t.toNNReal
      |>.measurable |>.mono (canonicalBrownianFiltration.le t.toNNReal) le_rfl
  have he : fieldGamma β h hβ μ t = ∫ ω,parisiGradient β μ
      (t,selectedParisiItoState β h hβ μ t.toNNReal ω)^2 ∂canonicalBrownianMeasure := by
    rw [fieldGamma_eq_selectedSecondMoment β h hβ μ]
    unfold selectedParisiSecondMoment
    apply integral_congr_ae
    exact .of_forall fun ω => by
      dsimp only
      rw [selectedParisiItoState_eq β h hβ μ
        (by simpa only [Real.coe_toNNReal _ ht.1] using ht.2),Real.coe_toNNReal _ ht.1]
  rw [he]
  unfold gridGamma
  apply norm_integral_sq_sub_sq_le canonicalBrownianMeasure
    (fun ω=>parisiFiniteGradient (parisiGridRSBScheme μ n) β
      (t,selectedParisiItoState β h hβ μ t.toNNReal ω))
    (fun ω=>parisiGradient β μ (t,selectedParisiItoState β h hβ μ t.toNNReal ω))
    ((continuous_parisiFiniteGradient _ _).measurable.comp (measurable_const.prodMk hm))
    ((continuous_parisiGradient β μ).measurable.comp (measurable_const.prodMk hm))
    (fun ω=>norm_parisiFiniteGradient_le_one _ _ _) (fun ω=>norm_parisiGradient_le_one _ _ _)
  intro ω
  rw [norm_sub_rev]
  exact parisiHJBGradientError_bound β μ n t _

 theorem gammaCurvatureSource_sub_norm_le (β h : ℝ) (hβ : β ≠ 0) (μ ν : Paper.ParisiMeasure)
    (t : ℝ) :
    ‖gammaCurvatureSource β h hβ μ ν t-gammaCurvatureSource β h hβ μ μ t‖ ≤
      2*β^2*‖bcfSpatialDerivative (parisiGradientBCF β ν) 1-
        bcfSpatialDerivative (parisiGradientBCF β μ) 1‖ := by
  let X := selectedParisiItoState β h hβ μ t.toNNReal
  have hm : Measurable (selectedParisiItoState β h hβ μ t.toNNReal) :=
    (boundedDriftItoCharacteristics_selectedParisiState β h hβ μ).adapted_state t.toNNReal
      |>.measurable |>.mono (canonicalBrownianFiltration.le t.toNNReal) le_rfl
  have hmν : Measurable (fun ω : Paper.BrownianSample => parisiSpatialJet β ν 2 t (X ω)) := by
    simp only [parisiSpatialJet_two]
    exact (continuous_parisiHessian_all β ν).measurable.comp (measurable_const.prodMk hm)
  have hmμ : Measurable (fun ω : Paper.BrownianSample => parisiSpatialJet β μ 2 t (X ω)) := by
    simp only [parisiSpatialJet_two]
    exact (continuous_parisiHessian_all β μ).measurable.comp (measurable_const.prodMk hm)
  have hh := norm_integral_sq_sub_sq_le canonicalBrownianMeasure
    (fun ω=>parisiSpatialJet β ν 2 t (X ω)) (fun ω=>parisiSpatialJet β μ 2 t (X ω))
    hmν hmμ
    (fun ω=>by rw [parisiSpatialJet_two];exact norm_parisiHessian_le_one_all _ _ _)
    (fun ω=>by rw [parisiSpatialJet_two];exact norm_parisiHessian_le_one_all _ _ _)
    ‖bcfSpatialDerivative (parisiGradientBCF β ν) 1-bcfSpatialDerivative (parisiGradientBCF β μ) 1‖
    (fun ω=>by
      change ‖parisiSlabExtend (by norm_num : (0:ℝ)≤1)
        (bcfSpatialDerivative (parisiGradientBCF β ν) 1) (t,X ω)-
        parisiSlabExtend (by norm_num : (0:ℝ)≤1)
          (bcfSpatialDerivative (parisiGradientBCF β μ) 1) (t,X ω)‖ ≤ _
      exact norm_parisiSlabExtend_sub_le (by norm_num) _ _ (t,X ω))
  unfold gammaCurvatureSource
  rw [integral_const_mul,integral_const_mul,← mul_sub,norm_mul,
    Real.norm_of_nonneg (sq_nonneg β)]
  exact (mul_le_mul_of_nonneg_left hh (sq_nonneg β)).trans_eq (by ring)

 theorem gridGamma_tail_remainder_le (β h : ℝ) (hβ : β ≠ 0) (μ : Paper.ParisiMeasure)
    (n : ℕ) {s : ℝ} (hs : s∈Icc (0:ℝ) 1) :
    ‖gridGamma β h hβ μ n 1-gridGamma β h hβ μ n s-
      ∫ t in s..1,gammaCurvatureSource β h hβ μ (parisiGridMeasure μ n) t‖ ≤
      2*β^2*(parisiCDFDistance μ (parisiGridMeasure μ n)+parisiHJBGradientError β μ n) := by
  let T := parisiGradientMeshTime n s
  let S := gammaCurvatureSource β h hβ μ (parisiGridMeasure μ n)
  let F : ℕ→ℝ := fun i=>gridGamma β h hβ μ n (T i)-∫ t in s..T i,S t
  have hS : Continuous S := continuous_gammaCurvatureSource β h hβ μ _
  have htel := parisiGradientMesh_norm_telescope F (fun t=>2*parisiGradientGridError β μ n t)
    T (n+1) (fun i _ => (parisiGradientGridError_intervalIntegrable β μ n _ _).const_mul 2) (by
      intro i hi
      rcases parisiGradientMeshTime_step_cases n s i with heq | hlt
      · change T i=T (i+1) at heq
        simp only [F,heq,sub_self,intervalIntegral.integral_same,norm_zero,le_refl]
      · have hia := parisiGradientMeshTime_mem n hs (by omega : i≤n+1)
        have hib := parisiGradientMeshTime_mem n hs (by omega : i+1≤n+1)
        let a : ℝ≥0 := ⟨T i,hia.1⟩
        let b : ℝ≥0 := ⟨T (i+1),hib.1⟩
        have hab : a<b := NNReal.coe_lt_coe.mp hlt
        have hcell := parisiGradientMeshTime_cell_subset n s i hlt
        have hh := gradient_square_grid_cell_bound β h hβ μ n i hi a b hab
          (hcell ⟨le_rfl,hlt.le⟩) (parisiGradientMeshTime_step_lt_terminal n s i hlt)
        have heF : F (i+1)-F i = gridGamma β h hβ μ n b-gridGamma β h hβ μ n a-
            ∫ t in (a:ℝ)..(b:ℝ),S t := by
          change (gridGamma β h hβ μ n (T (i+1))-(∫ t in s..T (i+1),S t))-
            (gridGamma β h hβ μ n (T i)-(∫ t in s..T i,S t)) =
              gridGamma β h hβ μ n (T (i+1))-gridGamma β h hβ μ n (T i)-
                ∫ t in T i..T (i+1),S t
          have hii : (∫ t in s..T (i+1),S t)-(∫ t in s..T i,S t)=
              ∫ t in T i..T (i+1),S t :=
            intervalIntegral.integral_interval_sub_left (hS.intervalIntegrable _ _)
              (hS.intervalIntegrable _ _)
          linarith
        rw [heF]
        exact hh)
  have hfull : (∫ t in s..1,2*parisiGradientGridError β μ n t) ≤
      2*β^2*(parisiCDFDistance μ (parisiGridMeasure μ n)+parisiHJBGradientError β μ n) := by
    have hh := parisiGradientMesh_integral_le_full hs
      ((parisiGradientGridError_intervalIntegrable β μ n 0 1).const_mul 2)
      (fun t=>mul_nonneg (by norm_num) (parisiGradientGridError_nonneg _ _ _ _))
    apply hh.trans_eq
    simp only [parisiGradientGridError,parisiCDFDistance]
    simp_rw [← mul_assoc]
    rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_add]
    · simp
    · exact parisiCDF_abs_diff_intervalIntegrable _ _ _ _
    · exact intervalIntegrable_const
  simp only [T,parisiGradientMeshTime_terminal n hs.2,parisiGradientMeshTime_zero n hs.1] at htel
  have hh : ‖(gridGamma β h hβ μ n 1-(∫ t in s..1,S t))-gridGamma β h hβ μ n s‖ ≤
      2*β^2*(parisiCDFDistance μ (parisiGridMeasure μ n)+parisiHJBGradientError β μ n) := by
    simpa only [F,T,parisiGradientMeshTime_terminal n hs.2,parisiGradientMeshTime_zero n hs.1,
      intervalIntegral.integral_same,sub_zero] using htel.trans hfull
  have healg : (gridGamma β h hβ μ n 1-(∫ t in s..1,S t))-gridGamma β h hβ μ n s =
      gridGamma β h hβ μ n 1-gridGamma β h hβ μ n s-(∫ t in s..1,S t) := by ring
  rw [healg] at hh
  exact hh


/-- The finite-grid source converges uniformly in time, along the fixed actual
state, to the actual curvature-square source. -/
theorem tendsto_grid_curvature_integral (β h : ℝ) (hβ : β ≠ 0) (μ : Paper.ParisiMeasure)
    {s : ℝ} (hs : s∈Icc (0:ℝ) 1) :
    Tendsto (fun n=>∫ t in s..1,gammaCurvatureSource β h hβ μ (parisiGridMeasure μ n) t)
      atTop (nhds (∫ t in s..1,gammaCurvatureSource β h hβ μ μ t)) := by
  let E : ℕ→ℝ := fun n=>2*β^2*‖bcfSpatialDerivative (parisiGradientBCF β (parisiGridMeasure μ n)) 1-
    bcfSpatialDerivative (parisiGradientBCF β μ) 1‖
  have hE : Tendsto E atTop (nhds 0) := by
    have hh := (tendsto_spatialDerivativeBCF_of_weak β 1 μ _ (tendsto_parisiGridMeasure μ)).sub_const
      (bcfSpatialDerivative (parisiGradientBCF β μ) 1) |>.norm
    simpa only [sub_self,norm_zero,mul_zero,E] using hh.const_mul (2*β^2)
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [hE.eventually (eventually_lt_nhds hε)] with n hn
  rw [dist_eq_norm,← intervalIntegral.integral_sub
    ((continuous_gammaCurvatureSource β h hβ μ _).intervalIntegrable _ _)
    ((continuous_gammaCurvatureSource β h hβ μ _).intervalIntegrable _ _)]
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const (a:=s) (b:=1)
    (fun t _=>gammaCurvatureSource_sub_norm_le β h hβ μ (parisiGridMeasure μ n) t)
  apply hh.trans_lt
  rw [abs_of_nonneg (sub_nonneg.mpr hs.2)]
  exact (mul_le_mul_of_nonneg_left (by linarith [hs.1] : 1-s≤1)
    (by dsimp [E];positivity : 0≤E n)).trans_lt (by simpa only [mul_one,E] using hn)

/-- The genuine optimal diffusion Gamma identity for an arbitrary Parisi
measure. All finite-grid PDE, stochastic centering, and approximation inputs
have been discharged. -/
theorem Gamma_tail_integral (β h : ℝ) (hβ : β ≠ 0) (μ : Paper.ParisiMeasure)
    {s : ℝ} (hs : s∈Icc (0:ℝ) 1) :
    fieldGamma β h hβ μ 1-fieldGamma β h hβ μ s = ∫ t in s..1,gammaCurvatureSource β h hβ μ μ t := by
  have hG (t : ℝ) (ht:t∈Icc (0:ℝ) 1) :
      Tendsto (fun n=>gridGamma β h hβ μ n t) atTop (nhds (fieldGamma β h hβ μ t)) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    have he := (tendsto_parisiHJBGradientError β hβ μ).const_mul (2:ℝ)
    simp only [mul_zero] at he
    filter_upwards [he.eventually (eventually_lt_nhds hε)] with n hn
    rw [dist_eq_norm]
    exact (gridGamma_sub_Gamma_norm_le β h hβ μ n ht).trans_lt hn
  have hleft := ((hG 1 ⟨by norm_num,le_rfl⟩).sub (hG s hs)).sub
    (tendsto_grid_curvature_integral β h hβ μ hs) |>.norm
  have hright : Tendsto (fun n=>2*β^2*(parisiCDFDistance μ (parisiGridMeasure μ n)+
      parisiHJBGradientError β μ n)) atTop (nhds 0) := by
    simpa only [zero_add,mul_zero] using
      ((tendsto_parisiCDFDistance_grid μ).add (tendsto_parisiHJBGradientError β hβ μ)).const_mul (2*β^2)
  have hh := le_of_tendsto_of_tendsto hleft hright
    (.of_forall fun n=>gridGamma_tail_remainder_le β h hβ μ n hs)
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hh (norm_nonneg _)))

 theorem Gamma_integral (β h : ℝ) (hβ : β ≠ 0) (μ : Paper.ParisiMeasure)
    {t : ℝ} (ht : t∈Icc (0:ℝ) 1) :
    fieldGamma β h hβ μ t = fieldGamma β h hβ μ 0+∫ s in 0..t,gammaCurvatureSource β h hβ μ μ s := by
  have h0 := Gamma_tail_integral β h hβ μ ⟨le_rfl,by norm_num⟩
  have ht' := Gamma_tail_integral β h hβ μ ht
  have hi := intervalIntegral.integral_add_adjacent_intervals (μ:=volume)
    ((continuous_gammaCurvatureSource β h hβ μ μ).intervalIntegrable 0 t)
    ((continuous_gammaCurvatureSource β h hβ μ μ).intervalIntegrable t 1)
  linarith

/-- The paper's actual Gamma derivative at every interior physical time. -/
theorem hasDerivAt_Gamma (β h : ℝ) (hβ : β ≠ 0) (μ : Paper.ParisiMeasure)
    {t : ℝ} (ht:t∈Ioo (0:ℝ) 1) :
    HasDerivAt (fieldGamma β h hβ μ) (β^2*fieldCurvatureMoment2 β h hβ μ t) t := by
  have hc := continuous_gammaCurvatureSource β h hβ μ μ
  have hd := (intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 t)
    (hc.stronglyMeasurableAtFilter volume (nhds t)) hc.continuousAt).const_add (fieldGamma β h hβ μ 0)
  have he : fieldGamma β h hβ μ =ᶠ[nhds t] (fun r=>fieldGamma β h hβ μ 0+∫ s in 0..r,gammaCurvatureSource β h hβ μ μ s) := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with r hr
    exact Gamma_integral β h hβ μ ⟨hr.1.le,hr.2.le⟩
  rw [← gammaCurvatureSource_self β h hβ μ ⟨ht.1.le,ht.2.le⟩]
  exact hd.congr_of_eventuallyEq he

/-- The derivative formula includes genuine one-sided derivatives at both
physical endpoints. -/
theorem hasDerivWithinAt_Gamma (β h : ℝ) (hβ : β ≠ 0) (μ : Paper.ParisiMeasure)
    {t : ℝ} (ht:t∈Icc (0:ℝ) 1) :
    HasDerivWithinAt (fieldGamma β h hβ μ) (β^2*fieldCurvatureMoment2 β h hβ μ t) (Icc (0:ℝ) 1) t := by
  have hc := continuous_gammaCurvatureSource β h hβ μ μ
  have hd := (intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 t)
    (hc.stronglyMeasurableAtFilter volume (nhds t)) hc.continuousAt).const_add (fieldGamma β h hβ μ 0)
  rw [← gammaCurvatureSource_self β h hβ μ ht]
  exact hd.hasDerivWithinAt.congr_of_mem (fun r hr=>Gamma_integral β h hβ μ hr) ht

/-- Gamma is C¹ on the entire closed physical interval. -/
theorem contDiffOn_Gamma_one (β h : ℝ) (hβ : β ≠ 0) (μ : Paper.ParisiMeasure) :
    ContDiffOn ℝ 1 (fieldGamma β h hβ μ) (Icc (0:ℝ) 1) := by
  let f : ℝ→ℝ := fun t=>fieldGamma β h hβ μ 0+∫ s in 0..t,gammaCurvatureSource β h hβ μ μ s
  have hc := continuous_gammaCurvatureSource β h hβ μ μ
  have hd (t:ℝ) : HasDerivAt f (gammaCurvatureSource β h hβ μ μ t) t :=
    (intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 t)
      (hc.stronglyMeasurableAtFilter volume (nhds t)) hc.continuousAt).const_add _
  have hf : ContDiff ℝ 1 f := by
    rw [contDiff_one_iff_deriv]
    refine ⟨fun t=>(hd t).differentiableAt,?_⟩
    have he : deriv f=gammaCurvatureSource β h hβ μ μ := funext fun t=>(hd t).deriv
    rw [he]
    exact hc
  exact hf.contDiffOn.congr fun t ht=>Gamma_integral β h hβ μ ht

end FourPapersCommon
