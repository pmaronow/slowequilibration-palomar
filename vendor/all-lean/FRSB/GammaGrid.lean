module
public import FRSB.GammaCells
public import FRSB.GridMeasureIdentification
public import FRSB.FiniteTimeHierarchy
public import FRSB.OptimalCurvatureMoment
public import Paper.ParisiGradientGrid
public import Paper.ParisiGradientMesh

@[expose] public section

/-! Actual finite-grid squared-gradient Itô estimates and genuine curvature sources. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter StochasticCalculus Paper
open scoped NNReal Topology
namespace FRSB
set_option maxHeartbeats 1000000

 def gammaCurvatureSource (β : ℝ) (hβ : β ≠ 0) (μ ν : ParisiMeasure) (t : ℝ) : ℝ :=
  ∫ ω, β^2 * parisiSpatialJet β ν 2 t (selectedParisiItoState β 0 hβ μ t.toNNReal ω)^2
    ∂canonicalBrownianMeasure

 def gridGamma (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure) (n : ℕ) (t : ℝ) : ℝ :=
  ∫ ω, parisiFiniteGradient (parisiGridRSBScheme μ n) β
    (t,selectedParisiItoState β 0 hβ μ t.toNNReal ω)^2 ∂canonicalBrownianMeasure

 theorem continuous_gammaCurvatureSource (β : ℝ) (hβ : β ≠ 0) (μ ν : ParisiMeasure) :
    Continuous (gammaCurvatureSource β hβ μ ν) := by
  unfold gammaCurvatureSource
  simp only [parisiSpatialJet_two]
  apply continuous_of_dominated (μ := canonicalBrownianMeasure)
    (F := fun (t : ℝ) ω => β^2*parisiHessian β ν
      (t,selectedParisiItoState β 0 hβ μ t.toNNReal ω)^2) (bound := fun _ => β^2)
  · intro t
    have hm : Measurable (selectedParisiItoState β 0 hβ μ t.toNNReal) :=
      (boundedDriftItoCharacteristics_selectedParisiState β 0 hβ μ).adapted_state t.toNNReal
        |>.measurable |>.mono (canonicalBrownianFiltration.le t.toNNReal) le_rfl
    exact (measurable_const.mul (((continuous_parisiHessian_all β ν).measurable.comp
      (measurable_const.prodMk hm)).pow_const 2)).aestronglyMeasurable
  · intro t
    exact .of_forall fun ω => by
      rw [norm_mul,Real.norm_of_nonneg (sq_nonneg β),norm_pow]
      exact (mul_le_mul_of_nonneg_left (pow_le_one₀ (norm_nonneg _)
        (norm_parisiHessian_le_one_all β ν _)) (sq_nonneg β)).trans_eq (by ring)
  · exact integrable_const (β^2)
  · exact .of_forall fun ω => (((continuous_parisiHessian_all β ν).comp
      (continuous_id.prodMk (((boundedDriftItoCharacteristics_selectedParisiState β 0 hβ μ).continuous_state ω).comp
        continuous_real_toNNReal))).pow 2).const_mul _

 theorem gammaCurvatureSource_self (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    gammaCurvatureSource β hβ μ μ t = β^2*curvatureMoment2 β μ t := by
  unfold gammaCurvatureSource curvatureMoment2
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact .of_forall fun ω => by
    dsimp only
    rw [selectedParisiItoState_eq β 0 hβ μ
      (by simpa only [Real.coe_toNNReal _ ht.1] using ht.2),Real.coe_toNNReal _ ht.1]
    rfl

 theorem gradient_square_grid_cell_bound
    (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure) (n i : ℕ) (hi : i < n+1)
    (a b : ℝ≥0) (hab : a < b)
    (ha : (a:ℝ) ∈ Icc (hjbGridTime n i) (hjbGridTime n (i+1)))
    (hb : (b:ℝ) = hjbGridTime n (i+1)) :
    ‖gridGamma β hβ μ n b - gridGamma β hβ μ n a -
      ∫ t in (a:ℝ)..(b:ℝ), gammaCurvatureSource β hβ μ (parisiGridMeasure μ n) t‖ ≤
      ∫ t in (a:ℝ)..(b:ℝ), 2*parisiGradientGridError β μ n t := by
  let s := parisiGridRSBScheme μ n
  let X := selectedParisiItoState β 0 hβ μ
  let v := fun t x => parisiGradient β μ (t,x)
  let m := s.m (i+1)
  have hm : m ∈ Icc (0:ℝ) 1 := ⟨s.m_nonneg (by omega),s.m_le_one (by omega)⟩
  have hb1 : (b:ℝ) ≤ 1 := hb ▸ hjbGridTime_le_one n (i+1) (by omega)
  have hcell (t:ℝ) (ht:t∈Icc (a:ℝ) (b:ℝ)) :
      t∈Icc (hjbGridTime n i) (hjbGridTime n (i+1)) := ⟨ha.1.trans ht.1,ht.2.trans_eq hb⟩
  have hclose : ∀ ω, ∀ t∈Icc (a:ℝ) (b:ℝ),
      ‖v t (X t.toNNReal ω)-parisiSlabGradient s β (n+1-i) m b t (X t.toNNReal ω)‖ ≤
        parisiHJBGradientError β μ n := by
    intro ω t ht
    have hh := parisiHJBGradientError_bound β μ n t (X t.toNNReal ω)
    rw [hjbGrid_cell_gradient μ n β i hi t _ (hcell t ht)] at hh
    simpa only [v,s,m,hb] using hh
  have hh := canonicalParisiState_gradient_square_cell_bound β 0 hβ μ v
    (continuous_parisiGradient β μ) (fun t x=>norm_parisiGradient_le_one β μ (t,x))
    (lipschitzWith_parisiGradient β hβ μ) a b hab hb1 s (n+1-i) hm
    (parisiHJBGradientError_nonneg β μ n) hclose
  have hgrad (r:ℝ≥0) (hr:(r:ℝ)∈Icc (hjbGridTime n i) (hjbGridTime n (i+1))) (ω:BrownianSample) :
      parisiSlabGradient s β (n+1-i) m b r (X r ω) =
        parisiFiniteGradient s β (r,X r ω) := by
    simpa only [s,m,hb] using (hjbGrid_cell_gradient μ n β i hi r (X r ω) hr).symm
  have heSource : (∫ t in (a:ℝ)..(b:ℝ), ∫ ω, β^2*parisiSlabHessian s β (n+1-i) m b t
      (X t.toNNReal ω)^2 ∂canonicalBrownianMeasure) =
      ∫ t in (a:ℝ)..(b:ℝ),gammaCurvatureSource β hβ μ (parisiGridMeasure μ n) t := by
    apply intervalIntegral.integral_congr_uIoo
    rw [uIoo_of_le (NNReal.coe_lt_coe.mpr hab).le]
    intro t ht
    obtain ⟨hq0,hq1⟩ := hjbGrid_cell_q μ n i hi
    have hq : s.q (i+1)<s.q (i+1+1) := by
      simpa only [s,hq0,show i+1+1=i+2 by omega,hq1] using hjbGridTime_step_lt n i
    have htc : t∈Icc (s.q (i+1)) (s.q (i+1+1)) := by
      simpa only [s,hq0,show i+1+1=i+2 by omega,hq1] using hcell t ⟨ht.1.le,ht.2.le⟩
    dsimp only [gammaCurvatureSource]
    apply integral_congr_ae
    exact .of_forall fun ω => by
      have hj := (finiteCell_jet_one_two s β hβ (by omega) hq htc (X t.toNNReal ω)).2
      rw [parisiSchemeMeasure_grid_eq μ n] at hj
      have hqe : s.q (i+1+1) = hjbGridTime n (i+1) := by
        simpa only [s,show i+1+1=i+2 by omega] using hq1
      rw [hqe] at hj
      simpa only [s,m,hb,show n+1+1-(i+1)=n+1-i by omega,X] using
        congrArg (fun z=>β^2*z^2) hj.symm
  have hmass : (∫ t in (a:ℝ)..(b:ℝ),|parisiCDF μ t-m|) =
      ∫ t in (a:ℝ)..(b:ℝ),|parisiCDF μ t-parisiCDF (parisiGridMeasure μ n) t| := by
    apply intervalIntegral.integral_congr_uIoo
    rw [uIoo_of_le (NNReal.coe_lt_coe.mpr hab).le]
    intro t ht
    obtain ⟨hq0,hq1⟩ := hjbGrid_cell_q μ n i hi
    have htc : t∈Ico ((parisiGridRSBScheme μ n).q (i+1))
        ((parisiGridRSBScheme μ n).q (i+1+1)) := by
      simpa only [hq0,show i+1+1=i+2 by omega,hq1] using
        (show t∈Ico (hjbGridTime n i) (hjbGridTime n (i+1)) from
          ⟨ha.1.trans ht.1.le,ht.2.trans_eq hb⟩)
    dsimp only
    rw [parisiCDF_grid_eq_scheme_mass μ n (i+1) (by omega) (by omega) htc]
  have heError : (∫ t in (a:ℝ)..(b:ℝ),2*parisiGradientGridError β μ n t) =
      2*β^2*(∫ t in (a:ℝ)..(b:ℝ),|parisiCDF μ t-parisiCDF (parisiGridMeasure μ n) t|)+
        2*β^2*parisiHJBGradientError β μ n*((b:ℝ)-a) := by
    simp only [parisiGradientGridError]
    simp_rw [← mul_assoc]
    rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_add]
    · simp only [intervalIntegral.integral_const,smul_eq_mul]
      ring
    · exact parisiCDF_abs_diff_intervalIntegrable _ _ _ _
    · exact intervalIntegrable_const
  change ‖(∫ ω,parisiSlabGradient s β (n+1-i) m b b (X b ω)^2 ∂canonicalBrownianMeasure)-
    (∫ ω,parisiSlabGradient s β (n+1-i) m b a (X a ω)^2 ∂canonicalBrownianMeasure)-
    ∫ t in (a:ℝ)..(b:ℝ),∫ ω,β^2*parisiSlabHessian s β (n+1-i) m b t
      (X t.toNNReal ω)^2 ∂canonicalBrownianMeasure‖ ≤ _ at hh
  simp_rw [hgrad a ha,hgrad b ⟨(hjbGridTime_step_lt n i).le.trans_eq hb.symm,hb.le⟩] at hh
  rw [heSource,hmass,← heError] at hh
  simpa only [gridGamma,X,s,Real.toNNReal_coe] using hh

end FRSB
