module
public import FRSB.ConstantMassEvolution
public import FRSB.BackwardsTimeSpatial
public import Targets.Section4Variance

@[expose] public section

/-! The actual differentiated PDE on every constant-CDF interval, including
mass zero and arbitrary probability measures. -/
noncomputable section
open Set Filter Paper SpinGlass SpinGlass.Targets
open scoped Topology
namespace FRSB

theorem hasDerivAt_parisiPotential_constantCDF_time (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) {a b m : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1)
    (hc : ∀ s ∈ Ico a b, parisiCDF μ s = m)
    {t : ℝ} (ht : t ∈ Ioo a b) (x : ℝ) :
    HasDerivAt (fun r => parisiPotential β μ (r,x))
      (-(β^2/2) * (parisiHessian β μ (t,x) + m * parisiGradient β μ (t,x)^2)) t := by
  have hbt : b ∈ Icc (0 : ℝ) 1 := ⟨ha.trans hab.le,hb⟩
  let A : ℝ → ℝ := fun y => parisiPotential β μ (b,y)
  let A' : ℝ → ℝ := fun y => parisiGradient β μ (b,y)
  let A'' : ℝ → ℝ := fun y => parisiHessian β μ (b,y)
  have hA : SpinGlass.HasLinearGrowth A := by
    obtain ⟨C,D,hD,hg⟩ := parisiPotential_hasLinearGrowth β μ b hbt
    refine ⟨|C|,D,abs_nonneg _,hD,fun y => ?_⟩
    have hh : |A y| ≤ C + D * |y| := by simpa only [Real.norm_eq_abs] using hg y
    exact hh.trans (by linarith [le_abs_self C])
  have hC2 : SpinGlass.HasParisiC2 A A' A'' := by
    refine ⟨fun y => hasDerivAt_parisiPotential_spatial_all β μ b y hbt,
      fun y => hasDerivAt_parisiGradient_spatial_all β μ b y,
      fun y => (parisiHessian_pos_all β μ b y hbt).le,fun y => ?_⟩
    linarith [parisiHessian_add_gradient_sq_le_one_all β μ (b,y)]
  have hAm : Measurable A := ((continuous_parisiPotential β μ).comp (continuous_const.prodMk continuous_id)).measurable
  have hA'm : Measurable A' := ((continuous_parisiGradient β μ).comp (continuous_const.prodMk continuous_id)).measurable
  have hA''m : Measurable A'' := ((continuous_parisiHessian_all β μ).comp (continuous_const.prodMk continuous_id)).measurable
  have he (r : ℝ) (hr : r ∈ Icc a b) :
      parisiStep m (β^2*(b-r)) A = fun y => parisiPotential β μ (r,y) := by
    funext y
    have hn : 0 ≤ β^2*(b-r) := mul_nonneg (sq_nonneg _) (sub_nonneg.mpr hr.2)
    have hs := parisiStep_eq_coleHopf m (β^2*(b-r)).toNNReal hAm y
    rw [Real.coe_toNNReal _ hn] at hs
    exact hs.trans (parisiPotential_coleHopf_constant_interval β hβ μ ha hab hb hc hr
      ⟨hr.2,le_rfl⟩ y).symm
  have hd := hasDerivAt_parisiStep_variance_pde hA hC2 hAm hA'm hA''m m x
    (mul_pos (sq_pos_of_ne_zero hβ) (sub_pos.mpr ht.2))
  have hfirst : deriv (parisiStep m (β^2*(b-t)) A) = fun y => parisiGradient β μ (t,y) := by
    rw [he t ⟨ht.1.le,ht.2.le⟩]
    exact funext fun y => (hasDerivAt_parisiPotential_spatial_all β μ t y
      ⟨ha.trans ht.1.le,ht.2.le.trans hb⟩).deriv
  have hsecond : deriv (deriv (parisiStep m (β^2*(b-t)) A)) x = parisiHessian β μ (t,x) := by
    rw [hfirst]
    exact (hasDerivAt_parisiGradient_spatial_all β μ t x).deriv
  rw [hsecond,hfirst] at hd
  have hcomp := hd.comp t (((hasDerivAt_const t b).sub (hasDerivAt_id t)).const_mul (β^2))
  have hevent : (fun r => parisiPotential β μ (r,x)) =ᶠ[𝓝 t]
      (fun r => parisiStep m (β^2*(b-r)) A x) := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with r hr
    exact (congrFun (he r ⟨hr.1.le,hr.2.le⟩) x).symm
  convert hcomp.congr_of_eventuallyEq hevent using 1
  ring

theorem hasDerivAt_constantCDF_spatialJet_time (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) {a b m : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1)
    (hc : ∀ s ∈ Ico a b, parisiCDF μ s = m) (j : ℕ)
    {t : ℝ} (ht : t ∈ Ioo a b) (x : ℝ) :
    HasDerivAt (fun r => parisiSpatialJet β μ j r x)
      (cellTimeForcing β μ m j t x) t := by
  apply time_hierarchy_of_base_PDE β μ m a b ha hb ?_ j t ht x
  intro r hr y
  have hd := hasDerivAt_parisiPotential_constantCDF_time β hβ μ ha hab hb hc hr y
  have he : parisiSpatialJet β μ 2 r y = parisiHessian β μ (r,y) := by
    rw [← backwardD_eq_spatialJet β μ 2 r y]
    exact backwardC_eq_hessian β μ r y ⟨ha.trans hr.1.le,hr.2.le.trans hb⟩
  change HasDerivAt (fun s => parisiPotential β μ (s,y)) (cellTimeForcing β μ m 0 r y) r
  simpa only [cellTimeForcing,iteratedDeriv_zero,he,parisiSpatialJet_one] using hd

theorem hasDerivAt_constantCDF_backwardTauD (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) {a b m : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1)
    (hc : ∀ s ∈ Ico a b, parisiCDF μ s = m) (j : ℕ)
    {τ : ℝ} (hτ : backwardTime β τ ∈ Ioo a b) (x : ℝ) :
    HasDerivAt (fun r => backwardTauD β μ j (r,x))
      (backwardTauForcing β μ m j (τ,x)) τ := by
  have hd := (hasDerivAt_constantCDF_spatialJet_time β hβ μ ha hab hb hc j hτ x).comp τ
    (hasDerivAt_backwardTime β τ)
  convert hd using 1
  · exact funext fun r => backwardD_eq_spatialJet β μ j (backwardTime β r) x
  · rw [cellTimeForcing_eq]
    simp only [backwardTauForcing,backwardTauD,backwardD_eq_spatialJet]
    field_simp

end FRSB
