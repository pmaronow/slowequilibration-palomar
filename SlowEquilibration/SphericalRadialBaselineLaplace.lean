-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SphericalOnePointContactSaddle
public import SlowEquilibration.SphericalLocalMaxPhysicalIntensity
public import SlowEquilibration.RadialQuadraticBounds
public import SlowEquilibration.RadialLaplaceBounds

/-! Actual one-point Gaussian radial envelopes at the source contact energy.
The pointwise certificate, true semicircle derivatives and physical Kac--Rice
prefactors generate the Laplace normalization internally. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalMarkedWindows
open Set MeasureTheory Filter TwoAtomStationarity
open RadialGaussianBounds RadialLaplaceBounds RadialQuadraticBounds
open scoped Topology ENNReal
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

def sourceRadialEdge (μ : FiniteMixture) (Q : ℝ) : ℝ :=
  2*Real.sqrt (Q^2*μ.xi2 Q)

def sourceBaselineLowerCurvature (μ : FiniteMixture) (Q L : ℝ) : ℝ :=
  sourceRadialCurvature μ Q+1/(L-sourceRadialEdge μ Q)^2

/-- Both quadratic profile bounds follow from actual two-sided scalar
Hessians and the genuine contact equations. -/
theorem sourceBaseline_profile_bounds (μ : FiniteMixture) {β x Q L R : ℝ}
    (h : SphericalTAPCertificate.Certificate μ β x Q) (hnp : μ.minDegree<μ.maxDegree)
    (hL : sourceRadialEdge μ Q<L) (hm : markK μ β Q∈Ioo L R) :
    ∀ k∈Ioo L R,
      -(sourceBaselineLowerCurvature μ Q L/2)*(k-markK μ β Q)^2  ≤ 
        sourceRadialProfile μ Q (markE μ β x Q) k ∧
      sourceRadialProfile μ Q (markE μ β x Q) k  ≤ 
        -(sourceRadialCurvature μ Q/2)*(k-markK μ β Q)^2 := by
  let f := sourceRadialProfile μ Q (markE μ β x Q)
  let g := sourceRadialProfileDerivative μ Q (markE μ β x Q)
  have hf (k : ℝ) (hk : k∈Ioo L R) : HasDerivAt f (g k) k :=
    sourceRadialProfile_hasDerivAt μ h.overlap_range.1 (markE μ β x Q) k (hL.trans hk.1)
  have hg (k : ℝ) (hk : k∈Ioo L R) : HasDerivAt g (deriv g k) k :=
    (sourceRadialProfileDerivative_hasDerivAt μ h.overlap_range.1
      (markE μ β x Q) k (hL.trans hk.1)).differentiableAt.hasDerivAt
  have hs : g (markK μ β Q)=0 := sourceContact_radial_profile_derivative_zero μ h hnp
  have hU (k : ℝ) (hk : k∈Ioo L R) : deriv g k  ≤  -sourceRadialCurvature μ Q :=
    sourceRadialProfile_second_derivative_le μ h.overlap_range.1
      (markE μ β x Q) k (hL.trans hk.1)
  have hB (k : ℝ) (hk : k∈Ioo L R) : -sourceBaselineLowerCurvature μ Q L  ≤  deriv g k := by
    have he := sourceRadialProfile_second_derivative_ge μ h.overlap_range.1
      (markE μ β x Q) k (hL.trans hk.1)
    have hd : 0<L-sourceRadialEdge μ Q := sub_pos.mpr hL
    have hp : (L-sourceRadialEdge μ Q)^2  ≤  (k-sourceRadialEdge μ Q)^2 :=
      pow_le_pow_left₀ hd.le (sub_le_sub_right hk.1.le _) 2
    have hi := one_div_le_one_div_of_le (sq_pos_of_pos hd) hp
    change -sourceRadialCurvature μ Q-1/(k-sourceRadialEdge μ Q)^2  ≤  deriv g k at he
    unfold sourceBaselineLowerCurvature
    linarith
  have hUpper := quadratic_upper_of_second_derivative (convex_Ioo L R) hf hg hm hs hU
  have hLower := quadratic_lower_of_second_derivative (convex_Ioo L R) hf hg hm hs hB
  have hzero : f (markK μ β Q)=0 := sourceContact_radialProfile_zero μ h hnp
  intro k hk
  have hu := hUpper k hk
  have hl := hLower k hk
  rw [hzero] at hu hl
  exact ⟨by linarith,by linarith⟩

/-- The baseline density is the actual unnormalized-energy intensity of
local maxima, with the correct physical energy Jacobian. -/
def sourceBaselineDensity (n : ℕ) (μ : FiniteMixture) (β x Q k : ℝ) : ℝ :=
  (mixedLocalMaxPhysicalIntensity n μ Q ((n+2 : ℕ)*markE μ β x Q) k).toReal

theorem sourceBaselineDensity_measurable (n : ℕ) (μ : FiniteMixture) (β x Q : ℝ) :
    Measurable (sourceBaselineDensity n μ β x Q) := by
  unfold sourceBaselineDensity
  apply Measurable.ennreal_toReal
  unfold mixedLocalMaxPhysicalIntensity
  apply measurable_const.mul
  have hm : Measurable (fun k : ℝ => mixedNegativeIntensity n μ Q
      (scorePairEquiv (((n+2 : ℕ)*markE μ β x Q)/(n+2 : ℕ),k))) :=
    (mixedNegativeIntensity_measurable n μ Q).comp
      (scorePairEquiv.measurable.comp (measurable_const.prodMk measurable_id))
  convert hm using 1
  funext k
  rfl

/-- Every actual dimension shares fixed lower/upper Gaussian constants at
the contact, after a deterministic dimension threshold. -/
theorem sourceBaseline_density_gaussian_bounds (μ : FiniteMixture) {β x Q L R : ℝ}
    (h : SphericalTAPCertificate.Certificate μ β x Q) (hnp : μ.minDegree<μ.maxDegree)
    (hL : sourceRadialEdge μ Q<L) (hm : markK μ β Q∈Ioo L R) :
    ∃ c C : ℝ,0<c ∧ 0<C ∧ ∀ᶠ n : ℕ in atTop,∀ k∈Ioo L R,
      c*gaussian ((sourceBaselineLowerCurvature μ Q L/2)*(n+2 : ℕ)) (markK μ β Q) k  ≤ 
        sourceBaselineDensity n μ β x Q k ∧
      sourceBaselineDensity n μ β x Q k  ≤ 
        C*gaussian ((sourceRadialCurvature μ Q/2)*(n+2 : ℕ)) (markK μ β Q) k := by
  let d := (L-sourceRadialEdge μ Q)/2
  have hd : 0<d := by dsimp [d];linarith
  obtain ⟨c,C,hc,hC,hbound⟩ := mixed_localMax_physical_prefactors μ h.overlap_range.1 hnp
    (Z := R) hd
  have hProfile := sourceBaseline_profile_bounds μ h hnp hL hm
  refine ⟨c,C,hc,hC,?_⟩
  filter_upwards [hbound] with n hn
  intro k hk
  have hkR : k∈Icc (2*Real.sqrt (Q^2*μ.xi2 Q)+d) R := by
    constructor
    · dsimp [d,sourceRadialEdge] at *
      linarith [hk.1]
    · exact hk.2.le
  have hb := hn (markE μ β x Q) k hkR
  have hfinite := hb.2.1.trans hb.2.2
  have hl := ENNReal.toReal_mono (ne_of_lt (lt_of_le_of_lt hfinite ENNReal.ofReal_lt_top)) hb.1
  have hu := ENNReal.toReal_mono ENNReal.ofReal_ne_top hfinite
  rw [ENNReal.toReal_ofReal (by positivity)] at hl hu
  rw [←scorePairEquiv_apply] at hl hu
  change c*Real.exp ((n+2 : ℕ)*sourceRadialProfile μ Q (markE μ β x Q) k)  ≤ 
    sourceBaselineDensity n μ β x Q k at hl
  change sourceBaselineDensity n μ β x Q k  ≤ 
    C*Real.exp ((n+2 : ℕ)*sourceRadialProfile μ Q (markE μ β x Q) k) at hu
  have hp := hProfile k hk
  constructor
  · apply le_trans _ hl
    apply mul_le_mul_of_nonneg_left _ hc.le
    unfold gaussian
    apply Real.exp_le_exp.mpr
    nlinarith [Nat.cast_nonneg (α := ℝ) (n+2)]
  · apply hu.trans
    apply mul_le_mul_of_nonneg_left _ hC.le
    unfold gaussian
    apply Real.exp_le_exp.mpr
    nlinarith [Nat.cast_nonneg (α := ℝ) (n+2)]

/-- Actual radial intensity has its sharp square-root normalization at the
source contact energy, without an assumed count normalization or limit. -/
theorem sourceBaseline_radial_normalization (μ : FiniteMixture) {β x Q L R : ℝ}
    (h : SphericalTAPCertificate.Certificate μ β x Q) (hnp : μ.minDegree<μ.maxDegree)
    (hL : sourceRadialEdge μ Q<L) (hm : markK μ β Q∈Ioo L R) :
    ∃ c C : ℝ,0<c ∧ 0<C ∧ ∀ᶠ n : ℕ in atTop,
      c/Real.sqrt (n+2 : ℕ)  ≤  ∫ k in Ioo L R,sourceBaselineDensity n μ β x Q k ∧
      (∫ k in Ioo L R,sourceBaselineDensity n μ β x Q k)  ≤  C/Real.sqrt (n+2 : ℕ) := by
  obtain ⟨c,C,hc,hC,hbounds⟩ := sourceBaseline_density_gaussian_bounds μ h hnp hL hm
  let a := sourceRadialCurvature μ Q/2
  let b := sourceBaselineLowerCurvature μ Q L/2
  have hκ : 0<sourceRadialCurvature μ Q := sourceRadialCurvature_pos μ h.overlap_range.1 hnp
  have ha : 0<a := half_pos hκ
  have hb : 0<b := by dsimp [b,sourceBaselineLowerCurvature];positivity
  let u := min (markK μ β Q-L) (R-markK μ β Q)
  have hu : 0<u := lt_min (sub_pos.mpr hm.1) (sub_pos.mpr hm.2)
  have hWidth : Tendsto (fun n : ℕ => 1/Real.sqrt (n+2 : ℕ)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [one_div,Function.comp_def] using tendsto_inv_atTop_zero.comp
      (Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 2)))
  refine ⟨lowerConstant c b,upperConstant C a,lowerConstant_pos hc,by
    unfold upperConstant
    exact mul_pos hC (Real.sqrt_pos.mpr (div_pos Real.pi_pos ha)),?_⟩
  filter_upwards [hbounds,hWidth.eventually (gt_mem_nhds hu)] with n hn hwidth
  have hN : 0<((n+2 : ℕ) : ℝ) := by positivity
  have hfi : IntegrableOn (sourceBaselineDensity n μ β x Q) (Ioo L R) := by
    apply (((gaussian_integrable (mul_pos ha hN) (markK μ β Q)).const_mul C).restrict).mono'
    · exact (sourceBaselineDensity_measurable n μ β x Q).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with k hk
      rw [Real.norm_of_nonneg (show 0 ≤ sourceBaselineDensity n μ β x Q k from ENNReal.toReal_nonneg)]
      exact (hn k hk).2
  have hInside : Icc (markK μ β Q-1/Real.sqrt (n+2 : ℕ))
      (markK μ β Q+1/Real.sqrt (n+2 : ℕ))⊆Ioo L R := by
    intro k hk
    have hul := min_le_left (markK μ β Q-L) (R-markK μ β Q)
    have hur := min_le_right (markK μ β Q-L) (R-markK μ β Q)
    change u  ≤  _ at hul hur
    constructor <;> linarith [hk.1,hk.2]
  have hl := laplace_integral_lower measurableSet_Ioo hfi
    (fun _ _ => ENNReal.toReal_nonneg) hc.le hb.le hN hInside
    (θ := 0) (by intro k hk;simpa only [mul_zero,Real.exp_zero,mul_one] using (hn k (hInside hk)).1)
  have hupp := laplace_integral_upper measurableSet_Ioo hfi hC.le ha hN (θ := 0)
    (by intro k hk;simpa only [mul_zero,Real.exp_zero,mul_one] using (hn k hk).2)
  simpa only [mul_zero,Real.exp_zero,mul_one] using And.intro hl hupp
end SlowEquilibration.SphericalMarkedWindows
