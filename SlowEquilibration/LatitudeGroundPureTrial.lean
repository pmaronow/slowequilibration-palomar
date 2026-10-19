-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.LatitudeGroundTrialGap
public import SlowEquilibration.SphericalPureCriticalLatitudeLaw

/-! The actual proper-pure covariance and its certified ground trial.
The redundant radial score is never inverted. The covariance and all trial
derivatives are identified with the genuine finite Taylor residual. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.LatitudeGroundTrial
open Set SphericalParisiConditionedLatitudeCovariance
open SphericalParisiPureLatitudeCovariance SphericalCriticalLatitude
open SphericalTAPCertificate TwoAtomStationarity
set_option autoImplicit false
set_option maxHeartbeats 600000

theorem pure_valueTau_eq_centered (p : ℕ) (hp : 2 ≤ p) (c : ℝ) (hc : 0 < c)
    {Q : ℝ} (hQ : 0 < Q) (r t : ℝ) :
    sourceValueTau (FiniteMixture.pure p hp c hc) Q r t=
      centeredCovariance (FiniteMixture.pure p hp c hc) Q r t := by
  unfold sourceValueTau centeredCovariance sourceTau
  rw [pure_value_correction p hp c hc hQ]
  simp only [mul_zero,add_zero,sub_zero]
  ring

theorem pure_residual_trial_derivatives (p : ℕ) (hp : 2 ≤ p) (c : ℝ) (hc : 0 < c)
    {Q r : ℝ} (hQ : 0 < Q) (hr : r ∈ Ioo (0 : ℝ) 1) :
    (pureLatitudeResidual p hp c hc hQ hr).xi1=centeredFirst (FiniteMixture.pure p hp c hc) Q r ∧
      (pureLatitudeResidual p hp c hc hQ hr).xi2=centeredSecond (FiniteMixture.pure p hp c hc) Q r := by
  let μ := FiniteMixture.pure p hp c hc
  let θ := pureLatitudeResidual p hp c hc hQ hr
  have he : θ.xi=centeredCovariance μ Q r := by
    funext t
    exact (pure_valueTau_eq_residual_xi p hp c hc hQ hr t).symm.trans
      (pure_valueTau_eq_centered p hp c hc hQ r t)
  have h1 : θ.xi1=centeredFirst μ Q r := by
    funext t
    exact ((θ.hasDerivAt_xi t).congr_of_eventuallyEq (Filter.Eventually.of_forall
      (fun u => (congrFun he u).symm))).unique (centered_hasDerivAt μ Q r t)
  refine ⟨h1,?_⟩
  funext t
  exact ((θ.hasDerivAt_xi1 t).congr_of_eventuallyEq (Filter.Eventually.of_forall
    (fun u => (congrFun h1 u).symm))).unique (centeredFirst_hasDerivAt μ Q r t)

theorem pure_ground_mean_eq (p : ℕ) (hp : 2 ≤ p) (c : ℝ) (hc : 0 < c)
    (β x Q r : ℝ) :
    markE (FiniteMixture.pure p hp c hc) β x Q*r^p=
      (r*centerFirst (FiniteMixture.pure p hp c hc) Q r+
        markZ x Q*centerCovariance (FiniteMixture.pure p hp c hc) Q r)/markY β Q := by
  have ha : markA (FiniteMixture.pure p hp c hc) Q=c*Q^p*(p : ℝ) := by
    simpa only [centerFirst,markA,one_pow,mul_one] using
      pure_centerFirst p hp c hc Q 1
  have he : r*r^(p-1)=r^p := by
    rw [←pow_succ',Nat.sub_add_cancel (show 1 ≤ p by omega)]
  rw [markE,ha,FiniteMixture.pure_xi,pure_centerFirst,pure_centerCovariance]
  calc
    _=((c*Q^p*(p : ℝ)+markZ x Q*(c*Q^p))*r^p)/markY β Q := by ring
    _=_ := by rw [←he];ring

theorem pure_source_trial_completed_square (p : ℕ) (hp : 2 ≤ p) (c : ℝ) (hc : 0 < c)
    {β x Q r : ℝ} (h : Certificate (FiniteMixture.pure p hp c hc) β x Q)
    (hr : r ∈ Ioo (0 : ℝ) 1) :
    let μ := FiniteMixture.pure p hp c hc
    let θ := pureLatitudeResidual p hp c hc h.overlap_range.1 hr
    markE μ β x Q*r^p+
      functional θ.xi1 θ.xi2 (height (markY β Q) (markZ x Q) r)
        (markZ x Q/markY β Q) (location r)=
      markE μ β x Q-markZ x Q/(2*markY β Q)*slack μ Q (markZ x Q) r-
        (r*gradientVariance μ Q-D (markZ x Q) r*centerFirst μ Q r)^2/
          (2*markY β Q*gradientVariance μ Q*D (markZ x Q) r) := by
  dsimp only
  let μ := FiniteMixture.pure p hp c hc
  obtain ⟨h1,h2⟩ := pure_residual_trial_derivatives p hp c hc h.overlap_range.1 hr
  rw [h1,h2,pure_ground_mean_eq]
  have hy := markY_pos h.beta_pos h.overlap_range
  have hz : 0 < markZ x Q := div_pos
    (mul_pos h.weight_range.1 h.overlap_range.1) (sub_pos.mpr h.overlap_range.2)
  have ha : 0 < gradientVariance μ Q := by
    change 0 < Q*μ.xi1 (Q*1)
    rw [mul_one]
    exact mul_pos h.overlap_range.1 (μ.xi1_pos h.overlap_range.1)
  have hs : (markY β Q)^2=(1+markZ x Q)*gradientVariance μ Q := by
    simpa only [gradientVariance,centerFirst,mul_one,markA] using
      markY_sq_from_contact μ h.beta_pos h.weight_range h.overlap_range
        h.contact_value h.contact_derivative
  have he := completed_square μ Q hy hz hr ha hs
  simpa only [gradientVariance,centerFirst,mul_one,markE,markA] using he

theorem certified_trial_admissible (μ : FiniteMixture) {β x Q r : ℝ}
    (h : Certificate μ β x Q) (hr : r ∈ Ioo (0 : ℝ) 1) :
    location r ∈ Icc (0 : ℝ) 1 ∧
      0 < height (markY β Q) (markZ x Q) r ∧
      0 < markZ x Q/markY β Q ∧
      ∀ t ∈ Icc (0 : ℝ) 1,
        0 < profile (height (markY β Q) (markZ x Q) r)
          (markZ x Q/markY β Q) (location r) t := by
  have hy := markY_pos h.beta_pos h.overlap_range
  have hz : 0 < markZ x Q := div_pos
    (mul_pos h.weight_range.1 h.overlap_range.1) (sub_pos.mpr h.overlap_range.2)
  obtain ⟨hs,_he,hb⟩ := trial_endpoint hy hz hr
  have hα := div_pos hz hy
  have hnon := mul_nonneg hα.le (sub_nonneg.mpr hs.2)
  refine ⟨hs,by linarith,hα,?_⟩
  exact fun t ht => hb.trans_le (profile_lower hα.le hs ht)

theorem pure_source_trial_gap (p : ℕ) (hp : 2 ≤ p) (c : ℝ) (hc : 0 < c)
    {β x Q ε η : ℝ} (h : Certificate (FiniteMixture.pure p hp c hc) β x Q)
    (hε : 0 < ε) (hη : 0 < η) (hεη : ε < 1-η) :
    let μ := FiniteMixture.pure p hp c hc
    0 < gap μ Q (markY β Q) (markZ x Q) ε η ∧
      ∀ r (hr : r ∈ Ioo (0 : ℝ) 1), r ∈ Icc ε (1-η) →
        let θ := pureLatitudeResidual p hp c hc h.overlap_range.1 hr
        markE μ β x Q*r^p+
          functional θ.xi1 θ.xi2 (height (markY β Q) (markZ x Q) r)
            (markZ x Q/markY β Q) (location r) ≤
          markE μ β x Q-gap μ Q (markY β Q) (markZ x Q) ε η := by
  dsimp only
  let μ := FiniteMixture.pure p hp c hc
  obtain ⟨hgap,hbound⟩ := gap_positive μ h hε hη hεη
  refine ⟨hgap,?_⟩
  intro r hr hrc
  rw [pure_source_trial_completed_square p hp c hc h hr]
  have hy := markY_pos h.beta_pos h.overlap_range
  have ha : 0 < gradientVariance μ Q := by
    change 0 < Q*μ.xi1 (Q*1)
    rw [mul_one]
    exact mul_pos h.overlap_range.1 (μ.xi1_pos h.overlap_range.1)
  have hz : 0 < markZ x Q := div_pos
    (mul_pos h.weight_range.1 h.overlap_range.1) (sub_pos.mpr h.overlap_range.2)
  have hD : 0 < D (markZ x Q) r := by
    have hr1 : 0 < 1-r := sub_pos.mpr hr.2
    unfold D
    positivity
  have hn : 0 ≤ (r*gradientVariance μ Q-D (markZ x Q) r*centerFirst μ Q r)^2/
      (2*markY β Q*gradientVariance μ Q*D (markZ x Q) r) := by positivity
  linarith [hbound r hrc]

end SlowEquilibration.LatitudeGroundTrial
