-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourcePhysicalPairBandFailureProbability
public import SlowEquilibration.SphericalParisiPureLatitudePosteriorGround

/-! The proper-pure critical posterior has a genuine exponentially small
whole overlap-band failure. Its value-only conditioning, actual finite
radial net, and original tensor regularity are retained throughout. -/
@[expose] public section
namespace SlowEquilibration.PairConditionalDeterminantMoments
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open SphericalModel SphericalGaussianJet SphericalMarkedWindows SphericalCriticalLatitude
open SphericalParisiConditionedLatitudeCovariance SphericalParisiLatitudePosteriorGround
open SphericalParisiPureLatitudePosteriorGround LatitudeGroundTrial SphericalTAPCertificate
open TwoAtomStationarity
open scoped RealInnerProductSpace Topology
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

/-- Reduction from a scalar trial box; all posterior probabilities and
the dimension-independent radial mesh are internally derived. -/
theorem source_pure_physical_posterior_band_failure_of_trial_box
    (p:ℕ) (hp:2 ≤ p) (a:ℝ) (ha:0<a)
    {Q ε η E G δ y z:ℝ} (hQ:0<Q)
    (hε:0<ε) (hη:0<η) (hεη:ε ≤ 1-η) (hG:0<G) (hδ:0 ≤ δ)
    (hy:0<y) (hz:0<z)
    (htrial:∀ r ∈ Icc ε (1-η),∀ h ∈ Icc (E-δ) (E+δ),
      h*r^p+functional (centeredFirst (FiniteMixture.pure p hp a ha) Q r)
        (centeredSecond (FiniteMixture.pure p hp a ha) Q r)
          (height y z r) (z/y) (location r) ≤ E-7*G/8) :
    let μ:=FiniteMixture.pure p hp a ha
    ∃ K:ℝ,0<K ∧ ∃ grid:ℕ,1 ≤ grid ∧
      ∀ᶠ n:ℕ in atTop,∀ (u:Vector (n+1)) (hu:‖u‖^2=(n+1:ℕ)),
        ∀ h ∈ Icc (E-δ) (E+δ),
        let c:=centerCoefficients (mixtureCoefficients μ) Q
        (valueConditionedLaw c u hu h).real
          {J|¬sourceOverlapBandHeight c ε η ((n+1:ℕ)*(E-G/2)) J u} ≤
          sourceBandFailureRate μ Q G grid n:=by
  dsimp only
  let μ:=FiniteMixture.pure p hp a ha
  let M:=|E|+δ+1
  have hM:0 ≤ M:=by dsimp [M];positivity
  obtain ⟨K,hK,hreg⟩:=source_value_physical_posterior_orderedRegularity μ hQ hM
  let c:=centerCoefficients (mixtureCoefficients μ) Q
  obtain ⟨grid,hgrid,hmesh⟩:=source_radial_mesh_exists (a:=ε) (b:=1-η)
    (L:=sourcePosteriorDerivativeConstant c K) (s:=G/8) hεη
    (sourcePosteriorDerivativeConstant_pos c hK.le) (div_pos hG (by norm_num))
  have hpoints:∀ i:Fin (grid+1),∀ᶠ n:ℕ in atTop,
      ∀ (u:Vector (n+1)) (hu:‖u‖^2=(n+1:ℕ)),∀ h ∈ Icc (E-δ) (E+δ),
      (valueConditionedLaw c u hu h).real
        {J|(n+1:ℕ)*(E-5*G/8)<sourceUnitLatitudeMaximum c u (sourceLatitudeIsometry u hu)
          (latitudeMeshPoint grid ε (1-η) i) J} ≤
        Real.exp (-(n+1:ℕ)*(G/8)^2/(2*μ.xi Q)):=by
    intro i
    let r:=latitudeMeshPoint grid ε (1-η) i
    have hrband:r ∈ Icc ε (1-η):=latitudeMeshPoint_mem hgrid hεη i
    have hr:r ∈ Ioo (0:ℝ) 1:=⟨hε.trans_le hrband.1,by linarith [hrband.2]⟩
    obtain ⟨hs,_he,hb⟩:=trial_endpoint hy hz hr
    have ht:=eventual_actual_pure_latitude_trial_upper_tail p hp a ha hQ hr
      (div_nonneg hz.le hy.le) hs hb (ε:=G/8) (t:=G/8)
      (div_pos hG (by norm_num)) (by positivity)
    filter_upwards [ht] with n hn
    intro u hu h hh
    let ν:=valueConditionedLaw c u hu h
    let :IsProbabilityMeasure ν:=by unfold ν valueConditionedLaw;infer_instance
    have H:=hn u hu (sourceLatitudeIsometry u hu) (sourceLatitudeIsometry_orthogonal u hu) h
    dsimp only at H
    have hT:=htrial r hrband h hh
    apply (measureReal_mono (μ:=ν) ?_).trans H
    intro J hJ
    change (n+1:ℕ)*(h*r^p+
      functional (centeredFirst μ Q r) (centeredSecond μ Q r) (height y z r) (z/y) (location r)+G/8)+
        (n+1:ℕ)*(G/8) ≤ mixedLatitudeMaximum n μ Q r u (sourceLatitudeIsometry u hu) J
    change (n+1:ℕ)*(E-5*G/8) < mixedLatitudeMaximum n μ Q r u (sourceLatitudeIsometry u hu) J at hJ
    have hhT:=mul_le_mul_of_nonneg_left hT (show (0:ℝ) ≤ (n+1:ℕ) by positivity)
    nlinarith
  refine ⟨K,hK,grid,hgrid,?_⟩
  filter_upwards [Filter.eventually_all.mpr hpoints,eventually_ge_atTop (1:ℕ)] with n hn hdim
  intro u hu h hh
  let ν:=valueConditionedLaw c u hu h
  let :IsProbabilityMeasure ν:=by unfold ν valueConditionedLaw;infer_instance
  have hhM:|h| ≤ M:=by
    apply abs_le.mpr
    constructor <;> dsimp [M] <;> linarith [hh.1,hh.2,le_abs_self E,neg_le_abs E]
  have H:=sourceBandHeight_failure_probability_of_mesh hdim hgrid c hK.le hε hη hεη hmesh u hu ν
    (hreg n u hu h hhM) (fun i=>hn i u hu h hh)
  have he:(E-5*G/8)+G/8=E-G/2:=by ring
  simpa only [he,sourceBandFailureRate] using H

/-- The pure source gap controls every value mark in its actual compact
neighborhood; no desired band or trial inequality is assumed. -/
theorem source_pure_uniform_trial_gap (p:ℕ) (hp:2 ≤ p) (a:ℝ) (ha:0<a)
    {β x Q ε η δ:ℝ} (h:Certificate (FiniteMixture.pure p hp a ha) β x Q)
    (hε:0<ε) (hη:0<η) (hεη:ε<1-η) (hδ:0 ≤ δ)
    (hδG:δ ≤ gap (FiniteMixture.pure p hp a ha) Q (markY β Q) (markZ x Q) ε η/8) :
    let μ:=FiniteMixture.pure p hp a ha
    let E:=markE μ β x Q
    let G:=gap μ Q (markY β Q) (markZ x Q) ε η
    ∀ r ∈ Icc ε (1-η),∀ h₀ ∈ Icc (E-δ) (E+δ),
      h₀*r^p+functional (centeredFirst μ Q r) (centeredSecond μ Q r)
        (height (markY β Q) (markZ x Q) r) (markZ x Q/markY β Q) (location r) ≤ E-7*G/8:=by
  dsimp only
  intro r hr h₀ hh
  have hr':r ∈ Ioo (0:ℝ) 1:=⟨hε.trans_le hr.1,by linarith [hr.2]⟩
  obtain ⟨_hG,H⟩:=pure_source_trial_gap p hp a ha h hε hη hεη
  have H':=H r hr' hr
  dsimp only at H'
  obtain ⟨h1,h2⟩:=pure_residual_trial_derivatives p hp a ha h.overlap_range.1 hr'
  rw [h1,h2] at H'
  have hrp:0 ≤ r^p:=pow_nonneg hr'.1.le _
  have hrp1:r^p ≤ 1:=pow_le_one₀ hr'.1.le hr'.2.le
  have hpert:(h₀-markE (FiniteMixture.pure p hp a ha) β x Q)*r^p ≤ δ:=
    (mul_le_mul_of_nonneg_right (show h₀-markE (FiniteMixture.pure p hp a ha) β x Q ≤ δ by linarith [hh.2]) hrp).trans
      (mul_le_of_le_one_right hδ hrp1)
  linarith

/-- Actual proper-pure ground marks admit a dimension-independent
neighborhood and a genuine exponentially small whole-band failure. -/
theorem source_pure_physical_posterior_band_failure
    (p:ℕ) (hp:2 ≤ p) (a:ℝ) (ha:0<a)
    {β x Q ε η δMax:ℝ} (h:Certificate (FiniteMixture.pure p hp a ha) β x Q)
    (hε:0<ε) (hη:0<η) (hεη:ε<1-η) (hδMax:0<δMax) :
    let μ:=FiniteMixture.pure p hp a ha
    let E:=markE μ β x Q
    let G:=gap μ Q (markY β Q) (markZ x Q) ε η
    ∃ δ:ℝ,0<δ ∧ δ<G/4 ∧ δ ≤ δMax ∧ ∃ K:ℝ,0<K ∧ ∃ grid:ℕ,1 ≤ grid ∧
      ∀ᶠ n:ℕ in atTop,∀ (u:Vector (n+1)) (hu:‖u‖^2=(n+1:ℕ)),
        ∀ h₀ ∈ Icc (E-δ) (E+δ),
        let c:=centerCoefficients (mixtureCoefficients μ) Q
        (valueConditionedLaw c u hu h₀).real
          {J|¬sourceOverlapBandHeight c ε η ((n+1:ℕ)*(E-G/2)) J u} ≤
          sourceBandFailureRate μ Q G grid n:=by
  dsimp only
  let μ:=FiniteMixture.pure p hp a ha
  let G:=gap μ Q (markY β Q) (markZ x Q) ε η
  obtain ⟨hG,_⟩:=pure_source_trial_gap p hp a ha h hε hη hεη
  let δ:=min δMax (G/16)
  have hδ:0<δ:=lt_min hδMax (div_pos hG (by norm_num))
  have hδMax':δ ≤ δMax:=min_le_left _ _
  have hδ16:δ ≤ G/16:=min_le_right _ _
  have hδG:δ<G/4:=by linarith
  have hy:=markY_pos h.beta_pos h.overlap_range
  have hz:0 < markZ x Q:=div_pos (mul_pos h.weight_range.1 h.overlap_range.1)
    (sub_pos.mpr h.overlap_range.2)
  obtain ⟨K,hK,grid,hgrid,H⟩:=source_pure_physical_posterior_band_failure_of_trial_box p hp a ha
    h.overlap_range.1 hε hη hεη.le hG hδ.le hy hz
    (source_pure_uniform_trial_gap p hp a ha h hε hη hεη hδ.le (by linarith))
  exact ⟨δ,hδ,hδG,hδMax',K,hK,grid,hgrid,H⟩

end
end SlowEquilibration.PairConditionalDeterminantMoments
