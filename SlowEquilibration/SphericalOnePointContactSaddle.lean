-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SphericalOnePointRadialCurvature

/-! The literal source one-point saddle is derived from the actual pointwise
one-step certificate. Its energy rate, radial stationarity and zero complexity
are algebraic consequences of genuine contact equations and semicircle law. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalMarkedWindows
open Set TwoAtomStationarity SphericalTAPCertificate
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

private theorem geometric_shift_facts {r : ℝ} (hr : 1 < r) :
    2 < r+1/r ∧ 0 ≤ r-1/r ∧ (r+1/r)^2-4=(r-1/r)^2 := by
  have hpos : 0 < r := by linarith
  have hsmall : 1/r < 1 := (div_lt_one hpos).mpr hr
  have hg : 0 < (r-1)^2/r := div_pos (sq_pos_of_pos (sub_pos.mpr hr)) hpos
  have he : (r-1)^2/r=r+1/r-2 := by field_simp [hpos.ne'];ring
  rw [he] at hg
  refine ⟨by linarith,by linarith,?_⟩
  field_simp [hpos.ne']
  ring

theorem source_semicircle_geometric_potential {r : ℝ} (hr : 1 < r) :
    SemicirclePotential.potential (r+1/r)=Real.log r+1/(2*r^2) := by
  obtain ⟨hedge,hsub,hdisc⟩ := geometric_shift_facts hr
  have hpos : 0 < r := by linarith
  rw [SemicirclePotential.potential_explicit hedge,hdisc,Real.sqrt_sq_eq_abs,abs_of_nonneg hsub]
  have hl : (r+1/r+(r-1/r))/2=r := by ring
  rw [hl]
  field_simp [hpos.ne']
  ring

theorem source_semicircle_geometric_resolvent {r : ℝ} (hr : 1 < r) :
    SemicirclePotential.resolvent (r+1/r)=1/r := by
  obtain ⟨hedge,hsub,hdisc⟩ := geometric_shift_facts hr
  have he := (SemicirclePotential.potential_hasDerivAt hedge).unique
    (SemicirclePotential.potential_hasDerivAt_explicit hedge)
  rw [hdisc,Real.sqrt_sq_eq_abs,abs_of_nonneg hsub] at he
  exact he.trans (by ring)

theorem sourceContact_reduced_equation (μ : FiniteMixture) {β x Q : ℝ}
    (h : Certificate μ β x Q) :
    (markZ x Q)^2*μ.xi Q/(markY β Q)^2 =
      Real.log (1+markZ x Q)-markZ x Q/(1+markZ x Q) := by
  have hQ : 1-Q ≠ 0 := (sub_pos.mpr h.overlap_range.2).ne'
  have hC : 0 < profileConstant x Q := profileConstant_pos h.weight_range h.overlap_range
  have hz : 0 < markZ x Q := div_pos (mul_pos h.weight_range.1 h.overlap_range.1)
    (sub_pos.mpr h.overlap_range.2)
  have hz1 : 1+markZ x Q ≠ 0 := ne_of_gt (by linarith)
  have heC : profileConstant x Q/(1-Q)=1+markZ x Q := by
    unfold profileConstant markZ
    field_simp [hQ]
  have heF : x*Q/profileConstant x Q=markZ x Q/(1+markZ x Q) := by
    unfold profileConstant markZ
    field_simp [hQ,hC.ne',hz1]
  have hscale : (markZ x Q)^2*μ.xi Q/(markY β Q)^2=β^2*x^2*μ.xi Q := by
    calc
      _=(markZ x Q/markY β Q)^2*μ.xi Q := by rw [div_pow];ring
      _=β^2*x^2*μ.xi Q := by
        rw [markZ_div_markY h.beta_pos h.overlap_range]
        ring
  rw [hscale,h.contact_equations.2,heC,heF]

theorem sourceContact_geometric_ratio (μ : FiniteMixture) {β x Q : ℝ}
    (h : Certificate μ β x Q) :
    1 < markY β Q/Real.sqrt (markB μ Q) ∧
      markK μ β Q/Real.sqrt (markB μ Q)=
        markY β Q/Real.sqrt (markB μ Q)+1/(markY β Q/Real.sqrt (markB μ Q)) := by
  have hy := markY_pos h.beta_pos h.overlap_range
  have hb := markB_pos μ h.overlap_range.1
  have hs := Real.sqrt_pos.mpr hb
  have hs2 := Real.sq_sqrt hb.le
  have hfrac := h.edge_margin.1
  have hby : markB μ Q < (markY β Q)^2 := (div_lt_one (sq_pos_of_pos hy)).mp hfrac
  have hsy : Real.sqrt (markB μ Q) < markY β Q := by nlinarith [Real.sqrt_nonneg (markB μ Q)]
  refine ⟨(lt_div_iff₀ hs).mpr (by simpa only [one_mul] using hsy),?_⟩
  unfold markK
  field_simp [hy.ne',hs.ne']
  nlinarith [hs2]

/-- The literal source saddle lies strictly outside the GOE spectral edge. -/
theorem sourceContact_markK_above_edge (μ : FiniteMixture) {β x Q : ℝ}
    (h : Certificate μ β x Q) :
    2*Real.sqrt (Q^2*μ.xi2 Q) < markK μ β Q := by
  obtain ⟨hr,he⟩ := sourceContact_geometric_ratio μ h
  have hs := Real.sqrt_pos.mpr (markB_pos μ h.overlap_range.1)
  have hedge := (geometric_shift_facts hr).1
  rw [←he] at hedge
  exact (lt_div_iff₀ hs).mp hedge

theorem sourceContact_scoreQuadratic (μ : FiniteMixture) {β x Q : ℝ}
    (h : Certificate μ β x Q) (hnp : μ.minDegree < μ.maxDegree) :
    SphericalSequentialRegression.scoreQuadratic μ Q
      (scorePairEquiv (markE μ β x Q,markK μ β Q)) =
      1+(markZ x Q*markA μ Q+(markZ x Q)^2*μ.xi Q+markB μ Q)/(markY β Q)^2 := by
  rw [source_scoreQuadratic_eq_slopes,sourceEnergySlope_at_contact μ h hnp,
    sourceRadialSlope_at_contact μ h hnp,←markZ_div_markY h.beta_pos h.overlap_range]
  have hy := markY_pos h.beta_pos h.overlap_range
  unfold markE markK
  field_simp [hy.ne']
  ring

theorem sourceContact_semicircle_value (μ : FiniteMixture) {β x Q : ℝ}
    (h : Certificate μ β x Q) :
    SemicirclePotential.potential (markK μ β Q/Real.sqrt (markB μ Q)) =
      Real.log (markY β Q/Real.sqrt (markB μ Q))+markB μ Q/(2*(markY β Q)^2) := by
  obtain ⟨hr,he⟩ := sourceContact_geometric_ratio μ h
  rw [he,source_semicircle_geometric_potential hr]
  have hy := markY_pos h.beta_pos h.overlap_range
  have hb := markB_pos μ h.overlap_range.1
  have hs := Real.sqrt_pos.mpr hb
  congr 1
  field_simp [hy.ne',hs.ne']
  nlinarith [Real.sq_sqrt hb.le]

/-- The actual mixed marked complexity vanishes at the literal source marks. -/
theorem sourceContact_markedComplexity_zero (μ : FiniteMixture) {β x Q : ℝ}
    (h : Certificate μ β x Q) (hnp : μ.minDegree < μ.maxDegree) :
    markedComplexity μ Q (scorePairEquiv (markE μ β x Q,markK μ β Q))=0 := by
  have hy := markY_pos h.beta_pos h.overlap_range
  have ha : 0 < markA μ Q := mul_pos h.overlap_range.1 (μ.xi1_pos h.overlap_range.1)
  have hb := markB_pos μ h.overlap_range.1
  have hs := Real.sqrt_pos.mpr hb
  have hz : 0 < markZ x Q := div_pos (mul_pos h.weight_range.1 h.overlap_range.1)
    (sub_pos.mpr h.overlap_range.2)
  have hz1 : 1+markZ x Q ≠ 0 := ne_of_gt (by linarith)
  have hy2 := markY_sq_from_contact μ h.beta_pos h.weight_range h.overlap_range
    h.contact_value h.contact_derivative
  have hly := congrArg Real.log hy2
  rw [Real.log_pow,Real.log_mul hz1 ha.ne'] at hly
  norm_num at hly
  have hlog : Real.log (markB μ Q/markA μ Q)/2+
      Real.log (markY β Q/Real.sqrt (markB μ Q))=Real.log (1+markZ x Q)/2 := by
    rw [Real.log_div hb.ne' ha.ne',Real.log_div hy.ne' hs.ne',Real.log_sqrt hb.le]
    linarith
  have hza : markZ x Q*markA μ Q/(markY β Q)^2=markZ x Q/(1+markZ x Q) := by
    rw [hy2]
    field_simp [hz1,ha.ne']
  have hv := sourceContact_reduced_equation μ h
  change 1/2+Real.log (markB μ Q/markA μ Q)/2-
    SphericalSequentialRegression.scoreQuadratic μ Q
      (scorePairEquiv (markE μ β x Q,markK μ β Q))/2+
      SemicirclePotential.potential (markK μ β Q/Real.sqrt (markB μ Q))=0
  rw [sourceContact_scoreQuadratic μ h hnp,sourceContact_semicircle_value μ h]
  calc
    _=(Real.log (markB μ Q/markA μ Q)/2+Real.log (markY β Q/Real.sqrt (markB μ Q)))-
        (markZ x Q*markA μ Q/(markY β Q)^2+(markZ x Q)^2*μ.xi Q/(markY β Q)^2)/2 := by ring
    _=Real.log (1+markZ x Q)/2-(markZ x Q/(1+markZ x Q)+
        (Real.log (1+markZ x Q)-markZ x Q/(1+markZ x Q)))/2 := by rw [hlog,hza,hv]
    _=0 := by ring

theorem sourceContact_radial_profile_derivative_zero (μ : FiniteMixture) {β x Q : ℝ}
    (h : Certificate μ β x Q) (hnp : μ.minDegree < μ.maxDegree) :
    sourceRadialProfileDerivative μ Q (markE μ β x Q) (markK μ β Q)=0 := by
  obtain ⟨hr,he⟩ := sourceContact_geometric_ratio μ h
  have hres : SemicirclePotential.resolvent (markK μ β Q/Real.sqrt (markB μ Q))=
      1/(markY β Q/Real.sqrt (markB μ Q)) := by
    rw [he]
    exact source_semicircle_geometric_resolvent hr
  have hy := markY_pos h.beta_pos h.overlap_range
  have hs := Real.sqrt_pos.mpr (markB_pos μ h.overlap_range.1)
  change -sourceRadialSlope μ Q (markE μ β x Q) (markK μ β Q)+
    SemicirclePotential.resolvent (markK μ β Q/Real.sqrt (markB μ Q))/Real.sqrt (markB μ Q)=0
  rw [sourceRadialSlope_at_contact μ h hnp,hres]
  field_simp [hy.ne',hs.ne']
  ring

theorem sourceContact_radialProfile_zero (μ : FiniteMixture) {β x Q : ℝ}
    (h : Certificate μ β x Q) (hnp : μ.minDegree < μ.maxDegree) :
    sourceRadialProfile μ Q (markE μ β x Q) (markK μ β Q)=0 :=
  sourceContact_markedComplexity_zero μ h hnp

/-- Stationarity of the actual radial complexity at the certified marks. -/
theorem sourceContact_radial_stationary (μ : FiniteMixture) {β x Q : ℝ}
    (h : Certificate μ β x Q) (hnp : μ.minDegree < μ.maxDegree) :
    HasDerivAt (sourceRadialProfile μ Q (markE μ β x Q)) 0 (markK μ β Q) := by
  have hd := sourceRadialProfile_hasDerivAt μ h.overlap_range.1
    (markE μ β x Q) (markK μ β Q) (sourceContact_markK_above_edge μ h)
  change HasDerivAt _ (sourceRadialProfileDerivative μ Q
    (markE μ β x Q) (markK μ β Q)) _ at hd
  rwa [sourceContact_radial_profile_derivative_zero μ h hnp] at hd
end SlowEquilibration.SphericalMarkedWindows
