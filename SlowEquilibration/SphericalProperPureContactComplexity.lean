-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SphericalProperPureContactGeometry

/-! Zero actual proper-pure complexity and its contact derivative on the
literal scalar score graph, using the original contact equations. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalMarkedWindows
open Set TwoAtomStationarity SphericalTAPCertificate
set_option maxHeartbeats 500000

theorem sourcePure_contact_energy_square (p : ℕ) (hp : 2 ≤ p) (α : ℝ) (hα : 0 < α)
    {β x Q : ℝ} (h : Certificate (FiniteMixture.pure p hp α hα) β x Q) :
    (markE (FiniteMixture.pure p hp α hα) β x Q)^2/(FiniteMixture.pure p hp α hα).xi Q=
      1+(markZ x Q*markA (FiniteMixture.pure p hp α hα) Q+
        (markZ x Q)^2*(FiniteMixture.pure p hp α hα).xi Q+
        markB (FiniteMixture.pure p hp α hα) Q)/(markY β Q)^2 := by
  let μ := FiniteMixture.pure p hp α hα
  have hV := μ.xi_pos h.overlap_range.1
  have hy := markY_pos h.beta_pos h.overlap_range
  have hy2 := markY_sq_from_contact μ h.beta_pos h.weight_range h.overlap_range h.contact_value h.contact_derivative
  have hPure := sourcePure_contact_covariance_scalars p hp α hα Q
  have hDegenerate : (markA μ Q)^2=μ.xi Q*(markA μ Q+markB μ Q) := by
    rw [hPure.1,hPure.2]
    ring
  unfold markE
  have hNumerator :
      (markA μ Q + markZ x Q * μ.xi Q)^2 =
        μ.xi Q * ((markY β Q)^2 +
          markZ x Q * (markA μ Q + markZ x Q * μ.xi Q) + markB μ Q) := by
    rw [hy2]
    nlinarith [hDegenerate]
  field_simp [hV.ne',hy.ne']
  apply (div_eq_iff hV.ne').mpr
  convert hNumerator using 1; ring

theorem sourcePure_contact_complexity_zero (p : ℕ) (hp : 2 ≤ p) (α : ℝ) (hα : 0 < α)
    {β x Q : ℝ} (h : Certificate (FiniteMixture.pure p hp α hα) β x Q) :
    pureMarkedComplexity p hp α hα Q (markE (FiniteMixture.pure p hp α hα) β x Q)=0 := by
  let μ := FiniteMixture.pure p hp α hα
  have hy := markY_pos h.beta_pos h.overlap_range
  have ha : 0 < markA μ Q := mul_pos h.overlap_range.1 (μ.xi1_pos h.overlap_range.1)
  have hb := markB_pos μ h.overlap_range.1
  have hs := Real.sqrt_pos.mpr hb
  have hz : 0 < markZ x Q := div_pos (mul_pos h.weight_range.1 h.overlap_range.1) (sub_pos.mpr h.overlap_range.2)
  have hz1 : 1+markZ x Q ≠ 0 := ne_of_gt (by linarith)
  have hy2 := markY_sq_from_contact μ h.beta_pos h.weight_range h.overlap_range h.contact_value h.contact_derivative
  have hly := congrArg Real.log hy2
  rw [Real.log_pow,Real.log_mul hz1 ha.ne'] at hly
  norm_num at hly
  have hlog : Real.log (markB μ Q/markA μ Q)/2+Real.log (markY β Q/Real.sqrt (markB μ Q))=
      Real.log (1+markZ x Q)/2 := by
    rw [Real.log_div hb.ne' ha.ne',Real.log_div hy.ne' hs.ne',Real.log_sqrt hb.le]
    linarith
  have hza : markZ x Q*markA μ Q/(markY β Q)^2=markZ x Q/(1+markZ x Q) := by
    rw [hy2]
    field_simp [hz1,ha.ne']
  have hv := sourceContact_reduced_equation μ h
  change 1/2+Real.log (markB μ Q/markA μ Q)/2-(markE μ β x Q)^2/(2*μ.xi Q)+
    SemicirclePotential.potential ((p : ℝ)*markE μ β x Q/Real.sqrt (markB μ Q))=0
  rw [←sourcePure_contact_radial_graph p hp α hα h,sourceContact_semicircle_value μ h]
  have heSquare := sourcePure_contact_energy_square p hp α hα h
  have hEnergy : (markE μ β x Q)^2/(2*μ.xi Q)=
      (1+(markZ x Q*markA μ Q+(markZ x Q)^2*μ.xi Q+markB μ Q)/(markY β Q)^2)/2 := by
    rw [←heSquare]
    ring
  rw [hEnergy]
  calc
    _=(Real.log (markB μ Q/markA μ Q)/2+Real.log (markY β Q/Real.sqrt (markB μ Q)))-
      (markZ x Q*markA μ Q/(markY β Q)^2+(markZ x Q)^2*μ.xi Q/(markY β Q)^2)/2 := by ring
    _=0 := by rw [hlog,hza,hv];ring

theorem sourcePure_contact_complexity_hasDerivAt (p : ℕ) (hp : 2 ≤ p) (α : ℝ) (hα : 0 < α)
    {β x Q : ℝ} (h : Certificate (FiniteMixture.pure p hp α hα) β x Q) :
    HasDerivAt (pureMarkedComplexity p hp α hα Q) (-(β*x))
      (markE (FiniteMixture.pure p hp α hα) β x Q) := by
  have hEdge := sourceContact_markK_above_edge (FiniteMixture.pure p hp α hα) h
  rw [sourcePure_contact_radial_graph p hp α hα h] at hEdge
  have hd := sourcePureComplexity_hasDerivAt p hp α hα h.overlap_range.1 _ hEdge
  rw [sourcePure_contact_complexity_derivative p hp α hα h] at hd
  exact hd
end SlowEquilibration.SphericalMarkedWindows
