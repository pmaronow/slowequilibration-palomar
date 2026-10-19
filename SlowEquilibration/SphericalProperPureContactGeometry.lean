-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SphericalOnePointContactSaddle
public import SlowEquilibration.SphericalPureLocalMaxPhysicalIntensity
public import SlowEquilibration.SemicircleModifiedConcavity

/-! Actual proper-pure contact geometry on the literal scalar score graph.
No singular score-covariance inverse or mixed radial normalizer is used. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalMarkedWindows
open Set TwoAtomStationarity SphericalTAPCertificate CSPureModels
open scoped Topology
set_option maxHeartbeats 500000

theorem sourcePure_contact_covariance_scalars (p : ℕ) (hp : 2 ≤ p) (α : ℝ) (hα : 0 < α) (Q : ℝ) :
    markA (FiniteMixture.pure p hp α hα) Q=(p : ℝ)*(FiniteMixture.pure p hp α hα).xi Q ∧
    markB (FiniteMixture.pure p hp α hα) Q=(p : ℝ)*((p : ℝ)-1)*(FiniteMixture.pure p hp α hα).xi Q := by
  let μ := FiniteMixture.pure p hp α hα
  have hp1 : 1 ≤ p := by omega
  have hpow1 : Q^(p-1)*Q=Q^p := by rw [←pow_succ,Nat.sub_add_cancel hp1]
  have hpow2 : Q^(p-2)*Q^2=Q^p := by rw [←pow_add,Nat.sub_add_cancel hp]
  have hSupport : μ.coeff.support={p} := pure_support p hp α hα
  have hCoeff : μ.coeff p=α := Finsupp.single_eq_same
  have hxi1 : μ.xi1 Q=α*(p : ℝ)*Q^(p-1) := by
    unfold FiniteMixture.xi1
    rw [hSupport,Finset.sum_singleton,hCoeff]
  have hxi2 : μ.xi2 Q=α*(p : ℝ)*((p : ℝ)-1)*Q^(p-2) := by
    unfold FiniteMixture.xi2
    rw [hSupport,Finset.sum_singleton]
    unfold FiniteMixture.curvatureCoeff
    rw [hCoeff,Nat.cast_sub hp1]
    norm_num
  constructor
  · change Q*μ.xi1 Q=(p : ℝ)*μ.xi Q
    rw [hxi1,FiniteMixture.pure_xi]
    calc
      _=(p : ℝ)*α*(Q^(p-1)*Q) := by ring
      _=_ := by rw [hpow1];ring
  · change Q^2*μ.xi2 Q=(p : ℝ)*((p : ℝ)-1)*μ.xi Q
    rw [hxi2,FiniteMixture.pure_xi]
    calc
      _=(p : ℝ)*((p : ℝ)-1)*α*(Q^(p-2)*Q^2) := by ring
      _=_ := by rw [hpow2];ring

theorem sourcePure_contact_energy_formula (p : ℕ) (hp : 2 ≤ p) (α : ℝ) (hα : 0 < α)
    (β x Q : ℝ) :
    markE (FiniteMixture.pure p hp α hα) β x Q=
      ((p : ℝ)+markZ x Q)*(FiniteMixture.pure p hp α hα).xi Q/markY β Q := by
  unfold markE
  rw [(sourcePure_contact_covariance_scalars p hp α hα Q).1]
  ring

theorem sourcePure_contact_radial_graph (p : ℕ) (hp : 2 ≤ p) (α : ℝ) (hα : 0 < α)
    {β x Q : ℝ} (h : Certificate (FiniteMixture.pure p hp α hα) β x Q) :
    markK (FiniteMixture.pure p hp α hα) β Q=
      (p : ℝ)*markE (FiniteMixture.pure p hp α hα) β x Q := by
  let μ := FiniteMixture.pure p hp α hα
  have hScalars := sourcePure_contact_covariance_scalars p hp α hα Q
  have hY := markY_sq_from_contact μ h.beta_pos h.weight_range h.overlap_range h.contact_value h.contact_derivative
  rw [hScalars.1] at hY
  have hy := markY_pos h.beta_pos h.overlap_range
  change markK μ β Q=(p : ℝ)*markE μ β x Q
  unfold markK markE
  rw [hScalars.1,hScalars.2]
  field_simp [hy.ne']
  nlinarith [hY]

def sourcePureComplexityDerivative (p : ℕ) (hp : 2 ≤ p) (α : ℝ) (hα : 0 < α) (Q e : ℝ) : ℝ :=
  -e/(FiniteMixture.pure p hp α hα).xi Q+
    (p : ℝ)/Real.sqrt (Q^2*(FiniteMixture.pure p hp α hα).xi2 Q)*
      SemicirclePotential.resolvent ((p : ℝ)*e/Real.sqrt (Q^2*(FiniteMixture.pure p hp α hα).xi2 Q))

theorem sourcePureComplexity_hasDerivAt (p : ℕ) (hp : 2 ≤ p) (α : ℝ) (hα : 0 < α)
    {Q : ℝ} (hQ : 0 < Q) (e : ℝ)
    (he : 2*Real.sqrt (Q^2*(FiniteMixture.pure p hp α hα).xi2 Q) < (p : ℝ)*e) :
    HasDerivAt (pureMarkedComplexity p hp α hα Q) (sourcePureComplexityDerivative p hp α hα Q e) e := by
  let μ := FiniteMixture.pure p hp α hα
  have hV := μ.xi_pos hQ
  have hB := markB_pos μ hQ
  have hS := Real.sqrt_pos.mpr hB
  have hEdge : 2 < (p : ℝ)*e/Real.sqrt (Q^2*μ.xi2 Q) := (lt_div_iff₀ hS).mpr he
  have hQuad := (((hasDerivAt_id e).pow 2).div_const (2*μ.xi Q))
  have hArg := ((hasDerivAt_id e).const_mul (p : ℝ)).div_const (Real.sqrt (Q^2*μ.xi2 Q))
  have hOmega := (SemicirclePotential.potential_hasDerivAt hEdge).comp e hArg
  convert ((hasDerivAt_const e (1/2+Real.log ((Q^2*μ.xi2 Q)/(Q*μ.xi1 Q))/2)).sub hQuad).add hOmega using 1
  · rfl
  · unfold sourcePureComplexityDerivative
    dsimp only [μ, id_eq]
    field_simp [hV.ne', hS.ne']
    ring

/-- The pure contact energy has the source microscopic energy slope. -/
theorem sourcePure_contact_scalar_slope (p : ℕ) (hp : 2 ≤ p) (α : ℝ) (hα : 0 < α)
    {β x Q : ℝ} (h : Certificate (FiniteMixture.pure p hp α hα) β x Q) :
    markE (FiniteMixture.pure p hp α hα) β x Q/(FiniteMixture.pure p hp α hα).xi Q-
      (p : ℝ)/markY β Q=β*x := by
  have hV := (FiniteMixture.pure p hp α hα).xi_pos h.overlap_range.1
  have hy := markY_pos h.beta_pos h.overlap_range
  rw [sourcePure_contact_energy_formula]
  calc
    _=markZ x Q/markY β Q := by field_simp [hV.ne',hy.ne'];ring
    _=_ := markZ_div_markY h.beta_pos h.overlap_range

/-- The proper pure derivative on its actual one-dimensional score graph
at contact, without a singular covariance inverse. -/
theorem sourcePure_contact_complexity_derivative (p : ℕ) (hp : 2 ≤ p) (α : ℝ) (hα : 0 < α)
    {β x Q : ℝ} (h : Certificate (FiniteMixture.pure p hp α hα) β x Q) :
    sourcePureComplexityDerivative p hp α hα Q (markE (FiniteMixture.pure p hp α hα) β x Q)=-(β*x) := by
  let μ := FiniteMixture.pure p hp α hα
  have hb := markB_pos μ h.overlap_range.1
  have hs := Real.sqrt_pos.mpr hb
  have hy := markY_pos h.beta_pos h.overlap_range
  obtain ⟨hr,hRatio⟩ := sourceContact_geometric_ratio μ h
  have hG : SemicirclePotential.resolvent (markK μ β Q/Real.sqrt (markB μ Q))=
      Real.sqrt (markB μ Q)/markY β Q := by
    rw [hRatio,source_semicircle_geometric_resolvent hr]
    field_simp
  unfold sourcePureComplexityDerivative
  rw [←sourcePure_contact_radial_graph p hp α hα h]
  change -markE μ β x Q/μ.xi Q+(p : ℝ)/Real.sqrt (markB μ Q)*
    SemicirclePotential.resolvent (markK μ β Q/Real.sqrt (markB μ Q))=-(β*x)
  rw [hG]
  have he := sourcePure_contact_scalar_slope p hp α hα h
  change markE μ β x Q/μ.xi Q-(p : ℝ)/markY β Q=β*x at he
  have hCancel : (p : ℝ)/Real.sqrt (markB μ Q)*(Real.sqrt (markB μ Q)/markY β Q)=(p : ℝ)/markY β Q := by
    field_simp
  rw [hCancel,neg_div]
  linarith
end SlowEquilibration.SphericalMarkedWindows
