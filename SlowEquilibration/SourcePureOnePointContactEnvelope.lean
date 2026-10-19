-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SphericalProperPureContactComplexity
public import SlowEquilibration.SphericalCountPrefactors
public import SlowEquilibration.SphericalPureLocalMaxPhysicalIntensity
public import SlowEquilibration.PureScalarComplexityGeometry

/-! A source-derived global energy loss and the corresponding genuine pure
one-point intensity envelope on the positive exterior score graph. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalMarkedWindows
open Set Filter TwoAtomStationarity SphericalTAPCertificate SphericalModel
open PureScalarComplexityGeometry
open scoped Topology ENNReal
set_option maxHeartbeats 500000

private theorem pure_scalar_curvature_nonneg (p : ℕ) (hp : 2 ≤ p)
    (a : ℝ) (ha : 0 < a) {Q : ℝ} (hQ : 0 < Q) :
    0 ≤ curvature ((FiniteMixture.pure p hp a ha).xi Q)
      (Q^2*(FiniteMixture.pure p hp a ha).xi2 Q) (p : ℝ) := by
  let μ := FiniteMixture.pure p hp a ha
  have hV : 0 < μ.xi Q := μ.xi_pos hQ
  have hB : 0 < Q^2*μ.xi2 Q := mul_pos (sq_pos_of_pos hQ) (μ.xi2_pos hQ)
  have hId := (sourcePure_contact_covariance_scalars p hp a ha Q).2
  change Q^2*μ.xi2 Q = (p : ℝ)*((p : ℝ)-1)*μ.xi Q at hId
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp
  unfold curvature
  rw [hId]
  apply sub_nonneg.mpr
  have hDen : 0 < 2*((p : ℝ)*((p : ℝ)-1)*μ.xi Q) := by rw [←hId]; positivity
  apply (div_le_div_iff₀ hDen hV).mpr
  have hP : 0 ≤ (p : ℝ)*((p : ℝ)-2) := mul_nonneg (by linarith) (by linarith)
  nlinarith [mul_nonneg hP hV.le]

/-- The true scalar complexity has the contact tangent as a global upper
support, including scores inside the GOE spectral support. -/
theorem sourcePureMarkedComplexity_global_linear_loss
    (p : ℕ) (hp : 2 ≤ p) (a : ℝ) (ha : 0 < a)
    {β x Q : ℝ} (h : Certificate (FiniteMixture.pure p hp a ha) β x Q)
    (e : ℝ) :
    pureMarkedComplexity p hp a ha Q e ≤
      -(β*x)*(e-markE (FiniteMixture.pure p hp a ha) β x Q) := by
  let μ := FiniteMixture.pure p hp a ha
  let V := μ.xi Q
  let b := Q^2*μ.xi2 Q
  let E := markE μ β x Q
  let c := 1/2+Real.log (b/(Q*μ.xi1 Q))/2
  have hV : 0 < V := μ.xi_pos h.overlap_range.1
  have hb : 0 < b := mul_pos (sq_pos_of_pos h.overlap_range.1) (μ.xi2_pos h.overlap_range.1)
  have hedge : 2 < (p : ℝ)*E/Real.sqrt b := by
    apply (lt_div_iff₀ (Real.sqrt_pos.mpr hb)).mpr
    rw [←sourcePure_contact_radial_graph p hp a ha h]
    exact sourceContact_markK_above_edge μ h
  have hZero : profile V b (p : ℝ) c E=0 := sourcePure_contact_complexity_zero p hp a ha h
  have hSlope : -E/V+(p : ℝ)/Real.sqrt b*
      SemicirclePotential.resolvent ((p : ℝ)*E/Real.sqrt b)=-(β*x) :=
    sourcePure_contact_complexity_derivative p hp a ha h
  have hLoss := profile_contact_loss hV hb hedge hZero hSlope e
  have hκ := pure_scalar_curvature_nonneg p hp a ha h.overlap_range.1
  have hQuad : 0 ≤ curvature V b (p : ℝ)/2*(e-E)^2 := by positivity
  change profile V b (p : ℝ) c e ≤ -(β*x)*(e-E)
  change profile V b (p : ℝ) c e ≤ -(β*x)*(e-E)-curvature V b (p : ℝ)/2*(e-E)^2 at hLoss
  linarith

/-- Uniform upper envelope for the actual all-critical pure physical energy
intensity on every fixed interval to the right of the source contact. The
polynomial prefactor and the full source slope are retained. -/
theorem sourcePureCriticalPhysicalIntensity_right_contact_envelope
    (p : ℕ) (hp : 2 ≤ p) (a : ℝ) (ha : 0 < a)
    {β x Q : ℝ} (h : Certificate (FiniteMixture.pure p hp a ha) β x Q)
    {δ : ℝ} (_hδ : 0 ≤ δ) :
    let μ := FiniteMixture.pure p hp a ha
    let E := markE μ β x Q
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ∀ e ∈ Icc E (E+δ),
      pureCriticalPhysicalIntensity n p hp a ha Q ((n+2 : ℕ)*e) ≤
        ENNReal.ofReal (C / Real.sqrt (n+2 : ℕ) *
          Real.exp (-(β*x)*((n+2 : ℕ)*(e-E)))) := by
  let μ := FiniteMixture.pure p hp a ha
  let E := markE μ β x Q
  let edge := 2*Real.sqrt (Q^2*μ.xi2 Q)
  let g := ((p : ℝ)*E-edge)/2
  have hpPos : 0 < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
  have hGap : edge < (p : ℝ)*E := by
    rw [←sourcePure_contact_radial_graph p hp a ha h]
    exact sourceContact_markK_above_edge μ h
  have hg : 0 < g := by dsimp [g]; linarith
  obtain ⟨c,C,hc,hC,hPref⟩ := actual_pure_intensity_prefactors
    p hp a ha h.overlap_range.1 (Z := (p : ℝ)*(E+δ)) hg
  refine ⟨C,hC,?_⟩
  intro n e he
  have hEdge : (p : ℝ)*e ∈ Icc (edge+g) ((p : ℝ)*(E+δ)) := by
    constructor
    · have hmul := mul_le_mul_of_nonneg_left he.1 hpPos.le
      dsimp [edge,g]
      linarith
    · exact mul_le_mul_of_nonneg_left he.2 hpPos.le
  have hUpper : pureCriticalPhysicalIntensity n p hp a ha Q ((n+2 : ℕ)*e) ≤
      ENNReal.ofReal (C*(Real.sqrt (n+2 : ℕ))⁻¹ *
        Real.exp ((n+2 : ℕ)*pureMarkedComplexity p hp a ha Q e)) := by
    have hMul := mul_le_mul_right (hPref n e hEdge).2
      (ENNReal.ofReal ((n+2 : ℕ):ℝ)⁻¹)
    have heq : (((n+2 : ℕ):ℝ)*e)/(n+2 : ℕ)=e := mul_div_cancel_left₀ _ (by positivity)
    simp only [pureCriticalPhysicalIntensity,heq]
    rw [inverse_sqrt_dimension_prefactor] at hMul
    exact hMul
  have hLoss := sourcePureMarkedComplexity_global_linear_loss p hp a ha h e
  have hN : 0 ≤ ((n+2 : ℕ) : ℝ) := by positivity
  have hExp : Real.exp ((n+2 : ℕ)*pureMarkedComplexity p hp a ha Q e) ≤
      Real.exp (-(β*x)*((n+2 : ℕ)*(e-E))) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left hLoss hN]
  have hConst : 0 ≤ C*(Real.sqrt (n+2 : ℕ))⁻¹ := by positivity
  have hReal := mul_le_mul_of_nonneg_left hExp hConst
  calc
    pureCriticalPhysicalIntensity n p hp a ha Q ((n+2 : ℕ)*e) ≤
        ENNReal.ofReal (C*(Real.sqrt (n+2 : ℕ))⁻¹ *
          Real.exp ((n+2 : ℕ)*pureMarkedComplexity p hp a ha Q e)) := hUpper
    _ ≤ ENNReal.ofReal (C / Real.sqrt (n+2 : ℕ) *
          Real.exp (-(β*x)*((n+2 : ℕ)*(e-E)))) := by
      apply ENNReal.ofReal_le_ofReal
      convert hReal using 1; ring

end SlowEquilibration.SphericalMarkedWindows
