-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntrancePhysicalHittingSource

/-! Dimension-independent scalar constants for the literal source cutoff
gradient on the actual original disorder regularity event. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.ConditionedEntrance.PhysicalHitting
open MeasureTheory Set Filter
open SphericalModel SphericalForm SphericalAging HardSphereDynamics
open SphericalGaussianJet EntranceSmoothCutoffCalculus EntranceSmoothCutoffTensorApproximation
open scoped NNReal ENNReal ContDiff InnerProductSpace
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {N : ℕ}

def thetaConstant (μ : FiniteMixture) (Q : ℝ) : ℝ :=
  1 + coefficientBound μ.coeff.support (valueCoefficient μ Q) +
    coefficientBound μ.coeff.support (radialCoefficient μ Q) +
    coefficientBound μ.coeff.support (tangentCoefficient μ Q) +
    coefficientBound μ.coeff.support (fun p => valueCoefficient μ Q p * (p : ℝ)) +
    coefficientBound μ.coeff.support (fun p => radialCoefficient μ Q p * (p : ℝ)) +
    coefficientBound μ.coeff.support (fun p => tangentCoefficient μ Q p * ((p - 1 : ℕ) : ℝ))

theorem thetaConstant_pos (μ : FiniteMixture) (Q : ℝ) : 0 < thetaConstant μ Q := by
  unfold thetaConstant
  unfold coefficientBound
  positivity

theorem thetaConstant_bounds (μ : FiniteMixture) (Q r : ℝ) (hr : |r| ≤ 1) :
    |valueTheta μ Q r| ≤ thetaConstant μ Q ∧
    |radialTheta μ Q r| ≤ thetaConstant μ Q ∧
    |tangentTheta μ Q r| ≤ thetaConstant μ Q ∧
    |valueThetaDerivative μ Q r| ≤ thetaConstant μ Q ∧
    |radialThetaDerivative μ Q r| ≤ thetaConstant μ Q ∧
    |tangentThetaDerivative μ Q r| ≤ thetaConstant μ Q := by
  have hb (b : ℕ → ℝ) (n : ℕ → ℕ) :
      |monomialSum μ.coeff.support b n r| ≤ coefficientBound μ.coeff.support b := by
    simpa only [pow_zero,mul_one] using
      monomialSum_abs_le μ.coeff.support b n 0 (fun _ _ => Nat.zero_le _) hr
  have h1 := coefficientBound_nonneg μ.coeff.support (valueCoefficient μ Q)
  have h2 := coefficientBound_nonneg μ.coeff.support (radialCoefficient μ Q)
  have h3 := coefficientBound_nonneg μ.coeff.support (tangentCoefficient μ Q)
  have h4 := coefficientBound_nonneg μ.coeff.support (fun p => valueCoefficient μ Q p * (p : ℝ))
  have h5 := coefficientBound_nonneg μ.coeff.support (fun p => radialCoefficient μ Q p * (p : ℝ))
  have h6 := coefficientBound_nonneg μ.coeff.support (fun p => tangentCoefficient μ Q p * ((p - 1 : ℕ) : ℝ))
  refine ⟨(hb _ _).trans ?_,(hb _ _).trans ?_,(hb _ _).trans ?_,
    (hb _ _).trans ?_,(hb _ _).trans ?_,(hb _ _).trans ?_⟩ <;> unfold thetaConstant <;> linarith

theorem scalar_regression_bound {A a b c X Y Z : ℝ}
    (ha : |a| ≤ A) (hb : |b| ≤ A) (hc : |c| ≤ A) :
    |a * X + b * Y - c * Z| ≤ A * (|X| + |Y| + |Z|) := by
  calc
    _ ≤ |a * X + b * Y| + |c * Z| := by
      simpa only [sub_zero,zero_sub,abs_neg] using abs_sub_le (a * X + b * Y) 0 (c * Z)
    _ ≤ (|a * X| + |b * Y|) + |c * Z| := add_le_add (abs_add_le _ _) le_rfl
    _ ≤ (A * |X| + A * |Y|) + A * |Z| := by
      simp only [abs_mul]
      exact add_le_add (add_le_add (mul_le_mul_of_nonneg_right ha (abs_nonneg _))
        (mul_le_mul_of_nonneg_right hb (abs_nonneg _)))
        (mul_le_mul_of_nonneg_right hc (abs_nonneg _))
    _ = _ := by ring

def centerConstant (μ : FiniteMixture) (Q : ℝ) : ℝ :=
  derivativeConstant (centerCoefficients (mixtureCoefficients μ) Q)

def markConstant (μ : FiniteMixture) (Q h k : ℝ) : ℝ :=
  |h| + |k| + 3 * centerConstant μ Q

theorem centerConstant_pos (μ : FiniteMixture) (Q : ℝ) : 0 < centerConstant μ Q :=
  derivativeConstant_pos _

theorem markConstant_nonneg (μ : FiniteMixture) (Q h k : ℝ) : 0 ≤ markConstant μ Q h k := by
  unfold markConstant
  have := (centerConstant_pos μ Q).le
  positivity

/-- All center observations are taken from the same actual regular
disorder bank. Neither center value nor radial jet is independent data. -/
theorem regular_center_observations (D : SmoothKilled.SourceData N)
    (hJ : D.disorder ∈ regularDisorder) :
    let c := centerCoefficients (mixtureCoefficients D.mixture) D.Q
    |field c D.disorder D.axis| ≤ centerConstant D.mixture D.Q * (N : ℝ) ∧
    |jet c 1 D.axis (fun _ => D.axis) D.disorder| ≤ centerConstant D.mixture D.Q * (N : ℝ) ∧
    ‖surfaceGradient (field c D.disorder) D.axis‖ ≤ centerConstant D.mixture D.Q * Real.sqrt (N : ℝ) := by
  dsimp only
  have hn := LandscapeDerivatives.sphere_norm D.axis
    ((onSphere_iff_norm_sq D.axis).mp D.axis_onSphere)
  have hg := field_regularDisorder_ball_bounds D.dimension_ge_one
    (centerCoefficients (mixtureCoefficients D.mixture) D.Q) D.disorder hJ D.axis hn.le
  refine ⟨hg.1,?_,?_⟩
  · have he : jet (centerCoefficients (mixtureCoefficients D.mixture) D.Q) 1 D.axis
        (fun _ => D.axis) D.disorder =
        inner ℝ (gradient (field (centerCoefficients (mixtureCoefficients D.mixture) D.Q) D.disorder) D.axis) D.axis := by
      simp only [jet,iteratedFDeriv_one_apply,inner_gradient_left]
    rw [he]
    calc
      _ ≤ ‖gradient (field (centerCoefficients (mixtureCoefficients D.mixture) D.Q) D.disorder) D.axis‖ * ‖D.axis‖ := abs_real_inner_le_norm _ _
      _ ≤ (centerConstant D.mixture D.Q * Real.sqrt (N : ℝ)) * Real.sqrt (N : ℝ) := by
        rw [hn]
        exact mul_le_mul_of_nonneg_right hg.2.1 (Real.sqrt_nonneg _)
      _ = _ := by rw [mul_assoc,Real.mul_self_sqrt (Nat.cast_nonneg N)]
  · unfold surfaceGradient
    have hp := projection_norm_le_onSphere (show N ≠ 0 by have := D.dimension_ge_one; omega)
      D.axis (gradient (field (centerCoefficients (mixtureCoefficients D.mixture) D.Q) D.disorder) D.axis)
      D.axis_onSphere
    simpa only [tangentProjection_apply,centerConstant] using hp.trans hg.2.1

/-- True regular-disorder value and gradient bounds for the literal
source regression polynomial, with scalar constants independent of N. -/
theorem regular_source_regression_bounds (D : SmoothKilled.SourceData N)
    (hJ : D.disorder ∈ regularDisorder) (x : Vector N) (hx : OnSphere x) :
    let c := centerCoefficients (mixtureCoefficients D.mixture) D.Q
    let G := surfaceGradient (field c D.disorder) D.axis
    let F := regressionCorrection D.mixture D.Q D.axis G (field c D.disorder D.axis)
      (jet c 1 D.axis (fun _ => D.axis) D.disorder) D.energyMark D.radialMark
    |F x| ≤ thetaConstant D.mixture D.Q * markConstant D.mixture D.Q D.energyMark D.radialMark * (N : ℝ) ∧
    ‖gradient F x‖ ≤ thetaConstant D.mixture D.Q *
      (markConstant D.mixture D.Q D.energyMark D.radialMark + centerConstant D.mixture D.Q) * Real.sqrt (N : ℝ) := by
  dsimp only
  let c := centerCoefficients (mixtureCoefficients D.mixture) D.Q
  let G := surfaceGradient (field c D.disorder) D.axis
  let Hq := field c D.disorder D.axis
  let Kq := jet c 1 D.axis (fun _ => D.axis) D.disorder
  let A := thetaConstant D.mixture D.Q
  let K := centerConstant D.mixture D.Q
  let M := markConstant D.mixture D.Q D.energyMark D.radialMark
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr (by have := D.dimension_ge_one; omega)
  have hn := LandscapeDerivatives.sphere_norm x ((onSphere_iff_norm_sq x).mp hx)
  obtain ⟨hH,hK,hG⟩ := regular_center_observations D hJ
  change |Hq| ≤ K * (N : ℝ) at hH
  change |Kq| ≤ K * (N : ℝ) at hK
  change ‖G‖ ≤ K * Real.sqrt (N : ℝ) at hG
  have hr : |overlap x D.axis| ≤ 1 := abs_le.mpr
    (overlap_mem_Icc_of_norm_sq D.dimension_ge_one x D.axis
      ((onSphere_iff_norm_sq x).mp hx) ((onSphere_iff_norm_sq D.axis).mp D.axis_onSphere))
  obtain ⟨h1,h2,h3,h4,h5,h6⟩ := thetaConstant_bounds D.mixture D.Q (overlap x D.axis) hr
  have hinner : |inner ℝ G x| ≤ K * (N : ℝ) := by
    calc
      _ ≤ ‖G‖ * ‖x‖ := abs_real_inner_le_norm _ _
      _ ≤ (K * Real.sqrt (N : ℝ)) * Real.sqrt (N : ℝ) := by
        rw [hn]
        exact mul_le_mul_of_nonneg_right hG (Real.sqrt_nonneg _)
      _ = _ := by rw [mul_assoc,Real.mul_self_sqrt hNr.le]
  have hm : |(N : ℝ) * D.energyMark - Hq| + |(N : ℝ) * D.radialMark - Kq| +
      |inner ℝ G x| ≤ M * (N : ℝ) := by
    have he0 : |(N : ℝ) * D.energyMark - Hq| ≤ |(N : ℝ) * D.energyMark| + |Hq| := by
      simpa only [sub_zero,zero_sub,abs_neg] using abs_sub_le ((N : ℝ) * D.energyMark) 0 Hq
    have hk0 : |(N : ℝ) * D.radialMark - Kq| ≤ |(N : ℝ) * D.radialMark| + |Kq| := by
      simpa only [sub_zero,zero_sub,abs_neg] using abs_sub_le ((N : ℝ) * D.radialMark) 0 Kq
    have he := he0.trans (add_le_add le_rfl hH)
    have hk := hk0.trans (add_le_add le_rfl hK)
    rw [abs_mul,abs_of_nonneg hNr.le] at he hk
    dsimp [M,markConstant,K] at *
    nlinarith
  have hval : |regressionCorrection D.mixture D.Q D.axis G Hq Kq D.energyMark D.radialMark x| ≤ A * M * (N : ℝ) := by
    exact (scalar_regression_bound h1 h2 h3).trans
      ((mul_le_mul_of_nonneg_left hm (thetaConstant_pos _ _).le).trans_eq (by ring))
  have hrad : |correctionRadialCoefficient D.mixture D.Q D.axis G Hq Kq D.energyMark D.radialMark x| ≤ A * M * (N : ℝ) := by
    exact (scalar_regression_bound h4 h5 h6).trans
      ((mul_le_mul_of_nonneg_left hm (thetaConstant_pos _ _).le).trans_eq (by ring))
  refine ⟨hval,?_⟩
  rw [(regressionCorrection_hasGradientAt D.mixture D.Q D.axis G Hq Kq D.energyMark D.radialMark x).gradient]
  have hdiv : |correctionRadialCoefficient D.mixture D.Q D.axis G Hq Kq D.energyMark D.radialMark x / (N : ℝ)| ≤ A * M := by
    rw [abs_div,abs_of_pos hNr]
    exact (div_le_iff₀ hNr).mpr hrad
  have haxis := LandscapeDerivatives.sphere_norm D.axis ((onSphere_iff_norm_sq D.axis).mp D.axis_onSphere)
  calc
    _ ≤ ‖(correctionRadialCoefficient D.mixture D.Q D.axis G Hq Kq D.energyMark D.radialMark x / (N : ℝ)) • D.axis‖ +
        ‖tangentTheta D.mixture D.Q (overlap x D.axis) • G‖ := norm_sub_le _ _
    _ ≤ (A * M) * Real.sqrt (N : ℝ) + A * (K * Real.sqrt (N : ℝ)) := by
      simp only [norm_smul,Real.norm_eq_abs,haxis]
      exact add_le_add (mul_le_mul_of_nonneg_right hdiv (Real.sqrt_nonneg _))
        (mul_le_mul h3 hG (norm_nonneg _) (thetaConstant_pos _ _).le)
    _ = _ := by ring

end SlowEquilibration.ConditionedEntrance.PhysicalHitting
