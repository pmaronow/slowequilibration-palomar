-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntrancePhysicalHittingSourceGradient

/-! The literal source cutoff gradient bound is derived on the original
Gaussian tensor regularity event. All constants use only scalar source
parameters, and contain no dimension, disorder realization, or axis. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.ConditionedEntrance.PhysicalHitting
open MeasureTheory Set Filter
open SphericalModel SphericalForm SphericalAging HardSphereDynamics
open SphericalGaussianJet EntranceSmoothCutoffCalculus EntranceSmoothCutoffTensorApproximation
open SphericalSmoothTensorStationarity SphericalOverlapExponential
open scoped NNReal ENNReal ContDiff InnerProductSpace
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {N : ℕ}

theorem cutoffCorrection_gradient_norm_le (χ : ℝ → ℝ) (hχ : Differentiable ℝ χ)
    (u v : Vector N) (F : Vector N → ℝ) (x : Vector N) (hF : DifferentiableAt ℝ F x)
    {M B G : ℝ} (hM : 0 ≤ M)
    (h1 : |χ (inner ℝ u x)| ≤ M) (h2 : |χ (inner ℝ v x)| ≤ M)
    (hd1 : |deriv χ (inner ℝ u x)| ≤ M) (hd2 : |deriv χ (inner ℝ v x)| ≤ M)
    (hB : |F x| ≤ B) (hG : ‖gradient F x‖ ≤ G) :
    ‖gradient (cutoffCorrection χ χ u v F) x‖ ≤ M^2 * (B * (‖u‖ + ‖v‖) + G) := by
  have hb1 : |deriv χ (inner ℝ u x) * χ (inner ℝ v x)| ≤ M^2 := by
    rw [abs_mul,pow_two]
    exact mul_le_mul hd1 h2 (abs_nonneg _) hM
  have hb2 : |χ (inner ℝ u x) * deriv χ (inner ℝ v x)| ≤ M^2 := by
    rw [abs_mul,pow_two]
    exact mul_le_mul h1 hd2 (abs_nonneg _) hM
  have hb3 : |χ (inner ℝ u x) * χ (inner ℝ v x)| ≤ M^2 := by
    rw [abs_mul,pow_two]
    exact mul_le_mul h1 h2 (abs_nonneg _) hM
  rw [cutoffCorrection_gradient χ χ u v F x (hχ _) (hχ _) hF]
  calc
    _ ≤ (‖(deriv χ (inner ℝ u x) * χ (inner ℝ v x) * F x) • u‖ +
        ‖(χ (inner ℝ u x) * deriv χ (inner ℝ v x) * F x) • v‖) +
        ‖(χ (inner ℝ u x) * χ (inner ℝ v x)) • gradient F x‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ (M^2 * B * ‖u‖ + M^2 * B * ‖v‖) + M^2 * G := by
      simp only [norm_smul,Real.norm_eq_abs,abs_mul]
      rw [abs_mul] at hb1 hb2 hb3
      exact add_le_add (add_le_add
        (mul_le_mul_of_nonneg_right (mul_le_mul hb1 hB (abs_nonneg _) (sq_nonneg _)) (norm_nonneg _))
        (mul_le_mul_of_nonneg_right (mul_le_mul hb2 hB (abs_nonneg _) (sq_nonneg _)) (norm_nonneg _)))
        (mul_le_mul hb3 hG (norm_nonneg _) (sq_nonneg _))
    _ = _ := by ring

def scalarCutoffConstant (χ : ℝ → ℝ) (hχ : ContDiff ℝ 2 χ) (R : ℝ) : ℝ :=
  max 1 (max
    ((isCompact_Icc : IsCompact (Icc (-R) R)).exists_bound_of_continuousOn
      hχ.continuous.continuousOn).choose
    ((isCompact_Icc : IsCompact (Icc (-R) R)).exists_bound_of_continuousOn
      (hχ.of_le (by norm_num)).continuous_deriv_one.continuousOn).choose)

theorem scalarCutoffConstant_nonneg (χ : ℝ → ℝ) (hχ : ContDiff ℝ 2 χ) (R : ℝ) :
    0 ≤ scalarCutoffConstant χ hχ R :=
  zero_le_one.trans (le_max_left _ _)

theorem scalarCutoffConstant_bounds (χ : ℝ → ℝ) (hχ : ContDiff ℝ 2 χ) (R r : ℝ)
    (hr : r ∈ Icc (-R) R) :
    |χ r| ≤ scalarCutoffConstant χ hχ R ∧ |deriv χ r| ≤ scalarCutoffConstant χ hχ R := by
  let M0 := ((isCompact_Icc : IsCompact (Icc (-R) R)).exists_bound_of_continuousOn
    hχ.continuous.continuousOn).choose
  let M1 := ((isCompact_Icc : IsCompact (Icc (-R) R)).exists_bound_of_continuousOn
    (hχ.of_le (by norm_num)).continuous_deriv_one.continuousOn).choose
  have h0 : |χ r| ≤ M0 := by
    simpa only [Real.norm_eq_abs] using
      ((isCompact_Icc : IsCompact (Icc (-R) R)).exists_bound_of_continuousOn
        hχ.continuous.continuousOn).choose_spec r hr
  have h1 : |deriv χ r| ≤ M1 := by
    simpa only [Real.norm_eq_abs] using
      ((isCompact_Icc : IsCompact (Icc (-R) R)).exists_bound_of_continuousOn
        (hχ.of_le (by norm_num)).continuous_deriv_one.continuousOn).choose_spec r hr
  exact ⟨h0.trans ((le_max_left M0 M1).trans (le_max_right 1 (max M0 M1))),
    h1.trans ((le_max_right M0 M1).trans (le_max_right 1 (max M0 M1)))⟩

def sourceArgumentRadius (μ : FiniteMixture) (Q α : ℝ) : ℝ :=
  1 + (1 + centerConstant μ Q) / α

def sourceGradientConstant (μ : FiniteMixture) (Q h k α : ℝ)
    (χ : ℝ → ℝ) (hχ : ContDiff ℝ 2 χ) : ℝ :=
  derivativeConstant (mixtureCoefficients μ) +
    (scalarCutoffConstant χ hχ (sourceArgumentRadius μ Q α))^2 *
      (thetaConstant μ Q * markConstant μ Q h k * (1 + centerConstant μ Q) / α +
        thetaConstant μ Q * (markConstant μ Q h k + centerConstant μ Q))

theorem sourceGradientConstant_nonneg (μ : FiniteMixture) (Q h k : ℝ)
    {α : ℝ} (hα : 0 < α) (χ : ℝ → ℝ) (hχ : ContDiff ℝ 2 χ) :
    0 ≤ sourceGradientConstant μ Q h k α χ hχ := by
  unfold sourceGradientConstant
  have := (derivativeConstant_pos (mixtureCoefficients μ)).le
  have := (thetaConstant_pos μ Q).le
  have := markConstant_nonneg μ Q h k
  have := (centerConstant_pos μ Q).le
  positivity

/-- The source Hamiltonian's actual ambient gradient is bounded by
C sqrt N on the original Gaussian regularity event; no gradient bound
or conditional diffusion estimate is supplied as a hypothesis. -/
theorem regular_source_gradient_bound (D : SmoothKilled.SourceData N)
    (hJ : D.disorder ∈ regularDisorder) (x : Vector N) (hx : OnSphere x) :
    ‖gradient D.hamiltonian x‖ ≤
      sourceGradientConstant D.mixture D.Q D.energyMark D.radialMark D.cutoffScale D.cutoff D.cutoff_smooth *
        Real.sqrt (N : ℝ) := by
  let c := centerCoefficients (mixtureCoefficients D.mixture) D.Q
  let G := surfaceGradient (field c D.disorder) D.axis
  let F := regressionCorrection D.mixture D.Q D.axis G (field c D.disorder D.axis)
    (jet c 1 D.axis (fun _ => D.axis) D.disorder) D.energyMark D.radialMark
  let v1 := ((N : ℝ) * D.cutoffScale)⁻¹ • D.axis
  let v2 := ((N : ℝ) * D.cutoffScale)⁻¹ • G
  let A := thetaConstant D.mixture D.Q
  let K := centerConstant D.mixture D.Q
  let M := markConstant D.mixture D.Q D.energyMark D.radialMark
  let R := sourceArgumentRadius D.mixture D.Q D.cutoffScale
  let L := scalarCutoffConstant D.cutoff D.cutoff_smooth R
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr (by have := D.dimension_ge_one; omega)
  have hα := D.cutoffScale_pos
  have hK : 0 ≤ K := (centerConstant_pos _ _).le
  have hA : 0 ≤ A := (thetaConstant_pos _ _).le
  have hM : 0 ≤ M := markConstant_nonneg _ _ _ _
  have hL : 0 ≤ L := scalarCutoffConstant_nonneg _ _ _
  have hxn := LandscapeDerivatives.sphere_norm x ((onSphere_iff_norm_sq x).mp hx)
  have hun := LandscapeDerivatives.sphere_norm D.axis ((onSphere_iff_norm_sq D.axis).mp D.axis_onSphere)
  have hG : ‖G‖ ≤ K * Real.sqrt (N : ℝ) := (regular_center_observations D hJ).2.2
  have hv1 : ‖v1‖ = ((N : ℝ) * D.cutoffScale)⁻¹ * Real.sqrt (N : ℝ) := by
    simp only [v1,norm_smul,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr (mul_nonneg hNr.le hα.le)),hun]
  have hv2 : ‖v2‖ ≤ ((N : ℝ) * D.cutoffScale)⁻¹ * K * Real.sqrt (N : ℝ) := by
    simp only [v2,norm_smul,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr (mul_nonneg hNr.le hα.le))]
    exact (mul_le_mul_of_nonneg_left hG (inv_nonneg.mpr (mul_nonneg hNr.le hα.le))).trans_eq (by ring)
  have harg1 : |inner ℝ v1 x| ≤ 1 / D.cutoffScale := by
    calc
      _ ≤ ‖v1‖ * ‖x‖ := abs_real_inner_le_norm _ _
      _ = 1 / D.cutoffScale := by
        rw [hv1,hxn,mul_assoc,Real.mul_self_sqrt hNr.le]
        field_simp
  have harg2 : |inner ℝ v2 x| ≤ K / D.cutoffScale := by
    calc
      _ ≤ ‖v2‖ * ‖x‖ := abs_real_inner_le_norm _ _
      _ ≤ (((N : ℝ) * D.cutoffScale)⁻¹ * K * Real.sqrt (N : ℝ)) * Real.sqrt (N : ℝ) := by
        rw [hxn]
        exact mul_le_mul_of_nonneg_right hv2 (Real.sqrt_nonneg _)
      _ = K / D.cutoffScale := by
        rw [mul_assoc,Real.mul_self_sqrt hNr.le]
        field_simp
  have hr1 : inner ℝ v1 x ∈ Icc (-R) R := by
    apply abs_le.mp
    apply harg1.trans
    change 1 / D.cutoffScale ≤ 1 + (1 + K) / D.cutoffScale
    rw [add_div]
    linarith [div_nonneg hK hα.le]
  have hr2 : inner ℝ v2 x ∈ Icc (-R) R := by
    apply abs_le.mp
    apply harg2.trans
    change K / D.cutoffScale ≤ 1 + (1 + K) / D.cutoffScale
    rw [add_div]
    linarith [one_div_pos.mpr hα]
  obtain ⟨h1,hd1⟩ := scalarCutoffConstant_bounds D.cutoff D.cutoff_smooth R (inner ℝ v1 x) hr1
  obtain ⟨h2,hd2⟩ := scalarCutoffConstant_bounds D.cutoff D.cutoff_smooth R (inner ℝ v2 x) hr2
  obtain ⟨hval,hgrad⟩ := regular_source_regression_bounds D hJ x hx
  change |F x| ≤ A * M * (N : ℝ) at hval
  change ‖gradient F x‖ ≤ A * (M + K) * Real.sqrt (N : ℝ) at hgrad
  have hF := (regressionCorrection_contDiff D.dimension_ge_one D.mixture D.Q D.axis G
    (field c D.disorder D.axis) (jet c 1 D.axis (fun _ => D.axis) D.disorder) D.energyMark D.radialMark).differentiable (by simp)
  have hcor := cutoffCorrection_gradient_norm_le D.cutoff
    (D.cutoff_smooth.differentiable (by norm_num)) v1 v2 F x (hF x) hL h1 h2 hd1 hd2 hval hgrad
  have hvs : ‖v1‖ + ‖v2‖ ≤ ((N : ℝ) * D.cutoffScale)⁻¹ * (1 + K) * Real.sqrt (N : ℝ) := by
    exact (add_le_add hv1.le hv2).trans_eq (by ring)
  have hc : ‖gradient (cutoffCorrection D.cutoff D.cutoff v1 v2 F) x‖ ≤
      L^2 * (A * M * (1 + K) / D.cutoffScale + A * (M + K)) * Real.sqrt (N : ℝ) := by
    apply hcor.trans
    calc
      _ ≤ L^2 * ((A * M * (N : ℝ)) *
          (((N : ℝ) * D.cutoffScale)⁻¹ * (1 + K) * Real.sqrt (N : ℝ)) +
          A * (M + K) * Real.sqrt (N : ℝ)) :=
        mul_le_mul_of_nonneg_left (add_le_add
          (mul_le_mul_of_nonneg_left hvs (mul_nonneg (mul_nonneg hA hM) hNr.le)) le_rfl) (sq_nonneg _)
      _ = _ := by field_simp
  have hb := (field_regularDisorder_ball_bounds D.dimension_ge_one (mixtureCoefficients D.mixture)
    D.disorder hJ x hxn.le).2.1
  have hbase := (fieldOfMixture_contDiff D.mixture D.disorder).differentiable (by simp)
  have hcut := (((D.cutoff_smooth.comp (innerSL ℝ v1).contDiff).mul
    (D.cutoff_smooth.comp (innerSL ℝ v2).contDiff)).mul
      ((regressionCorrection_contDiff D.dimension_ge_one D.mixture D.Q D.axis G
        (field c D.disorder D.axis) (jet c 1 D.axis (fun _ => D.axis) D.disorder) D.energyMark D.radialMark).of_le (by simp))).differentiable (by norm_num)
  have he : gradient D.hamiltonian x = gradient (fieldOfMixture D.mixture D.disorder) x +
      gradient (cutoffCorrection D.cutoff D.cutoff v1 v2 F) x := by
    change gradient (fun y => fieldOfMixture D.mixture D.disorder y + cutoffCorrection D.cutoff D.cutoff v1 v2 F y) x = _
    exact ((hbase x).hasFDerivAt.add (hcut x).hasFDerivAt).hasGradientAt.gradient.trans
      ((InnerProductSpace.toDual ℝ (Vector N)).symm.map_add _ _)
  rw [he]
  exact (norm_add_le _ _).trans ((add_le_add hb hc).trans_eq (by
    dsimp [sourceGradientConstant,L,R,A,M,K]
    ring))

/-- Fully concrete regular-source cap hitting endpoint. The generic C1
gradient hypothesis has been discharged from actual tensor regularity. -/
theorem regular_source_hitting_discounted_mass (D : SmoothKilled.SourceData N)
    (hJ : D.disorder ∈ regularDisorder) {β : ℝ} (hβ : 0 ≤ β)
    (x : Vector N) (hx : OnSphere x) {α : ℝ} (hα : 0 < α)
    {θ : ℝ} (hθ : 0 ≤ θ) (H T : ℝ≥0) (hT : 0 < T)
    (hsmall : 4 * (1 + β * sourceGradientConstant D.mixture D.Q D.energyMark D.radialMark
      D.cutoffScale D.cutoff D.cutoff_smooth) * (T : ℝ) ≤ α / 12) :
    exposureFactor θ H T *
      ((VectorBrownian.law N).real {omega | ∃ t : ℝ≥0,t ≤ H ∧
        α / 2 ≤ |overlapValue D.axis (SmoothKilled.process D β x t omega)|} -
          (SphericalOverlapExponential.gridSize H T : ℝ) * (2 * Real.exp (-(N : ℝ) * (α / 12)^2 / (16 * (T : ℝ))))) ≤
      ∫ t in (0 : ℝ)..((H + T : ℝ≥0) : ℝ),Real.exp (-θ * t) *
        SmoothKilled.expectation D β (capKilling α D.axis) t.toNNReal (capKilling α D.axis) x :=
  source_hitting_discounted_mass D hβ
    (sourceGradientConstant_nonneg D.mixture D.Q D.energyMark D.radialMark D.cutoffScale_pos D.cutoff D.cutoff_smooth)
    (regular_source_gradient_bound D hJ) x hx hα hθ H T hT hsmall

end SlowEquilibration.ConditionedEntrance.PhysicalHitting
