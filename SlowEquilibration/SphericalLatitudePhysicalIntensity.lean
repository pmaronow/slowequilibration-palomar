-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalLatitudeGeometricPrefactor
public import SlowEquilibration.SphericalLatitudeScorePrecision
public import SlowEquilibration.SphericalCountRectangles

@[expose] public section

/-! Literal affine-latitude critical counts as two ordinary scalar score
integrals, with the exact physical GOE mean and geometric normalization. -/

namespace SlowEquilibration.SphericalLatitudeChartKacRice
noncomputable section
open MeasureTheory ProbabilityTheory Set Function Classical
open SlowEquilibration.SphericalModel SlowEquilibration.SphericalGaussianJet
open SlowEquilibration.SphericalMarkedWindows SlowEquilibration.GOEPhysicalPotential
open SlowEquilibration.WholeFieldRegression
open scoped ENNReal
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

@[simp] theorem actualLatitudeScore_zero {n P : ℕ} (c : Degree P → ℝ)
    (w : Vector (n+2)) (e : Vector (n+1) →ₗᵢ[ℝ] Vector (n+2)) (q : ℝ)
    (J : Disorder (n+2) P) (y : Vector (n+1)) :
    actualLatitudeScore c w e q J y 0=latitudeField c J w e q y/((n+2 : ℕ) : ℝ) := by
  simp only [actualLatitudeScore, PiLp.smul_apply, smul_eq_mul, latitudeScoreCLM_apply_zero,
    unpack_euclideanDisorder, jet, iteratedFDeriv_zero_apply, latitudeField]
  ring

def latitudePhysicalIntensity {P : ℕ} (n : ℕ) (c : Degree P → ℝ) (q : ℝ)
    (z : EuclideanSpace ℝ (Fin 2)) : ℝ≥0∞ :=
  ENNReal.ofReal (latitudeGeometricFactor n (latitudeDerivativeVariance c q)) *
    latitudePhysicalScorePdf (n+1) c q z *
      ENNReal.ofReal (physicalMean n (n+3) (latitudeCurvatureVariance c q) (z 1))

theorem latitudePhysicalScorePdf_measurable {P : ℕ} (n : ℕ) (c : Degree P → ℝ) (q : ℝ) :
    Measurable (latitudePhysicalScorePdf n c q) := by
  unfold latitudePhysicalScorePdf latitudeScoreQuadratic
  fun_prop

theorem latitudePhysicalIntensity_measurable {P : ℕ} (n : ℕ) (c : Degree P → ℝ) (q : ℝ) :
    Measurable (latitudePhysicalIntensity n c q) :=
  (measurable_const.mul (latitudePhysicalScorePdf_measurable _ _ _)).mul
    (((physicalMean_measurable _ _ _).comp (by fun_prop)).ennreal_ofReal)

theorem actual_latitude_physical_count_intensity (n : ℕ) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 < Q) (w : Vector (n+3)) (hw : ‖w‖^2=((n+3 : ℕ) : ℝ))
    (e : Vector (n+2) →ₗᵢ[ℝ] Vector (n+3)) (he : ∀ x, inner ℝ (e x) w=0)
    {q : ℝ} (hq0 : q ≠ 0) (hq1 : |q| < 1)
    (f : EuclideanSpace ℝ (Fin 2) → ℝ≥0∞) (hf : Measurable f) :
    let c := centerCoefficients (mixtureCoefficients μ) Q
    (∫⁻ J, actualLatitudeSphereCount c w e q (fun J y => f (actualLatitudeScore c w e q J y)) J
        ∂disorderLaw (n+3) μ.maxDegree) =
      ∫⁻ z, latitudePhysicalIntensity n c q z*f z := by
  dsimp only
  let c := centerCoefficients (mixtureCoefficients μ) Q
  have ha := center_latitudeDerivativeVariance_pos μ hQ hq1
  have hv : 0 ≤ Q^2*μ.xi2 Q := mul_nonneg (sq_nonneg Q) (μ.xi2_pos hQ).le
  have hb : latitudeCurvatureVariance c q=(1-q^2)^2*(Q^2*μ.xi2 Q) := by
    rw [latitudeCurvatureVariance, secondCovariance_center, secondCovariance_mixture]
  let R : ℝ := (((n+3 : ℕ) : ℝ)/((n+2 : ℕ) : ℝ))^(n+1)
  have hR : 0 ≤ R := by dsimp only [R]; positivity
  rw [actual_latitude_normalized_count_intensity (by omega) μ hQ w hw e he hq0 hq1 f hf]
  have hfactor := latitude_combined_geometric_factor n c hq1.le ha
  have hfin : latitudeGradientDensity (n+1) c q * SphereChartVolume.manuscriptRoundVolume (n+1) univ ≠ ⊤ :=
    ENNReal.mul_ne_top (show latitudeGradientDensity (n+1) c q ≠ ⊤ from ENNReal.ofReal_ne_top)
      (manuscriptRoundVolume_mass_ne_top (n+1))
  rw [← lintegral_const_mul' (latitudeGradientDensity (n+1) c q * SphereChartVolume.manuscriptRoundVolume (n+1) univ) _ hfin]
  apply lintegral_congr
  intro z
  rw [latitudeDeterminantMean_eq_physicalMean n hv hq1.le]
  rw [ENNReal.ofReal_mul (show 0 ≤ (((n+3 : ℕ) : ℝ)/((n+2 : ℕ) : ℝ))^(n+1) by positivity)]
  change _=latitudePhysicalIntensity n c q z*f z
  unfold latitudePhysicalIntensity
  rw [hb, latitudeDerivativeVariance, ← hfactor]
  ac_rfl

theorem actual_latitude_rectangular_count (n : ℕ) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 < Q) (w : Vector (n+3)) (hw : ‖w‖^2=((n+3 : ℕ) : ℝ))
    (e : Vector (n+2) →ₗᵢ[ℝ] Vector (n+3)) (he : ∀ x, inner ℝ (e x) w=0)
    {q : ℝ} (hq0 : q ≠ 0) (hq1 : |q| < 1)
    (I U : Set ℝ) (hI : MeasurableSet I) (hU : MeasurableSet U) :
    let c := centerCoefficients (mixtureCoefficients μ) Q
    (∫⁻ J, actualLatitudeSphereCount c w e q
      (fun J y => if actualLatitudeScore c w e q J y ∈ rectangularScoreWindow I U then 1 else 0) J
        ∂disorderLaw (n+3) μ.maxDegree) =
      ∫⁻ h in I, ∫⁻ k in U, latitudePhysicalIntensity n c q (WithLp.toLp 2 ![h,k]) := by
  classical
  dsimp only
  let f : EuclideanSpace ℝ (Fin 2) → ℝ≥0∞ := fun z => if z ∈ rectangularScoreWindow I U then 1 else 0
  have hm : Measurable f := Measurable.ite (rectangularScoreWindow_measurable I U hI hU) measurable_const measurable_const
  apply (actual_latitude_physical_count_intensity n μ hQ w hw e he hq0 hq1 f hm).trans
  dsimp only [f]
  have hf := latitudePhysicalIntensity_measurable n (centerCoefficients (mixtureCoefficients μ) Q) q
  rw [show (fun z => latitudePhysicalIntensity n (centerCoefficients (mixtureCoefficients μ) Q) q z*
      (if z ∈ rectangularScoreWindow I U then 1 else 0))=
    (rectangularScoreWindow I U).indicator (latitudePhysicalIntensity n (centerCoefficients (mixtureCoefficients μ) Q) q) by
      funext z; split_ifs <;> simp_all]
  rw [lintegral_indicator (rectangularScoreWindow_measurable I U hI hU)]
  exact lintegral_rectangularScoreWindow I U _ hf

/-- A literal height window, in physical energy units N times the two
specified endpoints, equals the exact scalar GOE intensity integral. -/
theorem actual_latitude_height_count (n : ℕ) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 < Q) (w : Vector (n+3)) (hw : ‖w‖^2=((n+3 : ℕ) : ℝ))
    (e : Vector (n+2) →ₗᵢ[ℝ] Vector (n+3)) (he : ∀ x, inner ℝ (e x) w=0)
    {q : ℝ} (hq0 : q ≠ 0) (hq1 : |q| < 1) (L U : ℝ) :
    let c := centerCoefficients (mixtureCoefficients μ) Q
    (∫⁻ J, actualLatitudeSphereCount c w e q
      (fun J y => if latitudeField c J w e q y ∈ Icc (((n+3 : ℕ) : ℝ)*L) (((n+3 : ℕ) : ℝ)*U) then 1 else 0) J
        ∂disorderLaw (n+3) μ.maxDegree) =
      ∫⁻ h in Icc L U, ∫⁻ k, latitudePhysicalIntensity n c q (WithLp.toLp 2 ![h,k]) := by
  dsimp only
  let c := centerCoefficients (mixtureCoefficients μ) Q
  have hm : (fun J y => if latitudeField c J w e q y ∈ Icc (((n+3 : ℕ) : ℝ)*L) (((n+3 : ℕ) : ℝ)*U)
      then (1 : ℝ≥0∞) else 0)=
      (fun J y => if actualLatitudeScore c w e q J y ∈ rectangularScoreWindow (Icc L U) univ then 1 else 0) := by
    funext J y
    congr 1
    simp only [rectangularScoreWindow, mem_ofPred_eq, mem_univ, and_true, actualLatitudeScore_zero, mem_Icc]
    rw [le_div_iff₀ (by positivity : (0 : ℝ)<((n+3 : ℕ) : ℝ)),
      div_le_iff₀ (by positivity : (0 : ℝ)<((n+3 : ℕ) : ℝ))]
    simp only [mul_comm]
  change (∫⁻ J, actualLatitudeSphereCount c w e q _ J ∂disorderLaw (n+3) μ.maxDegree)=_
  rw [hm]
  simpa only [Measure.restrict_univ] using
    actual_latitude_rectangular_count n μ hQ w hw e he hq0 hq1 (Icc L U) univ measurableSet_Icc MeasurableSet.univ

end
end SlowEquilibration.SphericalLatitudeChartKacRice
