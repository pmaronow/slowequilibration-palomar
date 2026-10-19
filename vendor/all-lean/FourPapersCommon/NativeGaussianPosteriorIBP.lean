module

public import FourPapersCommon.NativePinnedPosteriorJets
public import QuantitativePaper.BoundedJets
public import OverlapPaper.CavityGaussianIBP
public import FourPapersCommon.GaussianSelectedCoordinateScale

@[expose] public section

/-! Gaussian integration by parts against a genuine smooth posterior
correction. Exponential growth and all Stein regularity bounds are
derived from the actual globally bounded positive jets. -/
noncomputable section
open MeasureTheory ProbabilityTheory QuantitativePaper OverlapPaper
open scoped ContDiff BigOperators
namespace FourPapersCommon
set_option autoImplicit false
set_option maxHeartbeats 400000
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem integrable_boundedJets_gaussian_weighted_linear
    (C P : EuclideanSpace ℝ ι → ℝ) (hC : BoundedPositiveJets C) (hP : BoundedJets P)
    (u : EuclideanSpace ℝ ι) :
    Integrable (fun z => Real.exp (-C z)*(inner ℝ z u*P z)) (stdGaussian (EuclideanSpace ℝ ι)) := by
  obtain ⟨B,hB,hCb⟩ := hC.2 1 le_rfl
  obtain ⟨R,hR,hPb⟩ := hP.2 0
  have hCn (z : EuclideanSpace ℝ ι) : ‖fderiv ℝ C z‖ ≤ B := by
    simpa only [norm_iteratedFDeriv_one] using hCb z
  have hPn (z : EuclideanSpace ℝ ι) : ‖P z‖ ≤ R := by
    simpa only [norm_iteratedFDeriv_zero] using hPb z
  have hLip : LipschitzWith ⟨B,hB⟩ C :=
    lipschitzWith_of_nnnorm_fderiv_le (hC.1.differentiable (by simp))
      (fun z => NNReal.coe_le_coe.mp (hCn z))
  have he (z : EuclideanSpace ℝ ι) : Real.exp (-C z) ≤ Real.exp (|C 0|)*Real.exp (B*‖z‖) := by
    have hn := hLip.norm_sub_le z 0
    simp only [sub_zero,Real.norm_eq_abs] at hn
    change |C z-C 0| ≤ B*‖z‖ at hn
    rw [←Real.exp_add]
    apply Real.exp_le_exp.mpr
    linarith [neg_le_abs (C 0),neg_le_abs (C z-C 0)]
  let T : EuclideanSpace ℝ ι → ℝ := fun z => Real.exp (-C z)*P z
  have hT : Measurable T := ((Real.continuous_exp.comp hC.1.continuous.neg).mul hP.1.continuous).measurable
  have hb (z : EuclideanSpace ℝ ι) : ‖T z‖ ≤ (R*Real.exp (|C 0|))*Real.exp (B*‖z‖) := by
    dsimp only [T]
    rw [norm_mul,Real.norm_of_nonneg (Real.exp_pos _).le]
    have hh := mul_le_mul (he z) (hPn z) (norm_nonneg _) (by positivity)
    nlinarith only [hh]
  have hh := integrable_inner_mul_gaussian_exponential_bound
    (stdGaussian (EuclideanSpace ℝ ι)) T hT (R*Real.exp (|C 0|)) B (by positivity) hb u
  simpa only [T,mul_assoc,mul_left_comm,mul_comm] using hh

theorem boundedPositiveJets_gaussian_posterior_ibp
    (C P : EuclideanSpace ℝ ι → ℝ) (hC : BoundedPositiveJets C) (hP : BoundedJets P)
    (u : EuclideanSpace ℝ ι) :
    (∫ z, Real.exp (-C z)*inner ℝ z u*P z ∂stdGaussian (EuclideanSpace ℝ ι)) =
      ∫ z, Real.exp (-C z)*(fderiv ℝ P z u-P z*fderiv ℝ C z u) ∂stdGaussian (EuclideanSpace ℝ ι) := by
  obtain ⟨B,hB,hCb⟩ := hC.2 1 le_rfl
  obtain ⟨R,hR,hPb⟩ := hP.2 0
  obtain ⟨D,hD,hPd⟩ := hP.2 1
  have hCn (z : EuclideanSpace ℝ ι) : ‖fderiv ℝ C z‖ ≤ B := by
    simpa only [norm_iteratedFDeriv_one] using hCb z
  have hPn (z : EuclideanSpace ℝ ι) : ‖P z‖ ≤ R := by
    simpa only [norm_iteratedFDeriv_zero] using hPb z
  have hPdn (z : EuclideanSpace ℝ ι) : ‖fderiv ℝ P z‖ ≤ D := by
    simpa only [norm_iteratedFDeriv_one] using hPd z
  have hLip : LipschitzWith ⟨B,hB⟩ C :=
    lipschitzWith_of_nnnorm_fderiv_le (hC.1.differentiable (by simp))
      (fun z => NNReal.coe_le_coe.mp (hCn z))
  have he (z : EuclideanSpace ℝ ι) : Real.exp (-C z) ≤ Real.exp (|C 0|)*Real.exp (B*‖z‖) := by
    have hn := hLip.norm_sub_le z 0
    simp only [sub_zero,Real.norm_eq_abs] at hn
    change |C z-C 0| ≤ B*‖z‖ at hn
    have hc : -C z ≤ |C 0|+B*‖z‖ := by
      have hzero := neg_le_abs (C 0)
      have hdiff := neg_le_abs (C z-C 0)
      linarith
    rw [←Real.exp_add]
    exact Real.exp_le_exp.mpr hc
  let T : EuclideanSpace ℝ ι → ℝ := fun z => Real.exp (-C z)*P z
  have hT : ContDiff ℝ 1 T := (hC.1.neg.exp.mul hP.1).of_le (by simp)
  have hdT (z : EuclideanSpace ℝ ι) :
      fderiv ℝ T z = Real.exp (-C z) • (fderiv ℝ P z-P z • fderiv ℝ C z) := by
    have hc := ((hC.1.differentiable (by simp) z).hasFDerivAt.neg.exp).mul
      (hP.1.differentiable (by simp) z).hasFDerivAt
    change HasFDerivAt T _ z at hc
    rw [hc.fderiv]
    ext w
    simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.neg_apply,ContinuousLinearMap.sub_apply,smul_eq_mul,Pi.neg_apply]
    ring
  let K := (R+D+R*B)*Real.exp (|C 0|)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hTn (z : EuclideanSpace ℝ ι) : ‖T z‖ ≤ K*Real.exp (B*‖z‖) := by
    dsimp only [T]
    rw [norm_mul,Real.norm_of_nonneg (Real.exp_pos _).le]
    calc
      _ ≤ (Real.exp (|C 0|)*Real.exp (B*‖z‖))*R :=
        mul_le_mul (he z) (hPn z) (norm_nonneg _) (by positivity)
      _ = R*Real.exp (|C 0|)*Real.exp (B*‖z‖) := by ring
      _ ≤ K*Real.exp (B*‖z‖) := by
        dsimp [K]
        gcongr
        nlinarith [mul_nonneg hR hB]
  have hdTn (z : EuclideanSpace ℝ ι) : ‖fderiv ℝ T z‖ ≤ K*Real.exp (B*‖z‖) := by
    rw [hdT,norm_smul,Real.norm_of_nonneg (Real.exp_pos _).le]
    have hb : ‖fderiv ℝ P z-P z • fderiv ℝ C z‖ ≤ D+R*B := by
      apply (norm_sub_le _ _).trans
      rw [norm_smul]
      exact add_le_add (hPdn z) (mul_le_mul (hPn z) (hCn z) (norm_nonneg _) hR)
    calc
      _ ≤ (Real.exp (|C 0|)*Real.exp (B*‖z‖))*(D+R*B) :=
        mul_le_mul (he z) hb (norm_nonneg _) (by positivity)
      _ = (D+R*B)*Real.exp (|C 0|)*Real.exp (B*‖z‖) := by ring
      _ ≤ K*Real.exp (B*‖z‖) := by
        dsimp [K]
        gcongr
        linarith
  have hh := cavityGaussian_covariant_ibp (stdGaussian (EuclideanSpace ℝ ι))
    integral_id_stdGaussian T hT K B hK hTn hdTn u
  simp only [covarianceOperator_stdGaussian_id,hdT,ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.sub_apply,smul_eq_mul] at hh
  simpa only [T,mul_assoc,mul_left_comm,mul_comm] using hh

end FourPapersCommon
