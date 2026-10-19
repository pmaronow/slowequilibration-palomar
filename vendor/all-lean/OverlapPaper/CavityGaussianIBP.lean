module
public import FourPapersCommon.FiniteStateCascadeGrowth
public import ParisiFormula.CoordStein
public import Lemmas.Gaussian.CanonicalModel

public import Mathlib.Probability.Distributions.Gaussian.Fernique

@[expose] public section

/-! Gaussian integration by parts with exponential growth, for the actual
centered finite-dimensional Gaussian measure and its actual covariance
operator. Degenerate covariance is permitted. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open PhysLean.Probability.GaussianIBP
open scoped Topology BigOperators RealInnerProductSpace
namespace OverlapPaper
open FourPapersCommon
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H] [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H]
  [SecondCountableTopology H]

theorem integrable_gaussian_exponential_bound (μ : Measure H) [IsGaussian μ]
    (f : H → ℝ) (hf : Measurable f) (C D : ℝ) (hC : 0 ≤ C)
    (hb : ∀ x, ‖f x‖ ≤ C * Real.exp (D * ‖x‖)) : Integrable f μ :=
  ((integrable_exp_mul_norm_gaussian μ D).const_mul C).mono' hf.aestronglyMeasurable
    (.of_forall hb)

theorem integrable_inner_mul_gaussian_exponential_bound (μ : Measure H) [IsGaussian μ]
    (f : H → ℝ) (hf : Measurable f) (C D : ℝ) (hC : 0 ≤ C)
    (hb : ∀ x, ‖f x‖ ≤ C * Real.exp (D * ‖x‖)) (h : H) :
    Integrable (fun x => inner ℝ x h * f x) μ := by
  apply integrable_gaussian_exponential_bound μ _ (by fun_prop)
    (‖h‖ * C) (D + 1) (mul_nonneg (norm_nonneg _) hC)
  intro x
  have he : ‖x‖ ≤ Real.exp ‖x‖ := (Real.add_one_le_exp ‖x‖).trans'
    (by linarith)
  calc
    ‖inner ℝ x h * f x‖ ≤ (‖x‖ * ‖h‖) * (C * Real.exp (D * ‖x‖)) := by
      rw [norm_mul]
      exact mul_le_mul (norm_inner_le_norm _ _) (hb x) (norm_nonneg _) (by positivity)
    _ ≤ (Real.exp ‖x‖ * ‖h‖) * (C * Real.exp (D * ‖x‖)) := by gcongr
    _ = (‖h‖ * C) * Real.exp ((D + 1) * ‖x‖) := by
      rw [add_mul, one_mul, Real.exp_add]
      ring

/-- The spectral covariance in the audited line-Stein proof is the actual
uncentered covariance operator of a centered Gaussian law. -/
theorem cavityGaussian_spectral_covariance_eq (μ : Measure H) [IsGaussian μ]
    (hmean : (∫ x, x ∂μ) = 0) :
    letI : MeasureSpace H := ⟨μ⟩
    covOp (IsGaussianHilbert.of_hasGaussianLaw id measurable_id
      IsGaussian.hasGaussianLaw_id hmean) = covarianceOperator μ := by
  letI : MeasureSpace H := ⟨μ⟩
  let hg := IsGaussianHilbert.of_hasGaussianLaw id measurable_id
    IsGaussian.hasGaussianLaw_id hmean
  change covOp hg = covarianceOperator μ
  ext h
  apply ext_inner_right ℝ
  intro u
  rw [← PhysLean.Probability.GaussianIBP.ProbabilityTheory.gaussian_covariance_pairing hg h u,
    covarianceOperator_inner IsGaussian.memLp_two_id]
  exact integral_congr_ae (.of_forall fun x => by
    simp only [id_eq, real_inner_comm])

/-- Genuine finite-dimensional Gaussian Stein identity for C¹ tests of
exponential growth. Every required integrability assertion is derived. -/
theorem cavityGaussian_covariant_ibp (μ : Measure H) [IsGaussian μ]
    (hmean : (∫ x, x ∂μ) = 0) (f : H → ℝ) (hf : ContDiff ℝ 1 f)
    (C D : ℝ) (hC : 0 ≤ C)
    (hb : ∀ x, ‖f x‖ ≤ C * Real.exp (D * ‖x‖))
    (hdb : ∀ x, ‖fderiv ℝ f x‖ ≤ C * Real.exp (D * ‖x‖)) (h : H) :
    (∫ x, inner ℝ x h * f x ∂μ) =
      ∫ x, (fderiv ℝ f x) (covarianceOperator μ h) ∂μ := by
  classical
  letI : MeasureSpace H := ⟨μ⟩
  let hg := IsGaussianHilbert.of_hasGaussianLaw id measurable_id
    IsGaussian.hasGaussianLaw_id hmean
  let df : hg.ι → H → ℝ := fun i x => (fderiv ℝ f x) (hg.w i)
  have hdm (i : hg.ι) : Measurable (df i) := by
    exact ((hf.continuous_fderiv (by norm_num)).clm_apply continuous_const).measurable
  have hdi (i : hg.ι) : Integrable (df i) μ := by
    apply integrable_gaussian_exponential_bound μ _ (hdm i) C D hC
    intro x
    exact ((fderiv ℝ f x).le_opNorm (hg.w i)).trans
      (by simpa only [hg.w.norm_eq_one, mul_one] using hdb x)
  have hci (i : hg.ι) : Integrable (fun x => hg.c i x * f x) μ := by
    have hi := integrable_inner_mul_gaussian_exponential_bound μ f hf.continuous.measurable
      C D hC hb (hg.w i)
    have he : ∀ x, hg.c i x = inner ℝ x (hg.w i) := fun x =>
      (congrFun (congrFun (coord_eq_c hg) i) x).symm
    simpa only [he] using hi
  have hline (i : hg.ι) (z : H) (x : ℝ) :
      HasDerivAt (fun t => f (z + t • hg.w i)) (df i (z + x • hg.w i)) x := by
    exact (hf.differentiable (by norm_num) (z + x • hg.w i)).hasFDerivAt.comp_hasDerivAt x
      (by simpa only [id_eq, one_smul] using
        ((hasDerivAt_id x).smul_const (hg.w i) |>.const_add z))
  have hs := SpinGlass.stein_inner_of_hasDerivAt hg h hline hf.continuous.measurable hdm hci
    (integrable_gaussian_exponential_bound μ f hf.continuous.measurable C D hC hb) hdi
  change (∫ x, inner ℝ x h * f x ∂μ) = _ at hs
  rw [hs]
  have hc : covOp hg = covarianceOperator μ := cavityGaussian_spectral_covariance_eq μ hmean
  rw [← hc, covOp_apply]
  simp only [map_sum, map_smul, smul_eq_mul]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    rw [integral_const_mul]
    rfl
  · intro i _
    exact (hdi i).const_mul _

end OverlapPaper
