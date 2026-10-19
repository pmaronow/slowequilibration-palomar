module
public import FourPapersCommon.FiniteJointLaw
public import Lemmas.SpinGlass.gaussian_concentration
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.Basic.ENNReal.BigOperators

@[expose] public section

/-! The genuine finite standard Gaussian density with respect to canonical
Lebesgue volume, including its Euclidean transport. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal NNReal
namespace FourPapersCommon

def standardGaussianProductDensity {ι : Type*} [Fintype ι] (x : ι → ℝ) : ℝ :=
  ∏ i,gaussianPDFReal 0 1 (x i)

theorem standardGaussianProductDensity_nonneg {ι : Type*} [Fintype ι] (x : ι → ℝ) :
    0 ≤ standardGaussianProductDensity x :=
  Finset.prod_nonneg fun _ _ => gaussianPDFReal_nonneg _ _ _

theorem integrable_standardGaussianProductDensity {ι : Type*} [Fintype ι] :
    Integrable (standardGaussianProductDensity (ι := ι)) := by
  exact Integrable.fintype_prod (fun _ => integrable_gaussianPDFReal 0 1)

theorem pi_standardGaussian_eq_withDensity {ι : Type*} [Fintype ι] :
    Measure.pi (fun _ : ι => gaussianReal 0 1) =
      volume.withDensity (fun x => ENNReal.ofReal (standardGaussianProductDensity x)) := by
  apply Measure.pi_eq
  intro s hs
  have hi := integrable_standardGaussianProductDensity (ι := ι)
  have hnonneg : ∀ᵐ x : ι → ℝ ∂volume.restrict (univ.pi s),
      0 ≤ standardGaussianProductDensity x :=
    .of_forall standardGaussianProductDensity_nonneg
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs),
    ←ofReal_integral_eq_lintegral_ofReal hi.restrict hnonneg]
  change ENNReal.ofReal (∫ x,standardGaussianProductDensity x
    ∂(Measure.pi (fun _ : ι => (volume : Measure ℝ))).restrict (univ.pi s)) = _
  rw [Measure.restrict_pi_pi]
  change ENNReal.ofReal (∫ x : ι → ℝ,∏ i,gaussianPDFReal 0 1 (x i)
    ∂Measure.pi (fun i => (volume : Measure ℝ).restrict (s i))) = _
  rw [integral_fintype_prod_eq_prod,
    ENNReal.ofReal_prod_of_nonneg (fun i _ => integral_nonneg (fun x => gaussianPDFReal_nonneg _ _ _))]
  apply Finset.prod_congr rfl
  intro i _
  rw [gaussianReal_of_var_ne_zero _ (by norm_num : (1 : ℝ≥0) ≠ 0),
    withDensity_apply _ (hs i)]
  exact ofReal_integral_eq_lintegral_ofReal (integrable_gaussianPDFReal 0 1).restrict
    (.of_forall fun x => gaussianPDFReal_nonneg _ _ _)

def standardGaussianEuclideanDensity {ι : Type*} [Fintype ι]
    (x : EuclideanSpace ℝ ι) : ℝ := standardGaussianProductDensity (WithLp.ofLp x)

theorem measurable_standardGaussianEuclideanDensity {ι : Type*} [Fintype ι] :
    Measurable (standardGaussianEuclideanDensity (ι := ι)) := by
  unfold standardGaussianEuclideanDensity standardGaussianProductDensity
  simp only [gaussianPDFReal,NNReal.coe_one,mul_one,sub_zero]
  fun_prop

theorem standardGaussianEuclidean_eq_withDensity {ι : Type*} [Fintype ι] :
    SYK.standardGaussianMeasureOnEuclidean ι =
      volume.withDensity (fun x => ENNReal.ofReal (standardGaussianEuclideanDensity x)) := by
  rw [SYK.standardGaussianMeasureOnEuclidean,pi_standardGaussian_eq_withDensity]
  have hp := map_withDensity_pullback (volume : Measure (ι → ℝ)) (WithLp.toLp 2)
    (by fun_prop) (fun x : EuclideanSpace ℝ ι => ENNReal.ofReal (standardGaussianEuclideanDensity x))
    measurable_standardGaussianEuclideanDensity.ennreal_ofReal
  change (volume.withDensity (fun x : ι → ℝ =>
    ENNReal.ofReal (standardGaussianEuclideanDensity (WithLp.toLp 2 x)))).map (WithLp.toLp 2) = _
  rw [hp,(PiLp.volume_preserving_toLp ι).map_eq]

theorem standardGaussianEuclideanDensity_eq {ι : Type*} [Fintype ι]
    (x : EuclideanSpace ℝ ι) :
    standardGaussianEuclideanDensity x =
      ((Real.sqrt (2*Real.pi))⁻¹)^(Fintype.card ι)*Real.exp (-‖x‖^2/2) := by
  unfold standardGaussianEuclideanDensity standardGaussianProductDensity
  simp only [gaussianPDFReal,NNReal.coe_one,mul_one,sub_zero]
  change (∏ i, (Real.sqrt (2*Real.pi))⁻¹*Real.exp (-(x i)^2/2)) = _
  rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,←Real.exp_sum]
  congr 1
  rw [EuclideanSpace.real_norm_sq_eq]
  congr 1
  rw [←Finset.sum_div,Finset.sum_neg_distrib]

def standardGaussianPotential {ι : Type*} [Fintype ι] (x : EuclideanSpace ℝ ι) : ℝ :=
  ‖x‖^2/2+(Fintype.card ι : ℝ)*Real.log (Real.sqrt (2*Real.pi))

theorem exp_neg_standardGaussianPotential {ι : Type*} [Fintype ι]
    (x : EuclideanSpace ℝ ι) :
    Real.exp (-standardGaussianPotential x) = standardGaussianEuclideanDensity x := by
  have hp : 0 < Real.sqrt (2*Real.pi) := Real.sqrt_pos.2 (by positivity)
  have he : Real.exp (-((Fintype.card ι : ℝ)*Real.log (Real.sqrt (2*Real.pi)))) =
      ((Real.sqrt (2*Real.pi))⁻¹)^(Fintype.card ι) := by
    rw [Real.exp_neg,Real.exp_nat_mul,Real.exp_log hp,inv_pow]
  rw [standardGaussianPotential,neg_add,Real.exp_add,he,standardGaussianEuclideanDensity_eq]
  ring

theorem standardGaussianEuclidean_eq_expDensity {ι : Type*} [Fintype ι] :
    SYK.standardGaussianMeasureOnEuclidean ι =
      volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-standardGaussianPotential x))) := by
  simp_rw [exp_neg_standardGaussianPotential]
  exact standardGaussianEuclidean_eq_withDensity

end FourPapersCommon
