module

public import SphericalAging.GaussianExponentialNorm
public import SphericalAging.GaussianRotationVariance
public import Mathlib.Analysis.Convex.Integral
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic

public section

/-! Actual conditional exponential moments of a bounded Gaussian dual
and their invariance under the Gaussian rotation. -/
noncomputable section
set_option maxHeartbeats 400000
namespace SphericalAging.GaussianRotationExponential
open Set MeasureTheory ProbabilityTheory GaussianExponentialNorm GaussianRotationVariance
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem dual_hasLaw (L : E→L[ℝ] ℝ) :
    HasLaw (fun x => L x) (gaussianReal 0 (‖L‖^2).toNNReal) (stdGaussian E) := by
  have hG : HasGaussianLaw (fun x => L x) (stdGaussian E) := by
    simpa only [id_eq] using
      (IsGaussian.hasGaussianLaw_id (μ := stdGaussian E)).map_fun L
  refine ⟨hG.aemeasurable,?_⟩
  rw [hG.map_eq_gaussianReal,integral_strongDual_stdGaussian,variance_dual_stdGaussian]

theorem dual_exponential_integral (L : E→L[ℝ] ℝ) (t : ℝ) :
    (∫x,Real.exp (t*L x) ∂stdGaussian E)=Real.exp (t^2*‖L‖^2/2) := by
  change mgf (fun x => L x) (stdGaussian E) t=_
  rw [mgf_gaussianReal (dual_hasLaw L),zero_mul,zero_add,
    Real.coe_toNNReal _ (sq_nonneg _)]
  congr 1
  ring

theorem bounded_dual_exponential_integrable (A : E→(E→L[ℝ] ℝ)) (hA : Continuous A)
    (L : ℝ) (hL : 0≤L) (hbound : ∀x,‖A x‖≤L) (t : ℝ) :
    Integrable (fun q : E×E => Real.exp (t*A q.1 q.2))
      ((stdGaussian E).prod (stdGaussian E)) := by
  have hI := (integrable_exp_norm (stdGaussian E) (|t| * L)).comp_snd (stdGaussian E)
  apply hI.mono'
    ((Real.continuous_exp.comp (((hA.comp continuous_fst).clm_apply continuous_snd).const_mul t)).stronglyMeasurable.aestronglyMeasurable)
  exact ae_of_all _ (fun q => by
    change ‖Real.exp (t*A q.1 q.2)‖≤Real.exp (|t| * L*‖q.2‖)
    rw [Real.norm_of_nonneg (Real.exp_nonneg _)]
    apply Real.exp_le_exp.mpr
    have h := (A q.1).le_opNorm q.2
    rw [Real.norm_eq_abs] at h
    calc
      t*A q.1 q.2 ≤ |t*A q.1 q.2| := le_abs_self _
      _=|t| * |A q.1 q.2| := abs_mul _ _
      _≤|t| * (‖A q.1‖*‖q.2‖) := mul_le_mul_of_nonneg_left h (abs_nonneg _)
      _≤|t| * (L*‖q.2‖) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (hbound q.1) (norm_nonneg _)) (abs_nonneg _)
      _=|t| * L*‖q.2‖ := (mul_assoc _ _ _).symm)

theorem bounded_dual_exponential_integral_le (A : E→(E→L[ℝ] ℝ)) (hA : Continuous A)
    (L : ℝ) (hL : 0≤L) (hbound : ∀x,‖A x‖≤L) (t : ℝ) :
    (∫q : E×E,Real.exp (t*A q.1 q.2) ∂(stdGaussian E).prod (stdGaussian E))≤
      Real.exp (t^2*L^2/2) := by
  have hI := bounded_dual_exponential_integrable A hA L hL hbound t
  rw [integral_prod _ hI]
  have hi : Integrable (fun x => Real.exp (t^2*‖A x‖^2/2)) (stdGaussian E) := by
    apply (integrable_const (Real.exp (t^2*L^2/2))).mono' (by fun_prop)
    exact ae_of_all _ (fun x => by
      rw [Real.norm_of_nonneg (Real.exp_nonneg _)]
      apply Real.exp_le_exp.mpr
      gcongr
      exact hbound x)
  calc
    _=(∫x,Real.exp (t^2*‖A x‖^2/2) ∂stdGaussian E) :=
      integral_congr_ae (ae_of_all _ (fun x => dual_exponential_integral (A x) t))
    _≤∫_x : E,Real.exp (t^2*L^2/2) ∂stdGaussian E := by
      apply integral_mono hi (integrable_const _)
      intro x
      apply Real.exp_le_exp.mpr
      gcongr
      exact hbound x
    _=_ := by simp

theorem rotated_derivative_exponential (f : E→ℝ) (hf : ContDiff ℝ 1 f)
    (L : ℝ) (hL : 0≤L) (hbound : ∀x,‖fderiv ℝ f x‖≤L) (t θ : ℝ) :
    Integrable (fun q : E×E => Real.exp (t*rotatedDerivative f (θ,q)))
        ((stdGaussian E).prod (stdGaussian E)) ∧
      (∫q : E×E,Real.exp (t*rotatedDerivative f (θ,q)) ∂(stdGaussian E).prod (stdGaussian E))≤
        Real.exp (t^2*L^2/2) := by
  have hc := hf.continuous_fderiv (by norm_num)
  have hrot : MeasurePreserving (ContinuousLinearMap.rotation θ : E×E→E×E)
      ((stdGaussian E).prod (stdGaussian E)) ((stdGaussian E).prod (stdGaussian E)) :=
    ⟨(ContinuousLinearMap.rotation θ : E×E→L[ℝ] E×E).continuous.measurable,
      IsGaussian.map_rotation_eq_self (μ := stdGaussian E) integral_id_stdGaussian θ⟩
  have hI := bounded_dual_exponential_integrable (fderiv ℝ f) hc L hL hbound t
  refine ⟨hrot.integrable_comp_of_integrable hI,?_⟩
  have he := hrot.hasLaw.integral_comp hI.aestronglyMeasurable
  exact he.trans_le (bounded_dual_exponential_integral_le (fderiv ℝ f) hc L hL hbound t)

end SphericalAging.GaussianRotationExponential
