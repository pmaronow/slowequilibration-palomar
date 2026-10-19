module

public import SphericalAging.GaussianRotationExponential
public import SphericalAging.CenteredGaussianConcentration

public section

/-! Dimension-free Gaussian exponential concentration, derived from the
actual rotation path, exponential Jensen, and conditional dual moments. -/
noncomputable section
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.GaussianRotationConcentration
open Set MeasureTheory ProbabilityTheory GaussianRotationVariance GaussianRotationExponential
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

@[expose] def angleMeasure : Measure ℝ := volume.restrict (Ioc (0:ℝ) (Real.pi/2))
instance : IsFiniteMeasure angleMeasure := by unfold angleMeasure;infer_instance
theorem angle_mass : angleMeasure univ=ENNReal.ofReal (Real.pi/2) := by
  simp only [angleMeasure,Measure.restrict_apply MeasurableSet.univ,univ_inter,Real.volume_Ioc,sub_zero]
theorem angle_mass_real : angleMeasure.real univ=Real.pi/2 := by
  rw [Measure.real_def,angle_mass,ENNReal.toReal_ofReal (by positivity)]
instance : NeZero angleMeasure := ⟨by
  intro hz
  have hh := congrArg (fun μ : Measure ℝ => μ univ) hz
  apply (ENNReal.ofReal_pos.mpr (by positivity : 0<Real.pi/2)).ne'
  simpa only [angle_mass,Measure.coe_zero,Pi.zero_apply] using hh⟩

theorem continuous_angle_integrable (g : ℝ→ℝ) (hg : Continuous g) : Integrable g angleMeasure :=
  (hg.continuousOn.integrableOn_compact isCompact_Icc).mono_set Ioc_subset_Icc_self

theorem rotation_integral_eq_difference (f : E→ℝ) (hf : ContDiff ℝ 1 f) (q : E×E) :
    (∫θ,rotatedDerivative f (θ,q) ∂angleMeasure)=f q.2-f q.1 := by
  have hc : Continuous (fun θ => rotatedDerivative f (θ,q)) :=
    (rotatedDerivative_continuous hf).comp (continuous_id.prodMk continuous_const)
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun θ _ => path_hasDerivAt hf q θ) (hc.intervalIntegrable _ _)
      (a := (0:ℝ)) (b := Real.pi/2)
  simp only [ContinuousLinearMap.rotation_apply,Real.cos_pi_div_two,Real.sin_pi_div_two,
    Real.cos_zero,Real.sin_zero,zero_smul,one_smul,zero_add,add_zero] at he
  rw [intervalIntegral.integral_of_le (by positivity : (0:ℝ)≤Real.pi/2)] at he
  exact he

theorem rotation_path_exponential_jensen (f : E→ℝ) (hf : ContDiff ℝ 1 f) (q : E×E) (t : ℝ) :
    Real.exp (t*(f q.2-f q.1))≤(Real.pi/2)⁻¹*
      (∫θ,Real.exp ((Real.pi/2*t)*rotatedDerivative f (θ,q)) ∂angleMeasure) := by
  let u : ℝ→ℝ := fun θ => (Real.pi/2*t)*rotatedDerivative f (θ,q)
  have hc : Continuous u := ((rotatedDerivative_continuous hf).comp
    (continuous_id.prodMk continuous_const)).const_mul _
  have hj := convexOn_exp.map_average_le Real.continuous_exp.continuousOn
    isClosed_univ (ae_of_all angleMeasure (fun _ => mem_univ _))
    (continuous_angle_integrable u hc)
    (continuous_angle_integrable (Real.exp∘u) (Real.continuous_exp.comp hc))
  have hu : (⨍θ,u θ ∂angleMeasure)=t*(f q.2-f q.1) := by
    rw [average_eq,angle_mass_real]
    change (Real.pi/2)⁻¹*(∫θ,(Real.pi/2*t)*rotatedDerivative f (θ,q) ∂angleMeasure)=_
    rw [integral_const_mul,rotation_integral_eq_difference f hf q]
    field_simp
  rw [hu,average_eq,angle_mass_real] at hj
  exact hj

theorem rotation_exponential_product_integrable (f : E→ℝ) (hf : ContDiff ℝ 1 f)
    (L : ℝ) (hL : 0≤L) (hbound : ∀x,‖fderiv ℝ f x‖≤L) (t : ℝ) :
    Integrable (fun z : ℝ×(E×E) => Real.exp ((Real.pi/2*t)*rotatedDerivative f z))
      (angleMeasure.prod ((stdGaussian E).prod (stdGaussian E))) := by
  have hsm : StronglyMeasurable (fun z : ℝ×(E×E) => Real.exp ((Real.pi/2*t)*rotatedDerivative f z)) :=
    (Real.continuous_exp.comp ((rotatedDerivative_continuous hf).const_mul _)).stronglyMeasurable
  apply (integrable_prod_iff hsm.aestronglyMeasurable).mpr
  refine ⟨ae_of_all _ (fun θ => (rotated_derivative_exponential f hf L hL hbound (Real.pi/2*t) θ).1),?_⟩
  apply (integrable_const (Real.exp ((Real.pi/2*t)^2*L^2/2))).mono'
    hsm.aestronglyMeasurable.norm.integral_prod_right'
  exact ae_of_all _ (fun θ => by
    rw [Real.norm_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
    simp only [Real.norm_of_nonneg (Real.exp_nonneg _)]
    exact (rotated_derivative_exponential f hf L hL hbound (Real.pi/2*t) θ).2)

theorem pair_exponential_integrable_and_le (f : E→ℝ) (hf : ContDiff ℝ 1 f)
    (L : ℝ) (hL : 0≤L) (hbound : ∀x,‖fderiv ℝ f x‖≤L) (t : ℝ) :
    Integrable (fun q : E×E => Real.exp (t*(f q.2-f q.1))) ((stdGaussian E).prod (stdGaussian E)) ∧
      (∫q : E×E,Real.exp (t*(f q.2-f q.1)) ∂(stdGaussian E).prod (stdGaussian E))≤
        Real.exp ((Real.pi/2*t)^2*L^2/2) := by
  let G : ℝ×(E×E)→ℝ := fun z => Real.exp ((Real.pi/2*t)*rotatedDerivative f z)
  have hI : Integrable G (angleMeasure.prod ((stdGaussian E).prod (stdGaussian E))) :=
    rotation_exponential_product_integrable f hf L hL hbound t
  have hJ : Integrable (fun q : E×E => (Real.pi/2)⁻¹*(∫θ,G (θ,q) ∂angleMeasure))
      ((stdGaussian E).prod (stdGaussian E)) := hI.integral_prod_right.const_mul _
  have hF : Integrable (fun q : E×E => Real.exp (t*(f q.2-f q.1)))
      ((stdGaussian E).prod (stdGaussian E)) := by
    apply hJ.mono' (by fun_prop)
    exact ae_of_all _ (fun q => by
      rw [Real.norm_of_nonneg (Real.exp_nonneg _)]
      exact rotation_path_exponential_jensen f hf q t)
  refine ⟨hF,?_⟩
  calc
    _≤∫q : E×E,(Real.pi/2)⁻¹*(∫θ,G (θ,q) ∂angleMeasure) ∂(stdGaussian E).prod (stdGaussian E) :=
      integral_mono hF hJ (fun q => rotation_path_exponential_jensen f hf q t)
    _=(Real.pi/2)⁻¹*(∫θ,∫q : E×E,G (θ,q) ∂(stdGaussian E).prod (stdGaussian E) ∂angleMeasure) := by
      rw [integral_const_mul]
      exact congrArg (fun a : ℝ => (Real.pi/2)⁻¹*a) (integral_integral_swap hI).symm
    _≤(Real.pi/2)⁻¹*(∫_θ,Real.exp ((Real.pi/2*t)^2*L^2/2) ∂angleMeasure) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact integral_mono hI.integral_prod_left (integrable_const _)
        (fun θ => (rotated_derivative_exponential f hf L hL hbound (Real.pi/2*t) θ).2)
    _=_ := by
      rw [integral_const,angle_mass_real,smul_eq_mul]
      field_simp

end SphericalAging.GaussianRotationConcentration
