module

public import SphericalAging.GaussianRotationVariance
public import Mathlib.Analysis.Calculus.FDeriv.Measurable

public section

/-! The Gaussian rotation variance estimate for everywhere Fréchet
differentiable functions. Derivative continuity is not a premise:
measurability is proved by the derivative measurability theorem, and the
required path integrability is derived by Gaussian/time Fubini. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace ENNReal BigOperators
namespace SphericalAging.DifferentiableGaussianVariance
open GaussianRotationVariance
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma rotatedDerivative_stronglyMeasurable (f : E → ℝ) : StronglyMeasurable (rotatedDerivative f) := by
  have hX : Measurable (fun q : ℝ × (E × E) => Real.cos q.1 • q.2.1+Real.sin q.1 • q.2.2) := by fun_prop
  have hY : StronglyMeasurable (fun q : ℝ × (E × E) => -Real.sin q.1 • q.2.1+Real.cos q.1 • q.2.2) := by
    exact (by fun_prop : Continuous (fun q : ℝ × (E × E) => -Real.sin q.1 • q.2.1+Real.cos q.1 • q.2.2)).stronglyMeasurable
  exact (continuous_fst.clm_apply continuous_snd).comp_stronglyMeasurable
    (((measurable_fderiv ℝ f).stronglyMeasurable.comp_measurable hX).prodMk hY)

lemma baseDerivative_integrable_sq (f : E → ℝ)
    (hg : Integrable (fun x => ‖fderiv ℝ f x‖^2) (stdGaussian E)) :
    Integrable (fun q : E × E => (fderiv ℝ f q.1 q.2)^2) ((stdGaussian E).prod (stdGaussian E)) := by
  have hm : StronglyMeasurable (fun q : E × E => (fderiv ℝ f q.1 q.2)^2) :=
    ((continuous_fst.clm_apply continuous_snd).comp_stronglyMeasurable
      ((measurable_fderiv ℝ f).stronglyMeasurable.comp_fst.prodMk continuous_snd.stronglyMeasurable)).pow 2
  have hv : Integrable (fun x : E => ‖x‖^2) (stdGaussian E) := by
    simpa only [id_eq] using (IsGaussian.memLp_two_id (μ := stdGaussian E)).integrable_norm_pow'
  apply (hg.mul_prod hv).mono' hm.aestronglyMeasurable
  exact .of_forall (fun q => by
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    have h := (fderiv ℝ f q.1).le_opNorm q.2
    rw [Real.norm_eq_abs] at h
    nlinarith [abs_nonneg (fderiv ℝ f q.1 q.2),mul_nonneg (norm_nonneg (fderiv ℝ f q.1)) (norm_nonneg q.2),sq_abs (fderiv ℝ f q.1 q.2)])

lemma rotatedDerivative_integral_sq (f : E → ℝ)
    (hg : Integrable (fun x => ‖fderiv ℝ f x‖^2) (stdGaussian E)) (θ : ℝ) :
    Integrable (fun q : E × E => (rotatedDerivative f (θ,q))^2) ((stdGaussian E).prod (stdGaussian E)) ∧
      (∫ q : E × E,(rotatedDerivative f (θ,q))^2 ∂(stdGaussian E).prod (stdGaussian E))=
        ∫ x,‖fderiv ℝ f x‖^2 ∂stdGaussian E := by
  have hrot : MeasurePreserving (ContinuousLinearMap.rotation θ : E × E → E × E)
      ((stdGaussian E).prod (stdGaussian E)) ((stdGaussian E).prod (stdGaussian E)) :=
    ⟨(ContinuousLinearMap.rotation θ : E × E →L[ℝ] E × E).continuous.measurable,
      IsGaussian.map_rotation_eq_self (μ := stdGaussian E) integral_id_stdGaussian θ⟩
  refine ⟨hrot.integrable_comp_of_integrable (baseDerivative_integrable_sq f hg),?_⟩
  calc
    _ = ∫ q : E × E,(fderiv ℝ f q.1 q.2)^2 ∂(stdGaussian E).prod (stdGaussian E) := by
      exact integral_map hrot.measurable.aemeasurable
        (by rw [hrot.map_eq];exact (baseDerivative_integrable_sq f hg).aestronglyMeasurable) |>.symm.trans
        (congrArg (fun μ => ∫ q : E × E,(fderiv ℝ f q.1 q.2)^2 ∂μ) hrot.map_eq)
    _ = _ := by
      rw [integral_prod _ (baseDerivative_integrable_sq f hg)]
      exact integral_congr_ae (.of_forall (fun x => dual_secondMoment (fderiv ℝ f x)))

lemma path_hasDerivAt {f : E → ℝ} (hf : Differentiable ℝ f) (q : E × E) (θ : ℝ) :
    HasDerivAt (fun t => f ((ContinuousLinearMap.rotation t q).1)) (rotatedDerivative f (θ,q)) θ := by
  exact (hf _).hasFDerivAt.comp_hasDerivAt θ
    (((Real.hasDerivAt_cos θ).smul_const q.1).add ((Real.hasDerivAt_sin θ).smul_const q.2))

theorem gaussian_variance_le_gradient {f : E → ℝ} (hf : Differentiable ℝ f)
    (h2 : MemLp f 2 (stdGaussian E))
    (hg : Integrable (fun x => ‖fderiv ℝ f x‖^2) (stdGaussian E)) :
    variance f (stdGaussian E)≤(Real.pi^2/8)*(∫ x,‖fderiv ℝ f x‖^2 ∂stdGaussian E) := by
  let τ : Measure ℝ := volume.restrict (Ioc (0 : ℝ) (Real.pi/2))
  let ρ := (stdGaussian E).prod (stdGaussian E)
  have hsm := (rotatedDerivative_stronglyMeasurable f).pow 2
  have hh (θ : ℝ) := rotatedDerivative_integral_sq f hg θ
  have houter : Integrable (fun θ => ∫ q : E × E,(rotatedDerivative f (θ,q))^2 ∂ρ) τ :=
    (integrable_const (∫ x,‖fderiv ℝ f x‖^2 ∂stdGaussian E)).congr (.of_forall (fun θ => (hh θ).2.symm))
  have hi : Integrable (fun q : ℝ × (E × E) => (rotatedDerivative f q)^2) (τ.prod ρ) := by
    apply (integrable_prod_iff hsm.aestronglyMeasurable).mpr
    refine ⟨.of_forall (fun θ => (hh θ).1),?_⟩
    convert houter using 1
    funext θ
    exact integral_congr_ae (.of_forall (fun q => Real.norm_of_nonneg (sq_nonneg _)))
  have hmass : τ.real univ=Real.pi/2 := by
    rw [Measure.real_def,Measure.restrict_apply MeasurableSet.univ,univ_inter,Real.volume_Ioc]
    rw [sub_zero,ENNReal.toReal_ofReal (by positivity)]
  have hint : (∫ q : E × E,∫ θ,(rotatedDerivative f (θ,q))^2 ∂τ ∂ρ)=
      (Real.pi/2)*(∫ x,‖fderiv ℝ f x‖^2 ∂stdGaussian E) := by
    rw [← integral_prod_symm _ hi,integral_prod _ hi]
    change (∫ θ,∫ q : E × E,(rotatedDerivative f (θ,q))^2 ∂ρ ∂τ)=_
    have hfunc : (fun θ => ∫ q : E × E,(rotatedDerivative f (θ,q))^2 ∂ρ)=
        fun _ : ℝ => ∫ x,‖fderiv ℝ f x‖^2 ∂stdGaussian E := funext (fun θ => (hh θ).2)
    rw [hfunc,integral_const]
    change τ.real univ*(∫ x,‖fderiv ℝ f x‖^2 ∂stdGaussian E)=_
    rw [hmass]
  have hpath : ∀ᵐ q ∂ρ,(f q.2-f q.1)^2≤(Real.pi/2)*(∫ θ,(rotatedDerivative f (θ,q))^2 ∂τ) := by
    filter_upwards [hi.prod_left_ae] with q hq
    have hdsm : StronglyMeasurable (fun θ => rotatedDerivative f (θ,q)) :=
      (rotatedDerivative_stronglyMeasurable f).comp_measurable (measurable_id.prodMk measurable_const)
    have hM : MemLp (fun θ => rotatedDerivative f (θ,q)) 2 τ := by
      apply (integrable_norm_rpow_iff hdsm.aestronglyMeasurable
        (by norm_num : (2 : ℝ≥0∞)≠0) (by norm_num : (2 : ℝ≥0∞)≠∞)).mp
      simpa only [ENNReal.toReal_ofNat,Real.rpow_two,Real.norm_eq_abs,sq_abs] using hq
    have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun θ _ => path_hasDerivAt hf q θ) (a := (0 : ℝ)) (b := Real.pi/2)
      (by rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by positivity : (0 : ℝ)≤Real.pi/2)];exact hM.integrable one_le_two)
    simp only [ContinuousLinearMap.rotation_apply,Real.cos_pi_div_two,Real.sin_pi_div_two,
      Real.cos_zero,Real.sin_zero,zero_smul,one_smul,zero_add,add_zero] at he
    rw [intervalIntegral.integral_of_le (by positivity : (0 : ℝ)≤Real.pi/2)] at he
    have hcs := PredictableDriftTime.integral_sq_le_measure_mul_integral_sq τ (fun θ => rotatedDerivative f (θ,q)) hM
    rw [he,hmass] at hcs
    exact hcs
  have hx := h2.comp_measurePreserving (measurePreserving_fst (μ := stdGaussian E) (ν := stdGaussian E))
  have hy := h2.comp_measurePreserving (measurePreserving_snd (μ := stdGaussian E) (ν := stdGaussian E))
  have hp : Integrable (fun q : E × E => (f q.2-f q.1)^2) ρ := (hy.sub hx).integrable_sq
  rw [pair_variance_identity hf.continuous.measurable h2]
  calc
    _ ≤ (1/2 : ℝ)*(∫ q : E × E,(Real.pi/2)*(∫ θ,(rotatedDerivative f (θ,q))^2 ∂τ) ∂ρ) :=
      mul_le_mul_of_nonneg_left (integral_mono_ae hp (hi.integral_prod_right.const_mul _) hpath) (by norm_num)
    _ = _ := by rw [integral_const_mul,hint];ring

end SphericalAging.DifferentiableGaussianVariance
