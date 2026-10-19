module

public import SphericalAging.PredictableDriftTime
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

public section

/-! A genuine dimension-independent Gaussian variance estimate, derived
from rotation invariance, the fundamental theorem of calculus, and L²
Cauchy--Schwarz. It is an analytic ingredient for actual-model
concentration, with differentiability and gradient integrability inputs. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace ENNReal BigOperators
namespace SphericalAging.GaussianRotationVariance
set_option maxHeartbeats 1300000
set_option backward.isDefEq.respectTransparency false
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma dual_secondMoment (L : E →L[ℝ] ℝ) :
    (∫ x,(L x)^2 ∂stdGaussian E)=‖L‖^2 := by
  have hm : MemLp (fun x => L x) 2 (stdGaussian E) := L.comp_memLp' IsGaussian.memLp_two_id
  have hv := variance_dual_stdGaussian L
  rw [variance_eq_sub hm] at hv
  simpa only [Pi.pow_apply,integral_strongDual_stdGaussian,zero_pow (by norm_num : 2≠0),sub_zero] using hv

@[expose] def rotatedDerivative (f : E → ℝ) (q : ℝ × (E × E)) : ℝ :=
  fderiv ℝ f ((ContinuousLinearMap.rotation q.1 q.2).1) ((ContinuousLinearMap.rotation q.1 q.2).2)

lemma baseDerivative_integrable_sq {f : E → ℝ} (hf : ContDiff ℝ 1 f)
    (hg : Integrable (fun x => ‖fderiv ℝ f x‖^2) (stdGaussian E)) :
    Integrable (fun q : E × E => (fderiv ℝ f q.1 q.2)^2) ((stdGaussian E).prod (stdGaussian E)) := by
  have hc := hf.continuous_fderiv (by norm_num)
  have hm : StronglyMeasurable (fun q : E × E => (fderiv ℝ f q.1 q.2)^2) := by
    exact ((hc.comp continuous_fst).clm_apply continuous_snd).pow 2 |>.stronglyMeasurable
  have hv : Integrable (fun x : E => ‖x‖^2) (stdGaussian E) := by
    simpa only [id_eq] using (IsGaussian.memLp_two_id (μ := stdGaussian E)).integrable_norm_pow'
  apply (hg.mul_prod hv).mono' hm.aestronglyMeasurable
  exact .of_forall (fun q => by
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    have h := (fderiv ℝ f q.1).le_opNorm q.2
    rw [Real.norm_eq_abs] at h
    nlinarith [abs_nonneg (fderiv ℝ f q.1 q.2),mul_nonneg (norm_nonneg (fderiv ℝ f q.1)) (norm_nonneg q.2),sq_abs (fderiv ℝ f q.1 q.2)])

lemma baseDerivative_integral_sq {f : E → ℝ} (hf : ContDiff ℝ 1 f)
    (hg : Integrable (fun x => ‖fderiv ℝ f x‖^2) (stdGaussian E)) :
    (∫ q : E × E,(fderiv ℝ f q.1 q.2)^2 ∂(stdGaussian E).prod (stdGaussian E))=
      ∫ x,‖fderiv ℝ f x‖^2 ∂stdGaussian E := by
  rw [integral_prod _ (baseDerivative_integrable_sq hf hg)]
  exact integral_congr_ae (.of_forall (fun x => dual_secondMoment (fderiv ℝ f x)))

lemma rotatedDerivative_integral_sq {f : E → ℝ} (hf : ContDiff ℝ 1 f)
    (hg : Integrable (fun x => ‖fderiv ℝ f x‖^2) (stdGaussian E)) (θ : ℝ) :
    Integrable (fun q : E × E => (rotatedDerivative f (θ,q))^2) ((stdGaussian E).prod (stdGaussian E)) ∧
      (∫ q : E × E,(rotatedDerivative f (θ,q))^2 ∂(stdGaussian E).prod (stdGaussian E))=
        ∫ x,‖fderiv ℝ f x‖^2 ∂stdGaussian E := by
  have hrot : MeasurePreserving (ContinuousLinearMap.rotation θ : E × E → E × E)
      ((stdGaussian E).prod (stdGaussian E)) ((stdGaussian E).prod (stdGaussian E)) :=
    ⟨(ContinuousLinearMap.rotation θ : E × E →L[ℝ] E × E).continuous.measurable,
      IsGaussian.map_rotation_eq_self (μ := stdGaussian E) integral_id_stdGaussian θ⟩
  have hi := hrot.integrable_comp_of_integrable (baseDerivative_integrable_sq hf hg)
  refine ⟨hi,?_⟩
  rw [← baseDerivative_integral_sq hf hg]
  exact integral_map hrot.measurable.aemeasurable
    (by rw [hrot.map_eq];exact (baseDerivative_integrable_sq hf hg).aestronglyMeasurable) |>.symm.trans
    (congrArg (fun μ => ∫ q : E × E,(fderiv ℝ f q.1 q.2)^2 ∂μ) hrot.map_eq)

lemma rotatedDerivative_continuous {f : E → ℝ} (hf : ContDiff ℝ 1 f) :
    Continuous (rotatedDerivative f) := by
  have hX : Continuous (fun q : ℝ × (E × E) => Real.cos q.1 • q.2.1+Real.sin q.1 • q.2.2) := by fun_prop
  have hY : Continuous (fun q : ℝ × (E × E) => -Real.sin q.1 • q.2.1+Real.cos q.1 • q.2.2) := by fun_prop
  exact ((hf.continuous_fderiv (by norm_num)).comp hX).clm_apply hY

lemma path_hasDerivAt {f : E → ℝ} (hf : ContDiff ℝ 1 f) (q : E × E) (θ : ℝ) :
    HasDerivAt (fun t => f ((ContinuousLinearMap.rotation t q).1)) (rotatedDerivative f (θ,q)) θ := by
  have hd := ((Real.hasDerivAt_cos θ).smul_const q.1).add ((Real.hasDerivAt_sin θ).smul_const q.2)
  exact ((hf.differentiable (by norm_num)).differentiableAt.hasFDerivAt).comp_hasDerivAt θ hd

lemma path_difference_sq_le {f : E → ℝ} (hf : ContDiff ℝ 1 f) (q : E × E) :
    (f q.2-f q.1)^2≤(Real.pi/2)*(∫ θ in Ioc (0 : ℝ) (Real.pi/2),(rotatedDerivative f (θ,q))^2) := by
  have hθ : Continuous (fun θ => rotatedDerivative f (θ,q)) :=
    (rotatedDerivative_continuous hf).comp (continuous_id.prodMk continuous_const)
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun θ _ => path_hasDerivAt hf q θ) (hθ.intervalIntegrable _ _)
      (a := (0 : ℝ)) (b := Real.pi/2)
  simp only [ContinuousLinearMap.rotation_apply,Real.cos_pi_div_two,Real.sin_pi_div_two,
    Real.cos_zero,Real.sin_zero,zero_smul,one_smul,zero_add,add_zero] at he
  have hm : MemLp (fun θ => rotatedDerivative f (θ,q)) 2 (volume.restrict (Ioc (0 : ℝ) (Real.pi/2))) := by
    apply (integrable_norm_rpow_iff hθ.stronglyMeasurable.aestronglyMeasurable
      (by norm_num : (2 : ℝ≥0∞)≠0) (by norm_num : (2 : ℝ≥0∞)≠∞)).mp
    have hs : Integrable (fun θ => ‖rotatedDerivative f (θ,q)‖^2)
        (volume.restrict (Ioc (0 : ℝ) (Real.pi/2))) := by
      have hI : IntegrableOn ((fun θ => ‖rotatedDerivative f (θ,q)‖)^2) (Icc (0 : ℝ) (Real.pi/2)) volume :=
        (hθ.norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc
      exact (hI.mono_set Ioc_subset_Icc_self).congr (.of_forall (fun θ => rfl))
    simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using hs
  have hcs := PredictableDriftTime.integral_sq_le_measure_mul_integral_sq
    (volume.restrict (Ioc (0 : ℝ) (Real.pi/2))) (fun θ => rotatedDerivative f (θ,q)) hm
  rw [intervalIntegral.integral_of_le (by positivity : (0 : ℝ)≤Real.pi/2)] at he
  rw [he] at hcs
  have hmass : (volume.restrict (Ioc (0 : ℝ) (Real.pi/2))).real univ=Real.pi/2 := by
    rw [Measure.real_def,Measure.restrict_apply MeasurableSet.univ,univ_inter,Real.volume_Ioc]
    rw [sub_zero,ENNReal.toReal_ofReal (by positivity)]
  simpa only [hmass] using hcs

lemma pair_variance_identity {f : E → ℝ} (hf : Measurable f) (h2 : MemLp f 2 (stdGaussian E)) :
    variance f (stdGaussian E)=(1/2 : ℝ)*(∫ q : E × E,(f q.2-f q.1)^2
      ∂(stdGaussian E).prod (stdGaussian E)) := by
  let μ := stdGaussian E
  have hx := h2.comp_measurePreserving (measurePreserving_fst (μ := μ) (ν := μ))
  have hy := h2.comp_measurePreserving (measurePreserving_snd (μ := μ) (ν := μ))
  change MemLp (fun q : E × E => f q.1) 2 (μ.prod μ) at hx
  change MemLp (fun q : E × E => f q.2) 2 (μ.prod μ) at hy
  have hmean : (∫ q : E × E,f q.2-f q.1 ∂μ.prod μ)=0 := by
    rw [integral_sub (hy.integrable one_le_two) (hx.integrable one_le_two),integral_fun_snd,integral_fun_fst]
    simp
  have hv := variance_of_integral_eq_zero ((hf.comp measurable_snd).sub (hf.comp measurable_fst)).aemeasurable hmean
  change variance (fun q : E × E => f q.2-f q.1) (μ.prod μ)=∫ q : E × E,(f q.2-f q.1)^2 ∂μ.prod μ at hv
  have hvar := variance_fun_sub hy hx
  rw [(indepFun_prod hf hf).symm.covariance_eq_zero hy hx,
    (measurePreserving_snd (μ := μ) (ν := μ)).variance_fun_comp hf.aemeasurable,
    (measurePreserving_fst (μ := μ) (ν := μ)).variance_fun_comp hf.aemeasurable,hv] at hvar
  linarith

lemma rotatedDerivative_time_integral {f : E → ℝ} (hf : ContDiff ℝ 1 f)
    (hg : Integrable (fun x => ‖fderiv ℝ f x‖^2) (stdGaussian E)) :
    Integrable (fun q : E × E => ∫ θ in Ioc (0 : ℝ) (Real.pi/2),(rotatedDerivative f (θ,q))^2)
      ((stdGaussian E).prod (stdGaussian E)) ∧
      (∫ q : E × E,∫ θ in Ioc (0 : ℝ) (Real.pi/2),(rotatedDerivative f (θ,q))^2
        ∂volume ∂(stdGaussian E).prod (stdGaussian E))=(Real.pi/2)*(∫ x,‖fderiv ℝ f x‖^2 ∂stdGaussian E) := by
  let τ : Measure ℝ := volume.restrict (Ioc (0 : ℝ) (Real.pi/2))
  let ρ := (stdGaussian E).prod (stdGaussian E)
  have hsm : StronglyMeasurable (fun q : ℝ × (E × E) => (rotatedDerivative f q)^2) :=
    (rotatedDerivative_continuous hf).pow 2 |>.stronglyMeasurable
  have hh (θ : ℝ) := rotatedDerivative_integral_sq hf hg θ
  have houter : Integrable (fun θ => ∫ q : E × E,(rotatedDerivative f (θ,q))^2 ∂ρ) τ :=
    (integrable_const (∫ x,‖fderiv ℝ f x‖^2 ∂stdGaussian E)).congr (.of_forall (fun θ => (hh θ).2.symm))
  have hi : Integrable (fun q : ℝ × (E × E) => (rotatedDerivative f q)^2) (τ.prod ρ) := by
    apply (integrable_prod_iff hsm.aestronglyMeasurable).mpr
    refine ⟨.of_forall (fun θ => (hh θ).1),?_⟩
    convert houter using 1
    funext θ
    exact integral_congr_ae (.of_forall (fun q => Real.norm_of_nonneg (sq_nonneg _)))
  refine ⟨hi.integral_prod_right,?_⟩
  rw [← integral_prod_symm _ hi,integral_prod _ hi]
  change (∫ θ,∫ q : E × E,(rotatedDerivative f (θ,q))^2 ∂ρ ∂τ)=_
  have hfunc : (fun θ => ∫ q : E × E,(rotatedDerivative f (θ,q))^2 ∂ρ)=
      fun _ : ℝ => ∫ x,‖fderiv ℝ f x‖^2 ∂stdGaussian E := funext (fun θ => (hh θ).2)
  rw [hfunc,integral_const]
  have hmass : τ.real univ=Real.pi/2 := by
    rw [Measure.real_def,Measure.restrict_apply MeasurableSet.univ,univ_inter,Real.volume_Ioc]
    rw [sub_zero,ENNReal.toReal_ofReal (by positivity)]
  change τ.real univ*(∫ x,‖fderiv ℝ f x‖^2 ∂stdGaussian E)=_
  rw [hmass]

/-- Dimension-independent Gaussian Poincaré estimate obtained from an
actual quarter-circle Gaussian rotation. The universal constant is π²/8. -/
theorem gaussian_variance_le_gradient {f : E → ℝ} (hf : ContDiff ℝ 1 f)
    (h2 : MemLp f 2 (stdGaussian E))
    (hg : Integrable (fun x => ‖fderiv ℝ f x‖^2) (stdGaussian E)) :
    variance f (stdGaussian E)≤(Real.pi^2/8)*(∫ x,‖fderiv ℝ f x‖^2 ∂stdGaussian E) := by
  have ht := rotatedDerivative_time_integral hf hg
  have hx := h2.comp_measurePreserving (measurePreserving_fst (μ := stdGaussian E) (ν := stdGaussian E))
  have hy := h2.comp_measurePreserving (measurePreserving_snd (μ := stdGaussian E) (ν := stdGaussian E))
  have hp : Integrable (fun q : E × E => (f q.2-f q.1)^2) ((stdGaussian E).prod (stdGaussian E)) :=
    (hy.sub hx).integrable_sq
  rw [pair_variance_identity hf.continuous.measurable h2]
  calc
    _ ≤ (1/2 : ℝ)*(∫ q : E × E,(Real.pi/2)*(∫ θ in Ioc (0 : ℝ) (Real.pi/2),
        (rotatedDerivative f (θ,q))^2) ∂(stdGaussian E).prod (stdGaussian E)) :=
      mul_le_mul_of_nonneg_left (integral_mono_ae hp (ht.1.const_mul _) (.of_forall (path_difference_sq_le hf))) (by norm_num)
    _ = _ := by rw [integral_const_mul,ht.2];ring

end SphericalAging.GaussianRotationVariance
