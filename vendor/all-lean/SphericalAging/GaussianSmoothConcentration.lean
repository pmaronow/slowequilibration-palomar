module

public import SphericalAging.GaussianRotationConcentration

public section

/-! The actual centered Gaussian sub-Gaussian MGF of a C1 function with
a bounded derivative. The dimension-free constant comes from the real
rotation/Jensen proof, rather than a concentration hypothesis. -/
noncomputable section
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.GaussianSmoothConcentration
open Set MeasureTheory ProbabilityTheory GaussianExponentialNorm GaussianRotationConcentration
open scoped NNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem integrable_lipschitz (f : E→ℝ) {L : ℝ≥0} (hf : LipschitzWith L f) :
    Integrable f (stdGaussian E) := by
  have hI : Integrable (fun x : E => |f 0|+(L:ℝ)*‖x‖) (stdGaussian E) :=
    (integrable_const _).add ((IsGaussian.integrable_id (μ := stdGaussian E)).norm.const_mul _)
  apply hI.mono' hf.continuous.stronglyMeasurable.aestronglyMeasurable
  exact ae_of_all _ (fun x => by
    rw [Real.norm_eq_abs]
    have hfl : |f x-f 0|≤(L:ℝ)*‖x‖ := by
      simpa only [Real.dist_eq,dist_zero_right] using hf.dist_le_mul x 0
    have hh := abs_add_le (f x-f 0) (f 0)
    rw [sub_add_cancel] at hh
    linarith)

theorem mean_minus_exponential_integrable_and_le (f : E→ℝ) (hf : ContDiff ℝ 1 f)
    (L : ℝ≥0) (hbound : ∀x,‖fderiv ℝ f x‖≤L) (t : ℝ) :
    Integrable (fun x => Real.exp (t*((∫y,f y ∂stdGaussian E)-f x))) (stdGaussian E) ∧
      (∫x,Real.exp (t*((∫y,f y ∂stdGaussian E)-f x)) ∂stdGaussian E)≤
        Real.exp ((Real.pi/2*t)^2*(L:ℝ)^2/2) := by
  have hLip : LipschitzWith L f := lipschitzWith_of_nnnorm_fderiv_le
    (hf.differentiable (by norm_num)) (fun x => hbound x)
  have hfi := integrable_lipschitz f hLip
  have hEi := integrable_exp_lipschitz (stdGaussian E) f hLip t
  have hp := pair_exponential_integrable_and_le f hf L L.coe_nonneg hbound t
  have hpoint (x : E) : Real.exp (t*((∫y,f y ∂stdGaussian E)-f x))≤
      ∫y,Real.exp (t*(f y-f x)) ∂stdGaussian E := by
    let u : E→ℝ := fun y => t*(f y-f x)
    have hui : Integrable u (stdGaussian E) := (hfi.sub (integrable_const _)).const_mul t
    have hei : Integrable (Real.exp∘u) (stdGaussian E) := by
      simpa only [Function.comp_def,u,mul_sub,Real.exp_sub] using hEi.div_const (Real.exp (t*f x))
    have hj := convexOn_exp.map_integral_le Real.continuous_exp.continuousOn isClosed_univ
      (ae_of_all _ (fun _ => mem_univ _)) hui hei
    have hu : (∫y,u y ∂stdGaussian E)=t*((∫y,f y ∂stdGaussian E)-f x) := by
      rw [integral_const_mul,integral_sub hfi (integrable_const _)];simp
    rw [hu] at hj
    exact hj
  have hi : Integrable (fun x => Real.exp (t*((∫y,f y ∂stdGaussian E)-f x)))
      (stdGaussian E) := by
    apply hp.1.integral_prod_left.mono' (by fun_prop)
    exact ae_of_all _ (fun x => by
      rw [Real.norm_of_nonneg (Real.exp_nonneg _)]
      exact hpoint x)
  refine ⟨hi,?_⟩
  calc
    _≤∫x,∫y,Real.exp (t*(f y-f x)) ∂stdGaussian E ∂stdGaussian E :=
      integral_mono hi hp.1.integral_prod_left hpoint
    _=(∫q : E×E,Real.exp (t*(f q.2-f q.1)) ∂(stdGaussian E).prod (stdGaussian E)) :=
      (integral_prod _ hp.1).symm
    _≤_ := hp.2

@[expose] def rotationConstant (L : ℝ≥0) : ℝ≥0 := ⟨(Real.pi/2)^2*(L:ℝ)^2,by positivity⟩

theorem centered_hasSubgaussianMGF (f : E→ℝ) (hf : ContDiff ℝ 1 f)
    (L : ℝ≥0) (hbound : ∀x,‖fderiv ℝ f x‖≤L) :
    HasSubgaussianMGF (fun x => f x-∫y,f y ∂stdGaussian E) (rotationConstant L) (stdGaussian E) := by
  have he (t : ℝ) : (fun x : E => Real.exp (-t*((∫y,f y ∂stdGaussian E)-f x)))=
      (fun x => Real.exp (t*(f x-∫y,f y ∂stdGaussian E))) := by
    funext x;congr 1;ring
  refine ⟨fun t => ?_,fun t => ?_⟩
  · have hi := (mean_minus_exponential_integrable_and_le f hf L hbound (-t)).1
    rw [he] at hi
    exact hi
  · have hb := (mean_minus_exponential_integrable_and_le f hf L hbound (-t)).2
    rw [he] at hb
    change _≤Real.exp ((rotationConstant L:ℝ)*t^2/2)
    exact hb.trans_eq (by
      congr 1
      change (Real.pi / 2 * -t)^2 * (L:ℝ)^2 / 2 =
        ((Real.pi / 2)^2 * (L:ℝ)^2) * t^2 / 2
      ring)

theorem centered_absolute_tail (f : E→ℝ) (hf : ContDiff ℝ 1 f)
    (L : ℝ≥0) (hbound : ∀x,‖fderiv ℝ f x‖≤L) (ε : ℝ) (hε : 0≤ε) :
    (stdGaussian E).real {x | ε≤|f x-∫y,f y ∂stdGaussian E|}≤
      2*Real.exp (-ε^2/(2*(rotationConstant L:ℝ))) := by
  let X : E→ℝ := fun x => f x-∫y,f y ∂stdGaussian E
  have hG := centered_hasSubgaussianMGF f hf L hbound
  have hs : {x | ε≤|X x|}={x | ε≤X x}∪{x | ε≤-X x} := by
    ext x
    change ε≤|X x| ↔ ε≤X x ∨ ε≤-X x
    exact le_abs
  change (stdGaussian E).real {x | ε≤|X x|}≤_
  rw [hs]
  have hn := hG.neg.measure_ge_le hε
  have hp := hG.measure_ge_le hε
  exact (measureReal_union_le _ _).trans (by simpa only [two_mul,Pi.neg_apply] using add_le_add hp hn)

end SphericalAging.GaussianSmoothConcentration
