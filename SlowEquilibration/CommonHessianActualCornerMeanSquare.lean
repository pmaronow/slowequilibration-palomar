-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.CommonHessianCornerMoments
public import SlowEquilibration.SphericalConditionalMatrices
public import SlowEquilibration.PairHessianMean

/-! Actual whole-tensor posterior corner second moments. The true corner
variance is at most 2b/N, and its literal regression mean is bounded using
the proved mixed/proper-value Hessian cross-covariance estimates. -/
@[expose] public section
namespace SlowEquilibration.SphericalCommonHessianRegression
noncomputable section
open Function MeasureTheory ProbabilityTheory SphericalModel SphericalGaussianJet WholeFieldRegression
open GaussianRegression GaussianRegressionCovariance SphericalConditionalMatrices
open NormalizedPairObservations PairHessianMean PairObservationNormBounds GaussianObservationCoercivity
open scoped RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
variable {F : Type*}
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]

omit [MeasurableSpace F] [BorelSpace F] in
/-- The literal centered corner square has the dimension-sharp Gaussian
variance bound. The diagonal factor two is derived from the actual field. -/
theorem conditional_centered_corner_second_moment {N P : ℕ} (hN : 0 < N)
    (c : Degree P → ℝ) (hc : ∀ p,0 ≤ c p) (x : Vector N) (hx : ‖x‖^2=(N:ℝ))
    (v : Vector N) (hv : ‖v‖=1) (hvtan : inner ℝ v x=0)
    (A : EuclideanDisorder N P →L[ℝ] F) (hA : Surjective A) :
    Integrable (fun u:ℝ=>u^2) (centeredLaw A (cornerCLM c x v)) ∧
      (∫ u,u^2 ∂centeredLaw A (cornerCLM c x v)) ≤ 2*secondCovariance c 1/(N:ℝ) := by
  have hInt : Integrable (fun u:ℝ=>u^2) (centeredLaw A (cornerCLM c x v)) :=
    (memLp_two_iff_integrable_sq aestronglyMeasurable_id).mp IsGaussian.memLp_two_id
  have hh:=centeredLaw_covariance_le_gram A hA (cornerCLM c x v) (1:ℝ)
  rw [cornerCLM_gram hN c hc x hx v hv hvtan] at hh
  rw [covarianceBilin_apply IsGaussian.memLp_two_id] at hh
  simp only [id_eq] at hh
  rw [centeredLaw_mean] at hh
  simpa only [sub_zero,smul_apply,ContinuousLinearMap.id_apply,smul_eq_mul,
    RCLike.inner_apply,conj_trivial,one_mul,mul_one,← pow_two] using And.intro hInt hh

@[simp] lemma actual_corner_eq_jet {N P : ℕ} (c : Degree P → ℝ)
    (x v : Vector N) (J : Disorder N P) :
    actualObservation (cornerCLM c x v) J=jet c 2 x ![v,v] J := by
  simp only [actualObservation,cornerCLM,flatJetCLM_apply,unpack_euclideanDisorder]

/-- Actual centered corner variance at every full-coefficient target,
including null observations and singular residual corner laws. -/
theorem actual_conditional_centered_corner_second_moment {N P : ℕ} (hN : 0 < N)
    (c : Degree P → ℝ) (hc : ∀ p,0 ≤ c p) (x : Vector N) (hx : ‖x‖^2=(N:ℝ))
    (v : Vector N) (hv : ‖v‖=1) (hvtan : inner ℝ v x=0)
    (A : EuclideanDisorder N P →L[ℝ] F) (hA : Surjective A) (w : F) :
    Integrable (fun J:Disorder N P=>(actualObservation (cornerCLM c x v) J-
      cornerCLM c x v (lift A w))^2) (coefficientKernel A w) ∧
      (∫ J,(actualObservation (cornerCLM c x v) J-cornerCLM c x v (lift A w))^2 ∂coefficientKernel A w) ≤
        2*secondCovariance c 1/(N:ℝ) := by
  have hC:=conditional_centered_corner_second_moment hN c hc x hx v hv hvtan A hA
  have hX:=centered_actualObservation_hasLaw A (cornerCLM c x v) w
  constructor
  · exact hX.integrable_comp hC.1
  · exact (hX.integral_comp (show AEStronglyMeasurable (fun u:ℝ=>u^2)
        (centeredLaw A (cornerCLM c x v)) from by fun_prop)).trans_le hC.2

/-- At every observation target, the actual original tensor corner has
second moment equal to its genuine centered variance plus squared lift mean. -/
theorem actual_conditional_corner_second_moment {N P : ℕ} (hN : 0 < N)
    (c : Degree P → ℝ) (hc : ∀ p,0 ≤ c p) (x : Vector N) (hx : ‖x‖^2=(N:ℝ))
    (v : Vector N) (hv : ‖v‖=1) (hvtan : inner ℝ v x=0)
    (A : EuclideanDisorder N P →L[ℝ] F) (hA : Surjective A) (w : F) :
    Integrable (fun J:Disorder N P=>(actualObservation (cornerCLM c x v) J)^2) (coefficientKernel A w) ∧
      (∫ J,(actualObservation (cornerCLM c x v) J)^2 ∂coefficientKernel A w) ≤
        2*secondCovariance c 1/(N:ℝ)+(cornerCLM c x v (lift A w))^2 := by
  let B:=cornerCLM c x v
  let μ:=centeredLaw A B
  let a:=B (lift A w)
  have hC:=conditional_centered_corner_second_moment hN c hc x hx v hv hvtan A hA
  have hId : Integrable (fun u:ℝ=>u) μ:=IsGaussian.integrable_fun_id
  have hSq : Integrable (fun u:ℝ=>(u+a)^2) μ :=
    (memLp_two_iff_integrable_sq (by fun_prop)).mp ((IsGaussian.memLp_two_id : MemLp (fun u:ℝ=>u) 2 μ).add (memLp_const a))
  have hExpansion : (∫ u,(u+a)^2 ∂μ)=(∫ u,u^2 ∂μ)+a^2 := by
    have heq (u:ℝ) : (u+a)^2=u^2+(2*a)*u+a^2:=by ring
    simp only [heq]
    have hCInt : Integrable (fun u:ℝ=>u^2) μ:=hC.1
    have hLin : Integrable (fun u:ℝ=>(2*a)*u) μ:=hId.const_mul _
    rw [integral_add (f:=fun u:ℝ=>u^2+(2*a)*u) (g:=fun _=>a^2) (hCInt.add hLin) (integrable_const _),
      integral_add (f:=fun u:ℝ=>u^2) (g:=fun u=>(2*a)*u) hCInt hLin,integral_const_mul,centeredLaw_mean]
    simp
  have hX:=centered_actualObservation_hasLaw A B w
  let Φ:=fun u:ℝ=>(u+a)^2
  have hΦ : Measurable Φ:=by fun_prop
  have hEq (J:Disorder N P) : Φ (actualObservation B J-B (lift A w))=(actualObservation B J)^2 := by
    simp only [Φ,a,sub_add_cancel]
  refine ⟨?_,?_⟩
  · simpa only [Function.comp_def,hEq] using hX.integrable_comp (f:=Φ) hSq
  · have hi:=hX.integral_comp hΦ.aestronglyMeasurable
    simp only [Function.comp_def,hEq] at hi
    rw [hi,hExpansion]
    exact add_le_add hC.2 le_rfl

/-- Genuine mixed-pair posterior corner bound, with constants independent
of sphere dimension. No corner moment or regression-mean premise is used. -/
theorem actual_common_corner_mixed_mse {N P m : ℕ} (hN : 0 < N)
    (c : Degree P → ℝ) (hc : ∀ p,0 ≤ c p) (hdeg : ∀ p,c p≠0 → 4 ≤ p.val.val)
    (x y v : Vector N) (hx : ‖x‖^2=(N:ℝ)) (hy : ‖y‖^2=(N:ℝ))
    (hv : ‖v‖=1) (hvtan : inner ℝ v x=0) (e f : Fin m → Vector N) (hf : Orthonormal ℝ f)
    (hr : |overlap x y| ≤ 1) {δ M : ℝ} (hδ : 0 < δ) (hM : 0 ≤ M)
    (hA : Surjective (pairHilbert (singleMixedObservation c x e) (singleMixedObservation c y f)))
    (hinv : ‖(gram (pairHilbert (singleMixedObservation c x e) (singleMixedObservation c y f))).inverse‖ ≤ 1/δ)
    (w : WithLp 2 (MixedObservationSpace m×MixedObservationSpace m)) (hw : ‖w‖ ≤ M*Real.sqrt (N:ℝ)) :
    let A:=pairHilbert (singleMixedObservation c x e) (singleMixedObservation c y f)
    Integrable (fun J:Disorder N P=>(actualObservation (cornerCLM c x v) J)^2) (coefficientKernel A w) ∧
      (∫ J,(actualObservation (cornerCLM c x v) J)^2 ∂coefficientKernel A w) ≤
        2*secondCovariance c 1/(N:ℝ)+(7*profileBound c*M/δ)^2*|overlap x y|^2 := by
  dsimp only
  have hh:=actual_conditional_corner_second_moment hN c hc x hx v hv hvtan _ hA w
  have hMean:=mixed_lift_hessian_bound hN c hc hdeg x y v v hx hy hv hv hvtan hvtan e f hf w hδ hM hinv hw hr
  refine ⟨hh.1,hh.2.trans (add_le_add le_rfl ?_)⟩
  have hMeanSq:=pow_le_pow_left₀ (abs_nonneg _) hMean 2
  simpa only [sq_abs,mul_pow,cornerCLM] using hMeanSq

/-- The proper value-only pair has the same genuine corner bound. -/
theorem actual_common_corner_value_mse {N P m : ℕ} (hN : 0 < N)
    (c : Degree P → ℝ) (hc : ∀ p,0 ≤ c p) (hdeg : ∀ p,c p≠0 → 4 ≤ p.val.val)
    (x y v : Vector N) (hx : ‖x‖^2=(N:ℝ)) (hy : ‖y‖^2=(N:ℝ))
    (hv : ‖v‖=1) (hvtan : inner ℝ v x=0) (e f : Fin m → Vector N) (hf : Orthonormal ℝ f)
    (hr : |overlap x y| ≤ 1) {δ M : ℝ} (hδ : 0 < δ) (hM : 0 ≤ M)
    (hA : Surjective (pairHilbert (singleValueObservation c x e) (singleValueObservation c y f)))
    (hinv : ‖(gram (pairHilbert (singleValueObservation c x e) (singleValueObservation c y f))).inverse‖ ≤ 1/δ)
    (w : WithLp 2 (ValueObservationSpace m×ValueObservationSpace m)) (hw : ‖w‖ ≤ M*Real.sqrt (N:ℝ)) :
    let A:=pairHilbert (singleValueObservation c x e) (singleValueObservation c y f)
    Integrable (fun J:Disorder N P=>(actualObservation (cornerCLM c x v) J)^2) (coefficientKernel A w) ∧
      (∫ J,(actualObservation (cornerCLM c x v) J)^2 ∂coefficientKernel A w) ≤
        2*secondCovariance c 1/(N:ℝ)+(7*profileBound c*M/δ)^2*|overlap x y|^2 := by
  dsimp only
  have hh:=actual_conditional_corner_second_moment hN c hc x hx v hv hvtan _ hA w
  have hMean:=value_lift_hessian_bound hN c hc hdeg x y v v hx hy hv hv hvtan hvtan e f hf w hδ hM hinv hw hr
  refine ⟨hh.1,hh.2.trans (add_le_add le_rfl ?_)⟩
  have hMeanSq:=pow_le_pow_left₀ (abs_nonneg _) hMean 2
  simpa only [sq_abs,mul_pow,cornerCLM] using hMeanSq

end
end SlowEquilibration.SphericalCommonHessianRegression
