-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalPairRegression
public import SlowEquilibration.ConditionedDeterminantMoments

/-! Actual full-coefficient conditional centered Hessian laws. The actual
residual covariance bound is derived; the small regression-mean hypothesis
remains explicit until the two-point small-overlap estimate is proved. -/

@[expose] public section
namespace SlowEquilibration.SphericalConditionalMatrices

noncomputable section
open MeasureTheory ProbabilityTheory Set Function
open SphericalModel SphericalGaussianJet SphericalForm SphereHessian
open WholeFieldRegression IntrinsicHessianLaw IntrinsicGradientRegression
open SphericalHessianTraceCovariance GaussianRegressionCovariance GaussianRegression
open GaussianMatrixMomentLaw SymmetricGaussianCovariance GOEAsymptotics
open OAI.CriticalSK
open scoped Topology RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 500000

variable {F G : Type*}
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]
  [MeasurableSpace G] [BorelSpace G]

omit [FiniteDimensional ℝ G] in
/-- The original full tensor posterior pushes forward to its genuine
coefficient-linear conditional law, with no replacement disorder space. -/
lemma coefficientKernel_linear_map {N P : ℕ}
    (A : EuclideanDisorder N P →L[ℝ] F) (B : EuclideanDisorder N P →L[ℝ] G) (w : F) :
    (coefficientKernel A w).map (actualObservation B)=conditionalLaw A B w := by
  have hm : Measurable (actualObservation B) := B.continuous.measurable.comp
    ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Coordinate N P => ℝ)).symm.continuous.measurable.comp
      (flatDisorder_measurable N P))
  rw [coefficientKernel_apply,Measure.map_map hm (unpackCLM N P).continuous.measurable]
  have he : actualObservation B ∘ unpackCLM N P=B := by
    funext g
    rfl
  rw [he]
  rfl

omit [FiniteDimensional ℝ G] in
/-- At every target, the centered actual matrix observation under the full
original coefficient posterior has the actual residual Gaussian matrix law. -/
lemma centered_actualObservation_hasLaw {N P : ℕ}
    (A : EuclideanDisorder N P →L[ℝ] F) (B : EuclideanDisorder N P →L[ℝ] G) (w : F) :
    HasLaw (fun J => actualObservation B J-B (lift A w)) (centeredLaw A B)
      (coefficientKernel A w) := by
  have hB : HasLaw (actualObservation B) (conditionalLaw A B w) (coefficientKernel A w) :=
    ⟨B.continuous.measurable.comp ((PiLp.continuousLinearEquiv 2 ℝ
      (fun _ : Coordinate N P => ℝ)).symm.continuous.measurable.comp (flatDisorder_measurable N P))
      |>.aemeasurable,coefficientKernel_linear_map A B w⟩
  have h := (hasLaw_map (show Measurable (fun z : G => z-B (lift A w)) from by fun_prop).aemeasurable).fun_comp hB
  rw [conditionalLaw_centered] at h
  exact h

omit [MeasurableSpace F] [BorelSpace F] in
/-- Actual spherical Hessian conditional centered law has symmetric support;
this follows from actual field second-derivative symmetry for every sample. -/
lemma centered_hessian_symmetric_ae {N P m : ℕ}
    (A : EuclideanDisorder N P →L[ℝ] F) (c : Degree P → ℝ) (x : Vector N) (e : Fin m → Vector N) :
    ∀ᵐ W ∂centeredLaw A (hessianGaussianCLM c x e),∀ i j,W i j=W j i := by
  rw [centeredLaw,ae_map_iff (by fun_prop) (measurableSet_setOfPred.mpr (by fun_prop))]
  exact ae_of_all _ fun g => hessianGaussianCLM_symmetric c x e (residual A g)

/-- Every actual conditional intrinsic determinant is the true affine
Gaussian raw determinant whenever its observed radial score is Nk. -/
theorem actual_intrinsicDet_conditional_hasLaw {n : ℕ}
    (μ : FiniteMixture) (Q : ℝ) (x : Vector (n+2)) (hx : ‖x‖^2=(n+2 : ℕ))
    (A : EuclideanDisorder (n+2) μ.maxDegree →L[ℝ] F) (w : F) (k : ℝ)
    (hrad : ∀ᵐ J ∂coefficientKernel A w,
      jet (centerCoefficients (mixtureCoefficients μ) Q) 1 x (fun _ => x) J=((n+2 : ℕ):ℝ)*k) :
    let c := centerCoefficients (mixtureCoefficients μ) Q
    let B := hessianGaussianCLM c x (tangentFrame x hx)
    let C := B (lift A w)
    HasLaw (ConditionedDeterminantMoments.intrinsicDet μ Q x)
      ((centeredLaw A B).map (rawDet C k)) (coefficientKernel A w) := by
  let c := centerCoefficients (mixtureCoefficients μ) Q
  let B := hessianGaussianCLM c x (tangentFrame x hx)
  let C := B (lift A w)
  have hX := centered_actualObservation_hasLaw A B w
  have h := (hasLaw_map (rawDet_measurable C k).aemeasurable).fun_comp hX
  apply h.congr
  filter_upwards [hrad] with J hJ
  have he : gaussianToMatrix (C+(actualObservation B J-C))=hessianMatrix c x (tangentFrame x hx) J := by
    ext i j
    change C i j+(hessianGaussianCLM c x (tangentFrame x hx) (euclideanDisorder J) i j-C i j)=_
    simp only [hessianGaussianCLM_apply,unpack_euclideanDisorder,hessianMatrix]
    ring
  change ConditionedDeterminantMoments.intrinsicDet μ Q x J=rawDet C k (actualObservation B J-C)
  rw [ConditionedDeterminantMoments.intrinsicDet,intrinsicHessian_det c J x hx]
  have hk : jet c 1 x (fun _ => x) J/(n+2 : ℕ)=k := by rw [hJ];field_simp
  rw [hk,ConditionedDeterminantMoments.shifted_abs_det]
  unfold rawDet GOERawMoments.matrixAbsoluteDet
  rw [he]

/-- A genuine full matrix law transfers proved bulk moments to the actual
intrinsic determinant, preserving its own ordinary expectation normalization. -/
lemma conditional_moments_of_matrix_law {Ω : Type*} [MeasurableSpace Ω] {η : Measure Ω}
    {n : ℕ} (μ : Measure (GOEAsymptotics.GaussianMatrix (n+1)))
    (C : GOEAsymptotics.GaussianMatrix (n+1)) (k rho : ℝ) (bound : ℝ → ℝ)
    (hbulk : MomentBounds μ C k rho bound) (D : Ω → ℝ)
    (hD : HasLaw D (μ.map (rawDet C k)) η) :
    Integrable D η ∧ (∫ z,D z ∂η)=(∫ W,rawDet C k W ∂μ) ∧
      0 < ∫ z,D z ∂η ∧ ∀ r : ℝ,0 ≤ r →
      Integrable (fun z => (D z/(∫ y,D y ∂η))^r) η ∧
      (∫ z,(D z/(∫ y,D y ∂η))^r ∂η) ≤ bound r := by
  have hd := rawDet_measurable C k
  have hid : Integrable id (μ.map (rawDet C k)) :=
    (integrable_map_measure aestronglyMeasurable_id hd.aemeasurable).mpr hbulk.integrable
  have he : (∫ z,D z ∂η)=∫ W,rawDet C k W ∂μ := by
    rw [hD.integral_eq]
    simpa only [id_eq] using integral_map (φ := rawDet C k) (f := id) hd.aemeasurable aestronglyMeasurable_id
  refine ⟨hD.integrable hid,he,by rw [he];exact hbulk.expectation_pos,?_⟩
  intro r hr
  rw [he]
  let f := fun v : ℝ => (v/(∫ W,rawDet C k W ∂μ))^r
  have hf : Measurable f := (measurable_id.div_const _).pow_const r
  have hfi : Integrable f (μ.map (rawDet C k)) :=
    (integrable_map_measure hf.aestronglyMeasurable hd.aemeasurable).mpr (hbulk.raw_integrable r hr)
  refine ⟨hD.integrable_comp hfi,?_⟩
  have hm := hD.integral_comp hf.aestronglyMeasurable
  rw [integral_map hd.aemeasurable hf.aestronglyMeasurable] at hm
  exact hm.trans_le ((hbulk.ordered r hr).trans (hbulk.upper r hr))

/-- Actual conditional spherical determinant moments from true regression
covariance contraction. Surjectivity and the actual regression-mean norm
remain explicit geometric hypotheses, rather than assuming the conclusion. -/
theorem conditional_intrinsicDet_moments {Q g : ℝ} (μ : FiniteMixture)
    (hQ : 0 < Q) (hg : 0 < g) :
    ∃ K : ℝ,1 ≤ K ∧ ∀ (n : ℕ) (x : Vector (n+2)) (hx : ‖x‖^2=(n+2 : ℕ)),
      ∀ (A : EuclideanDisorder (n+2) μ.maxDegree →L[ℝ] F),Surjective A →
      ∀ (w : F) (k : ℝ),2*Real.sqrt (Q^2*μ.xi2 Q)+g ≤ k →
      let c := centerCoefficients (mixtureCoefficients μ) Q
      let B := hessianGaussianCLM c x (tangentFrame x hx)
      ‖gaussianMatrixCLM (B (lift A w))‖ ≤ g/4 →
      (∀ᵐ J ∂coefficientKernel A w,jet c 1 x (fun _ => x) J=((n+2 : ℕ):ℝ)*k) →
      Integrable (ConditionedDeterminantMoments.intrinsicDet μ Q x) (coefficientKernel A w) ∧
      0 < ∫ J,ConditionedDeterminantMoments.intrinsicDet μ Q x J ∂coefficientKernel A w ∧
      ∀ r : ℝ,0 ≤ r →
      Integrable (fun J => (ConditionedDeterminantMoments.intrinsicDet μ Q x J/
        (∫ I,ConditionedDeterminantMoments.intrinsicDet μ Q x I ∂coefficientKernel A w))^r) (coefficientKernel A w) ∧
      (∫ J,(ConditionedDeterminantMoments.intrinsicDet μ Q x J/
        (∫ I,ConditionedDeterminantMoments.intrinsicDet μ Q x I ∂coefficientKernel A w))^r ∂coefficientKernel A w) ≤
        K^r*Real.exp (K*r^2) := by
  have hb : 0 < Q^2*μ.xi2 Q := mul_pos (sq_pos_of_pos hQ) (μ.xi2_pos hQ)
  obtain ⟨K,hK,hall⟩ := normalized_moments_all_dimensions hb hg
  refine ⟨K,hK,?_⟩
  intro n x hx A hA w k hk
  dsimp only
  intro hmean hrad
  let c := centerCoefficients (mixtureCoefficients μ) Q
  let B := hessianGaussianCLM c x (tangentFrame x hx)
  let ν := centeredLaw A B
  let C := B (lift A w)
  have hC : ∀ i j,C i j=C j i := hessianGaussianCLM_symmetric c x _ _
  have hvar (M : GOEAsymptotics.GaussianMatrix (n+1)) (hM : ∀ i j,M i j=M j i) :
      Var[fun W => Matrix.trace (entries W*entries M);ν] ≤
        (2*(Q^2*μ.xi2 Q)/(n+2 : ℕ))*Matrix.trace (entries M*entries M) := by
    have hv := conditioned_hessian_trace_variance_bound A hA (by omega) c
      (centerCoefficients_nonnegative _ (mixtureCoefficients_nonnegative μ) hQ.le) x
      (r := 1) (by simpa using hx) _ (tangentFrame_orthonormal x hx) (tangentFrame_tangent x hx) M hM
    dsimp only [c] at hv
    simpa only [secondCovariance_center,secondCovariance_mixture] using hv
  have hbulk := hall (n+2) n (by omega) ν (centeredLaw_mean A B)
    (centered_hessian_symmetric_ae A c x _) hvar C hC hmean k hk
  have hD := actual_intrinsicDet_conditional_hasLaw μ Q x hx A w k hrad
  have h := conditional_moments_of_matrix_law ν C k (g/2) _ hbulk
    (ConditionedDeterminantMoments.intrinsicDet μ Q x) hD
  exact ⟨h.1,h.2.2.1,h.2.2.2⟩

end
end SlowEquilibration.SphericalConditionalMatrices
