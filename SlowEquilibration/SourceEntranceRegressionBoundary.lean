-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalOriginalSourceContinuousLaw
public import SlowEquilibration.ConditionedEntranceSourceGradientCutoffRate
public import SlowEquilibration.ConditionedEntrancePureGradientCutoffRate
public import SlowEquilibration.EntranceLatitudeSourceCorrectionBound
public import SlowEquilibration.ConditionedEntrancePhysicalHittingSourceGradient
public import SlowEquilibration.ConditionedEntrancePureGradientBound
public import SlowEquilibration.SphericalPosteriorHorizonHitEvents
public import SlowEquilibration.EntranceLatitudePureSourceCorrectionBound
public import Mathlib.Algebra.MvPolynomial.Eval

/-! Manuscript `prop:ent-regression` and the unrestricted part of
`lem:ent-boundary`. Polynomial coefficients mean coefficients of commuting
monomials, not the redundant ordered tensor coordinates. The boundary law
includes an independent uniform axis, uniform initial state, and Wiener noise.
The correction estimates use the actual tensor regularity event; they only
need its field and derivative bounds, not its harmonic-sector strengthening. -/

@[expose] public section
noncomputable section

namespace SlowEquilibration.SourceEntranceRegressionBoundary

open MeasureTheory ProbabilityTheory Set Function Filter
open SphericalModel SphericalForm SphericalGaussianJet SphericalTaylorRemainder
open WholeFieldRegression IntrinsicGradientRegression IntrinsicHessianLaw ValueTangentConditioning GaussianRegression
open SphericalSequentialRegression SphericalPosteriorMaps SphericalMarkedWindows
open SphericalCriticalLatitude ConditionedEntrance SphericalPosteriorGradientIndependence
open SphericalAging HardSphereDynamics SphericalOverlapExponential
open scoped BigOperators RealInnerProductSpace NNReal ENNReal
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The actual commuting-variable polynomial, collecting repeated ordered
tensor monomials into their unique ordinary polynomial coefficients. -/
def fieldPolynomial {N P : ℕ} (c : Degree P → ℝ) (J : Disorder N P) :
    MvPolynomial (Fin N) ℝ :=
  ∑ p : Degree P, ∑ I : Fin p.val.val → Fin N,
    MvPolynomial.C (Real.sqrt (c p) *
      SphericalAging.FiniteModel.normalization N p.val.val * J p I) *
        ∏ i, MvPolynomial.X (I i)

/-- Its canonical coefficient vector, indexed by ordinary monomials. -/
def polynomialCoefficients {N P : ℕ} (c : Degree P → ℝ) (J : Disorder N P) :
    (Fin N →₀ ℕ) → ℝ := fun d => (fieldPolynomial c J).coeff d

private lemma fieldPolynomial_eval {N P : ℕ} (c : Degree P → ℝ)
    (J : Disorder N P) (x : Vector N) :
    MvPolynomial.eval (fun i => x i) (fieldPolynomial c J) = field c J x := by
  simp only [fieldPolynomial, MvPolynomial.eval_sum, map_mul,
    MvPolynomial.eval_C, MvPolynomial.eval_prod, MvPolynomial.eval_X,
    field, blockField, SphericalAging.FiniteModel.Hamiltonian,
    SphericalAging.FiniteModel.tensorMonomial, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro I hI
  ring

private lemma polynomialCoefficients_measurable {N P : ℕ} (c : Degree P → ℝ) :
    Measurable (polynomialCoefficients (N := N) c) := by
  apply Measurable.of_eval
  intro d
  simp only [polynomialCoefficients, fieldPolynomial, MvPolynomial.coeff_sum,
    MvPolynomial.coeff_C_mul]
  fun_prop

/-- The exact deleted polynomial in the nonpure branch. -/
def mixedDeletedPolynomial (n : ℕ) (μ : FiniteMixture) (Q : ℝ)
    (u : Vector (n+1)) (J : Disorder (n+1) μ.maxDegree) :
    MvPolynomial (Fin (n+1)) ℝ :=
  fieldPolynomial (mixtureCoefficients μ)
    (unpackDisorder (mixedPosterior n μ Q u 0 (euclideanDisorder J)))

/-- The exact deleted polynomial for proper value/gradient conditioning. -/
def valueDeletedPolynomial (n : ℕ) (μ : FiniteMixture) (Q : ℝ)
    (u : Vector (n+1)) (J : Disorder (n+1) μ.maxDegree) :
    MvPolynomial (Fin (n+1)) ℝ :=
  fieldPolynomial (mixtureCoefficients μ)
    (unpackDisorder (valuePosterior n μ Q u 0 (euclideanDisorder J)))

lemma mixedDeletedPolynomial_eval (n : ℕ) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 < Q) (hnp : μ.minDegree < μ.maxDegree)
    (u : Vector (n+1)) (hu : ‖u‖^2 = (n+1 : ℕ))
    (J : Disorder (n+1) μ.maxDegree) (x : Vector (n+1)) :
    MvPolynomial.eval (fun i => x i) (mixedDeletedPolynomial n μ Q u J) =
      fieldOfMixture μ J x + sourceRegressionCorrection μ Q hQ hnp J u 0 0 x := by
  rw [mixedDeletedPolynomial, fieldPolynomial_eval]
  have hz : scorePairEquiv (0,0) = 0 := by
    ext i
    fin_cases i <;> rfl
  simpa only [fieldOfMixture, unpack_euclideanDisorder, hz] using
    actual_mixedPosterior_original_field n μ hQ hnp u hu 0 0 (euclideanDisorder J) x

lemma valueDeletedPolynomial_eval (n : ℕ) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 < Q) (u : Vector (n+1)) (hu : ‖u‖^2 = (n+1 : ℕ))
    (J : Disorder (n+1) μ.maxDegree) (x : Vector (n+1)) :
    MvPolynomial.eval (fun i => x i) (valueDeletedPolynomial n μ Q u J) =
      fieldOfMixture μ J x + sourceValueRegressionCorrection μ Q J u 0 x := by
  rw [valueDeletedPolynomial, fieldPolynomial_eval]
  simpa only [fieldOfMixture, unpack_euclideanDisorder] using
    actual_valuePosterior_original_field n μ hQ u hu 0 (euclideanDisorder J) x

private lemma mixedPosterior_zero_eq_residual (n : ℕ) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 < Q) (hnp : μ.minDegree < μ.maxDegree)
    (u : Vector (n+1)) (hu : ‖u‖^2 = (n+1 : ℕ)) :
    mixedPosterior n μ Q u 0 =
      residual (jointCLM (centerCoefficients (mixtureCoefficients μ) Q) u
        (tangentFrame u hu)) := by
  let c := centerCoefficients (mixtureCoefficients μ) Q
  have hc := centerCoefficients_nonnegative _ (mixtureCoefficients_nonnegative μ) hQ.le
  have h := orthogonal_joint_residual (intrinsicGamma c u) (scoreCLM c u)
    (jointCLM c u (tangentFrame u hu))
    (center_intrinsicGamma_surjective (by omega) μ hQ u hu)
    (center_score_surjective (by omega) μ hQ hnp u hu)
    (center_joint_surjective (by omega) μ hQ hnp u hu _
      (tangentFrame_orthonormal u hu) (tangentFrame_tangent u hu))
    (orthogonal_observation_symm _ _ (score_intrinsic_adjoint_zero c hc u))
    (jointCLM_ker_intrinsic_score c u hu)
  funext g
  simp only [mixedPosterior, smul_zero, map_zero, add_zero,
    gradientResidual_eq n μ hQ u hu, scoreResidual_eq n μ hQ.le u hu]
  exact congrArg (fun L => L g) h.symm

private lemma valuePosterior_zero_eq_residual (n : ℕ) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 < Q) (u : Vector (n+1)) (hu : ‖u‖^2 = (n+1 : ℕ)) :
    valuePosterior n μ Q u 0 =
      residual (valueTangentCLM (centerCoefficients (mixtureCoefficients μ) Q) u
        (tangentFrame u hu)) := by
  let c := centerCoefficients (mixtureCoefficients μ) Q
  have hc := centerCoefficients_nonnegative _ (mixtureCoefficients_nonnegative μ) hQ.le
  have h := orthogonal_joint_residual (intrinsicGamma c u) (valueCLM c u)
    (valueTangentCLM c u (tangentFrame u hu))
    (center_intrinsicGamma_surjective (by omega) μ hQ u hu)
    (center_value_surjective μ hQ u hu)
    (center_valueTangent_surjective (by omega) μ hQ u hu _
      (tangentFrame_orthonormal u hu) (tangentFrame_tangent u hu))
    (orthogonal_observation_symm _ _ (value_intrinsic_adjoint_zero c hc u))
    (valueTangentCLM_ker_intrinsic_value c u hu)
  funext g
  simp only [valuePosterior, mul_zero, map_zero, add_zero,
    gradientResidual_eq n μ hQ u hu, valueResidual_eq n μ hQ.le u hu]
  exact congrArg (fun L => L g) h.symm

/-- Independence concerns the unique polynomial coefficients, and holds
against the full actual joint observation under the original tensor law. -/
private theorem mixed_deleted_coefficients_independent (n : ℕ) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 < Q) (hnp : μ.minDegree < μ.maxDegree)
    (u : Vector (n+1)) (hu : ‖u‖^2 = (n+1 : ℕ)) :
    (μ.scoreCovariance Q).det > 0 ∧
    IndepFun (fun J : Disorder (n+1) μ.maxDegree =>
      fun d => (mixedDeletedPolynomial n μ Q u J).coeff d)
      (actualObservation (jointCLM (centerCoefficients (mixtureCoefficients μ) Q) u
        (tangentFrame u hu))) (disorderLaw (n+1) μ.maxDegree) := by
  refine ⟨μ.scoreCovariance_det_pos hQ hnp, ?_⟩
  let A := jointCLM (centerCoefficients (mixtureCoefficients μ) Q) u (tangentFrame u hu)
  have hA := center_joint_surjective (by omega) μ hQ hnp u hu _
    (tangentFrame_orthonormal u hu) (tangentFrame_tangent u hu)
  have h := (residual_observation_independent A hA).comp
    ((polynomialCoefficients_measurable (mixtureCoefficients μ)).comp
      (unpackCLM (n+1) μ.maxDegree).continuous.measurable) measurable_id
  have he := mixedPosterior_zero_eq_residual n μ hQ hnp u hu
  have hLaw := actual_flattened_gaussian (n+1) μ.maxDegree
  have hf := (hasLaw_map (P := stdGaussian (EuclideanDisorder (n+1) μ.maxDegree)) (((polynomialCoefficients_measurable (mixtureCoefficients μ)).comp
    (unpackCLM (n+1) μ.maxDegree).continuous.measurable).comp
      (residual A).continuous.measurable).aemeasurable)
  have hg := hasLaw_map (P := stdGaussian (EuclideanDisorder (n+1) μ.maxDegree)) A.continuous.measurable.aemeasurable
  have h' := (indepFun_iff_hasLaw_prodMk_prod
    (hf.fun_comp hLaw) (hg.fun_comp hLaw)).mpr
      ((h.hasLaw_prod hf hg).fun_comp hLaw)
  change IndepFun (fun J => polynomialCoefficients (mixtureCoefficients μ)
    (unpackDisorder (mixedPosterior n μ Q u 0 (euclideanDisorder J))))
    (fun J => A (euclideanDisorder J)) (disorderLaw (n+1) μ.maxDegree)
  rw [he]
  exact h'

/-- Proper scalar-value regression, including pure mixtures, requires no
singular two-dimensional score inverse. -/
private theorem value_deleted_coefficients_independent (n : ℕ) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 < Q) (u : Vector (n+1)) (hu : ‖u‖^2 = (n+1 : ℕ)) :
    IndepFun (fun J : Disorder (n+1) μ.maxDegree =>
      fun d => (valueDeletedPolynomial n μ Q u J).coeff d)
      (actualObservation (valueTangentCLM (centerCoefficients (mixtureCoefficients μ) Q) u
        (tangentFrame u hu))) (disorderLaw (n+1) μ.maxDegree) := by
  let A := valueTangentCLM (centerCoefficients (mixtureCoefficients μ) Q) u (tangentFrame u hu)
  have hA := center_valueTangent_surjective (by omega) μ hQ u hu _
    (tangentFrame_orthonormal u hu) (tangentFrame_tangent u hu)
  have h := (residual_observation_independent A hA).comp
    ((polynomialCoefficients_measurable (mixtureCoefficients μ)).comp
      (unpackCLM (n+1) μ.maxDegree).continuous.measurable) measurable_id
  have he := valuePosterior_zero_eq_residual n μ hQ u hu
  have hLaw := actual_flattened_gaussian (n+1) μ.maxDegree
  have hf := (hasLaw_map (P := stdGaussian (EuclideanDisorder (n+1) μ.maxDegree)) (((polynomialCoefficients_measurable (mixtureCoefficients μ)).comp
    (unpackCLM (n+1) μ.maxDegree).continuous.measurable).comp
      (residual A).continuous.measurable).aemeasurable)
  have hg := hasLaw_map (P := stdGaussian (EuclideanDisorder (n+1) μ.maxDegree)) A.continuous.measurable.aemeasurable
  have h' := (indepFun_iff_hasLaw_prodMk_prod
    (hf.fun_comp hLaw) (hg.fun_comp hLaw)).mpr
      ((h.hasLaw_prod hf hg).fun_comp hLaw)
  change IndepFun (fun J => polynomialCoefficients (mixtureCoefficients μ)
    (unpackDisorder (valuePosterior n μ Q u 0 (euclideanDisorder J))))
    (fun J => A (euclideanDisorder J)) (disorderLaw (n+1) μ.maxDegree)
  rw [he]
  exact h'

private lemma observable_scale {N P : ℕ} (hN : 0 < N) (c : Degree P → ℝ)
    (J : Disorder N P) (x u : Vector N) :
    Real.sqrt (N : ℝ) * |EntranceLatitudeTangentObservable.observable c J x u| =
      |inner ℝ (surfaceGradient (field c J) u) x| := by
  have hs := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hN : (0 : ℝ) < N)
  unfold EntranceLatitudeTangentObservable.observable
  rw [abs_mul, abs_inv, abs_of_pos hs]
  field_simp

/-- The manuscript's actual `(H_Q,K_Q,G_u)` observation, including the
ambient tangent vector rather than coordinates in a chosen frame. -/
def mixedObservation {N : ℕ} (μ : FiniteMixture) (Q : ℝ) (u : Vector N)
    (J : Disorder N μ.maxDegree) : (ℝ × ℝ) × Vector N :=
  let cQ := centerCoefficients (mixtureCoefficients μ) Q
  ((field cQ J u, jet cQ 1 u (fun _ => u) J), surfaceGradient (field cQ J) u)

/-- The nonredundant actual `(H_Q,G_u)` observation. -/
def valueObservationVector {N : ℕ} (μ : FiniteMixture) (Q : ℝ) (u : Vector N)
    (J : Disorder N μ.maxDegree) : ℝ × Vector N :=
  let cQ := centerCoefficients (mixtureCoefficients μ) Q
  (field cQ J u, surfaceGradient (field cQ J) u)

private lemma tangent_frame_reconstruction {n P : ℕ} (cQ : Degree P → ℝ)
    (u : Vector (n+1)) (hu : ‖u‖^2 = (n+1 : ℕ)) (g : EuclideanDisorder (n+1) P) :
    (∑ i, gradientCLM cQ u (tangentFrame u hu) g i • tangentFrame u hu i) =
      surfaceGradient (field cQ (unpackDisorder g)) u := by
  rw [tangentFrame_gradient_eq]
  have h := congrArg (fun v : tangentPlane u => (v : Vector (n+1)))
    ((tangentBasis u hu).sum_repr (intrinsicGamma cQ u g))
  simpa only [Submodule.coe_sum, Submodule.coe_smul, tangentFrame,
    intrinsicGamma_coe (by omega : n+1 ≠ 0) cQ u hu] using h

private theorem mixed_deleted_physical_observation_independent (n : ℕ) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 < Q) (hnp : μ.minDegree < μ.maxDegree)
    (u : Vector (n+1)) (hu : ‖u‖^2 = (n+1 : ℕ)) :
    IndepFun (fun J : Disorder (n+1) μ.maxDegree =>
      fun d => (mixedDeletedPolynomial n μ Q u J).coeff d)
      (mixedObservation μ Q u) (disorderLaw (n+1) μ.maxDegree) := by
  let f := fun w : EuclideanSpace ℝ (Fin 2 ⊕ Fin n) =>
    ((w (Sum.inl 0),w (Sum.inl 1)),∑ i, w (Sum.inr i) • tangentFrame u hu i)
  have hf : Measurable f := by dsimp [f]; fun_prop
  have h := (mixed_deleted_coefficients_independent n μ hQ hnp u hu).2.comp measurable_id hf
  have he : f ∘ actualObservation (jointCLM (centerCoefficients (mixtureCoefficients μ) Q) u
      (tangentFrame u hu)) = mixedObservation μ Q u := by
    funext J
    simp only [f, actualObservation, Function.comp_apply, jointCLM_apply_inl, jointCLM_apply_inr,
      scoreCLM_apply_zero, scoreCLM_apply_one, unpack_euclideanDisorder, jet,
      iteratedFDeriv_zero_apply, mixedObservation]
    congr 1
    simpa only [unpack_euclideanDisorder] using tangent_frame_reconstruction
      (centerCoefficients (mixtureCoefficients μ) Q) u hu (euclideanDisorder J)
  rw [he] at h
  exact h

private theorem value_deleted_physical_observation_independent (n : ℕ) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 < Q) (u : Vector (n+1)) (hu : ‖u‖^2 = (n+1 : ℕ)) :
    IndepFun (fun J : Disorder (n+1) μ.maxDegree =>
      fun d => (valueDeletedPolynomial n μ Q u J).coeff d)
      (valueObservationVector μ Q u) (disorderLaw (n+1) μ.maxDegree) := by
  let f := fun w : EuclideanSpace ℝ (Fin 1 ⊕ Fin n) =>
    (w (Sum.inl 0),∑ i, w (Sum.inr i) • tangentFrame u hu i)
  have hf : Measurable f := by dsimp [f]; fun_prop
  have h := (value_deleted_coefficients_independent n μ hQ u hu).comp measurable_id hf
  have he : f ∘ actualObservation (valueTangentCLM (centerCoefficients (mixtureCoefficients μ) Q) u
      (tangentFrame u hu)) = valueObservationVector μ Q u := by
    funext J
    simp only [f, actualObservation, Function.comp_apply, valueTangentCLM_apply_value,
      valueTangentCLM_apply_gradient, unpack_euclideanDisorder,
      jet, iteratedFDeriv_zero_apply, valueObservationVector]
    congr 1
    have hr := tangent_frame_reconstruction
      (centerCoefficients (mixtureCoefficients μ) Q) u hu (euclideanDisorder J)
    simpa only [gradientCLM_apply, unpack_euclideanDisorder, jet] using hr
  rw [he] at h
  exact h

private lemma mark_difference_bound {N : ℕ} {B K e H : ℝ}
    (he : |e| ≤ B) (hH : |H| ≤ K*(N : ℝ)) :
    |(N : ℝ)*e-H| ≤ (B+K)*(N : ℝ) := by
  calc
    _ ≤ |(N : ℝ)*e|+|H| := abs_sub _ _
    _ ≤ (N : ℝ)*B+K*(N : ℝ) := by
      rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg N)]
      exact add_le_add (mul_le_mul_of_nonneg_left he (Nat.cast_nonneg N)) hH
    _ = _ := by ring

/-- The printed correction bounds follow solely from the three center
observation bounds in `eq:ent-regularity`. Thus they hold on the manuscript's
event whenever its defining regularity clauses hold, independently of how
that event or its harmonic sectors are constructed. -/
theorem regression_correction_bounds_of_center_bounds (μ : FiniteMixture) (Q : ℝ)
    {B K : ℝ} (hB : 0 ≤ B) (hK : 0 ≤ K) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (u G x : Vector (n+1)) (Hq Kq e k : ℝ),
      ‖u‖^2 = (n+1 : ℕ) → ‖x‖^2 = (n+1 : ℕ) →
      |Hq| ≤ K*((n+1 : ℕ) : ℝ) → |Kq| ≤ K*((n+1 : ℕ) : ℝ) →
      ‖G‖ ≤ K*Real.sqrt ((n+1 : ℕ) : ℝ) → |e| ≤ B → |k| ≤ B →
      let δ := regressionCorrection μ Q u G Hq Kq e k
      |δ x| ≤ C*((n+1 : ℕ) : ℝ)*|overlap x u|^μ.minDegree +
        C*|overlap x u|^(μ.minDegree-1)*|inner ℝ G x| ∧
      ‖surfaceGradient δ x‖ ≤ C*Real.sqrt ((n+1 : ℕ) : ℝ) := by
  let R := regressionOrderConstant μ Q
  let A := PhysicalHitting.thetaConstant μ Q
  let L := A*(2*B+4*K)
  let C := R*(1+B+K)+L+1
  have hR : 0 ≤ R := (regressionOrderConstant_pos μ Q).le
  have hA : 0 ≤ A := (PhysicalHitting.thetaConstant_pos μ Q).le
  have hL : 0 ≤ L := mul_nonneg hA (by positivity)
  have hRB : 0 ≤ R*B := mul_nonneg hR hB
  have hRK : 0 ≤ R*K := mul_nonneg hR hK
  have hCR : R ≤ C := by dsimp [C]; nlinarith
  have hCR' : R*(B+K) ≤ C := by dsimp [C]; nlinarith
  have hCL : L ≤ C := by dsimp [C]; nlinarith
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro n u G x Hq Kq e k hu hx hH hKq hG he hk
  have hN : (0 : ℝ) < (n+1 : ℕ) := by positivity
  have hun := LandscapeDerivatives.sphere_norm u hu
  have hxn := LandscapeDerivatives.sphere_norm x hx
  have hr : |overlap x u| ≤ 1 := abs_le.mpr
    (overlap_mem_Icc_of_norm_sq (by omega : 1 ≤ n+1) x u hx hu)
  have hE := mark_difference_bound he hH
  have hK' := mark_difference_bound hk hKq
  have hinner : |inner ℝ G x| ≤ K*((n+1 : ℕ) : ℝ) := by
    calc
      _ ≤ ‖G‖*‖x‖ := abs_real_inner_le_norm _ _
      _ ≤ (K*Real.sqrt ((n+1 : ℕ) : ℝ))*Real.sqrt ((n+1 : ℕ) : ℝ) := by
        rw [hxn]; exact mul_le_mul_of_nonneg_right hG (Real.sqrt_nonneg _)
      _ = _ := by rw [mul_assoc, Real.mul_self_sqrt hN.le]
  obtain ⟨hv,ht,_⟩ := mixed_regression_orders μ Q hr
  have htan : |tangentTheta μ Q (overlap x u)| ≤ R*|overlap x u|^(μ.minDegree-1) := by
    linarith [abs_nonneg (valueThetaDerivative μ Q (overlap x u)),
      abs_nonneg (radialThetaDerivative μ Q (overlap x u))]
  have hval : |regressionCorrection μ Q u G Hq Kq e k x| ≤
      R*(B+K)*((n+1 : ℕ) : ℝ)*|overlap x u|^μ.minDegree +
        R*|overlap x u|^(μ.minDegree-1)*|inner ℝ G x| := by
    unfold regressionCorrection
    calc
      _ ≤ |valueTheta μ Q (overlap x u)*(((n+1 : ℕ) : ℝ)*e-Hq)|+
          |radialTheta μ Q (overlap x u)*(((n+1 : ℕ) : ℝ)*k-Kq)|+
          |tangentTheta μ Q (overlap x u)*inner ℝ G x| :=
        (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ (|valueTheta μ Q (overlap x u)|+|radialTheta μ Q (overlap x u)|)*
          ((B+K)*((n+1 : ℕ) : ℝ))+
          (R*|overlap x u|^(μ.minDegree-1))*|inner ℝ G x| := by
        simp only [abs_mul]
        have h1 := mul_le_mul_of_nonneg_left hE (abs_nonneg (valueTheta μ Q (overlap x u)))
        have h2 := mul_le_mul_of_nonneg_left hK' (abs_nonneg (radialTheta μ Q (overlap x u)))
        have h3 := mul_le_mul_of_nonneg_right htan (abs_nonneg (inner ℝ G x))
        nlinarith [h1,h2,h3]
      _ ≤ _ := by
        have hh := mul_le_mul_of_nonneg_right hv (by positivity : 0 ≤ (B+K)*((n+1 : ℕ) : ℝ))
        nlinarith [hh]
  obtain ⟨_,_,h3,h4,h5,h6⟩ := PhysicalHitting.thetaConstant_bounds μ Q (overlap x u) hr
  have hrad : |correctionRadialCoefficient μ Q u G Hq Kq e k x| ≤
      A*(2*B+3*K)*((n+1 : ℕ) : ℝ) := by
    have hh := PhysicalHitting.scalar_regression_bound h4 h5 h6
      (X := ((n+1 : ℕ) : ℝ)*e-Hq) (Y := ((n+1 : ℕ) : ℝ)*k-Kq) (Z := inner ℝ G x)
    have hm : |((n+1 : ℕ) : ℝ)*e-Hq|+|((n+1 : ℕ) : ℝ)*k-Kq|+|inner ℝ G x| ≤
        (2*B+3*K)*((n+1 : ℕ) : ℝ) := by nlinarith [hE,hK',hinner]
    exact hh.trans ((mul_le_mul_of_nonneg_left hm hA).trans_eq (by ring))
  have hdiv : |correctionRadialCoefficient μ Q u G Hq Kq e k x/((n+1 : ℕ) : ℝ)| ≤
      A*(2*B+3*K) := by
    rw [abs_div, abs_of_pos hN]
    exact (div_le_iff₀ hN).mpr hrad
  have hg : ‖gradient (regressionCorrection μ Q u G Hq Kq e k) x‖ ≤
      L*Real.sqrt ((n+1 : ℕ) : ℝ) := by
    rw [(regressionCorrection_hasGradientAt μ Q u G Hq Kq e k x).gradient]
    calc
      _ ≤ ‖(correctionRadialCoefficient μ Q u G Hq Kq e k x/((n+1 : ℕ) : ℝ)) • u‖+
          ‖tangentTheta μ Q (overlap x u) • G‖ := norm_sub_le _ _
      _ ≤ (A*(2*B+3*K))*Real.sqrt ((n+1 : ℕ) : ℝ)+A*(K*Real.sqrt ((n+1 : ℕ) : ℝ)) := by
        simp only [norm_smul, Real.norm_eq_abs, hun]
        exact add_le_add (mul_le_mul_of_nonneg_right hdiv (Real.sqrt_nonneg _))
          (mul_le_mul h3 hG (norm_nonneg _) hA)
      _ = _ := by dsimp [L]; ring
  constructor
  · exact hval.trans (add_le_add
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCR' hN.le) (by positivity))
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCR (by positivity)) (abs_nonneg _)))
  · have hh := (projection_norm_le_onSphere (by omega : n+1 ≠ 0) x
      (gradient (regressionCorrection μ Q u G Hq Kq e k) x)
      ((onSphere_iff_norm_sq x).mpr hx)).trans
        (hg.trans (mul_le_mul_of_nonneg_right hCL (Real.sqrt_nonneg _)))
    simpa only [surfaceGradient, tangentProjection_apply] using hh

/-- Proper-pure correction bounds from exactly the center observations
controlled by the manuscript regularity event, without a score inverse. -/
theorem pure_correction_bounds_of_center_bounds (p : ℕ) (Q : ℝ)
    {B K : ℝ} (hB : 0 ≤ B) (hK : 0 ≤ K) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (u G x : Vector (n+1)) (Hq e : ℝ),
      ‖u‖^2 = (n+1 : ℕ) → ‖x‖^2 = (n+1 : ℕ) →
      |Hq| ≤ K*((n+1 : ℕ) : ℝ) →
      ‖G‖ ≤ K*Real.sqrt ((n+1 : ℕ) : ℝ) → |e| ≤ B →
      let δ := pureRegressionCorrection p Q u G Hq e
      |δ x| ≤ C*((n+1 : ℕ) : ℝ)*|overlap x u|^p +
        C*|overlap x u|^(p-1)*|inner ℝ G x| ∧
      ‖surfaceGradient δ x‖ ≤ C*Real.sqrt ((n+1 : ℕ) : ℝ) := by
  let R := pureOrderConstant Q p
  let L := R*(B+3*K)
  let C := R*(1+B+3*K)+1
  have hR : 0 ≤ R := (pureOrderConstant_pos Q p).le
  have hRB : 0 ≤ R*B := mul_nonneg hR hB
  have hRK : 0 ≤ R*K := mul_nonneg hR hK
  have hCR : R ≤ C := by dsimp [C]; nlinarith
  have hCR' : R*(B+K) ≤ C := by dsimp [C]; nlinarith
  have hCL : L ≤ C := by dsimp [C,L]; nlinarith
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro n u G x Hq e hu hx hH hG he
  have hE := mark_difference_bound he hH
  obtain ⟨h1,h2,_⟩ := pure_regression_orders Q p (overlap x u)
  have h2' : |pureTangentTheta Q p (overlap x u)| ≤ R*|overlap x u|^(p-1) := by
    linarith [abs_nonneg (purePrefactor Q p*(p : ℝ)*overlap x u^(p-1))]
  have hval : |pureRegressionCorrection p Q u G Hq e x| ≤
      R*(B+K)*((n+1 : ℕ) : ℝ)*|overlap x u|^p +
        R*|overlap x u|^(p-1)*|inner ℝ G x| := by
    have heq : pureRegressionCorrection p Q u G Hq e x =
        pureValueTheta Q p (overlap x u)*(((n+1 : ℕ) : ℝ)*e-Hq)-
          pureTangentTheta Q p (overlap x u)*inner ℝ G x := by
      unfold pureRegressionCorrection pureValueTheta pureTangentTheta purePrefactor; ring
    rw [heq]
    calc
      _ ≤ |pureValueTheta Q p (overlap x u)*(((n+1 : ℕ) : ℝ)*e-Hq)|+
          |pureTangentTheta Q p (overlap x u)*inner ℝ G x| := abs_sub _ _
      _ ≤ (R*|overlap x u|^p)*((B+K)*((n+1 : ℕ) : ℝ))+
          (R*|overlap x u|^(p-1))*|inner ℝ G x| := by
        simp only [abs_mul]
        exact add_le_add (mul_le_mul h1 hE (abs_nonneg _) (by positivity))
          (mul_le_mul_of_nonneg_right h2' (abs_nonneg _))
      _ = _ := by ring
  have hg := (pure_regression_value_gradient_bounds (by omega : 1 ≤ n+1) p Q u G x
    ((onSphere_iff_norm_sq u).mpr hu) ((onSphere_iff_norm_sq x).mpr hx)
    Hq e B K hB hK he hH hG).2
  constructor
  · exact hval.trans (add_le_add
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCR' (Nat.cast_nonneg _)) (by positivity))
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCR (by positivity)) (abs_nonneg _)))
  · have hh := (projection_norm_le_onSphere (by omega : n+1 ≠ 0) x
      (gradient (pureRegressionCorrection p Q u G Hq e) x)
      ((onSphere_iff_norm_sq x).mpr hx)).trans
        (hg.trans (mul_le_mul_of_nonneg_right hCL (Real.sqrt_nonneg _)))
    simpa only [surfaceGradient, tangentProjection_apply] using hh

/-- The two printed correction bounds with one constant chosen before
dimension, axis, regular seed, and bounded marks. The gradient is intrinsic. -/
theorem mixed_correction_bounds (μ : FiniteMixture)
    (hnp : μ.minDegree < μ.maxDegree) {Q B : ℝ}
    (hQ : 0 < Q) (hQ1 : Q ≤ 1) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (J : Disorder (n+1) μ.maxDegree),
      J ∈ regularDisorder → ∀ (u x : Vector (n+1)),
      ‖u‖^2 = (n+1 : ℕ) → ‖x‖^2 = (n+1 : ℕ) →
      ∀ e k : ℝ, |e| ≤ B → |k| ≤ B →
      let G := surfaceGradient (field (centerCoefficients (mixtureCoefficients μ) Q) J) u
      let δ := sourceRegressionCorrection μ Q hQ hnp J u e k
      |δ x| ≤ C*((n+1 : ℕ) : ℝ)*|overlap x u|^μ.minDegree +
        C*|overlap x u|^(μ.minDegree-1)*|inner ℝ G x| ∧
      ‖surfaceGradient δ x‖ ≤ C*Real.sqrt ((n+1 : ℕ) : ℝ) := by
  let A := EntranceLatitudeTangentObservable.sourceLatitudeCorrectionConstant μ Q B
  let K := PhysicalHitting.centerConstant μ Q
  let L := PhysicalHitting.thetaConstant μ Q * (2*B+4*K)
  let C := A+L+1
  have hA : 0 ≤ A := by
    dsimp [A, EntranceLatitudeTangentObservable.sourceLatitudeCorrectionConstant]
    have := (regressionOrderConstant_pos μ Q).le
    have := (derivativeConstant_pos (centerCoefficients (mixtureCoefficients μ) Q)).le
    positivity
  have hK : 0 ≤ K := (PhysicalHitting.centerConstant_pos μ Q).le
  have hL : 0 ≤ L := mul_nonneg (PhysicalHitting.thetaConstant_pos μ Q).le (by positivity)
  refine ⟨C, by dsimp [C]; linarith, ?_⟩
  intro n J hJ u x hu hx e k he hk
  dsimp only
  have hv := EntranceLatitudeTangentObservable.actual_sourceRegressionCorrection_abs_le_observable
    μ hQ hnp hB J hJ u x hu hx he hk
  have hs := observable_scale (by omega : 0 < n+1)
    (centerCoefficients (mixtureCoefficients μ) Q) J x u
  have hv' : |sourceRegressionCorrection μ Q hQ hnp J u e k x| ≤
      A*(((n+1 : ℕ) : ℝ)*|overlap x u|^μ.minDegree +
        |overlap x u|^(μ.minDegree-1)*
          |inner ℝ (surfaceGradient (field (centerCoefficients (mixtureCoefficients μ) Q) J) u) x|) := by
    have heq : Real.sqrt ((n+1 : ℕ) : ℝ)*|overlap x u|^(μ.minDegree-1)*
        |EntranceLatitudeTangentObservable.observable (centerCoefficients (mixtureCoefficients μ) Q) J x u| =
        |overlap x u|^(μ.minDegree-1)*
          |inner ℝ (surfaceGradient (field (centerCoefficients (mixtureCoefficients μ) Q) J) u) x| := by
      rw [mul_comm (Real.sqrt ((n+1 : ℕ) : ℝ)), mul_assoc, hs]
    simpa only [heq] using hv
  let D : SmoothKilled.SourceData (n+1) :=
    { dimension_ge_one := by omega
      mixture := μ, nonpure := hnp, Q := Q, Q_pos := hQ, Q_le_one := hQ1
      disorder := J, axis := u, axis_onSphere := (onSphere_iff_norm_sq u).mpr hu
      energyMark := e, radialMark := k, cutoffScale := 1
      cutoffScale_pos := by norm_num
      cutoff := fun _ => 1, cutoff_smooth := contDiff_const }
  have hg := (PhysicalHitting.regular_source_regression_bounds D hJ x
    ((onSphere_iff_norm_sq x).mpr hx)).2
  have hmark : PhysicalHitting.markConstant μ Q e k + K ≤ 2*B+4*K := by
    dsimp [PhysicalHitting.markConstant, K]
    linarith
  have hg' : ‖gradient (sourceRegressionCorrection μ Q hQ hnp J u e k) x‖ ≤
      L*Real.sqrt ((n+1 : ℕ) : ℝ) := by
    exact hg.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hmark (PhysicalHitting.thetaConstant_pos μ Q).le)
        (Real.sqrt_nonneg _))
  constructor
  · have hAC : A ≤ C := by dsimp [C]; linarith
    exact hv'.trans ((mul_le_mul_of_nonneg_right hAC (by positivity)).trans_eq (by ring))
  · have hp := projection_norm_le_onSphere (by omega : n+1 ≠ 0) x
      (gradient (sourceRegressionCorrection μ Q hQ hnp J u e k) x)
      ((onSphere_iff_norm_sq x).mpr hx)
    have hb := hp.trans (hg'.trans (mul_le_mul_of_nonneg_right
      (by dsimp [C]; linarith : L ≤ C) (Real.sqrt_nonneg _)))
    simpa only [surfaceGradient, tangentProjection_apply] using hb

/-- The literal whole continuous-field posterior law, together with the
canonical coefficient independence and all three equatorial orders. -/
theorem mixed_whole_field_regression (n : ℕ) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 < Q) (hnp : μ.minDegree < μ.maxDegree)
    (u : Vector (n+1)) (hu : ‖u‖^2 = (n+1 : ℕ))
    {K : Type*} [TopologicalSpace K] [CompactSpace K] [SecondCountableTopology K]
    [T2Space K] [Nonempty K] (z : K → Vector (n+1)) (hz : Continuous z) (e k : ℝ) :
    (μ.scoreCovariance Q).det > 0 ∧
    IndepFun (fun J : Disorder (n+1) μ.maxDegree =>
      fun d => (mixedDeletedPolynomial n μ Q u J).coeff d)
      (mixedObservation μ Q u) (disorderLaw (n+1) μ.maxDegree) ∧
    (mixedConditionedLaw (centerCoefficients (mixtureCoefficients μ) Q) u hu
      (scorePairEquiv (e,k))).map
      (fun J => modelContinuousField (mixtureCoefficients μ) z hz (euclideanDisorder J)) =
        (disorderLaw (n+1) μ.maxDegree).map
          (originalMixedSourceContinuousField n μ hQ hnp u e k z hz) ∧
    ∀ r : ℝ, |r| ≤ 1 →
      |valueTheta μ Q r|+|radialTheta μ Q r| ≤ regressionOrderConstant μ Q*|r|^μ.minDegree ∧
      |valueThetaDerivative μ Q r|+|radialThetaDerivative μ Q r|+|tangentTheta μ Q r| ≤
        regressionOrderConstant μ Q*|r|^(μ.minDegree-1) ∧
      |tangentThetaDerivative μ Q r| ≤ regressionOrderConstant μ Q*|r|^(μ.minDegree-2) := by
  have h := mixed_deleted_coefficients_independent n μ hQ hnp u hu
  exact ⟨h.1,mixed_deleted_physical_observation_independent n μ hQ hnp u hu,
    actual_mixed_conditioned_original_source_continuous_law n μ hQ hnp u hu e k z hz,
    fun _ hr => mixed_regression_orders μ Q hr⟩

/-- Proper-pure counterpart of the printed correction bounds, with a
single constant uniform in the dimension, axes, and bounded value mark. -/
theorem pure_correction_bounds (p : ℕ) (hp : 2 ≤ p) (c : ℝ) (hc : 0 < c)
    {Q B : ℝ} (hQ : 0 < Q) (hB : 0 ≤ B) :
    let μ := FiniteMixture.pure p hp c hc
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (J : Disorder (n+1) μ.maxDegree),
      J ∈ regularDisorder → ∀ (u x : Vector (n+1)),
      ‖u‖^2 = (n+1 : ℕ) → ‖x‖^2 = (n+1 : ℕ) →
      ∀ e : ℝ, |e| ≤ B →
      let G := surfaceGradient (field (centerCoefficients (mixtureCoefficients μ) Q) J) u
      let δ := pureSourceRegressionCorrection p hp c hc Q J u e
      |δ x| ≤ C*((n+1 : ℕ) : ℝ)*|overlap x u|^p +
        C*|overlap x u|^(p-1)*|inner ℝ G x| ∧
      ‖surfaceGradient δ x‖ ≤ C*Real.sqrt ((n+1 : ℕ) : ℝ) := by
  let μ := FiniteMixture.pure p hp c hc
  let cQ := centerCoefficients (mixtureCoefficients μ) Q
  let A := EntranceLatitudeTangentObservable.sourceLatitudeCorrectionConstant μ Q B
  let K := derivativeConstant cQ
  let L := pureOrderConstant Q p*(B+3*K)
  let C := A+L+1
  have hA : 0 ≤ A := by
    dsimp [A, EntranceLatitudeTangentObservable.sourceLatitudeCorrectionConstant]
    have := (regressionOrderConstant_pos μ Q).le
    have := (derivativeConstant_pos cQ).le
    positivity
  have hK : 0 ≤ K := (derivativeConstant_pos cQ).le
  have hL : 0 ≤ L := mul_nonneg (pureOrderConstant_pos Q p).le (by positivity)
  refine ⟨C, by dsimp [C]; linarith, ?_⟩
  intro n J hJ u x hu hx e he
  have hv := EntranceLatitudeTangentObservable.actual_pureSourceRegressionCorrection_abs_le_observable
    p hp c hc hQ hB J hJ u x hu hx he
  dsimp only at hv
  rw [(CSPureModels.pure_degrees p hp c hc).1] at hv
  have hs := observable_scale (by omega : 0 < n+1) cQ J x u
  have heq : Real.sqrt ((n+1 : ℕ) : ℝ)*|overlap x u|^(p-1)*
      |EntranceLatitudeTangentObservable.observable cQ J x u| =
      |overlap x u|^(p-1)*|inner ℝ (surfaceGradient (field cQ J) u) x| := by
    rw [mul_comm (Real.sqrt ((n+1 : ℕ) : ℝ)), mul_assoc, hs]
  have hv' : |pureSourceRegressionCorrection p hp c hc Q J u e x| ≤
      A*(((n+1 : ℕ) : ℝ)*|overlap x u|^p +
        |overlap x u|^(p-1)*|inner ℝ (surfaceGradient (field cQ J) u) x|) := by
    dsimp only [cQ, μ] at heq
    simpa only [A, μ, cQ, heq] using hv
  have hobs := field_regularDisorder_ball_bounds (by omega : 1 ≤ n+1) cQ J hJ u
    (LandscapeDerivatives.sphere_norm u hu).le
  have hproj := projection_norm_le_onSphere (by omega : n+1 ≠ 0) u
    (gradient (field cQ J) u) ((onSphere_iff_norm_sq u).mpr hu)
  have hG : ‖surfaceGradient (field cQ J) u‖ ≤ K*Real.sqrt ((n+1 : ℕ) : ℝ) := by
    simpa only [surfaceGradient, tangentProjection_apply] using hproj.trans hobs.2.1
  have hg := (pure_regression_value_gradient_bounds (by omega : 1 ≤ n+1) p Q
    u (surfaceGradient (field cQ J) u) x ((onSphere_iff_norm_sq u).mpr hu)
    ((onSphere_iff_norm_sq x).mpr hx) (field cQ J u) e B K hB hK he hobs.1 hG).2
  constructor
  · exact hv'.trans ((mul_le_mul_of_nonneg_right
      (by dsimp [C]; linarith : A ≤ C) (by positivity)).trans_eq (by ring))
  · have hb := (projection_norm_le_onSphere (by omega : n+1 ≠ 0) x
      (gradient (pureRegressionCorrection p Q u (surfaceGradient (field cQ J) u)
        (field cQ J u) e) x) ((onSphere_iff_norm_sq x).mpr hx)).trans
        (hg.trans (mul_le_mul_of_nonneg_right
          (by dsimp [C]; linarith : L ≤ C) (Real.sqrt_nonneg _)))
    simpa only [pureSourceRegressionCorrection, surfaceGradient, tangentProjection_apply] using hb

/-- Proper-pure whole-field regression with the homogeneous correction;
the independent observation vector contains value and tangent gradient only. -/
theorem pure_whole_field_regression (n p : ℕ) (hp : 2 ≤ p) (c : ℝ) (hc : 0 < c)
    {Q : ℝ} (hQ : 0 < Q) (u : Vector (n+1)) (hu : ‖u‖^2 = (n+1 : ℕ))
    {K : Type*} [TopologicalSpace K] [CompactSpace K] [SecondCountableTopology K]
    [T2Space K] [Nonempty K] (z : K → Vector (n+1)) (hz : Continuous z) (e : ℝ) :
    let μ := FiniteMixture.pure p hp c hc
    IndepFun (fun J : Disorder (n+1) μ.maxDegree =>
      fun d => (valueDeletedPolynomial n μ Q u J).coeff d)
      (valueObservationVector μ Q u) (disorderLaw (n+1) μ.maxDegree) ∧
    (valueConditionedLaw (centerCoefficients (mixtureCoefficients μ) Q) u hu e).map
      (fun J => modelContinuousField (mixtureCoefficients μ) z hz (euclideanDisorder J)) =
        (disorderLaw (n+1) μ.maxDegree).map
          (originalPureSourceContinuousField n p hp c hc Q u e z hz) ∧
    (∀ (J : Disorder (n+1) μ.maxDegree) (x : Vector (n+1)),
      let cQ := centerCoefficients (mixtureCoefficients μ) Q
      jet cQ 1 x (fun _ => x) J = (p : ℝ)*field cQ J x) ∧
    ∀ r : ℝ,
      |pureValueTheta Q p r| ≤ pureOrderConstant Q p*|r|^p ∧
      |purePrefactor Q p*(p : ℝ)*r^(p-1)|+|pureTangentTheta Q p r| ≤
        pureOrderConstant Q p*|r|^(p-1) ∧
      |purePrefactor Q p*((p-1 : ℕ) : ℝ)*r^(p-2)| ≤
        pureOrderConstant Q p*|r|^(p-2) := by
  refine ⟨value_deleted_physical_observation_independent n _ hQ u hu,
    actual_pure_conditioned_original_source_continuous_law n p hp c hc hQ u hu e z hz,
    ?_, fun r => pure_regression_orders Q p r⟩
  intro J x
  simpa only [jet, iteratedFDeriv_zero_apply] using
    PureConditionedHessian.pure_radial_jet p hp c hc Q J x

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

/-- A uniform bound on measurable event sections survives an independent
axis average. This also proves the bound at the closed hitting threshold. -/
private lemma independent_axis_event_bound {A Z : Type*} [MeasurableSpace A]
    [MeasurableSpace Z] (σ : Measure A) (P : Measure Z)
    [IsProbabilityMeasure σ] [IsProbabilityMeasure P]
    (E : Set (A × Z)) (hE : MeasurableSet E) {q : ℝ} (hq : 0 ≤ q)
    (hsections : ∀ᵐ u ∂σ, P.real {z | (u,z) ∈ E} ≤ q) :
    (σ.prod P).real E ≤ q := by
  have h : (σ.prod P) E ≤ ENNReal.ofReal q := by
    rw [Measure.prod_apply hE]
    calc
      _ ≤ ∫⁻ _u, ENNReal.ofReal q ∂σ := lintegral_mono_ae (by
        filter_upwards [hsections] with u hu
        have hu' := ENNReal.ofReal_le_ofReal hu
        rw [ofReal_measureReal] at hu'
        exact hu')
      _ = _ := by simp
  simpa only [Measure.real, ENNReal.toReal_ofReal hq] using
    ENNReal.toReal_mono ENNReal.ofReal_ne_top h

abbrev BoundarySeed (n : ℕ) (μ : FiniteMixture) :=
  EuclideanDisorder (n+1) μ.maxDegree ×
    (Vector (n+1) × VectorBrownian.Space (n+1))

/-- Literal unrestricted law: axis, Gaussian tensor seed, uniform initial
state, and Brownian noise are sampled independently. -/
def boundarySeedLaw (n : ℕ) (μ : FiniteMixture) :
    Measure (Vector (n+1) × BoundarySeed n μ) :=
  (sphereLaw (n+1)).prod (posteriorTrajectoryLaw n μ)

def mixedGradientExit (n : ℕ) (μ : FiniteMixture) (Q β e k b : ℝ)
    (S H : ℝ≥0) : Set (Vector (n+1) × BoundarySeed n μ) :=
  {q | ∃ t : ℝ≥0, t ≤ H ∧ b ≤
    |mixedPosteriorOriginalGradientScore n μ Q q.1
      (scorePairEquiv (e,k)) β S t q.2|}

def valueGradientExit (n : ℕ) (μ : FiniteMixture) (Q β e b : ℝ)
    (S H : ℝ≥0) : Set (Vector (n+1) × BoundarySeed n μ) :=
  {q | ∃ t : ℝ≥0, t ≤ H ∧ b ≤
    |valuePosteriorOriginalGradientScore n μ Q q.1 e β S t q.2|}

private lemma joint_original_gradient_measurable (n : ℕ) (μ : FiniteMixture) (Q : ℝ) :
    Measurable (fun q : Vector (n+1) × BoundarySeed n μ =>
      surfaceGradient (field (centerCoefficients (mixtureCoefficients μ) Q)
        (unpackDisorder q.2.1)) q.1) := by
  have he : (fun q : Vector (n+1) × BoundarySeed n μ =>
      surfaceGradient (field (centerCoefficients (mixtureCoefficients μ) Q)
        (unpackDisorder q.2.1)) q.1) =
    fun q => surfaceGamma (centerCoefficients (mixtureCoefficients μ) Q) q.1 q.2.1 := by
    funext q
    simp only [surfaceGamma, ContinuousLinearMap.comp_apply, ambientGradientCLM_apply]
    rfl
  rw [he]
  exact (((surfaceGamma_continuous _).comp continuous_fst).clm_apply
    continuous_snd.fst).measurable

private lemma mixedGradientExit_measurable (n : ℕ) (μ : FiniteMixture) (Q β e k b : ℝ)
    (S H : ℝ≥0) : MeasurableSet (mixedGradientExit n μ Q β e k b S H) := by
  unfold mixedGradientExit
  apply SphericalHorizonHitMeasurable.measurableSet_horizon_hit
    (fun t (q : Vector (n+1) × BoundarySeed n μ) =>
      mixedPosteriorOriginalGradientScore n μ Q q.1 (scorePairEquiv (e,k)) β S t q.2)
  · intro q
    exact mixedPosteriorOriginalGradientScore_continuous n μ Q q.1
      (scorePairEquiv (e,k)) β S q.2
  · intro t
    have hp : Measurable (fun q : Vector (n+1) × BoundarySeed n μ =>
        mixedPosterior n μ Q q.1 (scorePairEquiv (e,k)) q.2.1) := by
      have hinput : Measurable (fun q : Vector (n+1) × BoundarySeed n μ =>
          ((q.1,scorePairEquiv (e,k)),q.2.1)) := by fun_prop
      change Measurable ((fun p : (Vector (n+1) × EuclideanSpace ℝ (Fin 2)) ×
          EuclideanDisorder (n+1) μ.maxDegree =>
            mixedPosterior n μ Q p.1.1 p.1.2 p.2) ∘
          (fun q : Vector (n+1) × BoundarySeed n μ => ((q.1,scorePairEquiv (e,k)),q.2.1)))
      exact (mixedPosterior_continuous n μ Q).measurable.comp hinput
    have hpath : Measurable (fun q : Vector (n+1) × BoundarySeed n μ =>
        mixedPosteriorContinuousPath n μ Q q.1 (scorePairEquiv (e,k)) β S q.2) := by
      have hinput : Measurable (fun q : Vector (n+1) × BoundarySeed n μ =>
          ((unpackDisorder (mixedPosterior n μ Q q.1 (scorePairEquiv (e,k)) q.2.1),q.2.2.1),q.2.2.2)) :=
        by
          have hj : Measurable (fun q : Vector (n+1) × BoundarySeed n μ =>
              unpackDisorder (mixedPosterior n μ Q q.1 (scorePairEquiv (e,k)) q.2.1)) :=
            (unpackCLM (n+1) μ.maxDegree).continuous.measurable.comp hp
          have hx : Measurable (fun q : Vector (n+1) × BoundarySeed n μ => q.2.2.1) :=
            measurable_snd.snd.fst
          have hw : Measurable (fun q : Vector (n+1) × BoundarySeed n μ => q.2.2.2) :=
            measurable_snd.snd.snd
          exact (hj.prodMk hx).prodMk hw
      exact (SphericalRotationCovariance.jointContinuousPath_measurable μ β S).comp hinput
    exact ((joint_original_gradient_measurable n μ Q).inner
      ((ContinuousMap.measurable_eval (clippedPathTime S t)).comp hpath)).div_const _

private lemma valueGradientExit_measurable (n : ℕ) (μ : FiniteMixture) (Q β e b : ℝ)
    (S H : ℝ≥0) : MeasurableSet (valueGradientExit n μ Q β e b S H) := by
  unfold valueGradientExit
  apply SphericalHorizonHitMeasurable.measurableSet_horizon_hit
    (fun t (q : Vector (n+1) × BoundarySeed n μ) =>
      valuePosteriorOriginalGradientScore n μ Q q.1 e β S t q.2)
  · intro q
    unfold valuePosteriorOriginalGradientScore clippedGradientScore gradientScore
    exact ((continuous_const.inner
      ((valuePosteriorContinuousPath n μ Q q.1 e β S q.2).continuous.comp
        (clippedPathTime_continuous S))).div_const _)
  · intro t
    have hp : Measurable (fun q : Vector (n+1) × BoundarySeed n μ =>
        valuePosterior n μ Q q.1 e q.2.1) := by
      have hinput : Measurable (fun q : Vector (n+1) × BoundarySeed n μ =>
          ((q.1,e),q.2.1)) := by fun_prop
      change Measurable ((fun p : (Vector (n+1) × ℝ) ×
          EuclideanDisorder (n+1) μ.maxDegree =>
            valuePosterior n μ Q p.1.1 p.1.2 p.2) ∘
          (fun q : Vector (n+1) × BoundarySeed n μ => ((q.1,e),q.2.1)))
      exact (valuePosterior_continuous n μ Q).measurable.comp hinput
    have hpath : Measurable (fun q : Vector (n+1) × BoundarySeed n μ =>
        valuePosteriorContinuousPath n μ Q q.1 e β S q.2) := by
      have hinput : Measurable (fun q : Vector (n+1) × BoundarySeed n μ =>
          ((unpackDisorder (valuePosterior n μ Q q.1 e q.2.1),q.2.2.1),q.2.2.2)) :=
        by
          have hj : Measurable (fun q : Vector (n+1) × BoundarySeed n μ =>
              unpackDisorder (valuePosterior n μ Q q.1 e q.2.1)) :=
            (unpackCLM (n+1) μ.maxDegree).continuous.measurable.comp hp
          have hx : Measurable (fun q : Vector (n+1) × BoundarySeed n μ => q.2.2.1) :=
            measurable_snd.snd.fst
          have hw : Measurable (fun q : Vector (n+1) × BoundarySeed n μ => q.2.2.2) :=
            measurable_snd.snd.snd
          exact (hj.prodMk hx).prodMk hw
      exact (SphericalRotationCovariance.jointContinuousPath_measurable μ β S).comp hinput
    exact ((joint_original_gradient_measurable n μ Q).inner
      ((ContinuousMap.measurable_eval (clippedPathTime S t)).comp hpath)).div_const _

/-- Unrestricted `lem:ent-boundary`, nonpure branch. All constants precede
the bounded marks. The extra path length only extends the representative;
on the observation horizon the score is exactly G_u dot X_t / N. -/
theorem mixed_uniform_axis_gradient_cutoff_not_reached
    (μ : FiniteMixture) (hnp : μ.minDegree < μ.maxDegree)
    {Q B β b : ℝ} (hQ : 0 < Q) (hQ1 : Q ≤ 1)
    (hB : 0 ≤ B) (hβ : 0 ≤ β) (hb : 0 < b) :
    ∃ (T : ℝ≥0), 0 < T ∧ ∃ γ c : ℝ, 0 < γ ∧ 0 < c ∧
      ∃ n0 : ℕ, ∀ n ≥ n0, ∀ e k : ℝ, |e| ≤ B → |k| ≤ B →
        let H := exponentialGridHorizon γ (n+1)
        (boundarySeedLaw n μ).real
          (mixedGradientExit n μ Q β e k b (H+2*T) H) ≤
            Real.exp (-c*((n+1 : ℕ) : ℝ)) := by
  obtain ⟨T,hT,γ,c,hγ,hc,hall⟩ :=
    source_mixedPosterior_uniform_gradient_cutoff_rate μ hnp hQ hQ1 hB hβ hb
  obtain ⟨n0, hn0⟩ := eventually_atTop.mp hall
  refine ⟨T,hT,γ,c,hγ,hc,n0,?_⟩
  intro n hn e k he hk
  apply independent_axis_event_bound _ _ _
    (mixedGradientExit_measurable _ _ _ _ _ _ _ _ _) (Real.exp_pos _).le
  filter_upwards [sphereLaw_support (by omega : 1 ≤ n+1)] with u hu
  exact hn0 n hn u hu e k he hk

/-- Unrestricted proper-pure boundary estimate. It uses scalar value and
zero-gradient conditioning and therefore includes every admissible k=p h.
In fact the scalar-value estimate holds for every finite mixture. -/
theorem value_uniform_axis_gradient_cutoff_not_reached
    (μ : FiniteMixture) {Q B β b : ℝ} (hQ : 0 < Q)
    (hB : 0 ≤ B) (hβ : 0 ≤ β) (hb : 0 < b) :
    ∃ (T : ℝ≥0), 0 < T ∧ ∃ γ c : ℝ, 0 < γ ∧ 0 < c ∧
      ∃ n0 : ℕ, ∀ n ≥ n0, ∀ e : ℝ, |e| ≤ B →
        let H := exponentialGridHorizon γ (n+1)
        (boundarySeedLaw n μ).real
          (valueGradientExit n μ Q β e b (H+2*T) H) ≤
            Real.exp (-c*((n+1 : ℕ) : ℝ)) := by
  obtain ⟨T,hT,γ,c,hγ,hc,hall⟩ :=
    source_valuePosterior_uniform_gradient_cutoff_rate μ hQ hB hβ hb
  obtain ⟨n0, hn0⟩ := eventually_atTop.mp hall
  refine ⟨T,hT,γ,c,hγ,hc,n0,?_⟩
  intro n hn e he
  apply independent_axis_event_bound _ _ _
    (valueGradientExit_measurable _ _ _ _ _ _ _ _) (Real.exp_pos _).le
  filter_upwards [sphereLaw_support (by omega : 1 ≤ n+1)] with u hu
  exact hn0 n hn u hu e he

end SlowEquilibration.SourceEntranceRegressionBoundary
