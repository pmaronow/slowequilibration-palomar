-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianFiberDensity
public import SlowEquilibration.SphericalConcentration
public import SlowEquilibration.SphericalGaussianJet
public import SlowEquilibration.ScoreCovariance
public import Mathlib.Probability.Kernel.Composition.MapComap

/-!
# Canonical regression of the actual tensor disorder

Flattening is proved to preserve the genuine finite tensor Gaussian law.
The regression kernel retains every disorder coordinate, so its disintegration
applies to arbitrary Borel marks of the whole random field.
-/

@[expose] public section

namespace SlowEquilibration.WholeFieldRegression

open MeasureTheory ProbabilityTheory Set Function
open SlowEquilibration.SphericalModel SlowEquilibration.SphericalGaussianJet
open scoped RealInnerProductSpace ENNReal Topology

noncomputable section

/-- Actual unflattening, as a continuous linear map. -/
def unpackCLM (N P : ℕ) : EuclideanDisorder N P →L[ℝ] Disorder N P :=
  ContinuousLinearMap.pi (fun p => ContinuousLinearMap.pi
    (fun I => EuclideanSpace.proj ⟨p, I⟩))

@[simp] theorem unpackCLM_apply {N P : ℕ} (g : EuclideanDisorder N P) :
    unpackCLM N P g = unpackDisorder g := rfl

/-- The actual coefficient law, rather than a substituted isotropic model. -/
theorem actual_flattened_gaussian (N P : ℕ) :
    HasLaw (euclideanDisorder (N := N) (P := P))
      (stdGaussian (EuclideanDisorder N P)) (disorderLaw N P) := by
  simpa only [SYK.standardGaussianMeasureOnEuclidean, map_pi_eq_stdGaussian] using
    euclideanDisorder_hasLaw N P

/-- Actual derivative of the random field as a linear observation of all coefficients. -/
def flatJetCLM {N P : ℕ} (c : Degree P → ℝ) (n : ℕ) (x : Vector N)
    (a : Fin n → Vector N) : EuclideanDisorder N P →L[ℝ] ℝ :=
  (jetCLM c n x a).comp (unpackCLM N P)

@[simp] theorem flatJetCLM_apply {N P : ℕ} (c : Degree P → ℝ) (n : ℕ)
    (x : Vector N) (a : Fin n → Vector N) (g : EuclideanDisorder N P) :
    flatJetCLM c n x a g = jet c n x a (unpackDisorder g) := by
  simp [flatJetCLM]

/-- The original tensor-coordinate observation associated with an actual
linear observation of the flattened coefficient space. -/
def actualObservation {N P : ℕ} {F : Type*} (A : EuclideanDisorder N P → F)
    (J : Disorder N P) : F := A (euclideanDisorder J)

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]

/-- Canonical whole-field conditional kernel, with the original tensor
coordinates retained at every target observation. -/
def coefficientKernel {N P : ℕ} (A : EuclideanDisorder N P →L[ℝ] F) :
    Kernel F (Disorder N P) :=
  (GaussianRegression.regressionKernel A).map (unpackCLM N P)

@[simp] theorem coefficientKernel_apply {N P : ℕ}
    (A : EuclideanDisorder N P →L[ℝ] F) (w : F) :
    coefficientKernel A w = (GaussianRegression.regressionKernel A w).map
      (unpackCLM N P) := by
  simp [coefficientKernel, Kernel.map_apply, (unpackCLM N P).continuous.measurable]

instance coefficientKernel_markov {N P : ℕ}
    (A : EuclideanDisorder N P →L[ℝ] F) : IsMarkovKernel (coefficientKernel A) := by
  exact Kernel.IsMarkovKernel.map _ (unpackCLM N P).continuous.measurable

/-- Genuine disintegration of all actual disorder coordinates, for arbitrary
nonnegative Borel marks and possibly infinite integrals. -/
theorem actual_disintegration {N P : ℕ} (A : EuclideanDisorder N P →L[ℝ] F)
    (hA : Surjective A) (phi : F × Disorder N P → ℝ≥0∞) (hphi : Measurable phi) :
    (∫⁻ J, phi (actualObservation A J, J) ∂disorderLaw N P) =
      ∫⁻ w, ∫⁻ J, phi (w, J) ∂coefficientKernel A w
        ∂GaussianRegression.observationLaw A := by
  have hm : Measurable (fun g : EuclideanDisorder N P => phi (A g, unpackCLM N P g)) :=
    hphi.comp (A.continuous.measurable.prodMk (unpackCLM N P).continuous.measurable)
  have h := (actual_flattened_gaussian N P).lintegral_comp hm.aemeasurable
  simp only [unpackCLM_apply, unpack_euclideanDisorder] at h
  change (∫⁻ J, phi (A (euclideanDisorder J), J) ∂disorderLaw N P) = _
  rw [h]
  have hp : Measurable (fun p : F × EuclideanDisorder N P => phi (p.1, unpackCLM N P p.2)) :=
    hphi.comp (measurable_fst.prodMk ((unpackCLM N P).continuous.measurable.comp measurable_snd))
  have hr := GaussianRegression.regression_disintegration A hA _ hp
  change (∫⁻ x, phi (A x, unpackCLM N P x) ∂stdGaussian (EuclideanDisorder N P)) = _
  rw [hr]
  apply lintegral_congr
  intro w
  rw [coefficientKernel_apply]
  simpa only [Function.comp_apply] using (lintegral_map
    (f := fun J : Disorder N P => phi (w, J))
    (hphi.comp (measurable_const.prodMk measurable_id))
    (unpackCLM N P).continuous.measurable).symm

/-- The observed actual field has its canonical pointwise Gaussian pdf. -/
theorem actualObservation_has_explicit_density {N P : ℕ}
    (A : EuclideanDisorder N P →L[ℝ] F) (hA : Surjective A) :
    HasLaw (actualObservation A)
      (volume.withDensity (GaussianRegression.observationPdf A)) (disorderLaw N P) := by
  rw [← GaussianRegression.observationLaw_eq_explicit_density A hA]
  refine ⟨?_, ?_⟩
  · exact (A.continuous.measurable.comp ((PiLp.continuousLinearEquiv 2 ℝ
      (fun _ : Coordinate N P => ℝ)).symm.continuous.measurable.comp
      (flatDisorder_measurable N P))).aemeasurable
  · change (disorderLaw N P).map (A ∘ euclideanDisorder) = _
    exact ((hasLaw_map A.continuous.measurable.aemeasurable).fun_comp
      (actual_flattened_gaussian N P)).map_eq

/-- Every target, including zero, gives an actual whole-field law supported
on the specified actual observation fiber. -/
theorem coefficientKernel_observation_ae {N P : ℕ}
    (A : EuclideanDisorder N P →L[ℝ] F) (hA : Surjective A) (w : F) :
    ∀ᵐ J ∂coefficientKernel A w, actualObservation A J = w := by
  rw [coefficientKernel_apply]
  have hm : Measurable (actualObservation A) :=
    A.continuous.measurable.comp ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Coordinate N P => ℝ)).symm.continuous.measurable.comp (flatDisorder_measurable N P))
  apply (ae_map_iff (unpackCLM N P).continuous.measurable.aemeasurable
    ((measurableSet_singleton w).preimage hm)).mpr
  have he : ∀ g : EuclideanDisorder N P, euclideanDisorder (unpackCLM N P g) = g := fun g => rfl
  simpa only [actualObservation, he, Set.mem_singleton_iff] using GaussianRegression.regressionKernel_observation_ae A hA w

/-- A finite actual jet family, interpreted in its genuine Euclidean observation space. -/
def jetFamilyCLM {N P : ℕ} (c : Degree P → ℝ)
    {ι : Type*} [Fintype ι] (n : ι → ℕ) (x : ι → Vector N)
    (a : (i : ι) → Fin (n i) → Vector N) :
    EuclideanDisorder N P →L[ℝ] EuclideanSpace ℝ ι :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i => flatJetCLM c (n i) (x i) (a i)))

@[simp] theorem jetFamilyCLM_apply {N P : ℕ} (c : Degree P → ℝ)
    {ι : Type*} [Fintype ι] (n : ι → ℕ) (x : ι → Vector N)
    (a : (i : ι) → Fin (n i) → Vector N) (g : EuclideanDisorder N P) (i : ι) :
    jetFamilyCLM c n x a g i = jet c (n i) (x i) (a i) (unpackDisorder g) := by
  simp [jetFamilyCLM]

/-- Actual coefficient covariance entries equal the genuine observation Gram entries. -/
theorem actual_covariance_gram {N P : ℕ} {ι : Type*} [Fintype ι]
    (A : EuclideanDisorder N P →L[ℝ] EuclideanSpace ℝ ι) (i j : ι) :
    cov[fun J : Disorder N P => actualObservation A J i,
      fun J : Disorder N P => actualObservation A J j; disorderLaw N P] =
      GaussianRegression.gram A (EuclideanSpace.basisFun ι ℝ j) i := by
  have h := (actual_flattened_gaussian N P).covariance_fun_comp
    (f := fun g => A g i) (g := fun g => A g j)
    (by fun_prop) (by fun_prop)
  change cov[fun J => A (euclideanDisorder J) i,
    fun J => A (euclideanDisorder J) j; disorderLaw N P] = _
  rw [h]
  have he (k : ι) : (fun g : EuclideanDisorder N P => A g k) =
      fun g => inner ℝ (A.adjoint (EuclideanSpace.basisFun ι ℝ k)) g := by
    funext g
    rw [A.adjoint_inner_left, EuclideanSpace.basisFun_inner]
  rw [he i, he j, ← covarianceBilin_apply_eq_cov IsGaussian.memLp_two_id,
    covarianceBilin_stdGaussian, innerSL_apply_apply, A.adjoint_inner_left,
    EuclideanSpace.basisFun_inner]
  rfl

omit [MeasurableSpace F] [BorelSpace F] in
/-- Nonsingular ordinary observation covariance implies actual surjectivity. -/
theorem surjective_of_gram_det_ne_zero {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (A : E →L[ℝ] F) (hd : (GaussianRegression.gram A).det ≠ 0) : Surjective A := by
  let e := (GaussianRegression.gram A).toLinearMap.equivOfIsUnitDet (isUnit_iff_ne_zero.mpr hd)
  intro w
  refine ⟨A.adjoint (e.symm w), ?_⟩
  have he : GaussianRegression.gram A (e.symm w) = w := by
    change (GaussianRegression.gram A).toLinearMap (e.symm w) = w
    rw [← LinearMap.equivOfIsUnitDet_apply]
    exact e.apply_symm_apply w
  exact he

/-- Genuine tangent-gradient observation, including all finite tensor coefficients. -/
def gradientCLM {N P k : ℕ} (c : Degree P → ℝ) (u : Vector N)
    (e : Fin k → Vector N) : EuclideanDisorder N P →L[ℝ] EuclideanSpace ℝ (Fin k) :=
  jetFamilyCLM c (fun _ => 1) (fun _ => u) (fun i _ => e i)

@[simp] theorem gradientCLM_apply {N P k : ℕ} (c : Degree P → ℝ) (u : Vector N)
    (e : Fin k → Vector N) (g : EuclideanDisorder N P) (i : Fin k) :
    gradientCLM c u e g i = jet c 1 u (fun _ => e i) (unpackDisorder g) := by
  simp [gradientCLM]

/-- The gradient covariance operator is derived from the actual field jet covariance. -/
theorem gradient_gram {N P k : ℕ} (hN : 0 < N) (c : Degree P → ℝ)
    (hc : ∀ p, 0 ≤ c p) (u : Vector N) (hu : ‖u‖ ^ 2 = (N : ℝ))
    (e : Fin k → Vector N) (he : Orthonormal ℝ e) (htan : ∀ i, inner ℝ (e i) u = 0) :
    GaussianRegression.gram (gradientCLM c u e) =
      firstCovariance c 1 • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin k)) := by
  apply ContinuousLinearMap.coe_injective
  apply (EuclideanSpace.basisFun (Fin k) ℝ).toBasis.ext
  intro j
  apply PiLp.ext
  intro i
  have h := actual_covariance_gram (gradientCLM c u e) i j
  simp only [actualObservation, gradientCLM_apply, unpack_euclideanDisorder] at h
  rw [tangent_gradient_covariance hN c hc u (e i) (e j) hu (htan i),
    orthonormal_iff_ite.mp he] at h
  change GaussianRegression.gram (gradientCLM c u e) (EuclideanSpace.basisFun (Fin k) ℝ j) i =
    (firstCovariance c 1 • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin k)))
      (EuclideanSpace.basisFun (Fin k) ℝ j) i
  rw [← h]
  simp [EuclideanSpace.basisFun_apply, eq_comm]

/-- Actual positive-variance tangent gradients are surjective observations,
proved from field covariance rather than posited as a conditional-law premise. -/
theorem gradient_surjective {N P k : ℕ} (hN : 0 < N) (c : Degree P → ℝ)
    (hc : ∀ p, 0 ≤ c p) (u : Vector N) (hu : ‖u‖ ^ 2 = (N : ℝ))
    (e : Fin k → Vector N) (he : Orthonormal ℝ e) (htan : ∀ i, inner ℝ (e i) u = 0)
    (hv : 0 < firstCovariance c 1) : Surjective (gradientCLM c u e) := by
  apply surjective_of_gram_det_ne_zero
  rw [gradient_gram hN c hc u hu e he htan]
  simp only [ContinuousLinearMap.det, ContinuousLinearMap.toLinearMap_smul,
    LinearMap.det_smul, ContinuousLinearMap.coe_id, LinearMap.det_id, mul_one]
  exact pow_ne_zero _ hv.ne'

/-- The actual value/radial score is one linear observation of all tensor coefficients. -/
def scoreCLM {N P : ℕ} (c : Degree P → ℝ) (u : Vector N) :
    EuclideanDisorder N P →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i => if i = 0 then
      flatJetCLM c 0 u (fun j => Fin.elim0 j) else flatJetCLM c 1 u (fun _ => u)))

@[simp] theorem scoreCLM_apply_zero {N P : ℕ} (c : Degree P → ℝ) (u : Vector N)
    (g : EuclideanDisorder N P) :
    scoreCLM c u g 0 = jet c 0 u (fun i => Fin.elim0 i) (unpackDisorder g) := by
  simp [scoreCLM]

@[simp] theorem scoreCLM_apply_one {N P : ℕ} (c : Degree P → ℝ) (u : Vector N)
    (g : EuclideanDisorder N P) :
    scoreCLM c u g 1 = jet c 1 u (fun _ => u) (unpackDisorder g) := by
  simp [scoreCLM]

/-- Exact score Gram matrix, from the actual mixed tensor jet covariance. -/
theorem center_score_gram_matrix {N : ℕ} (hN : 0 < N) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 ≤ Q) (u : Vector N) (hu : ‖u‖ ^ 2 = (N : ℝ)) :
    LinearMap.toMatrix (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
      (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
      (GaussianRegression.gram (scoreCLM (centerCoefficients (mixtureCoefficients μ) Q) u)).toLinearMap =
      (N : ℝ) • μ.scoreCovariance Q := by
  classical
  let c := centerCoefficients (mixtureCoefficients μ) Q
  have hc := center_value_radial_covariances hN μ hQ u hu
  ext i j
  rw [LinearMap.toMatrix_apply]
  change GaussianRegression.gram (scoreCLM c u) (EuclideanSpace.basisFun (Fin 2) ℝ j) i = _
  rw [← actual_covariance_gram]
  fin_cases i <;> fin_cases j
  · simpa [actualObservation, FiniteMixture.scoreCovariance] using hc.1
  · simpa [actualObservation, FiniteMixture.scoreCovariance] using hc.2.1
  · rw [covariance_comm]
    simpa [actualObservation, FiniteMixture.scoreCovariance] using hc.2.1
  · simpa [actualObservation, FiniteMixture.scoreCovariance] using hc.2.2

/-- Exact true score determinant, including the manuscript's factor N². -/
theorem center_score_gram_det {N : ℕ} (hN : 0 < N) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 ≤ Q) (u : Vector N) (hu : ‖u‖ ^ 2 = (N : ℝ)) :
    (GaussianRegression.gram (scoreCLM (centerCoefficients (mixtureCoefficients μ) Q) u)).det =
      (N : ℝ) ^ 2 * (μ.scoreCovariance Q).det := by
  rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis,
    center_score_gram_matrix hN μ hQ u hu, Matrix.det_smul]
  simp

/-- Nonpure mixtures give a genuinely surjective actual score observation. -/
theorem center_score_surjective {N : ℕ} (hN : 0 < N) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 < Q) (hnp : μ.minDegree < μ.maxDegree)
    (u : Vector N) (hu : ‖u‖ ^ 2 = (N : ℝ)) :
    Surjective (scoreCLM (centerCoefficients (mixtureCoefficients μ) Q) u) := by
  apply surjective_of_gram_det_ne_zero
  rw [center_score_gram_det hN μ hQ.le u hu]
  exact (mul_pos (sq_pos_of_pos (Nat.cast_pos.mpr hN))
    (μ.scoreCovariance_det_pos hQ hnp)).ne'

/-- The derivative variance is strictly positive for every genuine finite
mixture at every positive overlap. -/
theorem mixture_xi1_pos (μ : FiniteMixture) {Q : ℝ} (hQ : 0 < Q) : 0 < μ.xi1 Q := by
  classical
  unfold FiniteMixture.xi1
  apply Finset.sum_pos
  · intro p hp
    exact mul_pos (mul_pos (μ.coeff_pos hp) (Nat.cast_pos.mpr (by have := μ.degree_ge_two hp; omega)))
      (pow_pos hQ _)
  · exact μ.support_nonempty

/-- Every actual finite mixture gives a surjective tangent-gradient observation. -/
theorem center_gradient_surjective {N k : ℕ} (hN : 0 < N) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 < Q) (u : Vector N) (hu : ‖u‖ ^ 2 = (N : ℝ))
    (e : Fin k → Vector N) (he : Orthonormal ℝ e) (htan : ∀ i, inner ℝ (e i) u = 0) :
    Surjective (gradientCLM (centerCoefficients (mixtureCoefficients μ) Q) u e) := by
  apply gradient_surjective hN _
    (centerCoefficients_nonnegative _ (mixtureCoefficients_nonnegative μ) hQ.le) u hu e he htan
  rw [firstCovariance_center, firstCovariance_mixture]
  exact mul_pos hQ (mixture_xi1_pos μ hQ)

/-- Full Borel-mark regression at the actual tangent gradient, with its
nondegeneracy derived from the actual finite mixture. -/
theorem gradient_whole_field_disintegration {N k : ℕ} (hN : 0 < N) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 < Q) (u : Vector N) (hu : ‖u‖ ^ 2 = (N : ℝ))
    (e : Fin k → Vector N) (he : Orthonormal ℝ e) (htan : ∀ i, inner ℝ (e i) u = 0)
    (phi : EuclideanSpace ℝ (Fin k) × Disorder N μ.maxDegree → ℝ≥0∞) (hphi : Measurable phi) :
    let A := gradientCLM (centerCoefficients (mixtureCoefficients μ) Q) u e
    (∫⁻ J, phi (actualObservation A J, J) ∂disorderLaw N μ.maxDegree) =
      ∫⁻ w, ∫⁻ J, phi (w, J) ∂coefficientKernel A w
        ∂GaussianRegression.observationLaw A :=
  actual_disintegration _ (center_gradient_surjective hN μ hQ u hu e he htan) phi hphi

/-- Full Borel-mark regression at the actual value/radial score for a nonpure
mixture; the determinant premise is proved from the actual mixture coefficients. -/
theorem score_whole_field_disintegration {N : ℕ} (hN : 0 < N) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 < Q) (hnp : μ.minDegree < μ.maxDegree)
    (u : Vector N) (hu : ‖u‖ ^ 2 = (N : ℝ))
    (phi : EuclideanSpace ℝ (Fin 2) × Disorder N μ.maxDegree → ℝ≥0∞) (hphi : Measurable phi) :
    let A := scoreCLM (centerCoefficients (mixtureCoefficients μ) Q) u
    (∫⁻ J, phi (actualObservation A J, J) ∂disorderLaw N μ.maxDegree) =
      ∫⁻ w, ∫⁻ J, phi (w, J) ∂coefficientKernel A w
        ∂GaussianRegression.observationLaw A :=
  actual_disintegration _ (center_score_surjective hN μ hQ hnp u hu) phi hphi

/-- Actual tangent-gradient covariance determinant at the center overlap. -/
theorem center_gradient_gram_det {N k : ℕ} (hN : 0 < N) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 ≤ Q) (u : Vector N) (hu : ‖u‖ ^ 2 = (N : ℝ))
    (e : Fin k → Vector N) (he : Orthonormal ℝ e) (htan : ∀ i, inner ℝ (e i) u = 0) :
    (GaussianRegression.gram (gradientCLM (centerCoefficients (mixtureCoefficients μ) Q) u e)).det =
      (Q * μ.xi1 Q) ^ k := by
  rw [gradient_gram hN _ (centerCoefficients_nonnegative _ (mixtureCoefficients_nonnegative μ) hQ)
    u hu e he htan, firstCovariance_center, firstCovariance_mixture]
  simp [ContinuousLinearMap.det, ContinuousLinearMap.toLinearMap_smul,
    ContinuousLinearMap.coe_id, LinearMap.det_smul]

/-- Explicit observationPdf formula at literal gradient zero. It is the actual
pointwise density when Q>0; the algebraic identity also includes Q=0. -/
theorem center_gradient_pdf_zero {N k : ℕ} (hN : 0 < N) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 ≤ Q) (u : Vector N) (hu : ‖u‖ ^ 2 = (N : ℝ))
    (e : Fin k → Vector N) (he : Orthonormal ℝ e) (htan : ∀ i, inner ℝ (e i) u = 0) :
    GaussianRegression.observationPdf
      (gradientCLM (centerCoefficients (mixtureCoefficients μ) Q) u e) 0 =
      ENNReal.ofReal (GaussianDensity.normalizer (EuclideanSpace ℝ (Fin k)) /
        Real.sqrt ((Q * μ.xi1 Q) ^ k)) := by
  rw [GaussianRegression.observationPdf_zero, center_gradient_gram_det hN μ hQ u hu e he htan]

/-- Explicit observationPdf formula at literal score zero, with its true N²detΣ_Q
covariance. It is the actual density for positive Q and a nonpure mixture. -/
theorem center_score_pdf_zero {N : ℕ} (hN : 0 < N) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 ≤ Q) (u : Vector N) (hu : ‖u‖ ^ 2 = (N : ℝ)) :
    GaussianRegression.observationPdf
      (scoreCLM (centerCoefficients (mixtureCoefficients μ) Q) u) 0 =
      ENNReal.ofReal (GaussianDensity.normalizer (EuclideanSpace ℝ (Fin 2)) /
        Real.sqrt ((N : ℝ) ^ 2 * (μ.scoreCovariance Q).det)) := by
  rw [GaussianRegression.observationPdf_zero, center_score_gram_det hN μ hQ u hu]

end
end SlowEquilibration.WholeFieldRegression
