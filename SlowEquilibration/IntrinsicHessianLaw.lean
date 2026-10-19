-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.IntrinsicGradientRegression
public import SlowEquilibration.SphericalIntrinsicHessianJet

/-! # Actual full-tangent Hessian and canonical zero-gradient law

A complete tangent orthonormal basis is constructed from the actual sphere
point. Gaussian coefficient regression retains the joint value/radial/Hessian
law at the specified zero gradient. The intrinsic Hessian includes the genuine
radial identity shift.
-/

@[expose] public section

namespace SlowEquilibration.IntrinsicHessianLaw

open MeasureTheory ProbabilityTheory Set Function
open SlowEquilibration.SphericalModel SlowEquilibration.SphericalForm
open SlowEquilibration.SphericalGaussianJet SlowEquilibration.WholeFieldRegression
open SlowEquilibration.IntrinsicGradientRegression SlowEquilibration.SphereHessian
open scoped RealInnerProductSpace ENNReal Topology BigOperators

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000

/-- A complete actual tangent orthonormal basis, in its true dimension. -/
def tangentBasis {n : ℕ} (x : Vector (n + 1)) (hx : ‖x‖ ^ 2 = (n + 1 : ℕ)) :
    OrthonormalBasis (Fin n) ℝ (tangentPlane x) :=
  (stdOrthonormalBasis ℝ (tangentPlane x)).reindex (finCongr (tangentPlane_finrank x hx))

def tangentFrame {n : ℕ} (x : Vector (n + 1)) (hx : ‖x‖ ^ 2 = (n + 1 : ℕ)) :
    Fin n → Vector (n + 1) := fun i => tangentBasis x hx i

lemma tangentFrame_orthonormal {n : ℕ} (x : Vector (n + 1))
    (hx : ‖x‖ ^ 2 = (n + 1 : ℕ)) : Orthonormal ℝ (tangentFrame x hx) := by
  simpa only [orthonormal_iff_ite, tangentFrame, Submodule.coe_inner] using
    (tangentBasis x hx).orthonormal

lemma tangentFrame_tangent {n : ℕ} (x : Vector (n + 1))
    (hx : ‖x‖ ^ 2 = (n + 1 : ℕ)) (i : Fin n) : inner ℝ (tangentFrame x hx i) x = 0 := by
  rw [real_inner_comm]
  exact Submodule.mem_orthogonal_singleton_iff_inner_right.mp (tangentBasis x hx i).2

/-- A genuine coefficient-linear observation annihilating the observed lift
has its original law under the canonical whole-coefficient zero kernel. -/
theorem coefficientKernel_zero_map_linear {N P : ℕ} {F G : Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F]
    [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]
    [MeasurableSpace G] [BorelSpace G]
    (A : EuclideanDisorder N P →L[ℝ] F) (B : EuclideanDisorder N P →L[ℝ] G)
    (hBA : B.comp A.adjoint = 0) :
    (coefficientKernel A 0).map (actualObservation B) =
      (disorderLaw N P).map (actualObservation B) := by
  have hm : Measurable (actualObservation B) :=
    B.continuous.measurable.comp ((PiLp.continuousLinearEquiv 2 ℝ
      (fun _ : Coordinate N P => ℝ)).symm.continuous.measurable.comp
      (flatDisorder_measurable N P))
  have hBres : B.comp (GaussianRegression.residual A) = B := by
    ext g
    change B (g - A.adjoint ((GaussianRegression.gram A).inverse (A g))) = B g
    rw [map_sub]
    have hz := congrArg (fun L : F →L[ℝ] G => L ((GaussianRegression.gram A).inverse (A g))) hBA
    change B (A.adjoint ((GaussianRegression.gram A).inverse (A g))) = 0 at hz
    rw [hz, sub_zero]
  rw [coefficientKernel_apply, GaussianRegression.regressionKernel_apply,
    Measure.map_map hm (unpackCLM N P).continuous.measurable,
    Measure.map_map (hm.comp (unpackCLM N P).continuous.measurable) (by fun_prop)]
  have he : (actualObservation B ∘ unpackCLM N P) ∘
      (fun g => GaussianRegression.residual A g + GaussianRegression.lift A 0) = B := by
    funext g
    simp only [Function.comp_apply, actualObservation, map_zero, add_zero]
    change B (GaussianRegression.residual A g) = B g
    exact congrArg (fun L : EuclideanDisorder N P →L[ℝ] G => L g) hBres
  rw [he]
  exact ((hasLaw_map B.continuous.measurable.aemeasurable).fun_comp
    (actual_flattened_gaussian N P)).map_eq.symm

/-- Actual scalar cross covariance identifies the coefficient lift coupling. -/
theorem actual_scalar_cross_covariance {N P : ℕ} {F : Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (f : EuclideanDisorder N P →L[ℝ] ℝ) (A : EuclideanDisorder N P →L[ℝ] F) (w : F) :
    cov[fun J : Disorder N P => f (euclideanDisorder J),
      fun J : Disorder N P => inner ℝ w (A (euclideanDisorder J)); disorderLaw N P] =
      f (A.adjoint w) := by
  have h := (actual_flattened_gaussian N P).covariance_fun_comp
    (f := f) (g := fun g => inner ℝ w (A g)) f.continuous.measurable.aemeasurable
    (continuous_const.inner A.continuous).measurable.aemeasurable
  rw [h]
  have hf : (f : EuclideanDisorder N P → ℝ) =
      fun g => inner ℝ (f.adjoint 1) g := by
    funext g
    rw [f.adjoint_inner_left]
    simp
  have hA : (fun g : EuclideanDisorder N P => inner ℝ w (A g)) =
      fun g => inner ℝ (A.adjoint w) g := by
    funext g
    rw [A.adjoint_inner_left]
  rw [hf, hA, ← covarianceBilin_apply_eq_cov IsGaussian.memLp_two_id,
    covarianceBilin_stdGaussian, innerSL_apply_apply, f.adjoint_inner_left]
  simpa using congrFun hf (A.adjoint w)

/-- The complete Hessian and the value/radial pair, jointly observed as actual
linear functions of the full Gaussian tensor coefficients. -/
def scoreHessianCLM {N P k : ℕ} (c : Degree P → ℝ) (x : Vector N)
    (e : Fin k → Vector N) : EuclideanDisorder N P →L[ℝ]
      EuclideanSpace ℝ (Sum (Fin 2) (Fin k × Fin k)) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Sum (Fin 2) (Fin k × Fin k) => ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (Sum.elim
      (fun i => (EuclideanSpace.proj i).comp (scoreCLM c x))
      (fun ij => flatJetCLM c 2 x ![e ij.1, e ij.2])))

@[simp] theorem scoreHessianCLM_apply_inl {N P k : ℕ} (c : Degree P → ℝ)
    (x : Vector N) (e : Fin k → Vector N) (g : EuclideanDisorder N P) (i : Fin 2) :
    scoreHessianCLM c x e g (Sum.inl i) = scoreCLM c x g i := by simp [scoreHessianCLM]

@[simp] theorem scoreHessianCLM_apply_inr {N P k : ℕ} (c : Degree P → ℝ)
    (x : Vector N) (e : Fin k → Vector N) (g : EuclideanDisorder N P) (i j : Fin k) :
    scoreHessianCLM c x e g (Sum.inr (i,j)) = hessianEntry c x e i j (unpackDisorder g) := by
  simp [scoreHessianCLM, hessianEntry]

/-- Zero cross covariance with the actual full intrinsic gradient annihilates
its actual coefficient lift, for the combined score/Hessian observation. -/
theorem scoreHessian_intrinsic_lift_zero {N P k : ℕ} (c : Degree P → ℝ)
    (hc : ∀ p, 0 ≤ c p) (x : Vector N) (e : Fin k → Vector N)
    (htan : ∀ i, inner ℝ (e i) x = 0) :
    (scoreHessianCLM c x e).comp (intrinsicGamma c x).adjoint = 0 := by
  apply ContinuousLinearMap.ext
  intro w
  apply PiLp.ext
  intro i
  let f := (EuclideanSpace.proj i).comp (scoreHessianCLM c x e)
  have h := actual_scalar_cross_covariance f (intrinsicGamma c x) w
  simp only [f, ContinuousLinearMap.comp_apply,
    intrinsicGamma_inner, unpack_euclideanDisorder] at h
  change cov[fun J : Disorder N P => scoreHessianCLM c x e (euclideanDisorder J) i,
    jet c 1 x (fun _ => (w : Vector N)); disorderLaw N P] =
      scoreHessianCLM c x e ((intrinsicGamma c x).adjoint w) i at h
  change scoreHessianCLM c x e ((intrinsicGamma c x).adjoint w) i = 0
  rw [← h]
  have hw : inner ℝ (w : Vector N) x = 0 := by
    rw [real_inner_comm]
    exact Submodule.mem_orthogonal_singleton_iff_inner_right.mp w.2
  cases i with
  | inl i =>
    fin_cases i
    · change cov[fun J : Disorder N P => scoreCLM c x (euclideanDisorder J) 0,
        jet c 1 x (fun _ => (w : Vector N)); disorderLaw N P] = 0
      simpa only [scoreCLM_apply_zero, unpack_euclideanDisorder] using
        value_tangent_gradient_covariance_zero c hc x w hw
    · change cov[fun J : Disorder N P => scoreCLM c x (euclideanDisorder J) 1,
        jet c 1 x (fun _ => (w : Vector N)); disorderLaw N P] = 0
      simpa only [scoreCLM_apply_one, unpack_euclideanDisorder] using
        radial_tangent_gradient_covariance_zero c hc x w hw
  | inr ij =>
    rcases ij with ⟨i,j⟩
    change cov[fun J : Disorder N P => scoreHessianCLM c x e (euclideanDisorder J) (Sum.inr (i,j)),
      jet c 1 x (fun _ => (w : Vector N)); disorderLaw N P] = 0
    simp only [scoreHessianCLM_apply_inr, unpack_euclideanDisorder]
    exact hessian_gradient_covariance_zero c hc x e htan i j w

/-- The canonical actual full-coefficient law conditioned on intrinsic gradient
zero retains the complete joint score/ambient-Hessian law, pointwise at zero. -/
theorem scoreHessian_zeroKernel_law {N P k : ℕ} (c : Degree P → ℝ)
    (hc : ∀ p, 0 ≤ c p) (x : Vector N) (e : Fin k → Vector N)
    (htan : ∀ i, inner ℝ (e i) x = 0) :
    (coefficientKernel (intrinsicGamma c x) 0).map (actualObservation (scoreHessianCLM c x e)) =
      (disorderLaw N P).map (actualObservation (scoreHessianCLM c x e)) :=
  coefficientKernel_zero_map_linear _ _ (scoreHessian_intrinsic_lift_zero c hc x e htan)

/-- The complete Hessian and actual value/radial pair decoded from the joint
linear observation; no field coordinates are replaced. -/
def scoreHessianDecode (k : ℕ)
    (y : EuclideanSpace ℝ (Sum (Fin 2) (Fin k × Fin k))) :
    (Option (Fin 1) → ℝ) × Matrix (Fin k) (Fin k) ℝ :=
  ((fun i => match i with | none => y (Sum.inl 0) | some _ => y (Sum.inl 1)),
    fun i j => y (Sum.inr (i,j)))

lemma scoreHessianDecode_measurable (k : ℕ) : Measurable (scoreHessianDecode k) := by
  apply Measurable.prodMk
  · apply Measurable.of_eval
    intro i
    cases i <;> exact (EuclideanSpace.proj _).continuous.measurable
  · apply Measurable.of_eval
    intro i
    apply Measurable.of_eval
    intro j
    exact (EuclideanSpace.proj _).continuous.measurable

lemma scoreHessianDecode_actual {N P k : ℕ} (c : Degree P → ℝ)
    (x : Vector N) (e : Fin k → Vector N) (J : Disorder N P) :
    scoreHessianDecode k (actualObservation (scoreHessianCLM c x e) J) =
      (valueGradient c x (fun _ : Fin 1 => x) J, hessianMatrix c x e J) := by
  apply Prod.ext
  · funext i
    cases i with
    | none =>
      change scoreCLM c x (euclideanDisorder J) 0 = jet c 0 x (fun i => Fin.elim0 i) J
      rw [scoreCLM_apply_zero, unpack_euclideanDisorder]
    | some i =>
      change scoreCLM c x (euclideanDisorder J) 1 = jet c 1 x (fun _ => x) J
      rw [scoreCLM_apply_one, unpack_euclideanDisorder]
  · funext i j
    change scoreHessianCLM c x e (euclideanDisorder J) (Sum.inr (i,j)) = hessianEntry c x e i j J
    rw [scoreHessianCLM_apply_inr, unpack_euclideanDisorder]

/-- Canonical zero-gradient conditioning preserves the full actual joint
value/radial/ambient-Hessian law, at the literal specified target zero. -/
theorem joint_score_hessian_zeroKernel {N P k : ℕ} (c : Degree P → ℝ)
    (hc : ∀ p, 0 ≤ c p) (x : Vector N) (e : Fin k → Vector N)
    (htan : ∀ i, inner ℝ (e i) x = 0) :
    (coefficientKernel (intrinsicGamma c x) 0).map
      (fun J => (valueGradient c x (fun _ : Fin 1 => x) J, hessianMatrix c x e J)) =
    (disorderLaw N P).map
      (fun J => (valueGradient c x (fun _ : Fin 1 => x) J, hessianMatrix c x e J)) := by
  have hm : Measurable (actualObservation (scoreHessianCLM c x e)) :=
    (scoreHessianCLM c x e).continuous.measurable.comp ((PiLp.continuousLinearEquiv 2 ℝ
      (fun _ : Coordinate N P => ℝ)).symm.continuous.measurable.comp
      (flatDisorder_measurable N P))
  have h := congrArg (fun m => m.map (scoreHessianDecode k))
    (scoreHessian_zeroKernel_law c hc x e htan)
  rw [Measure.map_map (scoreHessianDecode_measurable k) hm,
    Measure.map_map (scoreHessianDecode_measurable k) hm] at h
  simpa only [Function.comp_def, scoreHessianDecode_actual] using h

/-- The exact independent score/GOE product law holds under the canonical
whole-field law at intrinsic gradient zero. -/
theorem zeroKernel_score_goe_product {N P k : ℕ} (hN : 0 < N)
    (c : Degree P → ℝ) (hc : ∀ p, 0 ≤ c p) (x : Vector N)
    (hx : ‖x‖ ^ 2 = (N : ℝ)) (e : Fin k → Vector N)
    (he : Orthonormal ℝ e) (htan : ∀ i, inner ℝ (e i) x = 0) :
    (coefficientKernel (intrinsicGamma c x) 0).map
      (fun J => (valueGradient c x (fun _ : Fin 1 => x) J, hessianMatrix c x e J)) =
      ((disorderLaw N P).map (valueGradient c x (fun _ : Fin 1 => x))).prod
        (goeLaw k N (secondCovariance c 1)) := by
  rw [joint_score_hessian_zeroKernel c hc x e htan]
  have h := hessian_marginal_conditional_disintegration hN c hc x
    (r := 1) (by simpa using hx) e he htan (fun _ : Fin 1 => x)
  unfold hessianConditionalKernel at h
  rw [Measure.compProd_const] at h
  exact h.symm

/-- Literal matrix of the full intrinsic Hessian in the constructed complete
orthonormal basis, with the true radial identity shift. -/
theorem intrinsicHessian_toMatrix {n P : ℕ} (c : Degree P → ℝ)
    (J : Disorder (n + 1) P) (x : Vector (n + 1))
    (hx : ‖x‖ ^ 2 = (n + 1 : ℕ)) :
    LinearMap.toMatrix (tangentBasis x hx).toBasis (tangentBasis x hx).toBasis
      (intrinsicHessian (field c J) x).toLinearMap =
      hessianMatrix c x (tangentFrame x hx) J -
        radialMultiplier (field c J) x • (1 : Matrix (Fin n) (Fin n) ℝ) := by
  classical
  have hsphere : SphericalAging.HardSphereDynamics.OnSphere x := by
    change inner ℝ x x = _
    rw [real_inner_self_eq_norm_sq]
    exact hx
  ext i j
  rw [LinearMap.toMatrix_apply]
  change (tangentBasis x hx).repr (intrinsicHessian (field c J) x (tangentBasis x hx j)) i = _
  rw [OrthonormalBasis.repr_apply_apply, real_inner_comm,
    intrinsicHessian_frame_entry (by omega) c J x hsphere (tangentBasis x hx) j i,
    orthonormal_iff_ite.mp (tangentBasis x hx).orthonormal]
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply, hessianMatrix]
  change hessianEntry c x (fun a => (tangentBasis x hx a : Vector (n + 1))) j i J -
    (jet c 1 x (fun _ => x) J / (n + 1 : ℕ)) * (if j = i then 1 else 0) =
      hessianEntry c x (fun a => (tangentBasis x hx a : Vector (n + 1))) i j J -
        radialMultiplier (field c J) x * (if i = j then 1 else 0)
  rw [hessianEntry_symm c x (fun a => (tangentBasis x hx a : Vector (n + 1))) j i]
  simp only [radialMultiplier_eq_jet, eq_comm]

/-- The ordinary intrinsic operator determinant is exactly the ordinary
full-tangent shifted GOE-matrix determinant, for the actual same disorder. -/
theorem intrinsicHessian_det {n P : ℕ} (c : Degree P → ℝ)
    (J : Disorder (n + 1) P) (x : Vector (n + 1))
    (hx : ‖x‖ ^ 2 = (n + 1 : ℕ)) :
    (intrinsicHessian (field c J) x).det =
      (hessianMatrix c x (tangentFrame x hx) J -
        (jet c 1 x (fun _ => x) J / (n + 1 : ℕ)) • 1).det := by
  rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix (tangentBasis x hx).toBasis,
    intrinsicHessian_toMatrix c J x hx, radialMultiplier_eq_jet]

/-- Arbitrary Borel joint marks retain the actual independent score/GOE law
under full-field intrinsic-gradient-zero conditioning. -/
theorem zeroKernel_score_goe_lintegral {N P k : ℕ} (hN : 0 < N)
    (c : Degree P → ℝ) (hc : ∀ p, 0 ≤ c p) (x : Vector N)
    (hx : ‖x‖ ^ 2 = (N : ℝ)) (e : Fin k → Vector N)
    (he : Orthonormal ℝ e) (htan : ∀ i, inner ℝ (e i) x = 0)
    (phi : (Option (Fin 1) → ℝ) × Matrix (Fin k) (Fin k) ℝ → ℝ≥0∞)
    (hphi : Measurable phi) :
    (∫⁻ J, phi (valueGradient c x (fun _ : Fin 1 => x) J, hessianMatrix c x e J)
      ∂coefficientKernel (intrinsicGamma c x) 0) =
      ∫⁻ a, ∫⁻ W, phi (a,W) ∂goeLaw k N (secondCovariance c 1)
        ∂(disorderLaw N P).map (valueGradient c x (fun _ : Fin 1 => x)) := by
  have hm : Measurable (actualObservation (scoreHessianCLM c x e)) :=
    (scoreHessianCLM c x e).continuous.measurable.comp ((PiLp.continuousLinearEquiv 2 ℝ
      (fun _ : Coordinate N P => ℝ)).symm.continuous.measurable.comp
      (flatDisorder_measurable N P))
  have hj : Measurable (fun J : Disorder N P =>
      (valueGradient c x (fun _ : Fin 1 => x) J, hessianMatrix c x e J)) := by
    convert (scoreHessianDecode_measurable k).comp hm using 1
    funext J
    exact (scoreHessianDecode_actual c x e J).symm
  rw [← lintegral_map hphi hj, zeroKernel_score_goe_product hN c hc x hx e he htan]
  exact lintegral_prod _ hphi.aemeasurable

/-- Actual one-point Hessian factor for the canonical spherical mixed field:
the full intrinsic operator determinant under literal zero gradient is the
independent GOE determinant with its actual radial score shift. -/
theorem one_point_hessian_integral {n : ℕ} (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 < Q) (x : Vector (n + 1)) (hx : ‖x‖ ^ 2 = (n + 1 : ℕ))
    (psi : (Option (Fin 1) → ℝ) → ℝ≥0∞) (hpsi : Measurable psi) :
    let c := centerCoefficients (mixtureCoefficients μ) Q
    (∫⁻ J, ENNReal.ofReal |(intrinsicHessian (field c J) x).det| *
      psi (valueGradient c x (fun _ : Fin 1 => x) J)
      ∂coefficientKernel (intrinsicGamma c x) 0) =
      ∫⁻ a, ∫⁻ W, ENNReal.ofReal |(W - (a (some 0) / (n + 1 : ℕ)) •
        (1 : Matrix (Fin n) (Fin n) ℝ)).det| * psi a
        ∂goeLaw n (n + 1) (Q ^ 2 * μ.xi2 Q)
        ∂(disorderLaw (n + 1) μ.maxDegree).map (valueGradient c x (fun _ : Fin 1 => x)) := by
  dsimp only
  let c := centerCoefficients (mixtureCoefficients μ) Q
  let phi : (Option (Fin 1) → ℝ) × Matrix (Fin n) (Fin n) ℝ → ℝ≥0∞ :=
    fun p => ENNReal.ofReal |(p.2 - (p.1 (some 0) / (n + 1 : ℕ)) • 1).det| * psi p.1
  have hm0 : Continuous (fun p : (Option (Fin 1) → ℝ) × Matrix (Fin n) (Fin n) ℝ =>
      p.2 - (p.1 (some 0) / (n + 1 : ℕ)) • (1 : Matrix (Fin n) (Fin n) ℝ)) :=
    continuous_snd.sub ((((continuous_apply (some 0)).comp continuous_fst).div_const _).smul continuous_const)
  have hphi : Measurable phi :=
    hm0.matrix_det.abs.measurable.ennreal_ofReal.mul (hpsi.comp measurable_fst)
  have h := zeroKernel_score_goe_lintegral (by omega) c
    (centerCoefficients_nonnegative _ (mixtureCoefficients_nonnegative μ) hQ.le) x hx
    (tangentFrame x hx) (tangentFrame_orthonormal x hx) (tangentFrame_tangent x hx) phi hphi
  rw [secondCovariance_center, secondCovariance_mixture] at h
  convert h using 1
  apply lintegral_congr
  intro J
  rw [intrinsicHessian_det c J x hx]
  rfl

end
end SlowEquilibration.IntrinsicHessianLaw
