-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianRegression
public import Mathlib.Analysis.InnerProductSpace.NormDet
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

@[expose] public section

namespace SlowEquilibration.GaussianRegression

open MeasureTheory ProbabilityTheory Set Function
open scoped RealInnerProductSpace Topology ENNReal

noncomputable section

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]

/-- The actual observation restricted to its unobserved-kernel orthogonal complement. -/
def effectiveObservation (A : E →L[ℝ] F) : A.kerᗮ →L[ℝ] F := A.comp A.kerᗮ.subtypeL

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F] in
lemma effectiveObservation_bijective (A : E →L[ℝ] F) (hA : Surjective A) :
    Bijective (effectiveObservation A) := by
  constructor
  · intro x y h
    apply Subtype.ext
    have hd : (x : E) - y ∈ A.ker := by
      change A ((x : E) - y) = 0
      rw [map_sub]
      exact sub_eq_zero.mpr h
    have ho : (x : E) - y ∈ A.kerᗮ := A.kerᗮ.sub_mem x.2 y.2
    have hh : inner ℝ ((x : E) - y) ((x : E) - y) = 0 :=
      Submodule.inner_right_of_mem_orthogonal hd ho
    exact sub_eq_zero.mp (inner_self_eq_zero.mp hh)
  · intro w
    have hm : lift A w ∈ A.kerᗮ := by
      apply (Submodule.mem_orthogonal _ _).mpr
      intro x hx
      exact lift_orthogonal_ker A w x hx
    exact ⟨⟨lift A w, hm⟩, observation_lift_apply A hA w⟩

/-- The true continuous linear observation equivalence on the effective coordinates. -/
def effectiveEquiv (A : E →L[ℝ] F) (hA : Surjective A) : A.kerᗮ ≃L[ℝ] F :=
  (LinearEquiv.ofBijective (effectiveObservation A).toLinearMap
    (effectiveObservation_bijective A hA)).toContinuousLinearEquiv

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F] in
lemma effectiveEquiv_apply (A : E →L[ℝ] F) (hA : Surjective A) (x : A.kerᗮ) :
    effectiveEquiv A hA x = A x := rfl

/-- A genuine orthonormal coordinate isometry, used only to apply the ordinary
square-map Lebesgue Jacobian theorem. The final pdf is coordinate-independent. -/
def effectiveIsometry (A : E →L[ℝ] F) (hA : Surjective A) : F ≃ₗᵢ[ℝ] A.kerᗮ :=
  ((stdOrthonormalBasis ℝ F).reindex
    (finCongr (effectiveEquiv A hA).finrank_eq.symm)).repr.trans
      (stdOrthonormalBasis ℝ A.kerᗮ).repr.symm

/-- The actual invertible square-coordinate observation map. -/
def squareObservation (A : E →L[ℝ] F) (hA : Surjective A) : F ≃L[ℝ] F :=
  (effectiveIsometry A hA).toContinuousLinearEquiv.trans (effectiveEquiv A hA)

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F] in
lemma squareObservation_apply (A : E →L[ℝ] F) (hA : Surjective A) (w : F) :
    squareObservation A hA w = A (effectiveIsometry A hA w) := rfl

/-- Genuine orthogonal projection of the ordinary standard Gaussian is the
ordinary standard Gaussian of the actual Hilbert subspace. -/
lemma projection_stdGaussian (K : Submodule ℝ E) :
    (stdGaussian E).map K.orthogonalProjectionOnto = stdGaussian K := by
  apply Measure.ext_of_charFun
  funext x
  rw [charFun_stdGaussian, charFun_apply, integral_map (by fun_prop) (by fun_prop)]
  have hi (z : E) : inner ℝ (K.orthogonalProjectionOnto z) x = inner ℝ z (x : E) := by
    simpa only [Submodule.adjoint_orthogonalProjectionOnto, Submodule.subtypeL_apply] using
      ((K.orthogonalProjectionOnto).adjoint_inner_right z x).symm
  simp_rw [hi]
  rw [← charFun_apply, charFun_stdGaussian]
  rfl

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F] in
lemma observation_orthogonalProjection (A : E →L[ℝ] F) (hA : Surjective A) (x : E) :
    A (A.kerᗮ.orthogonalProjectionOnto x) = A x := by
  have h := A.ker.starProjection_add_starProjection_orthogonal x
  have hh := congrArg A h
  have hz : A (A.ker.starProjection x) = 0 := by
    rw [← residual_eq_starProjection A hA]
    exact residual_mem_ker A hA x
  simpa only [map_add, hz, zero_add, Submodule.coe_orthogonalProjectionOnto_apply] using hh

/-- The actual observation law is the invertible square map of a genuine
standard Gaussian in the actual target dimension. -/
theorem observationLaw_eq_squareGaussian (A : E →L[ℝ] F) (hA : Surjective A) :
    observationLaw A = (stdGaussian F).map (squareObservation A hA) := by
  have hproj := projection_stdGaussian (A.kerᗮ)
  have hmap := congrArg (fun μ => μ.map (effectiveEquiv A hA)) hproj
  rw [Measure.map_map (by fun_prop) (by fun_prop)] at hmap
  have he : (effectiveEquiv A hA) ∘ A.kerᗮ.orthogonalProjectionOnto = A := by
    funext x
    exact observation_orthogonalProjection A hA x
  rw [he] at hmap
  have hiso := stdGaussian_map (effectiveIsometry A hA)
  rw [← hiso, Measure.map_map (by fun_prop) (by fun_prop)] at hmap
  exact hmap

/-- Transport of a genuine density through an actual measurable equivalence. -/
lemma map_withDensity_equiv {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (e : X ≃ᵐ Y) (μ : Measure X) (f : X → ℝ≥0∞) (hf : Measurable f) :
    (μ.withDensity f).map e = (μ.map e).withDensity (f ∘ e.symm) := by
  apply Measure.ext_of_lintegral
  intro g hg
  rw [lintegral_map hg e.measurable]
  calc
    _ = ∫⁻ x, f x * g (e x) ∂μ := by
      simpa only [Function.comp_apply, Pi.mul_apply] using
        (lintegral_withDensity_eq_lintegral_mul μ hf (hg.comp e.measurable))
    _ = ∫⁻ x, f (e.symm (e x)) * g (e x) ∂μ := by simp
    _ = ∫⁻ y, f (e.symm y) * g y ∂μ.map e :=
      (lintegral_map ((hf.comp e.symm.measurable).mul hg) e.measurable).symm
    _ = _ := by
      simpa only [Function.comp_apply, Pi.mul_apply] using
        (lintegral_withDensity_eq_lintegral_mul (μ.map e) (hf.comp e.symm.measurable) hg).symm


/-- The genuine explicit pointwise pdf of an invertible linear image of a
standard Gaussian, before specializing to the observation. -/
def squarePdf (e : F ≃L[ℝ] F) (w : F) : ℝ≥0∞ :=
  ENNReal.ofReal (|(e : F →L[ℝ] F).det|⁻¹ * GaussianDensity.density (e.symm w))

lemma squarePdf_measurable (e : F ≃L[ℝ] F) : Measurable (squarePdf e) := by
  unfold squarePdf
  exact (measurable_const.mul
    (GaussianDensity.density_continuous.measurable.comp e.symm.continuous.measurable)).ennreal_ofReal

/-- Ordinary exact Lebesgue pdf transport, using the actual linear determinant. -/
theorem squareGaussian_eq_withDensity (e : F ≃L[ℝ] F) :
    (stdGaussian F).map e = volume.withDensity (squarePdf e) := by
  have hd : (e : F →L[ℝ] F).det ≠ 0 := e.toLinearEquiv.isUnit_det'.ne_zero
  have hm : (volume : Measure F).map e =
      ENNReal.ofReal |(e : F →L[ℝ] F).det⁻¹| • volume :=
    Measure.map_linearMap_addHaar_eq_smul_addHaar volume hd
  have ht := map_withDensity_equiv e.toHomeomorph.toMeasurableEquiv volume
    (fun x => ENNReal.ofReal (GaussianDensity.density x))
      GaussianDensity.density_continuous.measurable.ennreal_ofReal
  have hsym : ⇑e.toHomeomorph.symm = ⇑e.symm := rfl
  simp only [Homeomorph.toMeasurableEquiv_coe, Homeomorph.toMeasurableEquiv_symm_coe,
    ContinuousLinearEquiv.coe_toHomeomorph, hsym] at ht
  rw [GaussianDensity.stdGaussian_eq_withDensity, ht, hm, withDensity_smul_measure]
  rw [← withDensity_smul' _ _ ENNReal.ofReal_ne_top]
  congr 1
  funext w
  simp only [Pi.smul_apply, smul_eq_mul, Function.comp_apply, squarePdf, abs_inv]
  exact (ENNReal.ofReal_mul (inv_nonneg.mpr (abs_nonneg _))).symm

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F] in
/-- The actual square-coordinate covariance equals the actual observation Gram. -/
lemma squareObservation_gram (A : E →L[ℝ] F) (hA : Surjective A) :
    (squareObservation A hA : F →L[ℝ] F).comp (squareObservation A hA : F →L[ℝ] F).adjoint = gram A := by
  let j := effectiveIsometry A hA
  have he : (squareObservation A hA : F →L[ℝ] F) =
      A.comp (A.kerᗮ.subtypeL.comp (j : F →L[ℝ] A.kerᗮ)) := by
    apply ContinuousLinearMap.ext
    intro w
    rfl
  rw [he, ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp,
    j.adjoint_eq_symm, Submodule.adjoint_subtypeL]
  apply ContinuousLinearMap.ext
  intro w
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv, j.apply_symm_apply, Submodule.subtypeL_apply]
  exact observation_orthogonalProjection A hA (A.adjoint w)

omit [MeasurableSpace F] [BorelSpace F] in
lemma det_adjoint_real (T : F →L[ℝ] F) : T.adjoint.det = T.det := by
  let b := stdOrthonormalBasis ℝ F
  change LinearMap.det T.adjoint.toLinearMap = LinearMap.det T.toLinearMap
  rw [← LinearMap.det_toMatrix b.toBasis, ← LinearMap.det_toMatrix b.toBasis,
    ← ContinuousLinearMap.adjoint_toLinearMap, LinearMap.toMatrix_adjoint,
    Matrix.det_conjTranspose]
  simp

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F] in
/-- The exact square-root covariance determinant factor of the observation pdf. -/
theorem squareObservation_abs_det (A : E →L[ℝ] F) (hA : Surjective A) :
    |(squareObservation A hA : F →L[ℝ] F).det| = Real.sqrt (gram A).det := by
  have h := congrArg ContinuousLinearMap.det (squareObservation_gram A hA)
  change LinearMap.det ((squareObservation A hA : F →L[ℝ] F).toLinearMap.comp
    (squareObservation A hA : F →L[ℝ] F).adjoint.toLinearMap) = _ at h
  rw [LinearMap.det_comp] at h
  change (squareObservation A hA : F →L[ℝ] F).det *
    (squareObservation A hA : F →L[ℝ] F).adjoint.det = (gram A).det at h
  rw [det_adjoint_real] at h
  rw [← h, ← pow_two, Real.sqrt_sq_eq_abs]

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F] in
lemma squareObservation_inverse_norm (A : E →L[ℝ] F) (hA : Surjective A) (w : F) :
    ‖(squareObservation A hA).symm w‖ = ‖lift A w‖ := by
  let j := effectiveIsometry A hA
  have h0 : (j ((squareObservation A hA).symm w) : E) = lift A w := by
    have hobs : A (j ((squareObservation A hA).symm w)) = w :=
      (squareObservation A hA).apply_symm_apply w
    have horth : lift A w ∈ A.kerᗮ := (Submodule.mem_orthogonal _ _).mpr
      (fun x hx => lift_orthogonal_ker A w x hx)
    have hEq : j ((squareObservation A hA).symm w) = (⟨lift A w, horth⟩ : A.kerᗮ) :=
      (effectiveObservation_bijective A hA).1 (hobs.trans (observation_lift_apply A hA w).symm)
    exact congrArg Subtype.val hEq
  rw [← h0, Submodule.norm_coe, j.norm_map]

/-- The canonical explicit observation pdf, pointwise also at observation zero. -/
def observationPdf (A : E →L[ℝ] F) (w : F) : ℝ≥0∞ :=
  ENNReal.ofReal ((Real.sqrt (gram A).det)⁻¹ * GaussianDensity.normalizer F *
    Real.exp (-(1 / 2 : ℝ) * ‖lift A w‖ ^ 2))

/-- The actual observation Gaussian has the canonical explicit pointwise pdf;
no Radon--Nikodym values on null slices are used. -/
theorem observationLaw_eq_explicit_density (A : E →L[ℝ] F) (hA : Surjective A) :
    observationLaw A = volume.withDensity (observationPdf A) := by
  rw [observationLaw_eq_squareGaussian A hA, squareGaussian_eq_withDensity]
  congr 1
  funext w
  unfold squarePdf GaussianDensity.density observationPdf
  rw [squareObservation_abs_det A hA, squareObservation_inverse_norm A hA]
  congr 1
  ring

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F] in
/-- The genuine pointwise density at zero is the standard Gaussian normalizer
divided by the square root of the actual covariance determinant. -/
theorem observationPdf_zero (A : E →L[ℝ] F) :
    observationPdf A 0 = ENNReal.ofReal (GaussianDensity.normalizer F / Real.sqrt (gram A).det) := by
  simp [observationPdf, div_eq_mul_inv, mul_comm]

end
end SlowEquilibration.GaussianRegression
