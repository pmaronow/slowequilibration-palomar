-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianFiberDensity
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# The coefficient graph and the orthogonal Gaussian fiber

An invertible observation block gives an actual linear graph parametrization
of the kernel. Its volume Jacobian is derived from the observation covariance
by the Weinstein--Aronszajn determinant identity.
-/

@[expose] public section

namespace SlowEquilibration.GaussianBlockFiber

open MeasureTheory ProbabilityTheory Set Function
open scoped RealInnerProductSpace ENNReal Topology

noncomputable section

variable {U V : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

abbrev Coeff (U V : Type*) := WithLp 2 (U × V)

/-- The actual observation with invertible first coefficient block. -/
def observation (G : U ≃L[ℝ] U) (H : V →L[ℝ] U) : Coeff U V →L[ℝ] U :=
  (G : U →L[ℝ] U).comp (WithLp.fstL 2 ℝ U V) + H.comp (WithLp.sndL 2 ℝ U V)

omit [FiniteDimensional ℝ U] [FiniteDimensional ℝ V] in
@[simp] theorem observation_apply (G : U ≃L[ℝ] U) (H : V →L[ℝ] U) (z : Coeff U V) :
    observation G H z = G z.ofLp.1 + H z.ofLp.2 := rfl

/-- The true coefficient graph slope. -/
def slope (G : U ≃L[ℝ] U) (H : V →L[ℝ] U) : V →L[ℝ] U := (G.symm : U →L[ℝ] U).comp H

/-- The genuine graph inclusion of the zero-observation coefficients. -/
def graph (G : U ≃L[ℝ] U) (H : V →L[ℝ] U) : V →L[ℝ] Coeff U V :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ U V).symm.toContinuousLinearMap.comp
    ((-slope G H).prod (ContinuousLinearMap.id ℝ V))

omit [FiniteDimensional ℝ U] [FiniteDimensional ℝ V] in
@[simp] theorem graph_apply (G : U ≃L[ℝ] U) (H : V →L[ℝ] U) (v : V) :
    graph G H v = WithLp.toLp 2 (-G.symm (H v), v) := rfl

omit [FiniteDimensional ℝ U] [FiniteDimensional ℝ V] in
@[simp] theorem graph_observation (G : U ≃L[ℝ] U) (H : V →L[ℝ] U) (v : V) :
    observation G H (graph G H v) = 0 := by
  simp [observation_apply, graph_apply]

omit [FiniteDimensional ℝ U] [FiniteDimensional ℝ V] in
/-- The invertible block proves actual observation surjectivity. -/
theorem observation_surjective (G : U ≃L[ℝ] U) (H : V →L[ℝ] U) : Surjective (observation G H) := by
  intro w
  exact ⟨WithLp.toLp 2 (G.symm w, 0), by simp⟩

/-- The coefficient graph is the actual entire observation kernel. -/
def graphToKernel (G : U ≃L[ℝ] U) (H : V →L[ℝ] U) : V →L[ℝ] (observation G H).ker :=
  (graph G H).codRestrict _ (fun v => graph_observation G H v)

omit [FiniteDimensional ℝ U] [FiniteDimensional ℝ V] in
theorem graphToKernel_bijective (G : U ≃L[ℝ] U) (H : V →L[ℝ] U) :
    Bijective (graphToKernel G H) := by
  constructor
  · intro v w hv
    exact congrArg (fun z : (observation G H).ker => z.val.ofLp.2) hv
  · intro k
    refine ⟨k.val.ofLp.2, ?_⟩
    apply Subtype.ext
    apply (WithLp.equiv 2 (U × V)).injective
    apply Prod.ext
    · change -G.symm (H k.val.ofLp.2) = k.val.ofLp.1
      apply G.injective
      have hk : G k.val.ofLp.1 + H k.val.ofLp.2 = 0 := k.2
      simpa using (add_eq_zero_iff_eq_neg.mp hk).symm
    · rfl

/-- The actual coefficient graph parametrization as a continuous linear equivalence. -/
def graphEquiv (G : U ≃L[ℝ] U) (H : V →L[ℝ] U) : V ≃L[ℝ] (observation G H).ker :=
  (LinearEquiv.ofBijective (graphToKernel G H).toLinearMap
    (graphToKernel_bijective G H)).toContinuousLinearEquiv

omit [FiniteDimensional ℝ U] in
@[simp] theorem graphEquiv_coe (G : U ≃L[ℝ] U) (H : V →L[ℝ] U) (v : V) :
    (graphEquiv G H v : Coeff U V) = graph G H v := rfl

/-- Ordinary finite-dimensional determinant identity for rectangular compositions. -/
theorem det_id_add_comp_comm (C : V →L[ℝ] U) (D : U →L[ℝ] V) :
    (ContinuousLinearMap.id ℝ U + C.comp D).det =
      (ContinuousLinearMap.id ℝ V + D.comp C).det := by
  classical
  let b := stdOrthonormalBasis ℝ U
  let c := stdOrthonormalBasis ℝ V
  change LinearMap.det (LinearMap.id + C.toLinearMap.comp D.toLinearMap) =
    LinearMap.det (LinearMap.id + D.toLinearMap.comp C.toLinearMap)
  rw [← LinearMap.det_toMatrix b.toBasis, ← LinearMap.det_toMatrix c.toBasis,
    map_add, map_add, LinearMap.toMatrix_id, LinearMap.toMatrix_id,
    LinearMap.toMatrix_comp b.toBasis c.toBasis b.toBasis,
    LinearMap.toMatrix_comp c.toBasis b.toBasis c.toBasis]
  exact Matrix.det_one_add_mul_comm _ _

/-- The actual adjoint of the coefficient observation. -/
theorem observation_adjoint_apply (G : U ≃L[ℝ] U) (H : V →L[ℝ] U) (w : U) :
    (observation G H).adjoint w = WithLp.toLp 2 ((G : U →L[ℝ] U).adjoint w, H.adjoint w) := by
  apply ext_inner_right ℝ
  intro z
  rw [(observation G H).adjoint_inner_left, WithLp.prod_inner_apply]
  simp only [observation_apply, inner_add_right,
    ContinuousLinearMap.adjoint_inner_left, ContinuousLinearEquiv.coe_coe]

/-- The actual graph Gram operator. -/
theorem graph_adjoint_apply (G : U ≃L[ℝ] U) (H : V →L[ℝ] U) (z : Coeff U V) :
    (graph G H).adjoint z = -(slope G H).adjoint z.ofLp.1 + z.ofLp.2 := by
  apply ext_inner_right ℝ
  intro v
  rw [(graph G H).adjoint_inner_left, graph_apply, WithLp.prod_inner_apply]
  simp only [inner_add_left, inner_neg_left, inner_neg_right,
    ContinuousLinearMap.adjoint_inner_left, slope, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_comp]
  rfl

/-- The graph metric has Gram matrix I+C†C for the actual graph slope. -/
theorem graph_gram (G : U ≃L[ℝ] U) (H : V →L[ℝ] U) :
    (graph G H).adjoint.comp (graph G H) =
      ContinuousLinearMap.id ℝ V + (slope G H).adjoint.comp (slope G H) := by
  ext v
  simp [graph_adjoint_apply, graph_apply, slope, add_comm]

/-- The true observation covariance factors through its invertible block. -/
theorem observation_gram (G : U ≃L[ℝ] U) (H : V →L[ℝ] U) :
    GaussianRegression.gram (observation G H) =
      (G : U →L[ℝ] U).comp ((ContinuousLinearMap.id ℝ U +
        (slope G H).comp (slope G H).adjoint).comp (G : U →L[ℝ] U).adjoint) := by
  have hh : H = (G : U →L[ℝ] U).comp (slope G H) := by
    ext v
    simp [slope]
  ext w
  simp only [GaussianRegression.gram, ContinuousLinearMap.comp_apply, observation_adjoint_apply,
    observation_apply, add_apply, ContinuousLinearMap.id_apply,
    map_add]
  conv_lhs => rw [hh, ContinuousLinearMap.adjoint_comp]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]

/-- The exact graph metric determinant equals observation covariance divided
by the squared determinant of the chosen invertible coefficient block. -/
theorem observation_det_graph_gram (G : U ≃L[ℝ] U) (H : V →L[ℝ] U) :
    (GaussianRegression.gram (observation G H)).det =
      (G : U →L[ℝ] U).det ^ 2 * ((graph G H).adjoint.comp (graph G H)).det := by
  rw [observation_gram, ContinuousLinearMap.det, ContinuousLinearMap.toLinearMap_comp,
    ContinuousLinearMap.toLinearMap_comp, LinearMap.det_comp, LinearMap.det_comp]
  change (G : U →L[ℝ] U).det *
    ((ContinuousLinearMap.id ℝ U + (slope G H).comp (slope G H).adjoint).det *
      (G : U →L[ℝ] U).adjoint.det) = _
  rw [GaussianRegression.det_adjoint_real, det_id_add_comp_comm, ← graph_gram]
  ring

/-- Orthonormal coordinates for the actual coefficient kernel, derived from
its graph equivalence and the genuine finite-dimensional Hilbert structure. -/
def kernelIsometry (G : U ≃L[ℝ] U) (H : V →L[ℝ] U) :
    V ≃ₗᵢ[ℝ] (observation G H).ker :=
  ((stdOrthonormalBasis ℝ V).reindex (finCongr (graphEquiv G H).finrank_eq)).repr.trans
    (stdOrthonormalBasis ℝ (observation G H).ker).repr.symm

/-- Actual square-coordinate graph map, used to apply the ordinary Lebesgue Jacobian. -/
def squareGraph (G : U ≃L[ℝ] U) (H : V →L[ℝ] U) : V ≃L[ℝ] V :=
  (graphEquiv G H).trans (kernelIsometry G H).symm.toContinuousLinearEquiv

/-- Its ordinary square-map Gram is the actual embedded coefficient graph metric. -/
theorem squareGraph_gram (G : U ≃L[ℝ] U) (H : V →L[ℝ] U) :
    (squareGraph G H : V →L[ℝ] V).adjoint.comp (squareGraph G H : V →L[ℝ] V) =
      (graph G H).adjoint.comp (graph G H) := by
  ext v
  apply ext_inner_right ℝ
  intro w
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_left]
  change inner ℝ ((kernelIsometry G H).symm (graphEquiv G H v))
      ((kernelIsometry G H).symm (graphEquiv G H w)) = inner ℝ (graph G H v) (graph G H w)
  rw [(kernelIsometry G H).symm.inner_map_map]
  rfl

/-- The squared ordinary graph Jacobian is its actual metric determinant. -/
theorem squareGraph_det_sq (G : U ≃L[ℝ] U) (H : V →L[ℝ] U) :
    (squareGraph G H : V →L[ℝ] V).det ^ 2 = ((graph G H).adjoint.comp (graph G H)).det := by
  have h := congrArg ContinuousLinearMap.det (squareGraph_gram G H)
  rw [ContinuousLinearMap.det, ContinuousLinearMap.toLinearMap_comp, LinearMap.det_comp] at h
  change (squareGraph G H : V →L[ℝ] V).adjoint.det *
    (squareGraph G H : V →L[ℝ] V).det = _ at h
  rw [GaussianRegression.det_adjoint_real] at h
  simpa only [pow_two] using h

/-- The exact ordinary graph-fiber Jacobian required to convert a chosen
invertible coefficient block to the canonical orthogonal Gaussian fiber. -/
theorem graph_jacobian (G : U ≃L[ℝ] U) (H : V →L[ℝ] U) :
    |(squareGraph G H : V →L[ℝ] V).det| =
      Real.sqrt (GaussianRegression.gram (observation G H)).det / |(G : U →L[ℝ] U).det| := by
  have hd : (G : U →L[ℝ] U).det ≠ 0 := G.toLinearEquiv.isUnit_det'.ne_zero
  have h : Real.sqrt (GaussianRegression.gram (observation G H)).det =
      |(G : U →L[ℝ] U).det| * |(squareGraph G H : V →L[ℝ] V).det| := by
    rw [observation_det_graph_gram, ← squareGraph_det_sq,
      Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs, Real.sqrt_sq_eq_abs]
  rw [h]
  field_simp [hd]

variable [MeasurableSpace U] [BorelSpace U] [MeasurableSpace V] [BorelSpace V]

/-- The actual coefficient graph pushes Lebesgue measure to the kernel
volume with its proved ordinary Jacobian factor. -/
theorem graphEquiv_map_volume (G : U ≃L[ℝ] U) (H : V →L[ℝ] U) :
    (volume : Measure V).map (graphEquiv G H) =
      ENNReal.ofReal (|(squareGraph G H : V →L[ℝ] V).det|⁻¹) •
        (volume : Measure (observation G H).ker) := by
  have he : (graphEquiv G H : V → (observation G H).ker) =
      (kernelIsometry G H) ∘ (squareGraph G H) := by
    funext v
    exact ((kernelIsometry G H).apply_symm_apply (graphEquiv G H v)).symm
  have hs := Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure V)
    (squareGraph G H).toLinearEquiv.isUnit_det'.ne_zero
  simp only [LinearEquiv.coe_coe, ContinuousLinearEquiv.coe_toLinearEquiv] at hs
  rw [he, ← Measure.map_map (kernelIsometry G H).continuous.measurable
    (squareGraph G H).continuous.measurable, hs,
    Measure.map_smul _ (kernelIsometry G H).continuous.measurable.aemeasurable,
    (kernelIsometry G H).measurePreserving.map_eq]
  simp only [abs_inv, ContinuousLinearMap.det,
    ContinuousLinearEquiv.toLinearMap_toContinuousLinearMap]

/-- Actual graph-to-kernel change of variables for every nonnegative Borel
mark, preserving possibly infinite integrals. -/
theorem graph_lintegral (G : U ≃L[ℝ] U) (H : V →L[ℝ] U)
    (f : (observation G H).ker → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ k, f k ∂volume) = ENNReal.ofReal |(squareGraph G H : V →L[ℝ] V).det| *
      ∫⁻ v, f (graphEquiv G H v) ∂volume := by
  have hd : 0 < |(squareGraph G H : V →L[ℝ] V).det| :=
    abs_pos.mpr (squareGraph G H).toLinearEquiv.isUnit_det'.ne_zero
  rw [← lintegral_map hf (graphEquiv G H).continuous.measurable,
    graphEquiv_map_volume, lintegral_smul_measure]
  rw [smul_eq_mul, ← mul_assoc, ← ENNReal.ofReal_mul hd.le, mul_inv_cancel₀ hd.ne', ENNReal.ofReal_one, one_mul]

/-- Full Borel-mark conditional regression on the literal zero coefficient
graph, with the exact inverse determinant of the chosen first block. -/
theorem graph_weighted_zero_fiber (G : U ≃L[ℝ] U) (H : V →L[ℝ] U)
    (phi : Coeff U V → ℝ≥0∞) (hphi : Measurable phi) :
    ENNReal.ofReal |(G : U →L[ℝ] U).det|⁻¹ *
      (∫⁻ v, ENNReal.ofReal (GaussianDensity.density (graph G H v)) * phi (graph G H v) ∂volume) =
      GaussianRegression.observationPdf (observation G H) 0 *
        ∫⁻ z, phi z ∂GaussianRegression.regressionKernel (observation G H) 0 := by
  have hg : 0 < |(G : U →L[ℝ] U).det| := abs_pos.mpr G.toLinearEquiv.isUnit_det'.ne_zero
  have hd := GaussianRegression.gram_sqrt_det_pos (observation G H) (observation_surjective G H)
  let f : (observation G H).ker → ℝ≥0∞ :=
    fun k => ENNReal.ofReal (GaussianDensity.density (k : Coeff U V)) * phi (k : Coeff U V)
  have hf : Measurable f :=
    (GaussianDensity.density_continuous.measurable.comp measurable_subtype_coe).ennreal_ofReal.mul
      (hphi.comp measurable_subtype_coe)
  have h0 := GaussianRegression.weighted_affine_fiber_formula (observation G H)
    (observation_surjective G H) 0 phi hphi
  simp only [map_zero, add_zero] at h0
  have h1 := (graph_lintegral G H f hf).symm.trans h0
  simp only [f, graphEquiv_coe] at h1
  rw [graph_jacobian, div_eq_mul_inv, ENNReal.ofReal_mul hd.le] at h1
  rw [mul_assoc, mul_assoc] at h1
  exact (ENNReal.mul_right_inj (ENNReal.ofReal_pos.mpr hd).ne' ENNReal.ofReal_ne_top).mp h1

/-- Conditional regression at gradient zero, with the determinant factor
inside the genuine nonnegative graph integral used by the local incidence theorem. -/
theorem graph_weighted_zero_fiber_integral (G : U ≃L[ℝ] U) (H : V →L[ℝ] U)
    (phi : Coeff U V → ℝ≥0∞) (hphi : Measurable phi) :
    (∫⁻ v, ENNReal.ofReal (GaussianDensity.density (graph G H v)) *
      phi (graph G H v) / ENNReal.ofReal |(G : U →L[ℝ] U).det| ∂volume) =
      GaussianRegression.observationPdf (observation G H) 0 *
        ∫⁻ z, phi z ∂GaussianRegression.regressionKernel (observation G H) 0 := by
  have hg : 0 < |(G : U →L[ℝ] U).det| := abs_pos.mpr G.toLinearEquiv.isUnit_det'.ne_zero
  simp only [div_eq_mul_inv]
  rw [lintegral_mul_const' _ _ (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr hg).ne')]
  rw [mul_comm, ← ENNReal.ofReal_inv_of_pos hg]
  exact graph_weighted_zero_fiber G H phi hphi

end
end SlowEquilibration.GaussianBlockFiber
