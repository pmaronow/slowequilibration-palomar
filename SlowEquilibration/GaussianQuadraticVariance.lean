-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianDiagonalQuadraticVariance
public import Mathlib.LinearAlgebra.Trace

/-! Actual finite-dimensional Gaussian quadratic-form variance bound,
derived from the spectral theorem and exact product Hermite second moments. -/
@[expose] public section
namespace SlowEquilibration.GaussianQuadraticVariance
noncomputable section
open Function MeasureTheory ProbabilityTheory OAI.MinUncut.GaussianHermite
open scoped RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def quadraticMean (S : E →L[ℝ] E) (hS : S.toLinearMap.IsSymmetric) : ℝ :=
  ∑ i : Fin (Module.finrank ℝ E),hS.eigenvalues rfl i

omit [MeasurableSpace E] [BorelSpace E] in
lemma quadraticMean_eq_trace (S : E →L[ℝ] E) (hS : S.toLinearMap.IsSymmetric) :
    quadraticMean S hS=LinearMap.trace ℝ E S.toLinearMap := by
  rw [LinearMap.trace_eq_matrix_trace ℝ (hS.eigenvectorBasis rfl).toBasis,
    hS.toMatrix_eigenvectorBasis rfl,Matrix.trace_diagonal]
  simp only [quadraticMean,Function.comp_def,RCLike.ofReal_real_eq_id,id_eq]

def centeredQuadratic (S : E →L[ℝ] E) (hS : S.toLinearMap.IsSymmetric) (x : E) : ℝ :=
  inner ℝ x (S x)-quadraticMean S hS

lemma centeredQuadratic_measurable (S : E →L[ℝ] E) (hS : S.toLinearMap.IsSymmetric) :
    Measurable (centeredQuadratic S hS) :=
  (continuous_id.inner S.continuous).measurable.sub_const _

omit [MeasurableSpace E] [BorelSpace E] in
lemma centeredQuadratic_eigen_coordinates (S : E →L[ℝ] E) (hS : S.toLinearMap.IsSymmetric)
    (z : Fin (Module.finrank ℝ E) → ℝ) :
    centeredQuadratic S hS ((hS.eigenvectorBasis rfl).repr.symm (WithLp.toLp 2 z))=
      diagonalQuadratic (hS.eigenvalues rfl) z := by
  let B:=hS.eigenvectorBasis (show Module.finrank ℝ E=Module.finrank ℝ E from rfl)
  let x:=B.repr.symm (WithLp.toLp 2 z)
  have hrepr (i : Fin (Module.finrank ℝ E)) : B.repr (S x) i=hS.eigenvalues rfl i*z i := by
    change (hS.eigenvectorBasis rfl).repr (S.toLinearMap x) i=_
    rw [hS.eigenvectorBasis_apply_self_apply rfl]
    simp only [x,B,LinearIsometryEquiv.apply_symm_apply,PiLp.toLp_apply,RCLike.ofReal_real_eq_id,id_eq]
  change inner ℝ x (S x)-∑ i,hS.eigenvalues rfl i=∑ i,hS.eigenvalues rfl i*(z i^2-1)
  rw [← B.repr.inner_map_map x (S x)]
  simp only [PiLp.inner_apply,RCLike.inner_apply,conj_trivial,hrepr]
  have hx (i : Fin (Module.finrank ℝ E)) : B.repr x i=z i := by
    simp only [x,LinearIsometryEquiv.apply_symm_apply,PiLp.toLp_apply]
  simp only [hx,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- Genuine exact mean and variance of the actual standard-Gaussian
quadratic form; its variance is at most 2 dim(E) times the squared norm. -/
theorem standard_gaussian_quadratic_variance (S : E →L[ℝ] E) (hS : S.toLinearMap.IsSymmetric) :
    MemLp (centeredQuadratic S hS) 2 (stdGaussian E) ∧
      (∫ x,centeredQuadratic S hS x ∂stdGaussian E)=0 ∧
      (∫ x,centeredQuadratic S hS x^2 ∂stdGaussian E)=
        2*∑ i : Fin (Module.finrank ℝ E),hS.eigenvalues rfl i^2 ∧
      (∫ x,centeredQuadratic S hS x^2 ∂stdGaussian E) ≤
        2*(Module.finrank ℝ E:ℝ)*‖S‖^2 := by
  let B:=hS.eigenvectorBasis (show Module.finrank ℝ E=Module.finrank ℝ E from rfl)
  let R : (Fin (Module.finrank ℝ E) → ℝ) → E:=fun z=>B.repr.symm (WithLp.toLp 2 z)
  have hm : Measurable R:=B.repr.symm.continuous.measurable.comp (WithLp.measurable_toLp 2 _)
  have hmap : (γpi (Fin (Module.finrank ℝ E))).map R=stdGaussian E := by
    rw [← stdGaussian_map B.repr.symm,← map_pi_eq_stdGaussian,
      Measure.map_map B.repr.symm.continuous.measurable (WithLp.measurable_toLp 2 _)]
    rfl
  have hcoords : (centeredQuadratic S hS) ∘ R=diagonalQuadratic (hS.eigenvalues rfl) := by
    funext z
    exact centeredQuadratic_eigen_coordinates S hS z
  have hLp : MemLp (centeredQuadratic S hS) 2 (stdGaussian E) := by
    rw [← hmap]
    exact (memLp_map_measure_iff (centeredQuadratic_measurable S hS).aestronglyMeasurable hm.aemeasurable).mpr
      (by rw [hcoords];exact diagonalQuadratic_memLp _)
  have hmean : (∫ x,centeredQuadratic S hS x ∂stdGaussian E)=0 := by
    rw [← hmap,integral_map hm.aemeasurable (centeredQuadratic_measurable S hS).aestronglyMeasurable]
    change (∫ z,((centeredQuadratic S hS) ∘ R) z ∂γpi _)=0
    rw [hcoords,diagonalQuadratic_mean]
  have hsq : (∫ x,centeredQuadratic S hS x^2 ∂stdGaussian E)=
      2*∑ i : Fin (Module.finrank ℝ E),hS.eigenvalues rfl i^2 := by
    rw [← hmap,integral_map hm.aemeasurable ((centeredQuadratic_measurable S hS).pow_const 2).aestronglyMeasurable]
    simp only [R,B,centeredQuadratic_eigen_coordinates,diagonalQuadratic_second_moment]
  refine ⟨hLp,hmean,hsq,?_⟩
  rw [hsq]
  have heig (i : Fin (Module.finrank ℝ E)) : |hS.eigenvalues rfl i| ≤ ‖S‖ := by
    have hnorm:=S.le_opNorm (B i)
    have hSv : S (B i)=hS.eigenvalues rfl i • B i := hS.apply_eigenvectorBasis rfl i
    rw [hSv,norm_smul,Real.norm_eq_abs,B.norm_eq_one i,mul_one,mul_one] at hnorm
    exact hnorm
  calc
    _ ≤ 2*∑ _i : Fin (Module.finrank ℝ E),‖S‖^2 := by
      apply mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i hi=>?_)) (by norm_num)
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).mpr (heig i)
    _=_ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul];ring

end
end SlowEquilibration.GaussianQuadraticVariance
