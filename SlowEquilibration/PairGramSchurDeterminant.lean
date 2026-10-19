-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianObservationCoercivity
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.LinearAlgebra.Basis.Prod

/-! Exact actual pair Gram blocks and their Schur determinant. -/
@[expose] public section
namespace SlowEquilibration.GaussianObservationCoercivity
noncomputable section
open Function Module GaussianRegression
open scoped RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 500000
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

abbrev gramPairBasis (b : OrthonormalBasis (Fin (Module.finrank ℝ F)) ℝ F) :
    Basis (Sum (Fin (Module.finrank ℝ F)) (Fin (Module.finrank ℝ F))) ℝ (WithLp 2 (F×F)) :=
  (b.toBasis.prod b.toBasis).map (WithLp.prodContinuousLinearEquiv 2 ℝ F F).symm.toLinearEquiv

omit [FiniteDimensional ℝ F] in
lemma gramPairBasis_repr_left (b : OrthonormalBasis (Fin (Module.finrank ℝ F)) ℝ F)
    (w : WithLp 2 (F×F)) (i : Fin (Module.finrank ℝ F)) :
    (gramPairBasis b).repr w (Sum.inl i)=b.repr w.fst i := by
  simp only [gramPairBasis,Basis.map_repr,LinearEquiv.trans_apply]
  rw [Basis.prod_repr_inl]
  rfl

omit [FiniteDimensional ℝ F] in
lemma gramPairBasis_repr_right (b : OrthonormalBasis (Fin (Module.finrank ℝ F)) ℝ F)
    (w : WithLp 2 (F×F)) (i : Fin (Module.finrank ℝ F)) :
    (gramPairBasis b).repr w (Sum.inr i)=b.repr w.snd i := by
  simp only [gramPairBasis,Basis.map_repr,LinearEquiv.trans_apply]
  rw [Basis.prod_repr_inr]
  rfl

omit [FiniteDimensional ℝ F] in
lemma gramPairBasis_apply_left (b : OrthonormalBasis (Fin (Module.finrank ℝ F)) ℝ F)
    (i : Fin (Module.finrank ℝ F)) : gramPairBasis b (Sum.inl i)=WithLp.toLp 2 (b i,0) := by
  simp only [gramPairBasis,Basis.map_apply,ContinuousLinearEquiv.coe_toLinearEquiv,
    WithLp.prodContinuousLinearEquiv_symm_apply]
  congr 1
  apply Prod.ext
  · exact Basis.prod_apply_inl_fst _ _ _
  · exact Basis.prod_apply_inl_snd _ _ _

omit [FiniteDimensional ℝ F] in
lemma gramPairBasis_apply_right (b : OrthonormalBasis (Fin (Module.finrank ℝ F)) ℝ F)
    (i : Fin (Module.finrank ℝ F)) : gramPairBasis b (Sum.inr i)=WithLp.toLp 2 (0,b i) := by
  simp only [gramPairBasis,Basis.map_apply,ContinuousLinearEquiv.coe_toLinearEquiv,
    WithLp.prodContinuousLinearEquiv_symm_apply]
  congr 1
  apply Prod.ext
  · exact Basis.prod_apply_inr_fst _ _ _
  · exact Basis.prod_apply_inr_snd _ _ _


lemma pair_gram_left (A B : E →L[ℝ] F) (w : WithLp 2 (F×F)) :
    (gram (pairHilbert A B) w).fst=gram A w.fst+(A.comp B.adjoint) w.snd := by
  rw [gram,ContinuousLinearMap.comp_apply,pairHilbert_adjoint]
  change A (A.adjoint w.fst+B.adjoint w.snd)=A (A.adjoint w.fst)+A (B.adjoint w.snd)
  rw [map_add]

lemma pair_gram_right (A B : E →L[ℝ] F) (w : WithLp 2 (F×F)) :
    (gram (pairHilbert A B) w).snd=(B.comp A.adjoint) w.fst+gram B w.snd := by
  rw [gram,ContinuousLinearMap.comp_apply,pairHilbert_adjoint]
  change B (A.adjoint w.fst+B.adjoint w.snd)=B (A.adjoint w.fst)+B (B.adjoint w.snd)
  rw [map_add]

/-- Literal diagonal/cross blocks of the true pair observation covariance. -/
theorem pair_gram_matrix (A B : E →L[ℝ] F)
    (b : OrthonormalBasis (Fin (Module.finrank ℝ F)) ℝ F) :
    LinearMap.toMatrix (gramPairBasis b) (gramPairBasis b) (gram (pairHilbert A B)).toLinearMap=
      Matrix.fromBlocks
        (LinearMap.toMatrix b.toBasis b.toBasis (gram A).toLinearMap)
        (LinearMap.toMatrix b.toBasis b.toBasis (A.comp B.adjoint).toLinearMap)
        (LinearMap.toMatrix b.toBasis b.toBasis (B.comp A.adjoint).toLinearMap)
        (LinearMap.toMatrix b.toBasis b.toBasis (gram B).toLinearMap) := by
  ext i j
  rw [LinearMap.toMatrix_apply]
  cases i with
  | inl i =>
    cases j with
    | inl j =>
      rw [gramPairBasis_apply_left,gramPairBasis_repr_left]
      rw [Matrix.fromBlocks_apply₁₁,LinearMap.toMatrix_apply]
      change b.repr ((gram (pairHilbert A B) (WithLp.toLp 2 (b j,0))).fst) i=b.repr (gram A (b j)) i
      rw [pair_gram_left]
      simp only [WithLp.toLp_fst,WithLp.toLp_snd,map_zero,add_zero]
    | inr j =>
      rw [gramPairBasis_apply_right,gramPairBasis_repr_left]
      rw [Matrix.fromBlocks_apply₁₂,LinearMap.toMatrix_apply]
      change b.repr ((gram (pairHilbert A B) (WithLp.toLp 2 (0,b j))).fst) i=b.repr ((A.comp B.adjoint) (b j)) i
      rw [pair_gram_left]
      simp only [WithLp.toLp_fst,WithLp.toLp_snd,map_zero,zero_add]
  | inr i =>
    cases j with
    | inl j =>
      rw [gramPairBasis_apply_left,gramPairBasis_repr_right]
      rw [Matrix.fromBlocks_apply₂₁,LinearMap.toMatrix_apply]
      change b.repr ((gram (pairHilbert A B) (WithLp.toLp 2 (b j,0))).snd) i=b.repr ((B.comp A.adjoint) (b j)) i
      rw [pair_gram_right]
      simp only [WithLp.toLp_fst,WithLp.toLp_snd,map_zero,add_zero]
    | inr j =>
      rw [gramPairBasis_apply_right,gramPairBasis_repr_right]
      rw [Matrix.fromBlocks_apply₂₂,LinearMap.toMatrix_apply]
      change b.repr ((gram (pairHilbert A B) (WithLp.toLp 2 (0,b j))).snd) i=b.repr (gram B (b j)) i
      rw [pair_gram_right]
      simp only [WithLp.toLp_fst,WithLp.toLp_snd,map_zero,zero_add]

/-- Exact quadratic cross-block Schur determinant for equal isotropic
marginal observations. This is a literal actual observation Gram identity. -/
theorem isotropic_pair_gram_det (A B : E →L[ℝ] F) {a : ℝ} (ha : a≠0)
    (hA : gram A=a • ContinuousLinearMap.id ℝ F)
    (hB : gram B=a • ContinuousLinearMap.id ℝ F) :
    (gram (pairHilbert A B)).det=
      a^(2*Module.finrank ℝ F)*
        (ContinuousLinearMap.id ℝ F-(a⁻¹^2) • ((B.comp A.adjoint).comp (A.comp B.adjoint))).det := by
  classical
  let b:=stdOrthonormalBasis ℝ F
  let U:=LinearMap.toMatrix b.toBasis b.toBasis (A.comp B.adjoint).toLinearMap
  let V:=LinearMap.toMatrix b.toBasis b.toBasis (B.comp A.adjoint).toLinearMap
  have hdiag : LinearMap.toMatrix b.toBasis b.toBasis (a • ContinuousLinearMap.id ℝ F).toLinearMap=
      a • (1 : Matrix (Fin (Module.finrank ℝ F)) (Fin (Module.finrank ℝ F)) ℝ) := by
    rw [ContinuousLinearMap.toLinearMap_smul,map_smul]
    simp only [ContinuousLinearMap.coe_id,LinearMap.toMatrix_id]
  have hmat:=pair_gram_matrix A B b
  rw [hA,hB,hdiag] at hmat
  have hfactor : Matrix.fromBlocks (a • 1) U V (a • 1)=
      a • Matrix.fromBlocks 1 (a⁻¹ • U) (a⁻¹ • V) 1 := by
    ext i j
    cases i <;> cases j <;> simp [Matrix.fromBlocks,smul_eq_mul,ha]
  have hbody : (1 : Matrix (Fin (Module.finrank ℝ F)) (Fin (Module.finrank ℝ F)) ℝ)-
      (a⁻¹ • V)*(a⁻¹ • U)=
      LinearMap.toMatrix b.toBasis b.toBasis
        (ContinuousLinearMap.id ℝ F-a⁻¹^2 • ((B.comp A.adjoint).comp (A.comp B.adjoint))).toLinearMap := by
    rw [ContinuousLinearMap.toLinearMap_sub,map_sub,ContinuousLinearMap.coe_id,LinearMap.toMatrix_id,
      ContinuousLinearMap.toLinearMap_smul,map_smul,ContinuousLinearMap.toLinearMap_comp,
      LinearMap.toMatrix_comp b.toBasis b.toBasis b.toBasis]
    change 1-(a⁻¹ • V)*(a⁻¹ • U)=1-a⁻¹^2 • (V*U)
    rw [Matrix.smul_mul,Matrix.mul_smul,smul_smul,pow_two]
  rw [ContinuousLinearMap.det,← LinearMap.det_toMatrix (gramPairBasis b),hmat,hfactor,Matrix.det_smul,
    Matrix.det_fromBlocks_one₁₁,hbody,LinearMap.det_toMatrix]
  simp only [Fintype.card_sum,Fintype.card_fin]
  congr 2
  omega

end
end SlowEquilibration.GaussianObservationCoercivity
