-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalPairBorderedFrame
public import SlowEquilibration.IntrinsicHessianLaw
public import SlowEquilibration.OneBorderMoments
public import SlowEquilibration.CommonHessianPosteriorBorder

/-! The actual full intrinsic Hessian is a genuine one-border matrix in
the complete geometric tangent basis; no matrix-law surrogate is used. -/
@[expose] public section
namespace SlowEquilibration.SphericalPairCommonFrame
noncomputable section
open Function MeasureTheory ProbabilityTheory SphericalModel SphericalGaussianJet SphericalForm
open IntrinsicHessianLaw SphereHessian SphericalCommonHessianRegression WholeFieldRegression
open scoped RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

def borderIndexEquiv (n : ℕ) : Unit⊕Fin n ≃ Fin (n+1) where
  toFun i:=Sum.elim (fun _=>0) Fin.succ i
  invFun i:=Fin.cases (Sum.inl ()) (fun j=>Sum.inr j) i
  left_inv i:=by cases i with | inl i=>cases i;rfl | inr i=>rfl
  right_inv i:=by refine Fin.cases ?_ (fun i=>?_) i <;> rfl

/-- Intrinsic Hessian coordinate identity in any actual complete tangent
orthonormal basis; completeness is carried by OrthonormalBasis. -/
theorem intrinsicHessian_toMatrix_basis {N P m : ℕ}
    (hN : N≠0) (c : Degree P → ℝ) (J : Disorder N P) (x : Vector N) (hx : ‖x‖^2=(N:ℝ))
    (B : OrthonormalBasis (Fin m) ℝ (tangentPlane x)) :
    LinearMap.toMatrix B.toBasis B.toBasis (intrinsicHessian (field c J) x).toLinearMap=
      hessianMatrix c x (fun i=>(B i:Vector N)) J-radialMultiplier (field c J) x • (1:Matrix (Fin m) (Fin m) ℝ) := by
  have hsphere : SphericalAging.HardSphereDynamics.OnSphere x := by
    change inner ℝ x x=_
    rw [real_inner_self_eq_norm_sq]
    exact hx
  ext i j
  rw [LinearMap.toMatrix_apply]
  change B.repr (intrinsicHessian (field c J) x (B j)) i=_
  rw [OrthonormalBasis.repr_apply_apply,real_inner_comm,
    intrinsicHessian_frame_entry hN c J x hsphere B j i,
    orthonormal_iff_ite.mp B.orthonormal]
  simp only [Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul,Matrix.one_apply,hessianMatrix]
  rw [hessianEntry_symm c x (fun a=>(B a:Vector N)) j i]
  simp only [radialMultiplier_eq_jet,eq_comm]

lemma borderedTangentBasis_coe {n : ℕ} (x y : Vector (n+2))
    (hx : ‖x‖^2=(n+2:ℕ)) (hy : ‖y‖^2=(n+2:ℕ)) (hr : |overlap x y| < 1)
    (i : Fin (n+1)) :
    (borderedTangentBasis x y hx hy hr i:Vector (n+2))=borderedFrame x y hx hy hr i := by
  simp only [borderedTangentBasis,OrthonormalBasis.coe_mk,borderedTangentVector]

/-- Exact full Hessian reindexing into plane/common blocks. Both border
row and corner are literal derivatives of the same original disorder. -/
theorem full_shifted_hessian_eq_border {n P : ℕ} (c : Degree P → ℝ)
    (J : Disorder (n+2) P) (x y : Vector (n+2))
    (hx : ‖x‖^2=(n+2:ℕ)) (hy : ‖y‖^2=(n+2:ℕ)) (hr : |overlap x y| < 1) (k : ℝ) :
    Matrix.reindex (borderIndexEquiv n).symm (borderIndexEquiv n).symm
      (k • (1:Matrix (Fin (n+1)) (Fin (n+1)) ℝ)-hessianMatrix c x (borderedFrame x y hx hy hr) J)=
    GOEBorderedDeterminant.border
      (k-jet c 2 x ![planeDirection x y,planeDirection x y] J)
      (fun i=>-jet c 2 x ![commonFrame (by omega) x y hx hy hr i,planeDirection x y] J)
      (fun i=>-jet c 2 x ![commonFrame (by omega) x y hx hy hr i,planeDirection x y] J)
      (k • (1:Matrix (Fin n) (Fin n) ℝ)-hessianMatrix (k:=n) c x (commonFrame (by omega) x y hx hy hr) J) := by
  ext i j
  cases i with
  | inl i=>
    cases i
    cases j with
    | inl j=>cases j;simp [Matrix.reindex_apply,borderIndexEquiv,GOEBorderedDeterminant.border,
        borderedFrame,hessianMatrix,hessianEntry]
    | inr j=>
      have hs:=hessianEntry_symm c x (borderedFrame x y hx hy hr) 0 j.succ J
      have hz : (0:Fin (n+1))≠j.succ:=(Fin.succ_ne_zero j).symm
      simpa [hz,Matrix.reindex_apply,borderIndexEquiv,GOEBorderedDeterminant.border,
        borderedFrame,hessianMatrix,hessianEntry,Matrix.one_apply] using congrArg Neg.neg hs
  | inr i=>
    cases j with
    | inl j=>cases j;simp [Matrix.reindex_apply,borderIndexEquiv,GOEBorderedDeterminant.border,
        borderedFrame,hessianMatrix,hessianEntry]
    | inr j=>simp [Matrix.reindex_apply,borderIndexEquiv,GOEBorderedDeterminant.border,
        borderedFrame,hessianMatrix,hessianEntry,Matrix.one_apply]

end
end SlowEquilibration.SphericalPairCommonFrame

