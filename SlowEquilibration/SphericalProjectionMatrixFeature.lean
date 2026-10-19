-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.PureTensorJetFeatures
public import SlowEquilibration.SphericalForm

/-! Literal Hilbert coefficient feature of Π_x. Its norm and increments
are computed from original coordinate entries, for use in higher projected
trace Gaussian comparison without a supplied covariance or supremum bound. -/

@[expose] public section
namespace SlowEquilibration.SphericalProjectionMatrixFeature
noncomputable section
open SphericalAging.FiniteModel
open scoped RealInnerProductSpace BigOperators
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def outerFeature {N : ℕ} (u v : Vector N) : EuclideanSpace ℝ (Fin N × Fin N) :=
  WithLp.toLp 2 (fun ij => u ij.1*v ij.2)

theorem outerFeature_inner {N : ℕ} (u v w z : Vector N) :
    inner ℝ (outerFeature u v) (outerFeature w z)=inner ℝ u w*inner ℝ v z := by
  simp only [PiLp.inner_apply,RCLike.inner_apply,conj_trivial,outerFeature,
    Fintype.sum_prod_type]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem outerFeature_norm {N : ℕ} (u v : Vector N) :
    ‖outerFeature u v‖=‖u‖*‖v‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp
  rw [←real_inner_self_eq_norm_sq,outerFeature_inner,real_inner_self_eq_norm_sq,
    real_inner_self_eq_norm_sq,mul_pow]

def identityFeature (N : ℕ) : EuclideanSpace ℝ (Fin N × Fin N) :=
  WithLp.toLp 2 (fun ij => if ij.1=ij.2 then 1 else 0)

theorem identityFeature_inner (N : ℕ) :
    inner ℝ (identityFeature N) (identityFeature N)=(N : ℝ) := by
  classical
  simp only [identityFeature,PiLp.inner_apply,RCLike.inner_apply,conj_trivial,
    Fintype.sum_prod_type]
  simp

theorem identityFeature_outer_inner {N : ℕ} (u v : Vector N) :
    inner ℝ (identityFeature N) (outerFeature u v)=inner ℝ u v := by
  classical
  simp only [PiLp.inner_apply,RCLike.inner_apply,conj_trivial,identityFeature,outerFeature,
    Fintype.sum_prod_type]
  simp only [mul_ite,mul_one,mul_zero,Fintype.sum_ite_eq]
  apply Finset.sum_congr rfl
  intro i hi
  ring

def projectionMatrixFeature {N : ℕ} (x : Vector N) : EuclideanSpace ℝ (Fin N × Fin N) :=
  identityFeature N-(N : ℝ)⁻¹ • outerFeature x x

/-- Exactly the actual spherical projection matrix, on original coordinate slots. -/
theorem projectionMatrixFeature_apply {N : ℕ} (x : Vector N) (i j : Fin N) :
    projectionMatrixFeature x (i,j)=(if i=j then 1 else 0)-x i*x j/(N : ℝ) := by
  simp only [projectionMatrixFeature,identityFeature,outerFeature,PiLp.sub_apply,
    PiLp.smul_apply,smul_eq_mul]
  ring

/-- Exact coefficient-space covariance of two actual spherical projection matrices. -/
theorem projectionMatrixFeature_inner {N : ℕ} (x y : Vector N) :
    inner ℝ (projectionMatrixFeature x) (projectionMatrixFeature y)=
      (N : ℝ)-‖x‖^2/(N : ℝ)-‖y‖^2/(N : ℝ)+(inner ℝ x y)^2/(N : ℝ)^2 := by
  have hcross : inner ℝ (outerFeature x x) (identityFeature N)=‖x‖^2 := by
    rw [real_inner_comm,identityFeature_outer_inner,real_inner_self_eq_norm_sq]
  have hdiag : ‖identityFeature N‖^2=(N : ℝ) := by
    rw [←real_inner_self_eq_norm_sq,identityFeature_inner]
  unfold projectionMatrixFeature
  simp only [inner_sub_left,inner_sub_right,real_inner_smul_right,
    real_inner_smul_left,identityFeature_outer_inner,hcross,hdiag,
    outerFeature_inner,real_inner_self_eq_norm_sq]

  ring

/-- A paired projection block annihilates the actual value direction
and every one-gradient replacement at the same physical axis. -/
theorem projectionMatrixFeature_outer_axis_inner {N : ℕ} (hN : 0 < N)
    (x z : Vector N) (hx : ‖x‖^2=(N : ℝ)) :
    inner ℝ (projectionMatrixFeature x) (outerFeature x z)=0 := by
  unfold projectionMatrixFeature
  rw [inner_sub_left,real_inner_smul_left,identityFeature_outer_inner,
    outerFeature_inner,real_inner_self_eq_norm_sq,hx]
  field_simp [show (N : ℝ)≠0 from (Nat.cast_pos.mpr hN).ne']
  ring

/-- The other original ordered slot has the same exact annihilation. -/
theorem projectionMatrixFeature_outer_axis_inner_right {N : ℕ} (hN : 0 < N)
    (x z : Vector N) (hx : ‖x‖^2=(N : ℝ)) :
    inner ℝ (projectionMatrixFeature x) (outerFeature z x)=0 := by
  unfold projectionMatrixFeature
  rw [inner_sub_left,real_inner_smul_left,identityFeature_outer_inner,
    outerFeature_inner,real_inner_self_eq_norm_sq,hx,real_inner_comm z x]
  field_simp [show (N : ℝ)≠0 from (Nat.cast_pos.mpr hN).ne']
  ring

/-- The true Hilbert-Schmidt size is sqrt(N−1) on the actual sphere. -/
theorem projectionMatrixFeature_norm_sq {N : ℕ} (hN : 0 < N) (x : Vector N)
    (hx : ‖x‖^2=(N : ℝ)) : ‖projectionMatrixFeature x‖^2=(N : ℝ)-1 := by
  rw [←real_inner_self_eq_norm_sq,projectionMatrixFeature_inner,real_inner_self_eq_norm_sq,hx]
  field_simp [show (N : ℝ)≠0 from (Nat.cast_pos.mpr hN).ne']
  ring

theorem outerFeature_sub_diagonal {N : ℕ} (x y : Vector N) :
    outerFeature x x-outerFeature y y=outerFeature (x-y) x+outerFeature y (x-y) := by
  ext ij
  simp only [outerFeature,PiLp.sub_apply,PiLp.add_apply]
  ring

theorem outerFeature_sub_diagonal_norm_le {N : ℕ} (x y : Vector N) :
    ‖outerFeature x x-outerFeature y y‖ ≤ (‖x‖+‖y‖)*‖x-y‖ := by
  rw [outerFeature_sub_diagonal]
  apply (norm_add_le _ _).trans_eq
  rw [outerFeature_norm,outerFeature_norm]
  ring

/-- Genuine physical chord-distance cost of moving Π_x, in its original
matrix coefficient Hilbert norm. -/
theorem projectionMatrixFeature_increment_le {N : ℕ} (hN : 0 < N) (x y : Vector N)
    (hx : ‖x‖^2=(N : ℝ)) (hy : ‖y‖^2=(N : ℝ)) :
    ‖projectionMatrixFeature x-projectionMatrixFeature y‖ ≤
      (2/Real.sqrt N)*‖x-y‖ := by
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hs : Real.sqrt (N : ℝ)≠0 := (Real.sqrt_pos.mpr hNr).ne'
  have hxn := SphericalAging.LandscapeDerivatives.sphere_norm x hx
  have hyn := SphericalAging.LandscapeDerivatives.sphere_norm y hy
  have he : projectionMatrixFeature x-projectionMatrixFeature y=
      -(N : ℝ)⁻¹ • (outerFeature x x-outerFeature y y) := by
    unfold projectionMatrixFeature
    module
  rw [he,norm_smul,Real.norm_eq_abs,abs_neg,abs_inv,abs_of_pos hNr]
  apply (mul_le_mul_of_nonneg_left (outerFeature_sub_diagonal_norm_le x y) (inv_nonneg.mpr hNr.le)).trans_eq
  rw [hxn,hyn]
  have hcoef : (N : ℝ)⁻¹*(Real.sqrt N+Real.sqrt N)=2/Real.sqrt N := by
    field_simp [hNr.ne',hs]
    nlinarith [Real.sq_sqrt hNr.le]
  rw [←mul_assoc,hcoef]

end
end SlowEquilibration.SphericalProjectionMatrixFeature
