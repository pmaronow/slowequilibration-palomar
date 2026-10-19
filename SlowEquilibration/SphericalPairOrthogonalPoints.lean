-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalPairCommonFrame

/-! Explicit orthogonal sphere points at every relevant ambient dimension. -/
@[expose] public section
namespace SlowEquilibration.SphericalPairCommonFrame
noncomputable section
open SphericalModel
open scoped RealInnerProductSpace

def coordinateSpherePoint (N : ℕ) (i : Fin N) : Vector N :=
  Real.sqrt (N:ℝ) • EuclideanSpace.basisFun (Fin N) ℝ i

lemma coordinateSpherePoint_norm_sq (N : ℕ) (i : Fin N) :
    ‖coordinateSpherePoint N i‖^2=(N:ℝ) := by
  rw [coordinateSpherePoint,norm_smul,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),
    (EuclideanSpace.basisFun (Fin N) ℝ).orthonormal.norm_eq_one,mul_one,Real.sq_sqrt (Nat.cast_nonneg _)]

lemma coordinateSpherePoint_overlap_zero (N : ℕ) (i j : Fin N) (hij : i≠j) :
    overlap (coordinateSpherePoint N i) (coordinateSpherePoint N j)=0 := by
  unfold overlap coordinateSpherePoint
  rw [real_inner_smul_left,real_inner_smul_right,
    orthonormal_iff_ite.mp (EuclideanSpace.basisFun (Fin N) ℝ).orthonormal,if_neg hij]
  simp

lemma exists_orthogonal_sphere_pair (n : ℕ) :
    ∃ x y : Vector (n+3),‖x‖^2=(n+3:ℕ) ∧ ‖y‖^2=(n+3:ℕ) ∧ |overlap x y|<1 := by
  let i : Fin (n+3):=⟨0,by omega⟩
  let j : Fin (n+3):=⟨1,by omega⟩
  have hij : i≠j:=by intro h;have := congrArg Fin.val h;norm_num [i,j] at this
  refine ⟨coordinateSpherePoint (n+3) i,coordinateSpherePoint (n+3) j,
    coordinateSpherePoint_norm_sq _ _,coordinateSpherePoint_norm_sq _ _,?_⟩
  rw [coordinateSpherePoint_overlap_zero _ _ _ hij]
  norm_num

end
end SlowEquilibration.SphericalPairCommonFrame
