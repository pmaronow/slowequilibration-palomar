-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.NearIdentityLogDeterminant
public import Mathlib.Analysis.InnerProductSpace.Trace

@[expose] public section

/-! The log determinant of a positive Schur correction is controlled by
its actual trace, rather than the dimension times its operator norm. -/
namespace SlowEquilibration.NearIdentityLogDeterminant
noncomputable section
open scoped BigOperators RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 700000

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem det_positive_and_abs_log_le_trace (C : E →L[ℝ] E)
    (hC : C.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E, 0 ≤ inner ℝ v (C v)) (hbound : ‖C‖ ≤ 1/2) :
    0 < (ContinuousLinearMap.id ℝ E-C).det ∧
    |Real.log (ContinuousLinearMap.id ℝ E-C).det| ≤
      2*LinearMap.trace ℝ E C.toLinearMap := by
  let T : E →L[ℝ] E := ContinuousLinearMap.id ℝ E-C
  have hT : T.toLinearMap.IsSymmetric := by
    intro x y
    change inner ℝ (x-C x) y=inner ℝ x (y-C y)
    rw [inner_sub_left,inner_sub_right]
    exact congrArg (fun t => inner ℝ x y-t) (hC x y)
  let m := Module.finrank ℝ E
  let B := hT.eigenvectorBasis (show Module.finrank ℝ E=m from rfl)
  let eig := hT.eigenvalues (show Module.finrank ℝ E=m from rfl)
  have hCv (i : Fin m) : C (B i)=(1-eig i) • B i := by
    have hTv := hT.apply_eigenvectorBasis rfl i
    change B i-C (B i)=eig i • B i at hTv
    calc
      C (B i)=B i-(B i-C (B i)) := by abel
      _ = B i-eig i • B i := by rw [hTv]
      _ = _ := by module
  have hinner (i : Fin m) : inner ℝ (B i) (C (B i))=1-eig i := by
    rw [hCv,inner_smul_right,real_inner_self_eq_norm_sq,B.norm_eq_one]
    simp
  have heps (i : Fin m) : 0 ≤ 1-eig i ∧ 1-eig i ≤ 1/2 := by
    have hp := hpos (B i)
    rw [hinner] at hp
    have hh := C.le_opNorm (B i)
    rw [hCv,norm_smul,Real.norm_eq_abs,B.norm_eq_one,mul_one,mul_one,
      abs_of_nonneg hp] at hh
    exact ⟨hp,hh.trans hbound⟩
  have heig (i : Fin m) : 0 < eig i ∧ |Real.log (eig i)| ≤ 2*(1-eig i) := by
    apply abs_log_le_twice_of_near_one (heps i).1 (heps i).2
    rw [abs_sub_comm,abs_of_nonneg (heps i).1]
  have hdet : T.det=∏ i : Fin m,eig i := hT.det_eq_prod_eigenvalues rfl
  have ht : LinearMap.trace ℝ E C.toLinearMap=∑ i : Fin m,(1-eig i) := by
    rw [LinearMap.trace_eq_sum_inner _ B]
    exact Finset.sum_congr rfl (fun i _ => hinner i)
  refine ⟨?_,?_⟩
  · rw [show (ContinuousLinearMap.id ℝ E-C).det=T.det from rfl,hdet]
    exact Finset.prod_pos (fun i _ => (heig i).1)
  · change |Real.log T.det| ≤ _
    rw [hdet,Real.log_prod (fun i _ => (heig i).1.ne'),ht]
    calc
      _ ≤ ∑ i : Fin m,|Real.log (eig i)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i : Fin m,2*(1-eig i) := Finset.sum_le_sum (fun i _ => (heig i).2)
      _ = _ := (Finset.mul_sum _ _ _).symm

theorem positive_schur_det_and_log_bound {ι : Type*} [Fintype ι]
    (B : OrthonormalBasis ι ℝ E) (T : E →L[ℝ] E) {a : ℝ}
    (ha : 0 < a) (hT : ‖T‖ ≤ a/2) :
    0 < (ContinuousLinearMap.id ℝ E-(a⁻¹)^2 • T.adjoint.comp T).det ∧
    |Real.log (ContinuousLinearMap.id ℝ E-(a⁻¹)^2 • T.adjoint.comp T).det| ≤
      (2/a^2)*(∑ i,‖T (B i)‖^2) := by
  let C : E →L[ℝ] E := (a⁻¹)^2 • T.adjoint.comp T
  have hC : C.toLinearMap.IsSymmetric := by
    intro x y
    change inner ℝ ((a⁻¹)^2 • T.adjoint (T x)) y=
      inner ℝ x ((a⁻¹)^2 • T.adjoint (T y))
    rw [inner_smul_left,inner_smul_right,T.adjoint_inner_left,T.adjoint_inner_right]
    simp only [conj_trivial]
  have hpositive (v : E) : 0 ≤ inner ℝ v (C v) := by
    change 0 ≤ inner ℝ v ((a⁻¹)^2 • T.adjoint (T v))
    rw [inner_smul_right,T.adjoint_inner_right,real_inner_self_eq_norm_sq]
    positivity
  have hnorm : ‖C‖ ≤ 1/2 := by
    change ‖(a⁻¹)^2 • T.adjoint.comp T‖ ≤ _
    rw [norm_smul,Real.norm_of_nonneg (sq_nonneg _),ContinuousLinearMap.norm_adjoint_comp_self,← pow_two]
    have hsq : ‖T‖^2 ≤ (a/2)^2 := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hT
    calc
      _ ≤ (a⁻¹)^2*(a/2)^2 := mul_le_mul_of_nonneg_left hsq (sq_nonneg _)
      _ = 1/4 := by field_simp [ha.ne'];ring
      _ ≤ _ := by norm_num
  have htrace : LinearMap.trace ℝ E C.toLinearMap=(a⁻¹)^2*(∑ i,‖T (B i)‖^2) := by
    rw [LinearMap.trace_eq_sum_inner _ B,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    change inner ℝ (B i) ((a⁻¹)^2 • T.adjoint (T (B i)))=_
    rw [inner_smul_right,T.adjoint_inner_right,real_inner_self_eq_norm_sq]
  have h := det_positive_and_abs_log_le_trace C hC hpositive hnorm
  refine ⟨h.1,h.2.trans_eq ?_⟩
  rw [htrace]
  field_simp

end
end SlowEquilibration.NearIdentityLogDeterminant
