-- SPDX-License-Identifier: Apache-2.0
module

public import Mathlib.Analysis.InnerProductSpace.Spectrum
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

@[expose] public section

/-! # Actual log-determinant bounds for a small symmetric perturbation -/
namespace SlowEquilibration.NearIdentityLogDeterminant
noncomputable section
open scoped BigOperators RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 500000

lemma abs_log_le_twice_of_near_one {x ε : ℝ}
    (hε : 0 ≤ ε) (hhalf : ε ≤ 1/2) (hx : |x-1| ≤ ε) :
    0 < x ∧ |Real.log x| ≤ 2*ε := by
  have hb := abs_le.mp hx
  have hpos : 0 < x := by linarith
  refine ⟨hpos,abs_le.mpr ⟨?_,?_⟩⟩
  · have hl := Real.one_sub_inv_le_log_of_pos hpos
    have hi : x⁻¹ ≤ 1+2*ε := by
      apply (inv_le_iff_one_le_mul₀ hpos).mpr
      have hp := mul_le_mul_of_nonneg_right (show 1-ε ≤ x by linarith)
        (show 0 ≤ 1+2*ε by linarith)
      nlinarith [mul_nonneg hε (show 0 ≤ 1-2*ε by linarith)]
    linarith
  · have hl := Real.log_le_sub_one_of_pos hpos
    linarith

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem det_positive_and_abs_log_le (C : E →L[ℝ] E)
    (hC : C.toLinearMap.IsSymmetric) {ε : ℝ} (hε : 0 ≤ ε)
    (hhalf : ε ≤ 1/2) (hbound : ‖C‖ ≤ ε) :
    0 < (ContinuousLinearMap.id ℝ E-C).det ∧
    |Real.log (ContinuousLinearMap.id ℝ E-C).det| ≤
      2*(Module.finrank ℝ E : ℝ)*ε := by
  let T : E →L[ℝ] E := ContinuousLinearMap.id ℝ E-C
  have hT : T.toLinearMap.IsSymmetric := by
    intro x y
    change inner ℝ (x-C x) y=inner ℝ x (y-C y)
    rw [inner_sub_left,inner_sub_right]
    exact congrArg (fun t => inner ℝ x y-t) (hC x y)
  let m := Module.finrank ℝ E
  let B := hT.eigenvectorBasis (show Module.finrank ℝ E=m from rfl)
  let eig := hT.eigenvalues (show Module.finrank ℝ E=m from rfl)
  have heig (i : Fin m) : |eig i-1| ≤ ε := by
    let v := B i
    have hv : ‖v‖=1 := B.norm_eq_one i
    have hTv : T v=eig i • v := hT.apply_eigenvectorBasis rfl i
    have hCv : C v=(1-eig i) • v := by
      change v-C v=eig i • v at hTv
      calc
        C v=v-(v-C v) := by abel
        _ = v-eig i • v := by rw [hTv]
        _ = _ := by module
    have hh := C.le_opNorm v
    rw [hCv,norm_smul,Real.norm_eq_abs,hv,mul_one,mul_one] at hh
    simpa only [abs_sub_comm] using hh.trans hbound
  have heig (i : Fin m) : 0 < eig i ∧ |Real.log (eig i)| ≤ 2*ε :=
    abs_log_le_twice_of_near_one hε hhalf (heig i)
  have hdet : T.det=∏ i : Fin m,eig i := hT.det_eq_prod_eigenvalues rfl
  have hpos : 0 < T.det := by
    rw [hdet]
    exact Finset.prod_pos (fun i _ => (heig i).1)
  refine ⟨hpos,?_⟩
  change |Real.log T.det| ≤ _
  rw [hdet,Real.log_prod (fun i _ => (heig i).1.ne')]
  calc
    _ ≤ ∑ i : Fin m,|Real.log (eig i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin m,2*ε := Finset.sum_le_sum (fun i _ => (heig i).2)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul];ring

end
end SlowEquilibration.NearIdentityLogDeterminant
