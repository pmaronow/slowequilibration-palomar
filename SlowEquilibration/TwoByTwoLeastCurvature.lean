-- SPDX-License-Identifier: Apache-2.0
module
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Tactic

/-! The actual least curvature of a positive symmetric two-by-two quadratic
form, including an attaining eigenvector and its Schur-complement bound. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.TwoByTwoLeastCurvature
set_option maxHeartbeats 300000

def least (A B C : ℝ) : ℝ := (A+C-Real.sqrt ((A-C)^2+4*B^2))/2
def quadratic (A B C e k : ℝ) : ℝ := A*e^2+2*B*e*k+C*k^2

theorem least_equation (A B C : ℝ) :
    (least A B C)^2-(A+C)*least A B C+A*C-B^2=0 := by
  have hs := Real.sq_sqrt (by positivity : 0 ≤ (A-C)^2+4*B^2)
  unfold least
  nlinarith

theorem least_le_diagonal (A B C : ℝ) : least A B C ≤ A ∧ least A B C ≤ C := by
  have hs := Real.sq_sqrt (by positivity : 0 ≤ (A-C)^2+4*B^2)
  have hn := Real.sqrt_nonneg ((A-C)^2+4*B^2)
  unfold least
  constructor <;> nlinarith [sq_nonneg B]

theorem least_lt_first {A B C : ℝ} (hB : B ≠ 0) : least A B C < A := by
  have hs := Real.sq_sqrt (by positivity : 0 ≤ (A-C)^2+4*B^2)
  have hn := Real.sqrt_nonneg ((A-C)^2+4*B^2)
  have hb := sq_pos_of_ne_zero hB
  unfold least
  nlinarith

theorem least_pos {A B C : ℝ} (hA : 0 < A) (hSchur : 0 < C-B^2/A) :
    0 < least A B C := by
  have hdet : 0 < A*C-B^2 := by
    have hh := mul_pos hA hSchur
    rw [mul_sub,mul_div_cancel₀ _ hA.ne'] at hh
    nlinarith
  have hC : 0 < C := by
    have hb := div_nonneg (sq_nonneg B) hA.le
    linarith
  have hs := Real.sq_sqrt (by positivity : 0 ≤ (A-C)^2+4*B^2)
  have hn := Real.sqrt_nonneg ((A-C)^2+4*B^2)
  unfold least
  nlinarith

/-- The explicit smaller spectral root controls the full quadratic form. -/
theorem quadratic_lower (A B C e k : ℝ) :
    least A B C*(e^2+k^2) ≤ quadratic A B C e k := by
  obtain ⟨hA,hC⟩ := least_le_diagonal A B C
  have heq := least_equation A B C
  by_cases hfirst : least A B C < A
  · have hd : 0 < A-least A B C := sub_pos.mpr hfirst
    have hfactor : quadratic A B C e k-least A B C*(e^2+k^2)=
        (A-least A B C)*(e+B/(A-least A B C)*k)^2 := by
      unfold quadratic
      field_simp [hd.ne']
      nlinarith [heq]
    have hn : 0 ≤ (A-least A B C)*(e+B/(A-least A B C)*k)^2 := by positivity
    rw [←hfactor] at hn
    linarith
  · have hz : least A B C=A := le_antisymm hA (le_of_not_gt hfirst)
    have hb : B=0 := by rw [hz] at heq; nlinarith [sq_nonneg B]
    unfold quadratic
    rw [hz,hb]
    nlinarith [mul_nonneg (sub_nonneg.mpr (by simpa only [hz] using hC)) (sq_nonneg k)]

theorem least_le_schur {A B C : ℝ} (hA : 0 < A) (hSchur : 0 < C-B^2/A) :
    least A B C ≤ C-B^2/A := by
  have hh := quadratic_lower A B C (-B/A) 1
  have hval : quadratic A B C (-B/A) 1=C-B^2/A := by
    unfold quadratic
    field_simp [hA.ne']
    ring
  rw [hval] at hh
  have hp := least_pos hA hSchur
  nlinarith [mul_nonneg hp.le (sq_nonneg (-B/A))]

/-- A genuine nonzero eigenvector attains the smaller spectral root. -/
theorem least_eigenvector {A B C : ℝ} (hB : B ≠ 0) :
    A*(-B/(A-least A B C))+B=least A B C*(-B/(A-least A B C)) ∧
      B*(-B/(A-least A B C))+C=least A B C := by
  have hd := (sub_pos.mpr (least_lt_first (A := A) (C := C) hB)).ne'
  have heq := least_equation A B C
  constructor
  · field_simp [hd]
    ring
  · field_simp [hd]
    nlinarith [heq]

/-- Every quadratic lower bound is at most the literal smaller eigenvalue. -/
theorem least_is_greatest_lower_bound {A B C : ℝ} (hB : B ≠ 0) {v : ℝ}
    (hv : ∀ e k, v*(e^2+k^2) ≤ quadratic A B C e k) : v ≤ least A B C := by
  obtain ⟨he,hk⟩ := least_eigenvector (A := A) (C := C) hB
  let e := -B/(A-least A B C)
  have hval : quadratic A B C e 1=least A B C*(e^2+1) := by
    change A*e^2+2*B*e*1+C*1^2=least A B C*(e^2+1)
    change A*e+B=least A B C*e at he
    change B*e+C=least A B C at hk
    nlinarith [congrArg (fun z : ℝ => z*e) he,hk]
  have hh := hv e 1
  rw [hval] at hh
  have hp : 0 < e^2+1 := by positivity
  nlinarith

end SlowEquilibration.TwoByTwoLeastCurvature
