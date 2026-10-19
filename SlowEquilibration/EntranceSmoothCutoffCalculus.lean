-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntrancePolynomialCutoff
public import SlowEquilibration.SphericalSmoothTensorStationarity

/-! Actual first-order calculus of the two linear entrance cutoffs.
Scalar polynomial approximation errors propagate to the literal ambient
gradient of the cutoff Hamiltonian, before any dynamics comparison. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.EntranceSmoothCutoffCalculus
open SphericalModel SphericalForm
open scoped RealInnerProductSpace
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {N : ℕ}

def cutoffCorrection (φ ψ : ℝ → ℝ) (u v : Vector N) (D : Vector N → ℝ)
    (x : Vector N) : ℝ := φ (inner ℝ u x)*ψ (inner ℝ v x)*D x

theorem cutoffCorrection_hasGradientAt (φ ψ : ℝ → ℝ) (u v : Vector N)
    (D : Vector N → ℝ) (x : Vector N)
    (hφ : DifferentiableAt ℝ φ (inner ℝ u x))
    (hψ : DifferentiableAt ℝ ψ (inner ℝ v x)) (hD : DifferentiableAt ℝ D x) :
    HasGradientAt (cutoffCorrection φ ψ u v D)
      ((deriv φ (inner ℝ u x)*ψ (inner ℝ v x)*D x) • u+
        (φ (inner ℝ u x)*deriv ψ (inner ℝ v x)*D x) • v+
        (φ (inner ℝ u x)*ψ (inner ℝ v x)) • gradient D x) x := by
  have h1 := hφ.hasDerivAt.comp_hasFDerivAt x ((innerSL ℝ u).hasFDerivAt (x := x))
  have h2 := hψ.hasDerivAt.comp_hasFDerivAt x ((innerSL ℝ v).hasFDerivAt (x := x))
  have hd := (h1.mul h2).mul hD.hasFDerivAt
  apply hd.congr_fderiv
  ext z
  simp only [InnerProductSpace.toDual_apply_apply,inner_add_left,real_inner_smul_left,
    add_apply,_root_.smul_apply,smul_eq_mul,Pi.mul_apply,
    innerSL_apply_apply,Function.comp_apply,inner_gradient_left]
  ring

theorem cutoffCorrection_gradient (φ ψ : ℝ → ℝ) (u v : Vector N)
    (D : Vector N → ℝ) (x : Vector N)
    (hφ : DifferentiableAt ℝ φ (inner ℝ u x))
    (hψ : DifferentiableAt ℝ ψ (inner ℝ v x)) (hD : DifferentiableAt ℝ D x) :
    gradient (cutoffCorrection φ ψ u v D) x=
      (deriv φ (inner ℝ u x)*ψ (inner ℝ v x)*D x) • u+
        (φ (inner ℝ u x)*deriv ψ (inner ℝ v x)*D x) • v+
        (φ (inner ℝ u x)*ψ (inner ℝ v x)) • gradient D x :=
  (cutoffCorrection_hasGradientAt φ ψ u v D x hφ hψ hD).gradient

/-- The exact product error for two bounded scalar factors. -/
theorem product_error_le {a b a' b' M ε : ℝ} (hM : 0 ≤ M) (hε : 0 ≤ ε)
    (hε1 : ε ≤ 1) (ha : |a| ≤ M) (hb : |b| ≤ M)
    (hea : |a'-a| ≤ ε) (heb : |b'-b| ≤ ε) :
    |a'*b'-a*b| ≤ (2*M+1)*ε := by
  have hbp : |b'| ≤ M+1 := by
    have he : b'=b+(b'-b) := by ring
    rw [he]
    exact (abs_add_le _ _).trans (by linarith)
  have he : a'*b'-a*b=(a'-a)*b'+a*(b'-b) := by ring
  rw [he]
  calc
    _ ≤ |(a'-a)*b'|+|a*(b'-b)| := abs_add_le _ _
    _ ≤ ε*(M+1)+M*ε := by
      rw [abs_mul,abs_mul]
      exact add_le_add (mul_le_mul hea hbp (abs_nonneg _) hε)
        (mul_le_mul ha heb (abs_nonneg _) hM)
    _ = _ := by ring

theorem cutoffCorrection_value_error_le (χ : ℝ → ℝ) (u v : Vector N)
    (D : Vector N → ℝ) (p q : Polynomial ℝ) (x : Vector N)
    {M ε B : ℝ} (hM : 0 ≤ M) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hχu : |χ (inner ℝ u x)| ≤ M) (hχv : |χ (inner ℝ v x)| ≤ M)
    (hp : |p.eval (inner ℝ u x)-χ (inner ℝ u x)| ≤ ε)
    (hq : |q.eval (inner ℝ v x)-χ (inner ℝ v x)| ≤ ε) (hD : |D x| ≤ B) :
    |cutoffCorrection p.eval q.eval u v D x-cutoffCorrection χ χ u v D x| ≤
      (2*M+1)*ε*B := by
  have hc := product_error_le hM hε hε1 hχu hχv hp hq
  have he : cutoffCorrection p.eval q.eval u v D x-cutoffCorrection χ χ u v D x=
      (p.eval (inner ℝ u x)*q.eval (inner ℝ v x)-χ (inner ℝ u x)*χ (inner ℝ v x))*D x := by
    unfold cutoffCorrection
    ring
  rw [he,abs_mul]
  exact mul_le_mul hc hD (abs_nonneg _) (by positivity)

/-- Uniform scalar C¹ approximation controls the actual ambient Riesz
gradient; the two cutoff arguments are ordinary linear forms. -/
theorem cutoffCorrection_gradient_error_le (χ : ℝ → ℝ) (u v : Vector N)
    (D : Vector N → ℝ) (p q : Polynomial ℝ) (x : Vector N)
    (hχ : Differentiable ℝ χ) (hDdiff : DifferentiableAt ℝ D x)
    {M ε B G : ℝ} (hM : 0 ≤ M) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hχu : |χ (inner ℝ u x)| ≤ M) (hχv : |χ (inner ℝ v x)| ≤ M)
    (hχu' : |deriv χ (inner ℝ u x)| ≤ M) (hχv' : |deriv χ (inner ℝ v x)| ≤ M)
    (hp : |p.eval (inner ℝ u x)-χ (inner ℝ u x)| ≤ ε)
    (hq : |q.eval (inner ℝ v x)-χ (inner ℝ v x)| ≤ ε)
    (hp' : |p.derivative.eval (inner ℝ u x)-deriv χ (inner ℝ u x)| ≤ ε)
    (hq' : |q.derivative.eval (inner ℝ v x)-deriv χ (inner ℝ v x)| ≤ ε)
    (hD : |D x| ≤ B) (hG : ‖gradient D x‖ ≤ G) :
    ‖gradient (cutoffCorrection p.eval q.eval u v D) x-
      gradient (cutoffCorrection χ χ u v D) x‖ ≤
      (2*M+1)*ε*(B*(‖u‖+‖v‖)+G) := by
  let C : ℝ := (2*M+1)*ε
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have h0 := product_error_le hM hε hε1 hχu hχv hp hq
  have h1 := product_error_le hM hε hε1 hχu' hχv hp' hq
  have h2 := product_error_le hM hε hε1 hχu hχv' hp hq'
  have he : gradient (cutoffCorrection p.eval q.eval u v D) x-
      gradient (cutoffCorrection χ χ u v D) x=
      ((p.derivative.eval (inner ℝ u x)*q.eval (inner ℝ v x)-deriv χ (inner ℝ u x)*χ (inner ℝ v x))*D x) • u+
      ((p.eval (inner ℝ u x)*q.derivative.eval (inner ℝ v x)-χ (inner ℝ u x)*deriv χ (inner ℝ v x))*D x) • v+
      (p.eval (inner ℝ u x)*q.eval (inner ℝ v x)-χ (inner ℝ u x)*χ (inner ℝ v x)) • gradient D x := by
    rw [cutoffCorrection_gradient p.eval q.eval u v D x
      (p.hasDerivAt _).differentiableAt (q.hasDerivAt _).differentiableAt hDdiff,
      cutoffCorrection_gradient χ χ u v D x (hχ _) (hχ _) hDdiff,
      (p.hasDerivAt _).deriv,(q.hasDerivAt _).deriv]
    module
  have hb1 : ‖((p.derivative.eval (inner ℝ u x)*q.eval (inner ℝ v x)-
      deriv χ (inner ℝ u x)*χ (inner ℝ v x))*D x) • u‖ ≤ C*B*‖u‖ := by
    rw [norm_smul,Real.norm_eq_abs,abs_mul]
    exact mul_le_mul_of_nonneg_right (mul_le_mul h1 hD (abs_nonneg _) hC) (norm_nonneg _)
  have hb2 : ‖((p.eval (inner ℝ u x)*q.derivative.eval (inner ℝ v x)-
      χ (inner ℝ u x)*deriv χ (inner ℝ v x))*D x) • v‖ ≤ C*B*‖v‖ := by
    rw [norm_smul,Real.norm_eq_abs,abs_mul]
    exact mul_le_mul_of_nonneg_right (mul_le_mul h2 hD (abs_nonneg _) hC) (norm_nonneg _)
  have hb0 : ‖(p.eval (inner ℝ u x)*q.eval (inner ℝ v x)-
      χ (inner ℝ u x)*χ (inner ℝ v x)) • gradient D x‖ ≤ C*G := by
    rw [norm_smul,Real.norm_eq_abs]
    exact mul_le_mul h0 hG (norm_nonneg _) hC
  rw [he]
  calc
    _ ≤ (C*B*‖u‖+C*B*‖v‖)+C*G :=
      (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add hb1 hb2)) hb0)
    _ = _ := by dsimp [C]; ring

end SlowEquilibration.EntranceSmoothCutoffCalculus
