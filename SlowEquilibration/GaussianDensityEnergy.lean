-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianFiberDensity
public import SlowEquilibration.GaussianGramInversePerturbation

/-! Exact ordinary Gaussian observation log densities and their genuine
inverse-Gram target energies, pointwise including null conditioning targets. -/
@[expose] public section
namespace SlowEquilibration.GaussianRegression
noncomputable section
open Function GaussianObservationCoercivity
open scoped RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 500000
variable {E E' F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup E'] [InnerProductSpace ℝ E'] [FiniteDimensional ℝ E']
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

def realObservationDensity (A : E →L[ℝ] F) (w : F) : ℝ :=
  (Real.sqrt (gram A).det)⁻¹*GaussianDensity.normalizer F*Real.exp (-(1/2:ℝ)*‖lift A w‖^2)

lemma realObservationDensity_pos (A : E →L[ℝ] F) (hA : Surjective A) (w : F) :
    0 < realObservationDensity A w := by
  exact mul_pos (mul_pos (inv_pos.mpr (gram_sqrt_det_pos A hA)) GaussianDensity.normalizer_pos) (Real.exp_pos _)

lemma realObservationDensity_eq_toReal (A : E →L[ℝ] F) (hA : Surjective A) (w : F) :
    realObservationDensity A w=(observationPdf A w).toReal := by
  exact (ENNReal.toReal_ofReal (realObservationDensity_pos A hA w).le).symm

lemma lift_norm_sq_energy (A : E →L[ℝ] F) (hA : Surjective A) (w : F) :
    ‖lift A w‖^2=inner ℝ w ((gram A).inverse w) := by
  rw [← real_inner_self_eq_norm_sq]
  change inner ℝ (A.adjoint ((gram A).inverse w)) (lift A w)=_
  rw [A.adjoint_inner_left,observation_lift_apply A hA w,real_inner_comm]

/-- Exact pointwise log pdf, in terms of the true actual Gram inverse. -/
theorem log_realObservationDensity (A : E →L[ℝ] F) (hA : Surjective A) (w : F) :
    Real.log (realObservationDensity A w)=
      Real.log (GaussianDensity.normalizer F)-Real.log (gram A).det/2-
        inner ℝ w ((gram A).inverse w)/2 := by
  unfold realObservationDensity
  rw [Real.log_mul (mul_pos (inv_pos.mpr (gram_sqrt_det_pos A hA)) GaussianDensity.normalizer_pos).ne' (Real.exp_pos _).ne',
    Real.log_mul (inv_pos.mpr (gram_sqrt_det_pos A hA)).ne' GaussianDensity.normalizer_pos.ne',
    Real.log_inv,Real.log_sqrt (gram_det_pos A hA).le,Real.log_exp,lift_norm_sq_energy A hA w]
  ring

/-- The normalizers cancel exactly between two true Gaussian score laws on
the same observation space, before any covariance perturbation estimate. -/
theorem log_density_ratio (A : E →L[ℝ] F) (hA : Surjective A)
    (B : E' →L[ℝ] F) (hB : Surjective B) (w : F) :
    Real.log (realObservationDensity A w/realObservationDensity B w)=
      -(Real.log (gram A).det-Real.log (gram B).det)/2-
        (inner ℝ w ((gram A).inverse w)-inner ℝ w ((gram B).inverse w))/2 := by
  rw [Real.log_div (realObservationDensity_pos A hA w).ne' (realObservationDensity_pos B hB w).ne',
    log_realObservationDensity A hA w,log_realObservationDensity B hB w]
  ring

/-- True target-density comparison from the separate log determinant and
inverse Gram perturbations. The squared target norm remains literal. -/
theorem log_density_ratio_bound (A : E →L[ℝ] F) (hA : Surjective A)
    (B : E' →L[ℝ] F) (hB : Surjective B) (w : F) {L : ℝ}
    (hdet : |Real.log (gram A).det-Real.log (gram B).det| ≤ L) :
    |Real.log (realObservationDensity A w/realObservationDensity B w)| ≤
      L/2+(‖(gram A).inverse‖*‖gram A-gram B‖*‖(gram B).inverse‖*‖w‖^2)/2 := by
  rw [log_density_ratio A hA B hB w]
  have henergy:=inverse_quadratic_difference_bound (gram A) (gram B)
    (gram_isInvertible A hA) (gram_isInvertible B hB) w
  have hab (a b : ℝ) : |a-b| ≤ |a|+|b| := by
    simpa only [sub_eq_add_neg,abs_neg] using abs_add_le a (-b)
  calc
    _ ≤ |-(Real.log (gram A).det-Real.log (gram B).det)/2|+
      |(inner ℝ w ((gram A).inverse w)-inner ℝ w ((gram B).inverse w))/2| := hab _ _
    _ ≤ L/2+(‖(gram A).inverse‖*‖gram A-gram B‖*‖(gram B).inverse‖*‖w‖^2)/2 := by
      simp only [abs_div,abs_neg,show |(2:ℝ)|=2 by norm_num]
      gcongr

end
end SlowEquilibration.GaussianRegression
