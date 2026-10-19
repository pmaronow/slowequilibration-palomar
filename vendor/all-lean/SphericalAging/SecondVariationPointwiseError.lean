module

public import SphericalAging.OperatorTaylorRemainder

public section
/-! Exact three-term Jacobian variation error and genuine Taylor bounds. -/
noncomputable section
open scoped NNReal ContDiff
namespace SphericalAging.SecondVariationPointwiseError
open HardSphereDynamics
variable {N : ℕ}

theorem jacobian_variation_error_bound {g : State N → ℝ} (hg : ContDiff ℝ ∞ g)
    {L M : ℝ≥0} (hL : LipschitzWith L (fderiv ℝ g))
    (hM : LipschitzWith M (fderiv ℝ (fderiv ℝ g))) (x y d Yx Yy : State N) :
    ‖(fderiv ℝ g y-fderiv ℝ g x) Yy-fderiv ℝ (fderiv ℝ g) x d Yx‖≤
      (M : ℝ)*‖y-x‖^2*‖Yy‖+(L : ℝ)*‖y-x-d‖*‖Yy‖+
        (L : ℝ)*‖d‖*‖Yy-Yx‖ := by
  let H := fderiv ℝ (fderiv ℝ g) x
  have he : (fderiv ℝ g y-fderiv ℝ g x) Yy-H d Yx=
      (fderiv ℝ g y-fderiv ℝ g x-H (y-x)) Yy+H (y-x-d) Yy+H d (Yy-Yx) := by
    simp only [map_sub,ContinuousLinearMap.sub_apply]
    ring
  rw [he]
  have hH (a z : State N) : ‖H a z‖≤(L : ℝ)*‖a‖*‖z‖ :=
    ((H a).le_opNorm z).trans (mul_le_mul_of_nonneg_right
      (H.le_of_opNorm_le (norm_fderiv_le_of_lipschitz ℝ hL) a) (norm_nonneg _))
  calc
    _ ≤ ‖(fderiv ℝ g y-fderiv ℝ g x-H (y-x)) Yy+H (y-x-d) Yy‖+‖H d (Yy-Yx)‖ := norm_add_le _ _
    _ ≤ (‖(fderiv ℝ g y-fderiv ℝ g x-H (y-x)) Yy‖+‖H (y-x-d) Yy‖)+‖H d (Yy-Yx)‖ :=
      add_le_add (norm_add_le _ _) (le_refl _)
    _ ≤ _ := add_le_add (add_le_add
      (OperatorTaylorRemainder.jacobian_remainder_bound hg hM x y Yy)
      (hH (y-x-d) Yy)) (hH d (Yy-Yx))

end SphericalAging.SecondVariationPointwiseError
