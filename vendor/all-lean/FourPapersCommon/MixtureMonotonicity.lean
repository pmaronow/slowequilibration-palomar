module
public import FourPapersCommon.MixtureJetBounds

@[expose] public section

/-! Monotonicity of the actual even-mixture curvature on nonnegative overlaps. -/
noncomputable section
open Set
namespace FourPapersCommon.AdmissibleEvenMixture

theorem second_monotoneOn (ξ : AdmissibleEvenMixture) :
    MonotoneOn ξ.second (Icc (0 : ℝ) 1) := by
  intro x hx y hy hxy
  apply Summable.tsum_le_tsum
  · intro p
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx.1 hxy (p - 2))
      (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (ξ.nonneg p))
  · exact ξ.summable_second (by rw [abs_of_nonneg hx.1]; exact hx.2)
  · exact ξ.summable_second (by rw [abs_of_nonneg hy.1]; exact hy.2)

end FourPapersCommon.AdmissibleEvenMixture
