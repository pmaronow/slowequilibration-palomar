module
public import QuantitativeFollowup.InverseFamily

@[expose] public section

/-! Uniform bounds on the actual first two derivatives of an inverse
operator family applied to a vector field. -/
noncomputable section
namespace QuantitativeFollowup

theorem inverseFamily_norm_le {E D : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup D] [NormedSpace ℝ D]
    (A : D → E →L[ℝ] E) (b : D → E) (L B₀ : ℝ)
    (hL : 0 ≤ L) (hI : ∀ x, ‖Ring.inverse (A x)‖ ≤ L)
    (hb : ∀ x, ‖b x‖ ≤ B₀) (x : D) : ‖inverseFamily A b x‖ ≤ L*B₀ := by
  unfold inverseFamily
  exact ((Ring.inverse (A x)).le_opNorm (b x)).trans
    (mul_le_mul (hI x) (hb x) (norm_nonneg _) hL)

theorem inverseFamily_directional_norm_le {E D : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup D] [NormedSpace ℝ D]
    (A : D → E →L[ℝ] E) (b : D → E) (hA : ContDiff ℝ 2 A)
    (hb : ContDiff ℝ 2 b) (hunit : ∀ x, IsUnit (A x))
    (L A₁ B₀ B₁ : ℝ) (hL : 0 ≤ L) (hA₁ : 0 ≤ A₁)
    (hB₀ : 0 ≤ B₀) (hB₁ : 0 ≤ B₁)
    (hI : ∀ x, ‖Ring.inverse (A x)‖ ≤ L)
    (hb₀ : ∀ x, ‖b x‖ ≤ B₀)
    (ha₁ : ∀ x z, ‖fderiv ℝ A x z‖ ≤ A₁*‖z‖)
    (hb₁ : ∀ x z, ‖fderiv ℝ b x z‖ ≤ B₁*‖z‖) (x z : D) :
    ‖fderiv ℝ (inverseFamily A b) x z‖ ≤ L*(B₁+A₁*L*B₀)*‖z‖ := by
  have heq : A x (fderiv ℝ (inverseFamily A b) x z)=
      fderiv ℝ b x z-fderiv ℝ A x z (inverseFamily A b x) := by
    rw [←inverseFamily_first_equation A b hA hb hunit x z]
    abel
  have hinv : fderiv ℝ (inverseFamily A b) x z=
      Ring.inverse (A x) (fderiv ℝ b x z-fderiv ℝ A x z (inverseFamily A b x)) := by
    rw [←heq]
    have hh := congrArg (fun C : E →L[ℝ] E => C (fderiv ℝ (inverseFamily A b) x z))
      (Ring.inverse_mul_cancel (A x) (hunit x))
    simpa only [ContinuousLinearMap.mul_apply,ContinuousLinearMap.one_apply] using hh.symm
  rw [hinv]
  calc
    _ ≤ ‖Ring.inverse (A x)‖ *
        ‖fderiv ℝ b x z-fderiv ℝ A x z (inverseFamily A b x)‖ :=
      (Ring.inverse (A x)).le_opNorm _
    _ ≤ L*(‖fderiv ℝ b x z‖+‖fderiv ℝ A x z (inverseFamily A b x)‖) := by
      gcongr
      exacts [hI x,norm_sub_le _ _]
    _ ≤ L*(B₁*‖z‖+(A₁*‖z‖)*(L*B₀)) := by
      gcongr
      · exact hb₁ x z
      · exact ((fderiv ℝ A x z).le_opNorm _).trans
          (mul_le_mul (ha₁ x z) (inverseFamily_norm_le A b L B₀ hL hI hb₀ x)
            (norm_nonneg _) (by positivity))
    _ = L*(B₁+A₁*L*B₀)*‖z‖ := by ring

theorem inverseFamily_second_directional_norm_le {E D : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup D] [NormedSpace ℝ D]
    (A : D → E →L[ℝ] E) (b : D → E) (hA : ContDiff ℝ 2 A)
    (hb : ContDiff ℝ 2 b) (hunit : ∀ x, IsUnit (A x))
    (L A₁ A₂ B₀ B₁ B₂ : ℝ) (hL : 0 ≤ L) (hA₁ : 0 ≤ A₁) (hA₂ : 0 ≤ A₂)
    (hB₀ : 0 ≤ B₀) (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (hI : ∀ x, ‖Ring.inverse (A x)‖ ≤ L)
    (hb₀ : ∀ x, ‖b x‖ ≤ B₀)
    (ha₁ : ∀ x z, ‖fderiv ℝ A x z‖ ≤ A₁*‖z‖)
    (ha₂ : ∀ x z, ‖fderiv ℝ (fderiv ℝ A) x z z‖ ≤ A₂*‖z‖^2)
    (hb₁ : ∀ x z, ‖fderiv ℝ b x z‖ ≤ B₁*‖z‖)
    (hb₂ : ∀ x z, ‖fderiv ℝ (fderiv ℝ b) x z z‖ ≤ B₂*‖z‖^2) (x z : D) :
    ‖fderiv ℝ (fderiv ℝ (inverseFamily A b)) x z z‖ ≤
      L*(B₂+A₂*L*B₀+2*A₁*L*(B₁+A₁*L*B₀))*‖z‖^2 := by
  let v := inverseFamily A b
  have heq : A x (fderiv ℝ (fderiv ℝ v) x z z)=
      fderiv ℝ (fderiv ℝ b) x z z-
        fderiv ℝ (fderiv ℝ A) x z z (v x)-
          (2:ℝ) • (fderiv ℝ A x z (fderiv ℝ v x z)) := by
    rw [←inverseFamily_second_equation A b hA hb hunit x z]
    module
  have hinv : fderiv ℝ (fderiv ℝ v) x z z=Ring.inverse (A x)
      (fderiv ℝ (fderiv ℝ b) x z z-fderiv ℝ (fderiv ℝ A) x z z (v x)-
        (2:ℝ) • (fderiv ℝ A x z (fderiv ℝ v x z))) := by
    rw [←heq]
    have hh := congrArg (fun C : E →L[ℝ] E => C (fderiv ℝ (fderiv ℝ v) x z z))
      (Ring.inverse_mul_cancel (A x) (hunit x))
    simpa only [ContinuousLinearMap.mul_apply,ContinuousLinearMap.one_apply] using hh.symm
  have hv₀ := inverseFamily_norm_le A b L B₀ hL hI hb₀ x
  have hv₁ := inverseFamily_directional_norm_le A b hA hb hunit L A₁ B₀ B₁
    hL hA₁ hB₀ hB₁ hI hb₀ ha₁ hb₁ x z
  change ‖fderiv ℝ (fderiv ℝ v) x z z‖ ≤ _
  rw [hinv]
  calc
    _ ≤ ‖Ring.inverse (A x)‖ * ‖fderiv ℝ (fderiv ℝ b) x z z-
        fderiv ℝ (fderiv ℝ A) x z z (v x)-
          (2:ℝ) • (fderiv ℝ A x z (fderiv ℝ v x z))‖ :=
      (Ring.inverse (A x)).le_opNorm _
    _ ≤ L*(‖fderiv ℝ (fderiv ℝ b) x z z‖+
        ‖fderiv ℝ (fderiv ℝ A) x z z (v x)‖+
          ‖(2:ℝ) • (fderiv ℝ A x z (fderiv ℝ v x z))‖) := by
      gcongr
      · exact hI x
      · exact (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    _ ≤ L*(B₂*‖z‖^2+(A₂*‖z‖^2)*(L*B₀)+
        2*((A₁*‖z‖)*(L*(B₁+A₁*L*B₀)*‖z‖))) := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
      gcongr
      · exact hb₂ x z
      · exact ((fderiv ℝ (fderiv ℝ A) x z z).le_opNorm _).trans
          (mul_le_mul (ha₂ x z) hv₀ (norm_nonneg _) (by positivity))
      · exact ((fderiv ℝ A x z).le_opNorm _).trans
          (mul_le_mul (ha₁ x z) hv₁ (norm_nonneg _) (by positivity))
    _ = L*(B₂+A₂*L*B₀+2*A₁*L*(B₁+A₁*L*B₀))*‖z‖^2 := by ring

end QuantitativeFollowup
