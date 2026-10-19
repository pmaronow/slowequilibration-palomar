module
public import QuantitativeFollowup.InverseFamilyBounds

@[expose] public section

/-! Quantitative bounds on the actual derivatives of an inner product of
two smooth bounded vector fields. -/
noncomputable section
namespace QuantitativeFollowup

theorem innerFamily_directional {E D : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup D] [NormedSpace ℝ D]
    (b v : D → E) (hb : ContDiff ℝ 2 b) (hv : ContDiff ℝ 2 v) (x z : D) :
    fderiv ℝ (fun y => inner ℝ (b y) (v y)) x z=
      inner ℝ (b x) (fderiv ℝ v x z)+inner ℝ (fderiv ℝ b x z) (v x) := by
  exact fderiv_inner_apply ℝ (hb.differentiable (by norm_num) x)
    (hv.differentiable (by norm_num) x) z

theorem innerFamily_second_directional {E D : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup D] [NormedSpace ℝ D]
    (b v : D → E) (hb : ContDiff ℝ 2 b) (hv : ContDiff ℝ 2 v) (x z : D) :
    directionalHessian (fun y => inner ℝ (b y) (v y)) x z=
      inner ℝ (b x) (fderiv ℝ (fderiv ℝ v) x z z)+
        2*inner ℝ (fderiv ℝ b x z) (fderiv ℝ v x z)+
          inner ℝ (fderiv ℝ (fderiv ℝ b) x z z) (v x) := by
  have hp := ((hasDerivAt_vector_on_affine_line b hb x z 0).inner ℝ
    (hasDerivAt_vector_directional_on_affine_line v hv x z 0)).add
    ((hasDerivAt_vector_directional_on_affine_line b hb x z 0).inner ℝ
      (hasDerivAt_vector_on_affine_line v hv x z 0))
  have heq : (fun s : ℝ => inner ℝ (b (x+s • z)) (fderiv ℝ v (x+s • z) z)+
      inner ℝ (fderiv ℝ b (x+s • z) z) (v (x+s • z))) =
      (fun s => fderiv ℝ (fun y => inner ℝ (b y) (v y)) (x+s • z) z) := by
    funext s
    exact (innerFamily_directional b v hb hv _ z).symm
  change HasDerivAt (fun s : ℝ => inner ℝ (b (x+s • z)) (fderiv ℝ v (x+s • z) z)+
    inner ℝ (fderiv ℝ b (x+s • z) z) (v (x+s • z))) _ 0 at hp
  rw [heq] at hp
  have hh := hp.unique (hasDerivAt_vector_directional_on_affine_line
    (fun y => inner ℝ (b y) (v y)) (hb.inner ℝ hv) x z 0)
  simp only [zero_smul,add_zero] at hh
  unfold directionalHessian
  rw [←hh]
  ring

theorem innerFamily_bounds {E D : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup D] [NormedSpace ℝ D]
    (b v : D → E) (hb : ContDiff ℝ 2 b) (hv : ContDiff ℝ 2 v)
    (B₀ B₁ B₂ V₀ V₁ V₂ : ℝ)
    (hB₀ : 0 ≤ B₀) (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (hV₀ : 0 ≤ V₀) (hV₁ : 0 ≤ V₁) (hV₂ : 0 ≤ V₂)
    (hb₀ : ∀ x, ‖b x‖ ≤ B₀) (hv₀ : ∀ x, ‖v x‖ ≤ V₀)
    (hb₁ : ∀ x z, ‖fderiv ℝ b x z‖ ≤ B₁*‖z‖)
    (hv₁ : ∀ x z, ‖fderiv ℝ v x z‖ ≤ V₁*‖z‖)
    (hb₂ : ∀ x z, ‖fderiv ℝ (fderiv ℝ b) x z z‖ ≤ B₂*‖z‖^2)
    (hv₂ : ∀ x z, ‖fderiv ℝ (fderiv ℝ v) x z z‖ ≤ V₂*‖z‖^2) :
    (∀ x, |inner ℝ (b x) (v x)| ≤ B₀*V₀) ∧
    (∀ x z, |fderiv ℝ (fun y => inner ℝ (b y) (v y)) x z| ≤
      (B₀*V₁+B₁*V₀)*‖z‖) ∧
    (∀ x z, |directionalHessian (fun y => inner ℝ (b y) (v y)) x z| ≤
      (B₀*V₂+2*B₁*V₁+B₂*V₀)*‖z‖^2) := by
  refine ⟨?_,?_,?_⟩
  · intro x
    exact (abs_real_inner_le_norm _ _).trans
      (mul_le_mul (hb₀ x) (hv₀ x) (norm_nonneg _) hB₀)
  · intro x z
    rw [innerFamily_directional b v hb hv]
    calc
      _ ≤ |inner ℝ (b x) (fderiv ℝ v x z)|+
          |inner ℝ (fderiv ℝ b x z) (v x)| := abs_add_le _ _
      _ ≤ B₀*(V₁*‖z‖)+(B₁*‖z‖)*V₀ := by
        apply add_le_add
        · exact (abs_real_inner_le_norm _ _).trans
            (mul_le_mul (hb₀ x) (hv₁ x z) (norm_nonneg _) hB₀)
        · exact (abs_real_inner_le_norm _ _).trans
            (mul_le_mul (hb₁ x z) (hv₀ x) (norm_nonneg _) (by positivity))
      _ = (B₀*V₁+B₁*V₀)*‖z‖ := by ring
  · intro x z
    rw [innerFamily_second_directional b v hb hv]
    calc
      _ ≤ |inner ℝ (b x) (fderiv ℝ (fderiv ℝ v) x z z)|+
          |2*inner ℝ (fderiv ℝ b x z) (fderiv ℝ v x z)|+
          |inner ℝ (fderiv ℝ (fderiv ℝ b) x z z) (v x)| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ B₀*(V₂*‖z‖^2)+2*((B₁*‖z‖)*(V₁*‖z‖))+(B₂*‖z‖^2)*V₀ := by
        rw [abs_mul,abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
        apply add_le_add
        · apply add_le_add
          · exact (abs_real_inner_le_norm _ _).trans
              (mul_le_mul (hb₀ x) (hv₂ x z) (norm_nonneg _) hB₀)
          · exact mul_le_mul_of_nonneg_left ((abs_real_inner_le_norm _ _).trans
              (mul_le_mul (hb₁ x z) (hv₁ x z) (norm_nonneg _) (by positivity))) (by norm_num)
        · exact (abs_real_inner_le_norm _ _).trans
            (mul_le_mul (hb₂ x z) (hv₀ x) (norm_nonneg _) (by positivity))
      _ = (B₀*V₂+2*B₁*V₁+B₂*V₀)*‖z‖^2 := by ring

end QuantitativeFollowup
