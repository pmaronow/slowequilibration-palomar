-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntranceQuenchedUniformCapHitFixedScales

/-! A single short overlap-grid cell works for every marked source field
in the prescribed compact rectangle. -/
@[expose] public section
noncomputable section
open SlowEquilibration.SphericalModel
open scoped NNReal
namespace SlowEquilibration.ConditionedEntrance
open PhysicalHitting
set_option autoImplicit false

theorem sourceGradientConstant_le_mark_bound
    (μ : FiniteMixture) (Q B α : ℝ) (hB : 0≤B) (hα : 0<α)
    (χ : ℝ→ℝ) (hχ : ContDiff ℝ 2 χ) (e k : ℝ)
    (he : |e|≤B) (hk : |k|≤B) :
    sourceGradientConstant μ Q e k α χ hχ ≤
      sourceGradientConstant μ Q B B α χ hχ := by
  have hm : markConstant μ Q e k ≤ markConstant μ Q B B := by
    unfold markConstant
    rw [abs_of_nonneg hB]
    linarith
  have hA : 0≤thetaConstant μ Q := (thetaConstant_pos μ Q).le
  have hK : 0≤centerConstant μ Q := (centerConstant_pos μ Q).le
  have hL : 0 ≤ scalarCutoffConstant χ hχ (sourceArgumentRadius μ Q α) :=
    scalarCutoffConstant_nonneg χ hχ _
  unfold sourceGradientConstant
  gcongr

def sourceShortCell (μ : FiniteMixture) (Q B α β : ℝ)
    (hα : 0<α) (hβ : 0≤β) (χ : ℝ→ℝ) (hχ : ContDiff ℝ 2 χ) : ℝ≥0 :=
  ⟨min (α/(48*(1+β*sourceGradientConstant μ Q B B α χ hχ))) (1/18),
    le_min (div_nonneg hα.le (by
      have hC := sourceGradientConstant_nonneg μ Q B B hα χ hχ
      positivity)) (by norm_num)⟩

theorem sourceShortCell_pos (μ : FiniteMixture) (Q B α β : ℝ)
    (hα : 0<α) (hβ : 0≤β) (χ : ℝ→ℝ) (hχ : ContDiff ℝ 2 χ) :
    0<sourceShortCell μ Q B α β hα hβ χ hχ := by
  unfold sourceShortCell
  apply lt_min
  · apply div_pos hα
    have hC := sourceGradientConstant_nonneg μ Q B B hα χ hχ
    positivity
  · norm_num

theorem sourceShortCell_le_eighteenth (μ : FiniteMixture) (Q B α β : ℝ)
    (hα : 0<α) (hβ : 0≤β) (χ : ℝ→ℝ) (hχ : ContDiff ℝ 2 χ) :
    (sourceShortCell μ Q B α β hα hβ χ hχ : ℝ)≤1/18 :=
  min_le_right _ _

theorem sourceShortCell_short
    (μ : FiniteMixture) (Q B α β : ℝ) (hB : 0≤B) (hα : 0<α) (hβ : 0≤β)
    (χ : ℝ→ℝ) (hχ : ContDiff ℝ 2 χ) (e k : ℝ)
    (he : |e|≤B) (hk : |k|≤B) :
    4*(1+β*sourceGradientConstant μ Q e k α χ hχ)*
      (sourceShortCell μ Q B α β hα hβ χ hχ : ℝ)≤α/12 := by
  have hC := sourceGradientConstant_le_mark_bound μ Q B α hB hα χ hχ e k he hk
  have hC0 := sourceGradientConstant_nonneg μ Q B B hα χ hχ
  have hA : 0<1+β*sourceGradientConstant μ Q B B α χ hχ := by positivity
  have hT := min_le_left
    (α/(48*(1+β*sourceGradientConstant μ Q B B α χ hχ))) (1/18)
  change (sourceShortCell μ Q B α β hα hβ χ hχ : ℝ)≤_ at hT
  have hT0 : 0≤(sourceShortCell μ Q B α β hα hβ χ hχ : ℝ) := by positivity
  have hApos : 0≤1+β*sourceGradientConstant μ Q e k α χ hχ := by
    have hCe := sourceGradientConstant_nonneg μ Q e k hα χ hχ
    positivity
  have hAC : 1+β*sourceGradientConstant μ Q e k α χ hχ≤
      1+β*sourceGradientConstant μ Q B B α χ hχ := by nlinarith
  have hTan := mul_le_mul_of_nonneg_left hT (mul_nonneg (by norm_num : (0:ℝ)≤4) hA.le)
  have hMark := mul_le_mul_of_nonneg_right hAC hT0
  have hDen := (le_div_iff₀ (by positivity : 0<48*(1+β*sourceGradientConstant μ Q B B α χ hχ))).mp hT
  nlinarith [hTan,hMark,hDen]

end SlowEquilibration.ConditionedEntrance
