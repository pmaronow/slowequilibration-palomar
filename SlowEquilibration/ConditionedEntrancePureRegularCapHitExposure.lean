-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntrancePureRegularGradient
public import SlowEquilibration.ConditionedEntrancePureCapHitExposure

/-! Proper-pure finite-horizon cap exposure with its gradient premise
discharged from the original tensor regularity event. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.ConditionedEntrance
open MeasureTheory ProbabilityTheory SphericalModel SphericalForm
open SphericalAging HardSphereDynamics SphericalOverlapExponential
open PhysicalHitting FeynmanKac
open scoped NNReal
set_option autoImplicit false
set_option maxHeartbeats 700000

def pureSourceShortCell (p : ℕ) (hp : 2 ≤ p) (c : ℝ) (hc : 0 < c)
    (Q B α β : ℝ) (hB : 0 ≤ B) (hα : 0 < α) (hβ : 0 ≤ β)
    (χ : ℝ → ℝ) (hχ : ContDiff ℝ 2 χ) : ℝ≥0 :=
  ⟨min (α/(48*(1+β*pureSourceGradientConstant p hp c hc Q B α χ hχ))) (1/18),
    le_min (div_nonneg hα.le (by
      have hC := pureSourceGradientConstant_nonneg p hp c hc Q B hB hα χ hχ
      positivity)) (by norm_num)⟩

theorem pureSourceShortCell_pos (p : ℕ) (hp : 2 ≤ p) (c : ℝ) (hc : 0 < c)
    (Q B α β : ℝ) (hB : 0 ≤ B) (hα : 0 < α) (hβ : 0 ≤ β)
    (χ : ℝ → ℝ) (hχ : ContDiff ℝ 2 χ) :
    0 < pureSourceShortCell p hp c hc Q B α β hB hα hβ χ hχ := by
  unfold pureSourceShortCell
  apply lt_min
  · apply div_pos hα
    have hC := pureSourceGradientConstant_nonneg p hp c hc Q B hB hα χ hχ
    positivity
  · norm_num

theorem pureSourceShortCell_le_eighteenth (p : ℕ) (hp : 2 ≤ p) (c : ℝ) (hc : 0 < c)
    (Q B α β : ℝ) (hB : 0 ≤ B) (hα : 0 < α) (hβ : 0 ≤ β)
    (χ : ℝ → ℝ) (hχ : ContDiff ℝ 2 χ) :
    (pureSourceShortCell p hp c hc Q B α β hB hα hβ χ hχ : ℝ) ≤ 1/18 :=
  min_le_right _ _

theorem pureSourceShortCell_short (p : ℕ) (hp : 2 ≤ p) (c : ℝ) (hc : 0 < c)
    (Q B α β : ℝ) (hB : 0 ≤ B) (hα : 0 < α) (hβ : 0 ≤ β)
    (χ : ℝ → ℝ) (hχ : ContDiff ℝ 2 χ) :
    4*(1+β*pureSourceGradientConstant p hp c hc Q B α χ hχ)*
      (pureSourceShortCell p hp c hc Q B α β hB hα hβ χ hχ : ℝ) ≤ α/12 := by
  have hC := pureSourceGradientConstant_nonneg p hp c hc Q B hB hα χ hχ
  have hA : 0 < 1+β*pureSourceGradientConstant p hp c hc Q B α χ hχ := by positivity
  have hT := min_le_left
    (α/(48*(1+β*pureSourceGradientConstant p hp c hc Q B α χ hχ))) (1/18)
  change (pureSourceShortCell p hp c hc Q B α β hB hα hβ χ hχ : ℝ) ≤ _ at hT
  have hDen := (le_div_iff₀ (by positivity :
    0 < 48*(1+β*pureSourceGradientConstant p hp c hc Q B α χ hχ))).mp hT
  nlinarith

/-- The original regular pure field, at every spherical start, has actual
cap exposure on one cell fixed before dimension and bounded value mark. -/
theorem regular_pure_axis_cap_hit_exposure {N : ℕ} (hN : 1 ≤ N)
    (p : ℕ) (hp : 2 ≤ p) (c : ℝ) (hc : 0 < c) (Q B α β : ℝ)
    (hB : 0 ≤ B) (hα : 0 < α) (hβ : 0 ≤ β)
    (χ : ℝ → ℝ) (hχ : ContDiff ℝ 2 χ)
    (J : Disorder N (FiniteMixture.pure p hp c hc).maxDegree)
    (hJ : J ∈ regularDisorder) (e : ℝ) (he : |e| ≤ B)
    (u x : Vector N) (hu : OnSphere u) (hx : OnSphere x)
    (θ : ℝ) (hθ : 0 ≤ θ) (H : ℝ≥0) :
    let T := pureSourceShortCell p hp c hc Q B α β hB hα hβ χ hχ
    let D := SmoothKilledGeneral.FieldData.ofPure hN p hp c hc Q J u e α χ hχ
    exposureFactor θ H T *
      (pureAxisCapHitProbability p hp c hc Q J β α χ hχ e H u x -
        (gridSize H T : ℝ)*
          (2*Real.exp (-(N : ℝ)*(α/12)^2/(16*(T : ℝ))))) ≤
      ∫ ω, finiteDiscountedMass (capKilling α u)
        (SmoothKilledGeneral.process D β x) θ (H+T) ω
        ∂VectorBrownian.law N := by
  dsimp only
  exact pure_axis_cap_hit_exposure_le_physical_firing hN p hp c hc Q J β α hβ hα
    χ hχ e u x hu hx (pureSourceGradientConstant p hp c hc Q B α χ hχ)
    (pureSourceGradientConstant_nonneg p hp c hc Q B hB hα χ hχ)
    (regular_pure_source_gradient_bound hN p hp c hc Q B hB hα χ hχ J hJ u hu e he)
    θ hθ H (pureSourceShortCell p hp c hc Q B α β hB hα hβ χ hχ)
    (pureSourceShortCell_pos p hp c hc Q B α β hB hα hβ χ hχ)
    (pureSourceShortCell_short p hp c hc Q B α β hB hα hβ χ hχ)

end SlowEquilibration.ConditionedEntrance
