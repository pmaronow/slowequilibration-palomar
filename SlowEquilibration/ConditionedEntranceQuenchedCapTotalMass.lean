-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntrancePhysicalCapAxisMean

/-! Uniform quenched total-mass control for the literal physical cap killing
under an independent uniform axis and the original Gibbs spin law. -/
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open SlowEquilibration.SphericalModel
open SlowEquilibration.SphericalOverlapExponential
namespace SlowEquilibration.ConditionedEntrance
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

/-- The physical cap killing has an exponentially small quenched mean,
uniform over every original disorder and inverse temperature. -/
theorem quenchedOriginalAxisGibbs_capKilling_mean_eventually_le
    (μ : FiniteMixture) {α : ℝ} (hα : 0 < α) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (J : Disorder (n+1) μ.maxDegree) (β : ℝ),
        (∫ z, PhysicalHitting.capKilling α z.1 z.2
          ∂((sphereLaw (n+1)).prod
            (gibbsLaw (n+1) β (fieldOfMixture μ J)))) ≤
              C * Real.exp (-((n+1 : ℕ) : ℝ) * α^2 / 64) := by
  obtain ⟨C,hC,hTail⟩ := physical_capKilling_axis_mean_eventually_le hα
  refine ⟨C,hC,?_⟩
  filter_upwards [(tendsto_add_atTop_nat 1).eventually hTail] with n hn
  intro J β
  let θ := sphereLaw (n+1)
  let π := gibbsLaw (n+1) β (fieldOfMixture μ J)
  let κ : Vector (n+1) × Vector (n+1) → ℝ :=
    fun z => PhysicalHitting.capKilling α z.1 z.2
  let : IsProbabilityMeasure θ := sphereLaw_probability (n+1)
  let : IsProbabilityMeasure π :=
    gibbsLaw_probability (by omega : 1 ≤ n+1) β
      (fieldOfMixture_contDiff μ J).continuous
  have hrc : Continuous
      (fun z : Vector (n+1) × Vector (n+1) => overlapValue z.1 z.2) := by
    simpa only [overlapValue_eq] using
      (continuous_inner (𝕜 := ℝ) (E := Vector (n+1))).div_const ((n+1 : ℕ) : ℝ)
  have hκc : Continuous κ := by
    exact ((SphericalCapCutoff.cutoff_contDiff _ _).continuous.comp hrc).add
      ((SphericalCapCutoff.cutoff_contDiff _ _).continuous.comp hrc.neg)
  have hiκ : Integrable κ (θ.prod π) := by
    apply Integrable.of_bound hκc.aestronglyMeasurable 1
    apply Filter.Eventually.of_forall
    intro z
    change ‖PhysicalHitting.capKilling α z.1 z.2‖ ≤ 1
    rw [Real.norm_eq_abs, abs_of_nonneg (PhysicalHitting.capKilling_nonneg α z.1 z.2)]
    exact PhysicalHitting.capKilling_le_one hα z.1 z.2
  have hinner : Integrable (fun x => ∫ u, κ (u,x) ∂θ) π :=
    hiκ.integral_prod_right
  have haxis : ∀ᵐ x ∂π,
      (∫ u, κ (u,x) ∂θ) ≤
        C * Real.exp (-((n+1 : ℕ) : ℝ) * α^2 / 64) := by
    filter_upwards [gibbsLaw_support (by omega : 1 ≤ n+1) β
      (fieldOfMixture μ J)] with x hx
    exact hn x hx
  have hmono : (∫ x, ∫ u, κ (u,x) ∂θ ∂π) ≤
      ∫ _ : Vector (n+1),
        C * Real.exp (-((n+1 : ℕ) : ℝ) * α^2 / 64) ∂π :=
    integral_mono_ae hinner (integrable_const _) haxis
  change (∫ z, κ z ∂θ.prod π) ≤ _
  rw [integral_prod_symm _ hiκ]
  calc
    _ ≤ ∫ _ : Vector (n+1),
      C * Real.exp (-((n+1 : ℕ) : ℝ) * α^2 / 64) ∂π := hmono
    _ = C * Real.exp (-((n+1 : ℕ) : ℝ) * α^2 / 64) := by
      simp only [integral_const,probReal_univ,one_smul]

end SlowEquilibration.ConditionedEntrance
