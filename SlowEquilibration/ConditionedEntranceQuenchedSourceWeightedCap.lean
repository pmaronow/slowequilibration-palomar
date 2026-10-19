-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntranceQuenchedCapTotalMass
public import SlowEquilibration.ConditionedEntrancePhysicalCutoffEnergy
public import SlowEquilibration.ConditionedEntranceJointHamiltonian

/-! The actual smooth source cutoff weight preserves the exponentially
small quenched physical cap mass, with its explicit energy cost. -/
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open SlowEquilibration.SphericalModel
open SlowEquilibration.SphericalForm
open SlowEquilibration.SphericalOverlapExponential
open SphericalAging HardSphereDynamics
namespace SlowEquilibration.ConditionedEntrance
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

/-- For every regular original disorder, the literal mixed source
cutoff weight costs at most its uniform cutoff energy in the quenched
physical cap-killing mass. The constant is uniform in disorder, marks,
cutoff, and dimension. -/
theorem quenchedMixedSource_weighted_capKilling_mean_eventually_le
    (μ : FiniteMixture) {Q : ℝ} (hQ : 0 < Q) (hQ1 : Q ≤ 1)
    (hnp : μ.minDegree < μ.maxDegree) {α : ℝ} (hα : 0 < α) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (J : Disorder (n+1) μ.maxDegree), J ∈ regularDisorder →
      ∀ (β : ℝ), 0 ≤ β →
      ∀ (χ : ℝ → ℝ), ContDiff ℝ 2 χ →
        (∀ s, |χ s| ≤ 1) → (∀ s, 2 < |s| → χ s = 0) →
      ∀ (B e k : ℝ), 0 ≤ B → |e| ≤ B → |k| ≤ B →
        let H₀ := fieldOfMixture μ J
        let w : Vector (n+1) × Vector (n+1) → ℝ := fun z =>
          β * (sourceSmoothCutoffField μ Q hQ hnp J z.1 e k α χ z.2 - H₀ z.2)
        (∫ z, Real.exp (w z) * PhysicalHitting.capKilling α z.1 z.2
          ∂((sphereLaw (n+1)).prod (gibbsLaw (n+1) β H₀))) ≤
            Real.exp (β * PhysicalHitting.uniformCutoffEnergyConstant μ Q B B 1 2 *
                ((n+1 : ℕ) : ℝ) * α^μ.minDegree) *
              (C * Real.exp (-((n+1 : ℕ) : ℝ) * α^2 / 64)) := by
  obtain ⟨C,hC,hTail⟩ := quenchedOriginalAxisGibbs_capKilling_mean_eventually_le μ hα
  refine ⟨C,hC,?_⟩
  filter_upwards [hTail] with n hn
  intro J hJ β hβ χ hχ hχb hχR B e k hB he hk
  dsimp only
  let H₀ := fieldOfMixture μ J
  let θ := sphereLaw (n+1)
  let π := gibbsLaw (n+1) β H₀
  let w : Vector (n+1) × Vector (n+1) → ℝ := fun z =>
    β * (sourceSmoothCutoffField μ Q hQ hnp J z.1 e k α χ z.2 - H₀ z.2)
  let κ : Vector (n+1) × Vector (n+1) → ℝ := fun z =>
    PhysicalHitting.capKilling α z.1 z.2
  let W := Real.exp (β * PhysicalHitting.uniformCutoffEnergyConstant μ Q B B 1 2 *
    ((n+1 : ℕ) : ℝ) * α^μ.minDegree)
  let : IsProbabilityMeasure θ := sphereLaw_probability (n+1)
  let : IsProbabilityMeasure π := gibbsLaw_probability (by omega : 1 ≤ n+1) β
    (fieldOfMixture_contDiff μ J).continuous
  have hH : Continuous (fun z : Vector (n+1) × Vector (n+1) =>
      sourceSmoothCutoffField μ Q hQ hnp J z.1 e k α χ z.2) :=
    (sourceSmoothCutoffField_jointContinuous μ Q hQ hnp α χ hχ.continuous).comp
      (show Continuous (fun z : Vector (n+1) × Vector (n+1) =>
        ((J,(z.1,(e,k))),z.2)) by fun_prop)
  have hw : Continuous w :=
    (hH.sub ((fieldOfMixture_contDiff μ J).continuous.comp continuous_snd)).const_mul β
  have hrc : Continuous
      (fun z : Vector (n+1) × Vector (n+1) => overlapValue z.1 z.2) := by
    simpa only [overlapValue_eq] using
      (continuous_inner (𝕜 := ℝ) (E := Vector (n+1))).div_const ((n+1 : ℕ) : ℝ)
  have hκc : Continuous κ := by
    exact ((SphericalCapCutoff.cutoff_contDiff _ _).continuous.comp hrc).add
      ((SphericalCapCutoff.cutoff_contDiff _ _).continuous.comp hrc.neg)
  have hweight : ∀ᵐ z ∂θ.prod π, Real.exp (w z) ≤ W := by
    apply (Measure.ae_prod_iff_ae_ae
      (measurableSet_le hw.rexp.measurable measurable_const)).mpr
    filter_upwards [sphereLaw_support (by omega : 1 ≤ n+1)] with u hu
    filter_upwards [gibbsLaw_support (by omega : 1 ≤ n+1) β H₀] with x hx
    let D : SmoothKilled.SourceData (n+1) := {
      dimension_ge_one := by omega
      mixture := μ
      nonpure := hnp
      Q := Q
      Q_pos := hQ
      Q_le_one := hQ1
      disorder := J
      axis := u
      axis_onSphere := (onSphere_iff_norm_sq u).mpr hu
      energyMark := e
      radialMark := k
      cutoffScale := α
      cutoffScale_pos := hα
      cutoff := χ
      cutoff_smooth := hχ }
    have hb := PhysicalHitting.regular_source_cutoff_weight_uniform_bound
      D hJ x ((onSphere_iff_norm_sq x).mpr hx) hβ he hk
      (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) ≤ 2) hχb hχR
    change Real.exp (w (u,x)) ≤ W at hb
    exact hb
  have hiκ : Integrable κ (θ.prod π) := by
    apply Integrable.of_bound hκc.aestronglyMeasurable 1
    apply Filter.Eventually.of_forall
    intro z
    change ‖PhysicalHitting.capKilling α z.1 z.2‖ ≤ 1
    rw [Real.norm_eq_abs, abs_of_nonneg (PhysicalHitting.capKilling_nonneg α z.1 z.2)]
    exact PhysicalHitting.capKilling_le_one hα z.1 z.2
  have hiwκ : Integrable (fun z => Real.exp (w z) * κ z) (θ.prod π) := by
    apply Integrable.of_bound (hw.rexp.mul hκc).aestronglyMeasurable W
    filter_upwards [hweight] with z hz
    change |Real.exp (w z) * κ z| ≤ W
    rw [abs_of_nonneg
      (mul_nonneg (Real.exp_nonneg _) (PhysicalHitting.capKilling_nonneg α z.1 z.2))]
    calc
      Real.exp (w z) * κ z ≤ W * κ z :=
        mul_le_mul_of_nonneg_right hz (PhysicalHitting.capKilling_nonneg α z.1 z.2)
      _ ≤ W * 1 := mul_le_mul_of_nonneg_left
        (PhysicalHitting.capKilling_le_one hα z.1 z.2) (Real.exp_nonneg _)
      _ = W := mul_one _
  have hpoint : ∀ᵐ z ∂θ.prod π,
      Real.exp (w z) * κ z ≤ W * κ z := by
    filter_upwards [hweight] with z hz
    exact mul_le_mul_of_nonneg_right hz (PhysicalHitting.capKilling_nonneg α z.1 z.2)
  have hmono : (∫ z, Real.exp (w z) * κ z ∂θ.prod π) ≤
      W * (∫ z, κ z ∂θ.prod π) := by
    simpa only [integral_const_mul] using
      integral_mono_ae hiwκ (hiκ.const_mul W) hpoint
  have hcap : (∫ z, κ z ∂θ.prod π) ≤
      C * Real.exp (-((n+1 : ℕ) : ℝ) * α^2 / 64) := hn J β
  calc
    (∫ z, Real.exp (w z) * κ z ∂θ.prod π) ≤
        W * (∫ z, κ z ∂θ.prod π) := hmono
    _ ≤ W * (C * Real.exp (-((n+1 : ℕ) : ℝ) * α^2 / 64)) :=
        mul_le_mul_of_nonneg_left hcap (Real.exp_nonneg _)

end SlowEquilibration.ConditionedEntrance
