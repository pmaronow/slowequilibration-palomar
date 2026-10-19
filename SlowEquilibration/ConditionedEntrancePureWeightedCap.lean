-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntrancePureCutoffEnergy
public import SlowEquilibration.ConditionedEntrancePureAxisCapHit
public import SlowEquilibration.ConditionedEntranceQuenchedCapTotalMass

/-! The proper pure cutoff tilt preserves the exponentially small quenched
cap-killing mass, with its true `N α^p` energy cost. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.ConditionedEntrance
open MeasureTheory ProbabilityTheory Filter
open SphericalModel SphericalForm SphericalGaussianJet
open SphericalAging HardSphereDynamics
open SphericalOverlapExponential
open scoped NNReal RealInnerProductSpace
set_option autoImplicit false
set_option maxHeartbeats 900000

def pureCutoffEnergyConstant (p : ℕ) (hp : 2 ≤ p)
    (c : ℝ) (hc : 0 < c) (Q B : ℝ) : ℝ :=
  ((Real.sqrt Q)^p)⁻¹ *
    (B + EntranceLatitudeTangentObservable.sourceLatitudeCenterConstant
      (FiniteMixture.pure p hp c hc) Q + 1) * 2^p

theorem pureCutoffEnergyConstant_nonneg (p : ℕ) (hp : 2 ≤ p)
    (c : ℝ) (hc : 0 < c) (Q B : ℝ) (hB : 0 ≤ B) :
    0 ≤ pureCutoffEnergyConstant p hp c hc Q B := by
  unfold pureCutoffEnergyConstant
  have hK := (derivativeConstant_pos
    (centerCoefficients (mixtureCoefficients (FiniteMixture.pure p hp c hc)) Q)).le
  dsimp only [EntranceLatitudeTangentObservable.sourceLatitudeCenterConstant]
  positivity

theorem quenchedPureSource_weighted_capKilling_mean_eventually_le
    (p : ℕ) (hp : 4 ≤ p) (c : ℝ) (hc : 0 < c)
    {Q α : ℝ} (hQ : 0 < Q) (hα : 0 < α) :
    let μ := FiniteMixture.pure p (by omega : 2 ≤ p) c hc
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (J : Disorder (n+1) μ.maxDegree), J ∈ regularDisorder →
      ∀ (β : ℝ), 0 ≤ β →
      ∀ (χ : ℝ → ℝ) (hχ : ContDiff ℝ 2 χ),
        (∀ s, |χ s| ≤ 1) → (∀ s, 2 < |s| → χ s = 0) →
      ∀ (B e : ℝ), 0 ≤ B → |e| ≤ B →
        let H₀ := fieldOfMixture μ J
        let w : Vector (n+1) × Vector (n+1) → ℝ := fun z =>
          β * (pureSourceSmoothCutoffField p (by omega) c hc Q J
            z.1 e α χ z.2 - H₀ z.2)
        (∫ z, Real.exp (w z) * PhysicalHitting.capKilling α z.1 z.2
          ∂((sphereLaw (n+1)).prod (gibbsLaw (n+1) β H₀))) ≤
            Real.exp (β * pureCutoffEnergyConstant p (by omega) c hc Q B *
                ((n+1 : ℕ) : ℝ) * α^p) *
              (C * Real.exp (-((n+1 : ℕ) : ℝ) * α^2 / 64)) := by
  dsimp only
  let μ := FiniteMixture.pure p (by omega : 2 ≤ p) c hc
  obtain ⟨C,hC,hTail⟩ := quenchedOriginalAxisGibbs_capKilling_mean_eventually_le μ hα
  refine ⟨C,hC,?_⟩
  filter_upwards [hTail] with n hn
  intro J hJ β hβ χ hχ hχb hχR B e hB he
  let H₀ := fieldOfMixture μ J
  let σ := sphereLaw (n+1)
  let π := gibbsLaw (n+1) β H₀
  let w : Vector (n+1) × Vector (n+1) → ℝ := fun z =>
    β * (pureSourceSmoothCutoffField p (by omega) c hc Q J z.1 e α χ z.2 - H₀ z.2)
  let κ : Vector (n+1) × Vector (n+1) → ℝ := fun z =>
    PhysicalHitting.capKilling α z.1 z.2
  let W := Real.exp (β * pureCutoffEnergyConstant p (by omega) c hc Q B *
    ((n+1 : ℕ) : ℝ) * α^p)
  let : IsProbabilityMeasure σ := sphereLaw_probability (n+1)
  let : IsProbabilityMeasure π := gibbsLaw_probability (by omega : 1 ≤ n+1)
    β (fieldOfMixture_contDiff μ J).continuous
  have hH : Continuous (fun z : Vector (n+1) × Vector (n+1) =>
      pureSourceSmoothCutoffField p (by omega) c hc Q J z.1 e α χ z.2) :=
    (pure_axisJointHamiltonian_contDiff p (by omega) c hc Q α χ hχ J e).continuous
  have hw : Continuous w :=
    (hH.sub ((fieldOfMixture_contDiff μ J).continuous.comp continuous_snd)).const_mul β
  have hrc : Continuous
      (fun z : Vector (n+1) × Vector (n+1) => overlapValue z.1 z.2) := by
    simpa only [overlapValue_eq] using
      (continuous_inner (𝕜 := ℝ) (E := Vector (n+1))).div_const ((n+1 : ℕ) : ℝ)
  have hκc : Continuous κ := by
    exact ((SphericalCapCutoff.cutoff_contDiff _ _).continuous.comp hrc).add
      ((SphericalCapCutoff.cutoff_contDiff _ _).continuous.comp hrc.neg)
  have hweight : ∀ᵐ z ∂σ.prod π, Real.exp (w z) ≤ W := by
    apply (Measure.ae_prod_iff_ae_ae
      (measurableSet_le hw.rexp.measurable measurable_const)).mpr
    filter_upwards [sphereLaw_support (by omega : 1 ≤ n+1)] with u hu
    filter_upwards [gibbsLaw_support (by omega : 1 ≤ n+1) β H₀] with x hx
    have hb := regular_pure_source_cutoff_energy_difference
      n p (by omega : 2 ≤ p) c hc hQ hB hα J hJ u x
      ((onSphere_iff_norm_sq u).mpr hu)
      ((onSphere_iff_norm_sq x).mpr hx) e he χ hχb hχR
    have hh : pureSourceSmoothCutoffField p (by omega) c hc Q J u e α χ x -
        H₀ x ≤ pureCutoffEnergyConstant p (by omega) c hc Q B *
          ((n+1 : ℕ) : ℝ) * α^p := by
      exact (le_abs_self _).trans hb
    change Real.exp (w (u,x)) ≤ W
    apply Real.exp_le_exp.mpr
    dsimp only [w,W]
    calc
      β * (pureSourceSmoothCutoffField p (by omega) c hc Q J u e α χ x - H₀ x) ≤
          β * (pureCutoffEnergyConstant p (by omega) c hc Q B *
            ((n+1 : ℕ) : ℝ) * α^p) := mul_le_mul_of_nonneg_left hh hβ
      _ = _ := by ring
  have hiκ : Integrable κ (σ.prod π) := by
    apply Integrable.of_bound hκc.aestronglyMeasurable 1
    apply Filter.Eventually.of_forall
    intro z
    change ‖PhysicalHitting.capKilling α z.1 z.2‖ ≤ 1
    rw [Real.norm_eq_abs, abs_of_nonneg (PhysicalHitting.capKilling_nonneg α z.1 z.2)]
    exact PhysicalHitting.capKilling_le_one hα z.1 z.2
  have hiwκ : Integrable (fun z => Real.exp (w z) * κ z) (σ.prod π) := by
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
  have hpoint : ∀ᵐ z ∂σ.prod π,
      Real.exp (w z) * κ z ≤ W * κ z := by
    filter_upwards [hweight] with z hz
    exact mul_le_mul_of_nonneg_right hz (PhysicalHitting.capKilling_nonneg α z.1 z.2)
  have hmono : (∫ z, Real.exp (w z) * κ z ∂σ.prod π) ≤
      W * (∫ z, κ z ∂σ.prod π) := by
    simpa only [integral_const_mul] using
      integral_mono_ae hiwκ (hiκ.const_mul W) hpoint
  have hcap : (∫ z, κ z ∂σ.prod π) ≤
      C * Real.exp (-((n+1 : ℕ) : ℝ) * α^2 / 64) := hn J β
  calc
    (∫ z, Real.exp (w z) * κ z ∂σ.prod π) ≤
        W * (∫ z, κ z ∂σ.prod π) := hmono
    _ ≤ W * (C * Real.exp (-((n+1 : ℕ) : ℝ) * α^2 / 64)) :=
        mul_le_mul_of_nonneg_left hcap (Real.exp_nonneg _)

end SlowEquilibration.ConditionedEntrance
