-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntranceQuenchedSourceWeightedCap
public import SlowEquilibration.ConditionedEntranceActualSourceGlobalTilt
public import SlowEquilibration.ConditionedEntranceCutoffExponentAbsorption

/-! The literal mixed-source smooth cap killing has exponentially small
mass under its one globally normalized tilt, for each good original
disorder. The same global normalizer makes the measure a probability. -/
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open SlowEquilibration.SphericalModel SlowEquilibration.SphericalForm
open SlowEquilibration.SphericalOverlapExponential
namespace SlowEquilibration.ConditionedEntrance
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

/-- For a fixed admissible small physical cap radius, the actual quenched
global source tilt is a probability and its smooth cap-killing mass is
exponentially small. The constant is uniform in the original disorder,
cutoff and bounded marks. -/
theorem quenchedMixedSource_normalized_capKilling_mean_eventually_le
    (μ : FiniteMixture) (hd : 4 ≤ μ.minDegree)
    {Q B β α : ℝ} (hQ : 0 < Q) (hQ1 : Q ≤ 1)
    (hnp : μ.minDegree < μ.maxDegree) (hB : 0 ≤ B) (hβ : 0 ≤ β)
    (hα : 0 < α)
    (hαmoment : α ≤
      EntranceLatitudeTangentObservable.sourceCutoffMomentScale μ Q B (2*β))
    (hαabsorb : α ≤ 1 / (128 * (1 + β *
      PhysicalHitting.uniformCutoffEnergyConstant μ Q B B 1 2))) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (J : Disorder (n+1) μ.maxDegree),
        J ∈ EntranceLatitudeTangentObservable.originalLatitudeMeanGood n μ →
      ∀ (χ : ℝ → ℝ), ContDiff ℝ 2 χ →
        (∀ s, |χ s| ≤ 1) → (∀ s, 2 < |s| → χ s = 0) →
      ∀ (e k : ℝ), |e| ≤ B → |k| ≤ B →
        let H₀ := fieldOfMixture μ J
        let w : Vector (n+1) × Vector (n+1) → ℝ := fun z =>
          β * (sourceSmoothCutoffField μ Q hQ hnp J z.1 e k α χ z.2 - H₀ z.2)
        let M := ∫ z, Real.exp (w z)
          ∂((sphereLaw (n+1)).prod (gibbsLaw (n+1) β H₀))
        IsProbabilityMeasure
          (normalizedTilt ((sphereLaw (n+1)).prod (gibbsLaw (n+1) β H₀)) w M) ∧
        (∫ z, PhysicalHitting.capKilling α z.1 z.2
          ∂normalizedTilt ((sphereLaw (n+1)).prod (gibbsLaw (n+1) β H₀)) w M) ≤
          2 * C * Real.exp (-((n+1 : ℕ) : ℝ) * α^2 / 128) := by
  obtain ⟨C,hC,hWeighted⟩ :=
    quenchedMixedSource_weighted_capKilling_mean_eventually_le
      μ hQ hQ1 hnp hα
  obtain ⟨Cmass,hCmass,hMass⟩ :=
    actual_mixedSource_globalTilt_mass_close_one μ hd hQ hnp hB hβ
  have hHalf := sourceTilt_eta_eventually_half μ.minDegree hd Cmass
  refine ⟨C,hC,?_⟩
  filter_upwards [hWeighted,hMass,hHalf] with n hn hm hs
  intro J hJ χ hχ hχb hχR e k he hk
  dsimp only
  let H₀ := fieldOfMixture μ J
  let w : Vector (n+1) × Vector (n+1) → ℝ := fun z =>
    β * (sourceSmoothCutoffField μ Q hQ hnp J z.1 e k α χ z.2 - H₀ z.2)
  let ν := (sphereLaw (n+1)).prod (gibbsLaw (n+1) β H₀)
  let M := ∫ z, Real.exp (w z) ∂ν
  let κ : Vector (n+1) × Vector (n+1) → ℝ := fun z =>
    PhysicalHitting.capKilling α z.1 z.2
  have hnorm := hm J hJ α hα hαmoment χ hχ hχb hχR e k he hk
  have hMclose : |M-1| ≤ Cmass*((n+1 : ℕ) : ℝ)^(1-(μ.minDegree : ℝ)/2) := hnorm.1
  have hprob : IsProbabilityMeasure (normalizedTilt ν w M) := hnorm.2 hs
  have hMhalf : 1/2 ≤ M := by
    have hl := (abs_le.mp hMclose).1
    linarith
  have hMpos : 0 < M := by linarith
  have hH : Continuous (fun z : Vector (n+1) × Vector (n+1) =>
      sourceSmoothCutoffField μ Q hQ hnp J z.1 e k α χ z.2) :=
    (sourceSmoothCutoffField_jointContinuous μ Q hQ hnp α χ hχ.continuous).comp
      (show Continuous (fun z : Vector (n+1) × Vector (n+1) =>
        ((J,(z.1,(e,k))),z.2)) by fun_prop)
  have hw : Measurable w :=
    ((hH.sub ((fieldOfMixture_contDiff μ J).continuous.comp
      continuous_snd)).const_mul β).measurable
  have hweighted : (∫ z, Real.exp (w z) * κ z ∂ν) ≤
      Real.exp (β * PhysicalHitting.uniformCutoffEnergyConstant μ Q B B 1 2 *
        ((n+1 : ℕ) : ℝ) * α^μ.minDegree) *
        (C * Real.exp (-((n+1 : ℕ) : ℝ) * α^2 / 64)) :=
    hn J hJ.1 β hβ χ hχ hχb hχR B e k hB he hk
  have habsorb := PhysicalHitting.uniform_source_cutoff_cap_tail_absorption
    μ hd hβ hB hB (by norm_num : (0 : ℝ) ≤ 2) hα hαabsorb (n+1)
  have hnum : (∫ z, Real.exp (w z) * κ z ∂ν) ≤
      C * Real.exp (-((n+1 : ℕ) : ℝ) * α^2 / 128) := by
    calc
      _ ≤ Real.exp (β * PhysicalHitting.uniformCutoffEnergyConstant μ Q B B 1 2 *
          ((n+1 : ℕ) : ℝ) * α^μ.minDegree) *
          (C * Real.exp (-((n+1 : ℕ) : ℝ) * α^2 / 64)) := hweighted
      _ = C * (Real.exp (β * PhysicalHitting.uniformCutoffEnergyConstant μ Q B B 1 2 *
          ((n+1 : ℕ) : ℝ) * α^μ.minDegree) *
          Real.exp (-((n+1 : ℕ) : ℝ) * α^2 / 64)) := by ring
      _ ≤ C * Real.exp (-((n+1 : ℕ) : ℝ) * α^2 / 128) :=
        mul_le_mul_of_nonneg_left habsorb hC.le
  refine ⟨hprob,?_⟩
  change (∫ z, κ z ∂normalizedTilt ν w M) ≤ _
  rw [integral_normalizedTilt ν w hw hMpos]
  apply (div_le_iff₀ hMpos).2
  have htail : 0 ≤ C * Real.exp (-((n+1 : ℕ) : ℝ) * α^2 / 128) := by positivity
  have hmprod := mul_le_mul_of_nonneg_left hMhalf (show 0 ≤
    2 * (C * Real.exp (-((n+1 : ℕ) : ℝ) * α^2 / 128)) by positivity)
  nlinarith only [hnum,hmprod]

end SlowEquilibration.ConditionedEntrance
