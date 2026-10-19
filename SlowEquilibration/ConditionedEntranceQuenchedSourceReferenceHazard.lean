-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntranceSourceReferenceWeightedCap
public import SlowEquilibration.ConditionedEntranceActualSourceGlobalTilt
public import SlowEquilibration.ConditionedEntrancePhysicalCapAxisMean
public import SlowEquilibration.ConditionedEntranceCutoffExponentAbsorption

/-! The literal unperturbed reference resolvent has exponentially small
physical cap hazard under the globally normalized mixed-source tilt. -/
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open SphericalAging HardSphereDynamics
open scoped NNReal
namespace SlowEquilibration.ConditionedEntrance
open SphericalModel SphericalForm SmoothKilled
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

/-- For each latitude-good original disorder, the actual base reference
resolvent weighted physical cap hazard is exponentially small under the
one globally normalized mixed-source axis–spin law. This holds uniformly
over physical cutoffs, bounded marks and positive reference rates. -/
theorem quenchedMixedSource_reference_normalized_capKilling_mean_eventually_le
    (μ : FiniteMixture) (hd : 4 ≤ μ.minDegree)
    {Q B β α : ℝ} (hQ : 0 < Q) (hQ1 : Q ≤ 1)
    (hnp : μ.minDegree < μ.maxDegree) (hB : 0 ≤ B) (hβ : 0 ≤ β)
    (hα : 0 < α)
    (hαmoment : α ≤ EntranceLatitudeTangentObservable.sourceCutoffMomentScale
      μ Q B (2*β))
    (hαenergy : α ≤ 1 / (128 * (1 + β *
      PhysicalHitting.uniformCutoffEnergyConstant μ Q B B 1 2))) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (J : Disorder (n+1) μ.maxDegree), J ∈
        EntranceLatitudeTangentObservable.originalLatitudeMeanGood n μ →
      ∀ (χ : ℝ → ℝ) (hχ : ContDiff ℝ 2 χ),
        (∀ s, |χ s| ≤ 1) → (∀ s, 2 < |s| → χ s = 0) →
      ∀ (e k : ℝ), |e| ≤ B → |k| ≤ B →
      ∀ (u : Vector (n+1)) (hu : OnSphere u),
      ∀ (θr : ℝ≥0), 0 < θr →
        let D := SourceData.atSourceParameters (by omega : 1 ≤ n+1)
          μ hnp Q hQ hQ1 α hα χ hχ (J,(u,(e,k))) hu
        let H₀ := fieldOfMixture μ J
        let w : Vector (n+1) × Vector (n+1) → ℝ := fun z =>
          β * (sourceSmoothCutoffField μ Q hQ hnp J z.1 e k α χ z.2 - H₀ z.2)
        let M := ∫ z, Real.exp (w z)
          ∂((sphereLaw (n+1)).prod (gibbsLaw (n+1) β H₀))
        (∫ z, PhysicalHitting.capKilling α z.1 z.2 *
            sourceReferencePositivePart D β θr z.2
          ∂normalizedTilt ((sphereLaw (n+1)).prod
            (gibbsLaw (n+1) β H₀)) w M) ≤
              4 * C * Real.exp (-((n+1 : ℕ) : ℝ) * α^2 / 128) := by
  obtain ⟨C,hC,hCap⟩ := physical_capKilling_axis_mean_eventually_le hα
  obtain ⟨Cm,hCm,hMom⟩ :=
    actual_mixedSource_globalTilt_mass_close_one μ hd hQ hnp hB hβ
  have hSmall := sourceTilt_eta_eventually_half μ.minDegree hd Cm
  refine ⟨C,hC,?_⟩
  filter_upwards [(tendsto_add_atTop_nat 1).eventually hCap,hMom,hSmall]
    with n hn hnorm hsmall
  intro J hJ χ hχ hχb hχR e k he hk u hu θr hθr
  dsimp only
  let D := SourceData.atSourceParameters (by omega : 1 ≤ n+1)
    μ hnp Q hQ hQ1 α hα χ hχ (J,(u,(e,k))) hu
  let H₀ := fieldOfMixture μ J
  let w : Vector (n+1) × Vector (n+1) → ℝ := fun z =>
    β * (sourceSmoothCutoffField μ Q hQ hnp J z.1 e k α χ z.2 - H₀ z.2)
  let M := ∫ z, Real.exp (w z)
    ∂((sphereLaw (n+1)).prod (gibbsLaw (n+1) β H₀))
  have hclose : |M-1| ≤ Cm*((n+1 : ℕ) : ℝ)^(1-(μ.minDegree : ℝ)/2) :=
    (hnorm J hJ α hα hαmoment χ hχ hχb hχR e k he hk).1
  have hM : 1/2 ≤ M := by
    have hl := (abs_le.mp hclose).1
    linarith
  have hJreg : J ∈ regularDisorder := hJ.1
  have hAxis : ∀ x : Vector (n+1), OnSphere x →
      (∫ v, PhysicalHitting.capKilling α v x ∂sphereLaw (n+1)) ≤
        C * Real.exp (-((n+1 : ℕ) : ℝ) * α^2 / 64) := by
    intro x hx
    exact hn x ((onSphere_iff_norm_sq x).mp hx)
  have hHaz := sourceReference_normalized_capKilling_le D β hβ θr hθr hJreg
    (hbar := B) (kbar := B) (B := 1) (R := 2)
    he hk (by norm_num) (by norm_num) hχb hχR
    (K := C * Real.exp (-((n+1 : ℕ) : ℝ) * α^2 / 64))
    (by positivity) hAxis
  have hM' : 1/2 ≤
      (∫ z, Real.exp
        (β * (sourceSmoothCutoffField D.mixture D.Q D.Q_pos D.nonpure
          D.disorder z.1 D.energyMark D.radialMark D.cutoffScale D.cutoff z.2 -
            D.baseData.hamiltonian z.2))
        ∂((sphereLaw (n+1)).prod (gibbsLaw (n+1) β D.baseData.hamiltonian))) := by
    simpa only [D,SourceData.baseData_hamiltonian,w,M,H₀,
      SourceData.atSourceParameters] using hM
  have hb := hHaz hM'
  have hAbs := PhysicalHitting.uniform_source_cutoff_cap_tail_absorption μ hd hβ
    hB hB (by norm_num : (0 : ℝ) ≤ 2) hα hαenergy (n+1)
  change (∫ z, PhysicalHitting.capKilling α z.1 z.2 *
      sourceReferencePositivePart D β θr z.2
      ∂normalizedTilt ((sphereLaw (n+1)).prod
        (gibbsLaw (n+1) β H₀)) w M) ≤ _
  have hb' : (∫ z, PhysicalHitting.capKilling α z.1 z.2 *
      sourceReferencePositivePart D β θr z.2
      ∂normalizedTilt ((sphereLaw (n+1)).prod
        (gibbsLaw (n+1) β H₀)) w M) ≤
      4 * Real.exp (β * PhysicalHitting.uniformCutoffEnergyConstant
        μ Q B B 1 2 * ((n+1 : ℕ) : ℝ) * α^μ.minDegree) *
          (C * Real.exp (-((n+1 : ℕ) : ℝ) * α^2 / 64)) := by
    simpa only [D,SourceData.baseData_hamiltonian,w,M,H₀,
      SourceData.atSourceParameters] using hb
  calc
    _ ≤ 4 * Real.exp (β * PhysicalHitting.uniformCutoffEnergyConstant
        μ Q B B 1 2 * ((n+1 : ℕ) : ℝ) * α^μ.minDegree) *
          (C * Real.exp (-((n+1 : ℕ) : ℝ) * α^2 / 64)) := hb'
    _ = 4 * C * (Real.exp (β * PhysicalHitting.uniformCutoffEnergyConstant
        μ Q B B 1 2 * ((n+1 : ℕ) : ℝ) * α^μ.minDegree) *
          Real.exp (-((n+1 : ℕ) : ℝ) * α^2 / 64)) := by ring
    _ ≤ 4 * C * Real.exp (-((n+1 : ℕ) : ℝ) * α^2 / 128) :=
      mul_le_mul_of_nonneg_left hAbs (by positivity)

end SlowEquilibration.ConditionedEntrance
