-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.ConditionedEntrancePureReferenceWeightedCap
public import SlowEquilibration.ConditionedEntranceActualSourceGlobalTilt
public import SlowEquilibration.ConditionedEntrancePhysicalCapAxisMean
public import SlowEquilibration.ConditionedEntrancePureNormalizedCap

/-! The literal unperturbed reference resolvent has exponentially small
physical cap hazard under the globally normalized proper-pure source tilt. -/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open SphericalAging HardSphereDynamics
open scoped NNReal
namespace SlowEquilibration.ConditionedEntrance
open SphericalModel SphericalForm SmoothKilledGeneral
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

set_option maxHeartbeats 900000 in
/-- For each latitude-good original disorder, the actual base reference
resolvent weighted physical cap hazard is exponentially small under the
one globally normalized proper-pure source axis–spin law. This holds uniformly
over physical cutoffs, bounded marks and positive reference rates. -/
theorem quenchedPureSource_reference_normalized_capKilling_mean_eventually_le
    (d : ℕ) (hd : 4 ≤ d) (c : ℝ) (hc : 0 < c)
    {Q B β α : ℝ} (hQ : 0 < Q) (hB : 0 ≤ B) (hβ : 0 ≤ β)
    (hα : 0 < α)
    (hαmoment : α ≤ EntranceLatitudeTangentObservable.sourceCutoffMomentScale
      (FiniteMixture.pure d (by omega : 2 ≤ d) c hc) Q B (2*β))
    (hαenergy : α ≤ 1 / (128 * (1 + β *
      pureCutoffEnergyConstant d (by omega) c hc Q B))) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (J : Disorder (n+1) (FiniteMixture.pure d (by omega : 2 ≤ d) c hc).maxDegree), J ∈
        EntranceLatitudeTangentObservable.originalLatitudeMeanGood n (FiniteMixture.pure d (by omega : 2 ≤ d) c hc) →
      ∀ (χ : ℝ → ℝ) (hχ : ContDiff ℝ 2 χ),
        (∀ s, |χ s| ≤ 1) → (∀ s, 2 < |s| → χ s = 0) →
      ∀ (e : ℝ), |e| ≤ B →
      ∀ (θr : ℝ≥0), 0 < θr →
        let D := FieldData.ofOriginal (by omega : 1 ≤ n+1) (FiniteMixture.pure d (by omega : 2 ≤ d) c hc) J
        let H₀ := fieldOfMixture (FiniteMixture.pure d (by omega : 2 ≤ d) c hc) J
        let w : Vector (n+1) × Vector (n+1) → ℝ := fun z =>
          β * (pureSourceSmoothCutoffField d (by omega) c hc Q J z.1 e α χ z.2 - H₀ z.2)
        let M := ∫ z, Real.exp (w z)
          ∂((sphereLaw (n+1)).prod (gibbsLaw (n+1) β H₀))
        (∫ z, PhysicalHitting.capKilling α z.1 z.2 *
            fieldReferencePositivePart D β θr z.2
          ∂normalizedTilt ((sphereLaw (n+1)).prod
            (gibbsLaw (n+1) β H₀)) w M) ≤
              4 * C * Real.exp (-((n+1 : ℕ) : ℝ) * α^2 / 128) := by
  let μ := FiniteMixture.pure d (by omega : 2 ≤ d) c hc
  have hdμ : μ.minDegree = d := (CSPureModels.pure_degrees d (by omega) c hc).1
  have hμd : 4 ≤ μ.minDegree := by rw [hdμ]; exact hd
  obtain ⟨C,hC,hCap⟩ := physical_capKilling_axis_mean_eventually_le hα
  obtain ⟨Cm,hCm,hMom⟩ := actual_pureSource_globalTilt_mass_close_one d hd c hc hQ hB hβ
  have hSmall := sourceTilt_eta_eventually_half μ.minDegree hμd Cm
  refine ⟨C,hC,?_⟩
  filter_upwards [(tendsto_add_atTop_nat 1).eventually hCap,hMom,hSmall]
    with n hn hnorm hsmall
  intro J hJ χ hχ hχb hχR e he θr hθr
  dsimp only
  let D := FieldData.ofOriginal (by omega : 1 ≤ n+1) μ J
  let H₀ := fieldOfMixture μ J
  let w : Vector (n+1) × Vector (n+1) → ℝ := fun z =>
    β * (pureSourceSmoothCutoffField d (by omega) c hc Q J z.1 e α χ z.2 - H₀ z.2)
  let M := ∫ z, Real.exp (w z)
    ∂((sphereLaw (n+1)).prod (gibbsLaw (n+1) β H₀))
  have hclose : |M-1| ≤ Cm*((n+1 : ℕ) : ℝ)^(1-(μ.minDegree : ℝ)/2) :=
    (hnorm J hJ α hα hαmoment χ hχ hχb hχR e he).1
  have hM : 1/2 ≤ M := by
    have hl := (abs_le.mp hclose).1
    linarith only [hl, hsmall]
  have hAxis : ∀ x : Vector (n+1), OnSphere x →
      (∫ v, PhysicalHitting.capKilling α v x ∂sphereLaw (n+1)) ≤
        C * Real.exp (-((n+1 : ℕ) : ℝ) * α^2 / 64) := by
    intro x hx
    exact hn x ((onSphere_iff_norm_sq x).mp hx)
  have hb := pureReference_normalized_capKilling_le n d (by omega) c hc
    hQ hB hα χ hχ hχb hχR J hJ.1 e he β hβ θr hθr
    (K := C * Real.exp (-((n+1 : ℕ) : ℝ) * α^2 / 64))
    (by positivity) hAxis
  simp only [FieldData.ofOriginal_hamiltonian] at hb
  have hb := hb hM
  have hAbs := pure_cutoff_cap_tail_absorption d hd c hc hB hβ hα hαenergy (n+1)
  change (∫ z, PhysicalHitting.capKilling α z.1 z.2 *
      fieldReferencePositivePart D β θr z.2
      ∂normalizedTilt ((sphereLaw (n+1)).prod
        (gibbsLaw (n+1) β H₀)) w M) ≤ _
  calc
    _ ≤ 4 * Real.exp (β * pureCutoffEnergyConstant d (by omega) c hc Q B *
        ((n+1 : ℕ) : ℝ) * α^d) *
        (C * Real.exp (-((n+1 : ℕ) : ℝ) * α^2 / 64)) := hb
    _ = 4*C*(Real.exp (β*pureCutoffEnergyConstant d (by omega) c hc Q B *
        ((n+1 : ℕ) : ℝ)*α^d)*Real.exp (-((n+1 : ℕ) : ℝ)*α^2/64)) := by ring
    _ ≤ 4*C*Real.exp (-((n+1 : ℕ) : ℝ)*α^2/128) :=
      mul_le_mul_of_nonneg_left hAbs (by positivity)

end SlowEquilibration.ConditionedEntrance
