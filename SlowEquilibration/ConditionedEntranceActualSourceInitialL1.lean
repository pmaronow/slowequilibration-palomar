-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntrancePhysicalGlobalInitialL1

/-! The uniform-start initial-density discrepancy for the literal mixed
source cutoff at each original disorder in the latitude-good event. -/
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Metric
open SlowEquilibration.SphericalModel SlowEquilibration.SphericalForm
namespace SlowEquilibration.ConditionedEntrance
set_option autoImplicit false
set_option maxHeartbeats 500000

/-- The actual mixed source first axis moment yields a quantitative L1
initial-density comparison under its one globally normalized tilt. The
constant is chosen before dimension, disorder, cutoff and marks. -/
theorem actual_mixedSource_globalInitialDensity_l1_bound (μ : FiniteMixture)
    (hd : 4 ≤ μ.minDegree) {Q B β : ℝ} (hQ : 0 < Q)
    (hnp : μ.minDegree < μ.maxDegree) (hB : 0 ≤ B) (hβ : 0 ≤ β) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (J : Disorder (n+1) μ.maxDegree), J ∈
        EntranceLatitudeTangentObservable.originalLatitudeMeanGood n μ →
      ∀ (α : ℝ), 0 < α →
        α ≤ EntranceLatitudeTangentObservable.sourceCutoffMomentScale μ Q B (2*β) →
      ∀ (χ : ℝ → ℝ), ContDiff ℝ 2 χ → (∀ s, |χ s| ≤ 1) →
        (∀ s, 2 < |s| → χ s = 0) →
      ∀ (e k : ℝ), |e| ≤ B → |k| ≤ B →
      let H₀ := fieldOfMixture μ J
      let w : Vector (n+1) × Vector (n+1) → ℝ := fun z =>
        β * (sourceSmoothCutoffField μ Q hQ hnp J z.1 e k α χ z.2 - H₀ z.2)
      let f₀ : Vector (n+1) → ℝ := fun x => (gibbsDensity (n+1) β H₀ x)⁻¹
      let M := ∫ z, Real.exp (w z)
        ∂((sphereLaw (n+1)).prod (gibbsLaw (n+1) β H₀))
      (∫ z, |M * Real.exp (-w z) * f₀ z.2 - f₀ z.2|
        ∂normalizedTilt ((sphereLaw (n+1)).prod (gibbsLaw (n+1) β H₀)) w M) ≤
          4 * (C*((n+1 : ℕ) : ℝ)^(1-(μ.minDegree : ℝ)/2)) := by
  obtain ⟨C,hC,hMom⟩ :=
    EntranceLatitudeTangentObservable.actual_sourceSmoothCutoffField_tilt_moments
      μ hd hQ hnp hB hβ
  have hSmall := sourceTilt_eta_eventually_half μ.minDegree hd C
  refine ⟨C,hC,?_⟩
  filter_upwards [hMom,hSmall] with n hn hs
  intro J hJ α hα hαsmall χ hχ hχb hχ0 e k he hk
  dsimp only
  let H₀ := fieldOfMixture μ J
  let w : Vector (n+1) × Vector (n+1) → ℝ := fun z =>
    β * (sourceSmoothCutoffField μ Q hQ hnp J z.1 e k α χ z.2 - H₀ z.2)
  have hN : 1 ≤ n+1 := by omega
  have hH₀ : Continuous H₀ := (fieldOfMixture_contDiff μ J).continuous
  have hH : Continuous (fun z : Vector (n+1) × Vector (n+1) =>
      sourceSmoothCutoffField μ Q hQ hnp J z.1 e k α χ z.2) :=
    (sourceSmoothCutoffField_jointContinuous μ Q hQ hnp α χ hχ.continuous).comp
      (show Continuous (fun z : Vector (n+1) × Vector (n+1) =>
        ((J,(z.1,(e,k))),z.2)) by fun_prop)
  have hw : Continuous w :=
    (hH.sub (hH₀.comp continuous_snd)).const_mul β
  have haxis : ∀ᵐ x ∂gibbsLaw (n+1) β H₀,
      (∫ u, |Real.exp (w (u,x))-1| ∂sphereLaw (n+1)) ≤
        C*((n+1 : ℕ) : ℝ)^(1-(μ.minDegree : ℝ)/2) := by
    filter_upwards [gibbsLaw_support hN β H₀] with x hx
    exact (hn J hJ x hx α hα hαsmall χ hχ hχb hχ0 e k he hk).1
  have hη : 0 ≤ C*((n+1 : ℕ) : ℝ)^(1-(μ.minDegree : ℝ)/2) := by
    positivity
  exact gibbsGlobalTilt_initialDensity_l1_le_four_eta hN β H₀ hH₀ w hw hη hs haxis

/-- The same physical initial-density estimate for the proper pure source,
using its homogeneous two-atom correction rather than a mixed inverse
covariance formula. -/
theorem actual_pureSource_globalInitialDensity_l1_bound
    (p : ℕ) (hp : 4 ≤ p) (c : ℝ) (hc : 0 < c)
    {Q B β : ℝ} (hQ : 0 < Q) (hB : 0 ≤ B) (hβ : 0 ≤ β) :
    let μ := FiniteMixture.pure p (by omega) c hc
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (J : Disorder (n+1) μ.maxDegree), J ∈
        EntranceLatitudeTangentObservable.originalLatitudeMeanGood n μ →
      ∀ (α : ℝ), 0 < α →
        α ≤ EntranceLatitudeTangentObservable.sourceCutoffMomentScale μ Q B (2*β) →
      ∀ (χ : ℝ → ℝ), ContDiff ℝ 2 χ → (∀ s, |χ s| ≤ 1) →
        (∀ s, 2 < |s| → χ s = 0) →
      ∀ (e : ℝ), |e| ≤ B →
      let H₀ := fieldOfMixture μ J
      let w : Vector (n+1) × Vector (n+1) → ℝ := fun z =>
        β * (pureSourceSmoothCutoffField
          p (by omega) c hc Q J z.1 e α χ z.2 - H₀ z.2)
      let f₀ : Vector (n+1) → ℝ := fun x => (gibbsDensity (n+1) β H₀ x)⁻¹
      let M := ∫ z, Real.exp (w z)
        ∂((sphereLaw (n+1)).prod (gibbsLaw (n+1) β H₀))
      (∫ z, |M * Real.exp (-w z) * f₀ z.2 - f₀ z.2|
        ∂normalizedTilt ((sphereLaw (n+1)).prod (gibbsLaw (n+1) β H₀)) w M) ≤
          4 * (C*((n+1 : ℕ) : ℝ)^(1-(μ.minDegree : ℝ)/2)) := by
  dsimp only
  let μ := FiniteMixture.pure p (by omega) c hc
  obtain ⟨C,hC,hMom⟩ :=
    EntranceLatitudeTangentObservable.actual_pureSourceSmoothCutoffField_tilt_moments
      p hp c hc hQ hB hβ
  have hμd : 4 ≤ μ.minDegree := by
    rw [(CSPureModels.pure_degrees p (by omega) c hc).1]
    exact hp
  have hSmall := sourceTilt_eta_eventually_half μ.minDegree hμd C
  refine ⟨C,hC,?_⟩
  filter_upwards [hMom,hSmall] with n hn hs
  intro J hJ α hα hαsmall χ hχ hχb hχ0 e he
  let H₀ := fieldOfMixture μ J
  let w : Vector (n+1) × Vector (n+1) → ℝ := fun z =>
    β * (pureSourceSmoothCutoffField
      p (by omega) c hc Q J z.1 e α χ z.2 - H₀ z.2)
  have hN : 1 ≤ n+1 := by omega
  have hH₀ : Continuous H₀ := (fieldOfMixture_contDiff μ J).continuous
  have hH : Continuous (fun z : Vector (n+1) × Vector (n+1) =>
      pureSourceSmoothCutoffField p (by omega) c hc Q J z.1 e α χ z.2) :=
    (pureSourceJointHamiltonian_contDiff
      p (by omega) c hc Q α χ hχ).continuous.comp
      (show Continuous (fun z : Vector (n+1) × Vector (n+1) =>
        ((J,(z.1,(e,(0 : ℝ)))),z.2)) by fun_prop)
  have hw : Continuous w :=
    (hH.sub (hH₀.comp continuous_snd)).const_mul β
  have haxis : ∀ᵐ x ∂gibbsLaw (n+1) β H₀,
      (∫ u, |Real.exp (w (u,x))-1| ∂sphereLaw (n+1)) ≤
        C*((n+1 : ℕ) : ℝ)^(1-(μ.minDegree : ℝ)/2) := by
    filter_upwards [gibbsLaw_support hN β H₀] with x hx
    exact (hn J hJ x hx α hα hαsmall χ hχ hχb hχ0 e he).1
  have hη : 0 ≤ C*((n+1 : ℕ) : ℝ)^(1-(μ.minDegree : ℝ)/2) := by
    positivity
  exact gibbsGlobalTilt_initialDensity_l1_le_four_eta hN β H₀ hH₀ w hw hη hs haxis

end SlowEquilibration.ConditionedEntrance
