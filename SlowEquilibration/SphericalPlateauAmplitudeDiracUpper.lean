-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalPlateauAmplitudeDiracWindow
public import SlowEquilibration.SphericalPlateauAmplitudeLatitudeFeature
public import SlowEquilibration.GaussianFeatureDiracUpper

@[expose] public section

/-! # Genuine compact Dirac upper for the perturbed source bank

The literal independent tensor-bank pressure is bounded by its fixed
original Dirac trial. The dimension threshold is uniform over the actual
amplitude box, both latitude signs, and every reference and latitude frame.
-/
namespace SlowEquilibration.SphericalPlateauAmplitudeModel
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open SphericalModel
open scoped Topology RealInnerProductSpace
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Actual perturbed-bank latitude pressure, with no pressure, positivity
or covariance conclusion supplied as a hypothesis. -/
theorem amplitudeLatitudeQuenchedPressure_eventually_uniform_dirac_upper
    (μ : FiniteMixture) (β : ℝ) (p₀ : Degree μ.maxDegree) {δ ρ : ℝ}
    (hδ : 0<δ) (hδρ : δ≤ρ) (hρ : ρ<1) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ n : ℕ in atTop,∀ (s : Fin 2 → ℝ),(∀ j,|s j|≤2) →
      ∀ r : ℝ,|r|∈Icc δ ρ → ∀ (u : Vector (n+1)),‖u‖^2=((n+1 : ℕ) : ℝ) →
      ∀ (e : Vector n →ₗᵢ[ℝ] Vector (n+1)),(∀ x,inner ℝ (e x) u=0) →
        amplitudeLatitudeQuenchedPressure n μ β u e p₀ s r≤amplitudeDiracTrial μ β p₀ s r+ε := by
  classical
  let Z := ↥(amplitudeDiracParameterSet δ ρ)
  let : CompactSpace Z := isCompact_iff_compactSpace.mp (amplitudeDiracParameterSet_compact δ ρ)
  let ξ : Z → ℝ → ℝ := fun z => amplitudeLatitudeCovariance μ p₀ z.val.1 z.val.2
  let t : Z → ℝ := fun z => amplitudeDiracAtom z.val.2
  let d : Z → ℝ := fun z => amplitudeLatitudeCovarianceFirst μ p₀ z.val.1 z.val.2 (t z)
  have ht : Continuous t := amplitudeDiracAtom_continuous.comp (continuous_snd.comp continuous_subtype_val)
  have hd : Continuous d := (amplitudeDirac_first_continuous μ p₀).comp continuous_subtype_val
  have htrange (z : Z) : t z∈Ico (0 : ℝ) 1 := amplitudeDiracAtom_mem z.val.2
  have hdnonneg (z : Z) : 0≤d z := by
    have hr := ((mem_amplitudeDiracParameterSet_iff δ ρ z.val).mp z.property).2
    exact amplitudeLatitudeCovarianceFirst_nonneg μ p₀ z.val.1 (hr.2.trans hρ.le)
      (amplitudeDiracAtom_mem z.val.2).1
  obtain ⟨η,C,hη,hη1,hC,hDef⟩ := exists_uniform_amplitudeDiracTangentDeficit_bound μ p₀ hδ hδρ hρ
  have hDefZ (z : Z) (R : ℝ) (hR : R∈Icc (-1 : ℝ) 1) :
      ξ z (t z)+d z*(R-t z)-ξ z R≤C*({r : ℝ | r< -η}.indicator (fun _ => (1 : ℝ))) R := by
    have hz := (mem_amplitudeDiracParameterSet_iff δ ρ z.val).mp z.property
    exact hDef z.val.1 hz.1 z.val.2 hz.2 R hR
  have hUpper := GaussianFeatureDirac.eventually_uniform_dirac_upper β ξ t d ht hd htrange hdnonneg
    hη hη1 hC hDefZ hε
  filter_upwards [hUpper,eventually_ge_atTop 1] with n hUpper hn
  intro s hs r hr u hu e he
  let z : Z := ⟨(s,r),(mem_amplitudeDiracParameterSet_iff δ ρ (s,r)).mpr ⟨hs,hr⟩⟩
  have hA := amplitudeLatitudeBankFeature_continuous μ u e p₀ s r
  have hGram (x y : Vector n) (_hx : ‖x‖^2=(n : ℝ)) (_hy : ‖y‖^2=(n : ℝ)) :
      inner ℝ (amplitudeLatitudeBankFeature μ u e p₀ s r x)
        (amplitudeLatitudeBankFeature μ u e p₀ s r y)=((n+1 : ℕ) : ℝ)*ξ z (overlap x y) :=
    amplitudeLatitudeBankFeature_inner hn μ u hu e he p₀ s (hr.2.trans hρ.le) x y
  have hb := hUpper z (BankCoordinate n μ) (amplitudeLatitudeBankFeature μ u e p₀ s r) hA hGram
  rw [amplitudeLatitudeQuenchedPressure_eq_gaussianMean hn μ β u e p₀ s r]
  change GaussianSpinInterpolation.averagedLogPartition (sphereLaw n)
    (amplitudeLatitudeBankLinear μ u e p₀ s r) β/((n+1 : ℕ) : ℝ)≤
      amplitudeDiracTrial μ β p₀ s r+ε at hb
  exact hb

/-- The source direction has the exact original trial plus its literal
τ(2+τ) coefficient, uniformly before every finite-volume dimension. -/
theorem amplitudeLatitudeQuenchedPressure_at_eventually_uniform_upper
    (μ : FiniteMixture) (β : ℝ) (p₀ : Degree μ.maxDegree) {δ ρ : ℝ}
    (hδ : 0<δ) (hδρ : δ≤ρ) (hρ : ρ<1) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ n : ℕ in atTop,∀ (k : Fin 2) (τ : ℝ),τ∈Icc (-1/2 : ℝ) (1/2) →
      ∀ r : ℝ,|r|∈Icc δ ρ → ∀ (u : Vector (n+1)),‖u‖^2=((n+1 : ℕ) : ℝ) →
      ∀ (e : Vector n →ₗᵢ[ℝ] Vector (n+1)),(∀ x,inner ℝ (e x) u=0) →
        amplitudeLatitudeQuenchedPressure n μ β u e p₀ (amplitudeAt k τ) r≤
          latitudePressureTrial μ β |r|+τ*(2+τ)*amplitudeDiracShiftCoefficient μ β p₀ k r+ε := by
  filter_upwards [amplitudeLatitudeQuenchedPressure_eventually_uniform_dirac_upper μ β p₀ hδ hδρ hρ hε]
    with n hUpper
  intro k τ hτ r hr u hu e he
  have hs := ((mem_amplitudeDiracParameterSet_iff δ ρ _).mp (amplitudeAt_mem_DiracParameterSet k hτ hr)).1
  have hh := hUpper (amplitudeAt k τ) hs r hr u hu e he
  rw [amplitudeDiracTrial_at,amplitudeDiracTrial_one μ β p₀ (hr.2.trans_lt hρ)] at hh
  exact hh

end
end SlowEquilibration.SphericalPlateauAmplitudeModel
