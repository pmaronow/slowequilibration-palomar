-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalPlateauAmplitudePhysicalMomentLimit
public import SlowEquilibration.SphericalLatitudeCoarea

@[expose] public section

/-! # Uniform physical moment extraction and exact planted norm-error limit

Every choice of one physical reference axis in each dimension has vanishing
actual norm error. A choice of an offending axis would contradict that limit,
giving the true uniform estimate required by the exact joint planting law.
Only actual uniform nearby envelope upper bounds and actual uniform physical
latitude L¹ localization remain as inputs.
-/
namespace SlowEquilibration.SphericalPlateauAmplitudeModel
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open SphericalModel SphericalWeightedReplicaPlateau
open scoped Topology
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- A limit along every sequence in varying nonempty state spaces is
uniform over the entire state space before choosing any point. -/
theorem eventually_uniform_le_of_all_sequences {Ω : ℕ → Type*}
    [∀ n,Nonempty (Ω n)] (f : (n : ℕ) → Ω n → ℝ)
    (h : ∀ x : (n : ℕ) → Ω n,Tendsto (fun n => f n (x n)) atTop (𝓝 (0:ℝ))) :
    ∀ ε : ℝ,0<ε → ∀ᶠ n : ℕ in atTop,∀ y : Ω n,f n y≤ε := by
  classical
  intro ε hε
  let x : (n : ℕ) → Ω n := fun n => if hn : ∃ y : Ω n,ε<f n y then
    Classical.choose hn else Classical.choice (inferInstance : Nonempty (Ω n))
  filter_upwards [(h x).eventually (gt_mem_nhds hε)] with n hn
  have hNo : ¬∃ y : Ω n,ε<f n y := by
    intro hBad
    have hxBad : ε<f n (x n) := by
      dsimp only [x]
      rw [dite_eq_left hBad]
      exact Classical.choose_spec hBad
    linarith
  intro y
  exact not_lt.mp (fun hy => hNo ⟨y,hy⟩)

/-- Exact all-axis uniformization of a true spherical sequence theorem.
No measurable choice of axes is required. -/
theorem eventually_uniform_sphere_le_of_all_axis_sequences
    (f : (n : ℕ) → Vector (n+1) → ℝ)
    (h : ∀ x : (n : ℕ) → Vector (n+1),(∀ n,‖x n‖^2=((n+1:ℕ):ℝ)) →
      Tendsto (fun n => f n (x n)) atTop (𝓝 (0:ℝ))) :
    ∀ ε : ℝ,0<ε → ∀ᶠ n : ℕ in atTop,∀ y : Vector (n+1),
      ‖y‖^2=((n+1:ℕ):ℝ) → f n y≤ε := by
  let Ω := fun n => {y : Vector (n+1) // ‖y‖^2=((n+1:ℕ):ℝ)}
  let _ : ∀ n,Nonempty (Ω n) := fun n => ⟨⟨latitudeChartPole n,latitudeChartPole_norm_sq n⟩⟩
  have hu := eventually_uniform_le_of_all_sequences (fun (n : ℕ) (y : Ω n) => f n y.val)
    (fun (x : (n : ℕ) → Ω n) => h (fun n => (x n).val) (fun n => (x n).property))
  intro ε hε
  filter_upwards [hu ε hε] with n hn
  intro y hy
  exact hn ⟨y,hy⟩

/-- Actual uniform nearby amplitude upper bounds and actual uniform
latitude L¹ localization close the genuine joint planted norm-error limit.
The all-finite contact, derivatives, moments, Jensen and planting-law
transport are proved internally by the imported providers. -/
theorem general_sourceNormError_planted_tendsto_of_uniform_upper_localization
    (μ : FiniteMixture) {β δ q₁ q₂ ρ : ℝ}
    (hβ : Thresholds.dynamicalThreshold μ.xi<β)
    (hβs : β<Thresholds.staticThreshold μ.xi) (hc : IsAdmissibleCollar μ β q₁ q₂)
    (hδ : 0≤δ) (p₀ : Degree μ.maxDegree) (hp₀ : 0 < mixtureCoefficients μ p₀)
    (hqρ : Thresholds.qStar μ.xi β≤ρ) (hρ : ρ<1)
    (hUpper : ∀ k : Fin 2,∀ τ∈Ioo (-1/2:ℝ) (1/2),∀ ε : ℝ,0<ε → ∀ᶠ n : ℕ in atTop,
      ∀ x : Vector (n+1),‖x‖^2=((n+1:ℕ):ℝ) →
      amplitudeExpectedPressure μ β (plantedCoreCost μ β) δ q₁ q₂
        x (latitudeFrameAt x) p₀ (amplitudeAt k τ)≤
      weightedAmplitudeTrialEnvelope μ β δ q₁ q₂ p₀ k ρ
        ((μ.qStar_solves_plateau hβ).1.1.le.trans hqρ) hρ τ+ε)
    (hLatitude : ∀ ε : ℝ,0<ε → ∀ᶠ n : ℕ in atTop,∀ x : Vector (n+1),
      ‖x‖^2=((n+1:ℕ):ℝ) → amplitudeLatitudeL1 μ β (plantedCoreCost μ β) δ q₁ q₂
        (Thresholds.qStar μ.xi β) x (latitudeFrameAt x) p₀ (fun _ => 1)≤ε) :
    Tendsto (fun N => ∫ z : Disorder N μ.maxDegree × Vector N,
      sourceNormError μ β (plantedCoreCost μ β) δ q₁ q₂ (Thresholds.qStar μ.xi β) z
      ∂plantedLaw (mixtureCoefficients μ) β) atTop (𝓝 (0:ℝ)) := by
  have hq : Thresholds.qStar μ.xi β∈Icc (0:ℝ) 1 :=
    ⟨(μ.qStar_solves_plateau hβ).1.1.le,(μ.qStar_solves_plateau hβ).1.2.le⟩
  apply sourceNormError_planted_tendsto_of_uniform_bank μ β (plantedCoreCost μ β) δ q₁ q₂ hq p₀
  have hu := eventually_uniform_sphere_le_of_all_axis_sequences
    (fun n x => ∫ D,amplitudeNormError μ β (plantedCoreCost μ β) δ q₁ q₂
      (Thresholds.qStar μ.xi β) x (latitudeFrameAt x) p₀ (fun _ => 1) D ∂bankLaw n μ) (by
      intro x hx
      have hLat : Tendsto (fun n => amplitudeLatitudeL1 μ β (plantedCoreCost μ β) δ q₁ q₂
          (Thresholds.qStar μ.xi β) (x n) (latitudeFrameAt (x n)) p₀ (fun _ => 1)) atTop (𝓝 (0:ℝ)) := by
        apply Metric.tendsto_nhds.mpr
        intro ε hε
        filter_upwards [hLatitude (ε/2) (half_pos hε)] with n hn
        have hn' := hn (x n) (hx n)
        have hNonneg : 0≤amplitudeLatitudeL1 μ β (plantedCoreCost μ β) δ q₁ q₂
            (Thresholds.qStar μ.xi β) (x n) (latitudeFrameAt (x n)) p₀ (fun _ => 1) := by
          unfold amplitudeLatitudeL1 amplitudeSingleAverage
          exact integral_nonneg fun D => integral_nonneg fun u => abs_nonneg _
        rw [Real.dist_eq,sub_zero,abs_of_nonneg hNonneg]
        exact hn'.trans_lt (by linarith)
      have hUp : ∀ k : Fin 2,∀ τ∈Ioo (-1/2:ℝ) (1/2),∀ ε : ℝ,0<ε → ∀ᶠ n : ℕ in atTop,
          amplitudeExpectedPressure μ β (plantedCoreCost μ β) δ q₁ q₂
            (x n) (latitudeFrameAt (x n)) p₀ (amplitudeAt k τ)≤
          weightedAmplitudeTrialEnvelope μ β δ q₁ q₂ p₀ k ρ
            ((μ.qStar_solves_plateau hβ).1.1.le.trans hqρ) hρ τ+ε := by
        intro k τ hτ ε hε
        filter_upwards [hUpper k τ hτ ε hε] with n hn
        exact hn (x n) (hx n)
      have hPair := (general_amplitudePhysicalMoments_and_pairError_tendsto_of_upper_localization
        μ hβ hβs hc hδ p₀ hp₀ hqρ hρ x hx hUp hLat).2.2
      exact amplitudeNormError_tendsto_of_pairError μ β (plantedCoreCost μ β) δ q₁ q₂ hq p₀ x hPair)
  intro ε hε
  filter_upwards [hu ε hε] with n hn
  intro x hx
  exact hn x (by simpa only [Nat.cast_add,Nat.cast_one] using hx)

end
end SlowEquilibration.SphericalPlateauAmplitudeModel
