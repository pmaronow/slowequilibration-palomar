-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalPlateauAmplitudeCompactPartitionUpper
public import SlowEquilibration.SphericalPlateauAmplitudeDenominatorLower

@[expose] public section

/-! # Genuine global sampled weighted amplitude envelope upper

A fixed polar cutoff is chosen before every amplitude, reference axis and
pressure tolerance. The compact sampled latitude bound, exact coarea profile
and annealed polar partition budget control the actual full partition.
-/
namespace SlowEquilibration.SphericalPlateauAmplitudeModel
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open SphericalModel SphericalBarycenter
open scoped Topology ENNReal
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem exists_amplitudeWeightedSampledPressure_upper (μ : FiniteMixture)
    {β δ q₁ q₂ : ℝ} (hβ : Thresholds.dynamicalThreshold μ.xi < β)
    (hβs : β < Thresholds.staticThreshold μ.xi) (hc : IsAdmissibleCollar μ β q₁ q₂)
    (hδ : 0 ≤ δ) (p₀ : Degree μ.maxDegree) :
    ∃ ρ : ℝ,∃ hqρ : Thresholds.qStar μ.xi β ≤ ρ,∃ hρ : ρ < 1,0 < ρ ∧
      ∀ ε : ℝ,0 < ε → ∃ γ : ℝ,0 < γ ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (k : Fin 2) (τ : ℝ),τ∈Icc (-1/2:ℝ) (1/2) →
      ∀ x : Vector (n+1),‖x‖^2=((n+1:ℕ):ℝ) →
        (bankLaw n μ).real {D | weightedAmplitudeTrialEnvelope μ β δ q₁ q₂ p₀ k ρ
          ((μ.qStar_solves_plateau hβ).1.1.le.trans hqρ) hρ τ+ε < Real.log (amplitudePartition μ β (plantedCoreCost μ β) δ q₁ q₂
            x (latitudeFrameAt x) p₀ (amplitudeAt k τ) D)/((n+1:ℕ):ℝ)} ≤ 2*Real.exp (-γ*((n+1:ℕ):ℝ)) := by
  let q := Thresholds.qStar μ.xi β
  let F := β^2*μ.xi 1/2-plantedCoreCost μ β
  let c := 3*(|weightedAmplitudeShift μ β p₀ 0 q|+|weightedAmplitudeShift μ β p₀ 1 q|)
  let M := F-c-1
  have hβpos : 0 < β := μ.dynamicalThreshold_pos.trans hβ
  have hq := (μ.qStar_solves_plateau hβ).1
  have hK : 0 ≤ sourceK (plantedCoreCost μ β) δ := by
    unfold sourceK
    have hJ := plantedCoreCost_pos μ hβ hβs
    linarith
  obtain ⟨ρ,hqρ,hρ,hρ0,hPolar⟩ := exists_amplitudePolarPartition_tail μ β (plantedCoreCost μ β) δ q₁ q₂ M hK
    (show q∈Ico (0:ℝ) 1 from ⟨hq.1.le,hq.2⟩)
  refine ⟨ρ,hqρ.le,hρ,hρ0,?_⟩
  intro ε hε
  obtain ⟨γ,hγ,hSample⟩ := amplitudeLatitudeSampledPressure_eventually_all_latitudes_dirac_upper μ hβpos p₀
    hρ0 hρ (by positivity : 0 < ε/6)
  refine ⟨min γ 1,lt_min hγ (by norm_num),?_⟩
  filter_upwards [hPolar,hSample,amplitudeCompactPartition_eventually_le_of_sampled_upper hρ0.le hρ (half_pos hε),
    amplitudePartition_sum_exp_eventually_le hε] with n hPolarN hSampleN hCompact hSum
  intro k τ hτ x hx
  let G := weightedAmplitudeTrialEnvelope μ β δ q₁ q₂ p₀ k ρ (hq.1.le.trans hqρ.le) hρ τ
  let s := amplitudeAt k τ
  let B : Set (BankDisorder n μ) := {D | ∃ r : ℝ,|r| ≤ ρ ∧
    amplitudeDiracTrial μ β p₀ s r+ε/6 < amplitudeLatitudeSampledPressure μ β x p₀ s r D}
  let P : Set (BankDisorder n μ) := {D | Real.exp (((n+1:ℕ):ℝ)*M) ≤ amplitudeRestrictedPartition μ β (plantedCoreCost μ β) δ q₁ q₂ x p₀ s (poleRegion x ρ) D}
  have hs : ∀ j,|s j| ≤ 2 := by
    intro j
    unfold s amplitudeAt
    split_ifs
    · exact abs_le.mpr ⟨by linarith [hτ.1],by linarith [hτ.2]⟩
    · norm_num
  have hSub : {D | G+ε < Real.log (amplitudePartition μ β (plantedCoreCost μ β) δ q₁ q₂
      x (latitudeFrameAt x) p₀ s D)/((n+1:ℕ):ℝ)}⊆B∪P := by
    intro D hD
    by_contra hBad
    have hDB : D∉B := fun h => hBad (Or.inl h)
    have hDP : D∉P := fun h => hBad (Or.inr h)
    have hGood : ∀ r : ℝ,|r| ≤ ρ → amplitudeLatitudeSampledPressure μ β x p₀ s r D ≤ amplitudeDiracTrial μ β p₀ s r+ε/6 := by
      intro r hr
      exact le_of_not_gt (fun h => hDB ⟨r,hr,h⟩)
    have hComp := hCompact μ β (plantedCoreCost μ β) δ q₁ q₂ x hx p₀ s D (Icc (-ρ) ρ)
      measurableSet_Icc (fun r hr => abs_le.mpr hr) G
      (fun r hr => by
        have ht : ε/2/3=ε/6 := by ring
        simpa only [ht] using hGood r (abs_le.mpr hr))
      (fun r hr => weightedAmplitudeBankTrial_le_envelope μ β δ q₁ q₂ p₀ k τ
        (hq.1.le.trans hqρ.le) hρ (abs_le.mpr hr))
    have hG : F-c ≤ G := amplitudeWeightedEnvelope_uniform_lower μ hβ hc p₀ hqρ.le hρ k hτ
    have hP : amplitudeRestrictedPartition μ β (plantedCoreCost μ β) δ q₁ q₂ x p₀ s (poleRegion x ρ) D ≤ Real.exp (((n+1:ℕ):ℝ)*(G+ε/2)) := by
      apply (le_of_lt (lt_of_not_ge hDP)).trans
      apply Real.exp_le_exp.mpr
      have hN : 0 ≤ ((n+1:ℕ):ℝ) := by positivity
      dsimp only [M]
      nlinarith
    have hZ := (amplitudePartition_le_compact_add_polar μ β (plantedCoreCost μ β) δ q₁ q₂ ρ x p₀ s D).trans
      (add_le_add hComp hP)
    have hZ' := hZ.trans (hSum G)
    have hLog := (Real.log_le_iff_le_exp (amplitudePartition_pos μ β (plantedCoreCost μ β) δ q₁ q₂
      x (latitudeFrameAt x) p₀ s D)).mpr hZ'
    have hPressure : Real.log (amplitudePartition μ β (plantedCoreCost μ β) δ q₁ q₂
        x (latitudeFrameAt x) p₀ s D)/((n+1:ℕ):ℝ) ≤ G+ε := by
      apply (div_le_iff₀ (by positivity : 0 < ((n+1:ℕ):ℝ))).mpr
      nlinarith
    exact (not_lt_of_ge hPressure) hD
  have hS := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hSampleN s hs x hx)
  have hS' : (bankLaw n μ).real B ≤ Real.exp (-γ*((n+1:ℕ):ℝ)) := by
    simpa only [Measure.real,ENNReal.toReal_ofReal (Real.exp_nonneg _),B] using hS
  have hP' : (bankLaw n μ).real P ≤ Real.exp (-((n+1:ℕ):ℝ)) := hPolarN x hx p₀ s hs
  apply ((measureReal_mono hSub).trans ((measureReal_union_le B P).trans (add_le_add hS' hP'))).trans
  have hN : 0 ≤ ((n+1:ℕ):ℝ) := by positivity
  have h1 : Real.exp (-γ*((n+1:ℕ):ℝ)) ≤ Real.exp (-(min γ 1)*((n+1:ℕ):ℝ)) :=
    Real.exp_le_exp.mpr (by nlinarith [min_le_left γ (1:ℝ)])
  have h2 : Real.exp (-((n+1:ℕ):ℝ)) ≤ Real.exp (-(min γ 1)*((n+1:ℕ):ℝ)) :=
    Real.exp_le_exp.mpr (by nlinarith [min_le_right γ (1:ℝ)])
  nlinarith

end
end SlowEquilibration.SphericalPlateauAmplitudeModel
