-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalPlateauAmplitudeWeightedLatitude

@[expose] public section

/-! # Actual compact weighted partitions from the sampled latitude upper

The physical coarea profile identity absorbs its genuine entropy coefficient
and chart prefactor uniformly in every field, axis and compact latitude set.
-/
namespace SlowEquilibration.SphericalPlateauAmplitudeModel
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open SphericalModel SphericalBarycenter
open scoped Topology
set_option maxHeartbeats 1700000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem amplitudeCompactPartition_eventually_le_of_sampled_upper
    {ρ ε : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,∀ (μ : FiniteMixture) (β J δ q₁ q₂ : ℝ)
      (x : Vector (n+1)),‖x‖^2=((n+1:ℕ):ℝ) →
      ∀ (p₀ : Degree μ.maxDegree) (s : Fin 2 → ℝ) (D : BankDisorder n μ)
        (A : Set ℝ),MeasurableSet A → (∀ r∈A,|r| ≤ ρ) → ∀ M : ℝ,
      (∀ r∈A,amplitudeLatitudeSampledPressure μ β x p₀ s r D ≤ amplitudeDiracTrial μ β p₀ s r+ε/3) →
      (∀ r∈A,β^2*μ.xi r+amplitudeDiracTrial μ β p₀ s r+Real.log (1-r^2)/2-
        2*sourceProfile J δ q₁ q₂ r ≤ M) →
      amplitudeRestrictedPartition μ β J δ q₁ q₂ x p₀ s (overlapRegion x A) D ≤ Real.exp (((n+1:ℕ):ℝ)*(M+ε)) := by
  have hThird : 0 < ε/3 := by positivity
  filter_upwards [amplitudeEntropyCorrection_eventually_le hρ0 hρ1 hThird,
    partitionOn_eventually_le_of_latitudeProfile_upper hThird,eventually_ge_atTop 1] with n hEntropy hLaplace hn
  intro μ β J δ q₁ q₂ x hx p₀ s D A hA hAr M hSample hTrial
  rw [amplitudeRestrictedPartition_eq_partitionOn]
  have hh := hLaplace 1 (amplitudeSourcePotential μ β J δ q₁ q₂ x p₀ s D)
    (amplitudeSourcePotential_continuous μ β J δ q₁ q₂ x p₀ s D) x hx A hA (M+2*ε/3) (by
      intro r hr _
      have hrρ := hAr r hr
      rw [amplitudeLatitude_weighted_profile hn μ β J δ q₁ q₂ x hx p₀ s
        (hrρ.trans hρ1.le) D]
      have hE := hEntropy r hrρ
      have hS := hSample r hr
      have hT := hTrial r hr
      linarith)
  convert hh using 1
  congr 1
  ring

theorem amplitudeWeightedEnvelope_uniform_lower (μ : FiniteMixture)
    {β δ q₁ q₂ : ℝ} (hβ : Thresholds.dynamicalThreshold μ.xi < β)
    (hc : IsAdmissibleCollar μ β q₁ q₂) (p₀ : Degree μ.maxDegree)
    {ρ : ℝ} (hqρ : Thresholds.qStar μ.xi β ≤ ρ) (hρ : ρ < 1)
    (k : Fin 2) {τ : ℝ} (hτ : τ∈Icc (-1/2:ℝ) (1/2)) :
    β^2*μ.xi 1/2-plantedCoreCost μ β-
        3*(|weightedAmplitudeShift μ β p₀ 0 (Thresholds.qStar μ.xi β)|+
          |weightedAmplitudeShift μ β p₀ 1 (Thresholds.qStar μ.xi β)|) ≤ weightedAmplitudeTrialEnvelope μ β δ q₁ q₂ p₀ k ρ
        ((μ.qStar_solves_plateau hβ).1.1.le.trans hqρ) hρ τ := by
  let q := Thresholds.qStar μ.xi β
  let c := weightedAmplitudeShift μ β p₀ k q
  have hq := (μ.qStar_solves_plateau hβ).1
  have hqabs : |q| ≤ ρ := by rw [abs_of_pos hq.1];exact hqρ
  have hTrial := weightedAmplitudeBankTrial_le_envelope μ β δ q₁ q₂ p₀ k τ
    (hq.1.le.trans hqρ) hρ hqabs
  rw [weightedAmplitudeBankTrial_at μ β δ q₁ q₂ p₀ k τ (by rw [abs_of_pos hq.1];exact hq.2),
    weightedAmplitudeTrialProfile_qStar μ hβ hc δ] at hTrial
  have hCoeff : |τ*(2+τ)| ≤ 3 := by
    have ht1 := hτ.1
    have ht2 := hτ.2
    rw [abs_mul]
    have ha : |τ| ≤ 1/2 := abs_le.mpr ⟨by linarith,ht2⟩
    have hb : |2+τ| ≤ 5/2 := abs_le.mpr ⟨by linarith,by linarith⟩
    nlinarith [abs_nonneg τ,abs_nonneg (2+τ)]
  have hcBound : |c| ≤ |weightedAmplitudeShift μ β p₀ 0 q|+|weightedAmplitudeShift μ β p₀ 1 q| := by
    fin_cases k
    · change |weightedAmplitudeShift μ β p₀ 0 q| ≤ _
      exact le_add_of_nonneg_right (abs_nonneg _)
    · change |weightedAmplitudeShift μ β p₀ 1 q| ≤ _
      exact le_add_of_nonneg_left (abs_nonneg _)
  have hMul := mul_le_mul hCoeff hcBound (abs_nonneg c) (by norm_num : (0:ℝ) ≤ 3)
  rw [← abs_mul] at hMul
  have hLower := neg_abs_le (τ*(2+τ)*c)
  dsimp only [q,c] at *
  linarith

/-- The sum of two true exponential partition budgets is absorbed by any
fixed positive pressure tolerance, uniformly over the numerical exponent. -/
theorem amplitudePartition_sum_exp_eventually_le {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,∀ M : ℝ,
      Real.exp (((n+1:ℕ):ℝ)*(M+ε/2))+Real.exp (((n+1:ℕ):ℝ)*(M+ε/2)) ≤ Real.exp (((n+1:ℕ):ℝ)*(M+ε)) := by
  have ht := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (Real.log 2)
  have ht' : Tendsto (fun n : ℕ => Real.log 2/((n+1:ℕ):ℝ)) atTop (𝓝 (0:ℝ)) := by
    simpa only [Nat.cast_add,Nat.cast_one,mul_zero,mul_one_div] using ht
  filter_upwards [ht'.eventually (gt_mem_nhds (half_pos hε))] with n hn
  intro M
  have hN : 0 < ((n+1:ℕ):ℝ) := by positivity
  have hLog : Real.log 2 ≤ ((n+1:ℕ):ℝ)*(ε/2) := by
    have hh := (div_lt_iff₀ hN).mp hn
    linarith
  have hTwo : (2:ℝ) ≤ Real.exp (((n+1:ℕ):ℝ)*(ε/2)) :=
    (Real.log_le_iff_le_exp (by norm_num)).mp hLog
  have hm := mul_le_mul_of_nonneg_right hTwo (Real.exp_nonneg (((n+1:ℕ):ℝ)*(M+ε/2)))
  rw [← Real.exp_add] at hm
  calc
    _ = 2*Real.exp (((n+1:ℕ):ℝ)*(M+ε/2)) := by ring
    _ ≤ Real.exp (((n+1:ℕ):ℝ)*(ε/2)+((n+1:ℕ):ℝ)*(M+ε/2)) := hm
    _ = _ := by congr 1;ring

end
end SlowEquilibration.SphericalPlateauAmplitudeModel
