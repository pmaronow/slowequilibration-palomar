-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalPlateauAmplitudeCompactPartitionUpper

@[expose] public section

/-! # Actual weighted numerator loses a strict exponent away from qStar

The actual sampled bank latitude bound, the proved unique trial maximizer,
physical coarea and the annealed polar budget give a genuine uniform
restricted-partition upper. No weighted mass or source limit is an input.
-/
namespace SlowEquilibration.SphericalPlateauAmplitudeModel
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open SphericalModel SphericalBarycenter
open scoped Topology ENNReal
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem exists_amplitudeRestrictedPartition_away_upper (μ : FiniteMixture)
    {β δ q₁ q₂ d : ℝ} (hβ : Thresholds.dynamicalThreshold μ.xi < β)
    (hβs : β < Thresholds.staticThreshold μ.xi) (hc : IsAdmissibleCollar μ β q₁ q₂)
    (hδ : 0 ≤ δ) (p₀ : Degree μ.maxDegree) (hd : 0 < d) :
    ∃ η : ℝ,0 < η ∧ ∃ γ : ℝ,0 < γ ∧ ∀ᶠ n : ℕ in atTop,
      ∀ x : Vector (n+1),‖x‖^2=((n+1:ℕ):ℝ) →
        (bankLaw n μ).real {D | Real.exp (((n+1:ℕ):ℝ)*
          (β^2*μ.xi 1/2-plantedCoreCost μ β-η)) ≤
          amplitudeRestrictedPartition μ β (plantedCoreCost μ β) δ q₁ q₂ x p₀ (fun _ => 1)
            (overlapRegion x {r : ℝ | d ≤ |r-Thresholds.qStar μ.xi β|}) D} ≤
          2*Real.exp (-γ*((n+1:ℕ):ℝ)) := by
  let q := Thresholds.qStar μ.xi β
  let F := β^2*μ.xi 1/2-plantedCoreCost μ β
  let A : Set ℝ := {r | d ≤ |r-q|}
  have hA : MeasurableSet A := (isClosed_le continuous_const ((continuous_id.sub continuous_const).abs)).measurableSet
  have hβpos : 0 < β := μ.dynamicalThreshold_pos.trans hβ
  have hq := (μ.qStar_solves_plateau hβ).1
  have hK : 0 ≤ sourceK (plantedCoreCost μ β) δ := by
    unfold sourceK
    have hJ := plantedCoreCost_pos μ hβ hβs
    linarith
  obtain ⟨ρ,hqρ,hρ,hρ0,hPolar⟩ := exists_amplitudePolarPartition_tail μ β (plantedCoreCost μ β) δ q₁ q₂ (F-1) hK
    (show q∈Ico (0:ℝ) 1 from ⟨hq.1.le,hq.2⟩)
  obtain ⟨a,ha,hGap⟩ := weightedAmplitudeTrialProfile_away_gap μ hβ hβs hc hδ hρ hd
  let ζ := min (a/4) (1/4:ℝ)
  have hζ : 0 < ζ := lt_min (by positivity) (by norm_num)
  have hζa : ζ ≤ a/4 := min_le_left _ _
  have hζ1 : ζ ≤ (1/4:ℝ) := min_le_right _ _
  obtain ⟨γ,hγ,hSample⟩ := amplitudeLatitudeSampledPressure_eventually_all_latitudes_dirac_upper μ hβpos p₀
    hρ0 hρ (by positivity : 0 < a/6)
  refine ⟨ζ/2,half_pos hζ,min γ 1,lt_min hγ (by norm_num),?_⟩
  filter_upwards [hPolar,hSample,amplitudeCompactPartition_eventually_le_of_sampled_upper hρ0.le hρ
    (half_pos ha),amplitudePartition_sum_exp_eventually_le (by positivity : 0 < 2*ζ)]
    with n hPolarN hSampleN hCompact hSum
  intro x hx
  let B : Set (BankDisorder n μ) := {D | ∃ r : ℝ,|r| ≤ ρ ∧
    amplitudeDiracTrial μ β p₀ (fun _ => 1) r+a/6 <
      amplitudeLatitudeSampledPressure μ β x p₀ (fun _ => 1) r D}
  let P : Set (BankDisorder n μ) := {D | Real.exp (((n+1:ℕ):ℝ)*(F-1)) ≤
    amplitudeRestrictedPartition μ β (plantedCoreCost μ β) δ q₁ q₂ x p₀ (fun _ => 1) (poleRegion x ρ) D}
  have hSub : {D | Real.exp (((n+1:ℕ):ℝ)*(F-ζ/2)) ≤
      amplitudeRestrictedPartition μ β (plantedCoreCost μ β) δ q₁ q₂ x p₀ (fun _ => 1)
        (overlapRegion x A) D}⊆B∪P := by
    intro D hD
    by_contra hBad
    have hDB : D∉B := fun h => hBad (Or.inl h)
    have hDP : D∉P := fun h => hBad (Or.inr h)
    have hGood : ∀ r : ℝ,|r| ≤ ρ → amplitudeLatitudeSampledPressure μ β x p₀ (fun _ => 1) r D ≤
        amplitudeDiracTrial μ β p₀ (fun _ => 1) r+a/6 := by
      intro r hr
      exact le_of_not_gt (fun h => hDB ⟨r,hr,h⟩)
    have hComp := hCompact μ β (plantedCoreCost μ β) δ q₁ q₂ x hx p₀ (fun _ => 1) D (A∩Icc (-ρ) ρ)
      (hA.inter measurableSet_Icc) (fun r hr => abs_le.mpr hr.2) (F-a)
      (fun r hr => by
        have ht : a/2/3=a/6 := by ring
        simpa only [ht] using hGood r (abs_le.mpr hr.2))
      (fun r hr => by
        rw [weightedAmplitudeBankTrial_one μ β δ q₁ q₂ p₀ ((abs_le.mpr hr.2).trans_lt hρ)]
        exact hGap r (abs_le.mpr hr.2) hr.1)
    have hN : 0 < ((n+1:ℕ):ℝ) := by positivity
    have hComp' : amplitudeRestrictedPartition μ β (plantedCoreCost μ β) δ q₁ q₂ x p₀ (fun _ => 1)
        (overlapRegion x (A∩Icc (-ρ) ρ)) D ≤ Real.exp (((n+1:ℕ):ℝ)*(F-2*ζ)) := by
      apply hComp.trans
      apply Real.exp_le_exp.mpr
      nlinarith
    have hP' : amplitudeRestrictedPartition μ β (plantedCoreCost μ β) δ q₁ q₂ x p₀ (fun _ => 1)
        (poleRegion x ρ) D ≤ Real.exp (((n+1:ℕ):ℝ)*(F-2*ζ)) := by
      apply (le_of_lt (lt_of_not_ge hDP)).trans
      apply Real.exp_le_exp.mpr
      nlinarith
    have hBudget : Real.exp (((n+1:ℕ):ℝ)*(F-2*ζ))+Real.exp (((n+1:ℕ):ℝ)*(F-2*ζ)) ≤
        Real.exp (((n+1:ℕ):ℝ)*(F-ζ)) := by
      convert hSum (F-3*ζ) using 1 <;> congr 1 <;> ring_nf
    have hZ := (amplitudeRestrictedPartition_le_compact_add_polar μ β (plantedCoreCost μ β) δ q₁ q₂ ρ
      x p₀ (fun _ => 1) A hA D).trans ((add_le_add hComp' hP').trans hBudget)
    have hStrict : Real.exp (((n+1:ℕ):ℝ)*(F-ζ)) < Real.exp (((n+1:ℕ):ℝ)*(F-ζ/2)) :=
      Real.exp_lt_exp.mpr (by nlinarith)
    exact (not_le_of_gt (hZ.trans_lt hStrict)) hD
  have hS := ENNReal.toReal_mono ENNReal.ofReal_ne_top
    (hSampleN (fun _ => 1) (by intro j;norm_num) x hx)
  have hS' : (bankLaw n μ).real B ≤ Real.exp (-γ*((n+1:ℕ):ℝ)) := by
    simpa only [Measure.real,ENNReal.toReal_ofReal (Real.exp_nonneg _),B] using hS
  have hP' : (bankLaw n μ).real P ≤ Real.exp (-((n+1:ℕ):ℝ)) :=
    hPolarN x hx p₀ (fun _ => 1) (by intro j;norm_num)
  apply ((measureReal_mono hSub).trans ((measureReal_union_le B P).trans (add_le_add hS' hP'))).trans
  have hN : 0 ≤ ((n+1:ℕ):ℝ) := by positivity
  have h1 : Real.exp (-γ*((n+1:ℕ):ℝ)) ≤ Real.exp (-(min γ 1)*((n+1:ℕ):ℝ)) :=
    Real.exp_le_exp.mpr (by nlinarith [min_le_left γ (1:ℝ)])
  have h2 : Real.exp (-((n+1:ℕ):ℝ)) ≤ Real.exp (-(min γ 1)*((n+1:ℕ):ℝ)) :=
    Real.exp_le_exp.mpr (by nlinarith [min_le_right γ (1:ℝ)])
  nlinarith

end
end SlowEquilibration.SphericalPlateauAmplitudeModel
