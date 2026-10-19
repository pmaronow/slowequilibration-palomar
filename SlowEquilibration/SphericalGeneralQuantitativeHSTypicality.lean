-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalQuantitativeHSTypicality
public import SlowEquilibration.SphericalGeneralHSTypicality

/-! Explicit cutoff-independent exponents for actual latitude and planted HS
probabilities. The deterministic gap is supplied by the actual static profile;
no stochastic typicality premise is used. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalModel
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators ENNReal
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem general_plantedLatitudeProfile_uniform_upper_explicit
    (μ : FiniteMixture)
    {β δ ρ ε B : ℝ} (hβ : 0 < β) (hδ : 0 < δ) (hδρ : δ ≤ ρ) (hρ : ρ < 1) (hε : 0 < ε) (hB : 0<B) (hvar : β^2*μ.xi 1≤B) :
    ∀ᶠ n : ℕ in atTop,
      ∀ (u : Vector (n+1)), ‖u‖^2=((n+1 : ℕ) : ℝ) →
      ∀ (e : Vector n →ₗᵢ[ℝ] Vector (n+1)), (∀ x, inner ℝ (e x) u=0) →
        disorderLaw (n+1) μ.maxDegree {J | ∃ q ∈ Icc (-ρ) ρ, δ ≤ |q| ∧
          plantedProfileTrial μ β |q|+ε ≤ plantedLatitudeProfile n μ β u e q J} ≤
          ENNReal.ofReal (Real.exp (-latitudeConcentrationRate (ε/2) B*((n+1 : ℕ) : ℝ))) := by
  have hconc := latitude_uniform_concentration_of_variance_bound
    (mixtureCoefficients μ) (mixtureCoefficients_nonnegative μ)
    (by rw [covariancePolynomial_mixture]; exact μ.xi_pos (by norm_num)) hβ (half_pos hε) hB (by rwa [covariancePolynomial_mixture])
  filter_upwards [hconc,general_plantedLatitudeMeanProfile_eventually_uniform_upper μ
    hβ hδ hδρ hρ (half_pos hε), eventually_ge_atTop 1] with n hconc hmean hn
  intro u hu e he
  apply (measure_mono ?_).trans (hconc (-ρ) ρ (by linarith) hρ.le
    (by linarith) u hu e he)
  rintro J ⟨q,hq,hδq,hJ⟩
  refine ⟨q,hq,?_⟩
  have hqa : |q| ≤ 1 := abs_le.mpr ⟨by linarith [hq.1],hq.2.trans hρ.le⟩
  have hqabs : |q| ∈ Icc δ ρ := ⟨hδq,abs_le.mpr hq⟩
  rw [plantedLatitudeProfile_centered hn μ hβ u hu e he hqa] at hJ
  have hm := (plantedLatitudeMeanProfile_le_abs hn μ hβ u hu e he hqa).trans
    (hmean |q| hqabs u hu e he)
  have hN : 0 < ((n+1 : ℕ) : ℝ) := by positivity
  have hf : ε/2 ≤ latitudeCenteredLogPartition (mixtureCoefficients μ) β u e q J/
      ((n+1 : ℕ) : ℝ) := by linarith
  exact ((le_div_iff₀ hN).mp hf).trans (le_abs_self _)
theorem general_planted_far_profile_explicit (μ : FiniteMixture)
    {β δ η₀ B : ℝ}
    (hβ : 0 < β) (hδ : δ ∈ Ioo (0 : ℝ) 1)
    (hη₀ : 0<η₀) (hB : 0<B) (hvar : β^2*μ.xi 1≤B)
    (hgap : ∀ q∈Ico δ 1,plantedProfileTrial μ β q≤β^2*μ.xi 1/2-η₀) :
    ∀ᶠ n : ℕ in atTop,
      ∀ (u : Vector (n+1)), ‖u‖^2=((n+1 : ℕ) : ℝ) →
      ∀ (e : Vector n →ₗᵢ[ℝ] Vector (n+1)), (∀ x, inner ℝ (e x) u=0) →
        disorderLaw (n+1) μ.maxDegree {J | ∃ q ∈ Ioo (-1 : ℝ) 1,
          δ ≤ |q| ∧ β^2*μ.xi 1/2-farProfileGap η₀ < plantedLatitudeProfile n μ β u e q J} ≤
            ENNReal.ofReal (Real.exp (-farProfileRate η₀ B*((n+1 : ℕ) : ℝ))) := by
  let A : ℝ := β^2*μ.xi 1/2
  obtain ⟨ρ,hρ,hpole⟩ := plantedLatitudeProfile_signed_pole_event μ hβ.le (A-1) δ hδ
  let η : ℝ := min (η₀/2) 1
  have hη : 0 < η := lt_min (half_pos hη₀) zero_lt_one
  let γ₀ := latitudeConcentrationRate (η₀/4) B
  have hγ₀ : 0<γ₀ := latitudeConcentrationRate_pos (by positivity) hB
  have hcompact := general_plantedLatitudeProfile_uniform_upper_explicit μ hβ hδ.1
    hρ.1.le hρ.2 (half_pos hη₀) hB hvar
  have htail := latitude_polynomial_tail_explicit 0 hγ₀
  filter_upwards [hcompact,htail,eventually_ge_atTop 5] with n hcompact htail hn
  intro u hu e he
  let E : Set (Disorder (n+1) μ.maxDegree) := {J | ∃ q ∈ Icc (-ρ) ρ, δ ≤ |q| ∧
    plantedProfileTrial μ β |q|+η₀/2 ≤ plantedLatitudeProfile n μ β u e q J}
  have hsub : {J : Disorder (n+1) μ.maxDegree | ∃ q ∈ Ioo (-1 : ℝ) 1,
      δ ≤ |q| ∧ A-η < plantedLatitudeProfile n μ β u e q J} ⊆ regularDisorderᶜ ∪ E := by
    rintro J ⟨q,hq,hδq,hJ⟩
    by_cases hreg : J ∈ regularDisorder
    · right
      by_contra hbad
      have habs : |q| < 1 := abs_lt.mpr hq
      by_cases hqρ : |q| ≤ ρ
      · have hgood : plantedLatitudeProfile n μ β u e q J < plantedProfileTrial μ β |q|+η₀/2 := by
          apply lt_of_not_ge
          intro hf
          exact hbad ⟨q,abs_le.mp hqρ,hδq,hf⟩
        have hg := hgap |q| ⟨hδq,habs⟩
        have hηle : η ≤ η₀/2 := min_le_left _ _
        change _ ≤ A-η₀ at hg
        linarith
      · have hp := (hpole n hn).2 J hreg u hu e he q ⟨(lt_of_not_ge hqρ).le,habs⟩
        have hηle : η ≤ 1 := min_le_right _ _
        linarith
    · exact Or.inl hreg
  have hreg : disorderLaw (n+1) μ.maxDegree (regularDisorder (N := n+1) (P := μ.maxDegree))ᶜ ≤
      ENNReal.ofReal (Real.exp (-((n+1 : ℕ) : ℝ))) := by
    apply (ENNReal.toReal_le_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top).mp
    rw [ENNReal.toReal_ofReal (Real.exp_nonneg _)]
    exact (hpole n hn).1
  have hcomp : disorderLaw (n+1) μ.maxDegree E ≤
      ENNReal.ofReal (Real.exp (-γ₀*((n+1 : ℕ) : ℝ))) := by simpa only [γ₀,div_div,show (2:ℝ)*2=4 by norm_num] using hcompact u hu e he
  apply ((measure_mono hsub).trans (measure_union_le _ _)).trans
  apply (add_le_add hreg hcomp).trans
  rw [← ENNReal.ofReal_add (Real.exp_nonneg _) (Real.exp_nonneg _)]
  apply ENNReal.ofReal_le_ofReal
  have hexp : Real.exp (-((n+1 : ℕ) : ℝ)) ≤ Real.exp (-((n+1 : ℕ) : ℝ)/2) := by
    apply Real.exp_le_exp.mpr
    have hN : (0 : ℝ) ≤ ((n+1 : ℕ) : ℝ) := by positivity
    linarith
  simp only [pow_zero] at htail
  have hp := Real.exp_pos (-γ₀*((n+1 : ℕ) : ℝ))
  change _ ≤ Real.exp (-min (1/4) (γ₀/2)*((n+1 : ℕ) : ℝ))
  linarith
theorem general_hs_planted_typicality_explicit (μ : FiniteMixture)
    {β δ η₀ B : ℝ}
    (hβ : 0 < β) (hδ : δ ∈ Ioo (0 : ℝ) 1)
    (hη₀ : 0<η₀) (hB : 0<B) (hvar : β^2*μ.xi 1≤B)
    (hgap : ∀ q∈Ico δ 1,plantedProfileTrial μ β q≤β^2*μ.xi 1/2-η₀) :
    ∀ᶠ n : ℕ in atTop,
      1-Real.exp (-farProfileRate η₀ B*((n+1 : ℕ) : ℝ)) ≤
        (plantedLaw (N := n+1) (mixtureCoefficients μ) β).real
          (hsTruncation (mixtureCoefficients μ) β δ
            (annealedExponent (n+1) (mixtureCoefficients μ) β-((n+1 : ℕ) : ℝ)*(farProfileGap η₀/2))) := by
  have hprofile := general_planted_far_profile_explicit μ hβ hδ hη₀ hB hvar hgap
  let η₁ := farProfileGap η₀
  have hη₁ : 0<η₁ := farProfileGap_pos hη₀
  filter_upwards [hprofile,partitionOn_eventually_le_of_latitudeProfile_upper (half_pos hη₁),
    eventually_ge_atTop 1] with n hprofile hlap hn
  let c := mixtureCoefficients μ
  let L : ℝ := annealedExponent (n+1) c β-((n+1 : ℕ) : ℝ)*(η₁/2)
  let T := hsTruncation (N := n+1) c β δ L
  have hT : MeasurableSet T := hsTruncation_measurable c β δ L
  have hconditional (u : Vector (n+1)) (hu : ‖u‖^2=((n+1 : ℕ) : ℝ)) :
      disorderLaw (n+1) μ.maxDegree {J | (J+plantedShift c β u,u) ∈ Tᶜ} ≤
        ENNReal.ofReal (Real.exp (-farProfileRate η₀ B*((n+1 : ℕ) : ℝ))) := by
    apply (measure_mono ?_).trans
      (hprofile u hu (latitudeFrameAt u) (latitudeFrameAt_orthogonal u hu))
    intro J hJ
    by_contra hbad
    have hgood : ∀ q ∈ farOverlapRegion δ, q ∈ Ioo (-1 : ℝ) 1 →
        latitudePartitionProfile n β (field c (J+plantedShift c β u)) u q ≤ β^2*μ.xi 1/2-η₁ := by
      intro q hq hq'
      apply le_of_not_gt
      intro hf
      exact hbad ⟨q,hq',hq,hf⟩
    have hZ := hlap β (field c (J+plantedShift c β u)) (field_contDiff c _).continuous
      u hu (farOverlapRegion δ) (farOverlapRegion_measurable δ) (β^2*μ.xi 1/2-η₁) hgood
    rw [← overlapPartition_far_eq_partitionOn] at hZ
    have hexp : ((n+1 : ℕ) : ℝ)*(β^2*μ.xi 1/2-η₁+η₁/2)=L := by
      dsimp [L,c,annealedExponent]
      rw [covariancePolynomial_mixture]
      ring
    rw [hexp] at hZ
    exact hJ hZ
  have hbad : (plantedLaw (N := n+1) c β).real Tᶜ ≤ Real.exp (-farProfileRate η₀ B*((n+1 : ℕ) : ℝ)) := by
    rw [plantedLaw_real_eq_shift_probability (by omega) c (mixtureCoefficients_nonnegative μ) β hT.compl]
    calc
      _ ≤ ∫ _u : Vector (n+1), Real.exp (-farProfileRate η₀ B*((n+1 : ℕ) : ℝ)) ∂sphereLaw (n+1) := by
        apply integral_mono_of_nonneg (.of_forall fun _ => measureReal_nonneg) (integrable_const _)
        filter_upwards [sphereLaw_support (show 1 ≤ n+1 by omega)] with u hu
        have hh := hconditional u hu
        have hr := (ENNReal.toReal_le_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top).mpr hh
        rwa [ENNReal.toReal_ofReal (Real.exp_nonneg _)] at hr
      _ = _ := by simp
  let : IsProbabilityMeasure (plantedLaw (N := n+1) c β) :=
    plantedLaw_probability (by omega) c (mixtureCoefficients_nonnegative μ) β
  have hsum := measureReal_add_measureReal_compl (μ := plantedLaw (N := n+1) c β) hT
  rw [probReal_univ] at hsum
  change 1-Real.exp (-farProfileRate η₀ B*((n+1 : ℕ) : ℝ)) ≤ (plantedLaw (N := n+1) c β).real T
  linarith


end SlowEquilibration.SphericalModel
