-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalHSProfileTypicality
public import SlowEquilibration.SphericalLatitudeLaplaceAsymptotics
public import SlowEquilibration.SphericalHSPressureLower

@[expose] public section

/-!
# The genuine Huang--Sellke planted first moment for even mixtures

The actual far-overlap profile event is integrated using the proved spherical
coarea formula and its true normalization. Averaging the resulting shifted
disorder probabilities under the exact Cameron--Martin planted law proves
typicality of the explicit HS truncation; no first-moment premise remains.
-/

noncomputable section
namespace SlowEquilibration.SphericalModel

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators ENNReal

set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def farOverlapRegion (δ : ℝ) : Set ℝ := {q | δ ≤ |q|}

theorem farOverlapRegion_measurable (δ : ℝ) : MeasurableSet (farOverlapRegion δ) :=
  measurableSet_le measurable_const continuous_abs.measurable

theorem overlapPartition_far_eq_partitionOn {N P : ℕ} (c : Degree P → ℝ) (β δ : ℝ)
    (J : Disorder N P) (u : Vector N) :
    overlapPartition c β (smallOverlap δ)ᶜ J u =
      partitionOn β (field c J) (overlapRegion u (farOverlapRegion δ)) := by
  unfold overlapPartition partitionOn
  rw [← integral_indicator (overlapRegion_measurable u (farOverlapRegion_measurable δ))]
  apply integral_congr_ae
  exact .of_forall fun v => by
    dsimp only
    have hR : overlap u v=overlap v u := by unfold overlap; rw [real_inner_comm]
    by_cases hv : δ ≤ |overlap v u|
    · have hp : (u,v) ∈ (smallOverlap δ)ᶜ := by simpa only [smallOverlap,mem_compl_iff,mem_ofPred_eq,hR,not_lt] using hv
      have hq : v ∈ overlapRegion u (farOverlapRegion δ) := hv
      rw [indicator_of_mem hp,indicator_of_mem hq]
    · have hp : (u,v) ∉ (smallOverlap δ)ᶜ := by simpa only [smallOverlap,mem_compl_iff,mem_ofPred_eq,hR,not_lt] using hv
      have hq : v ∉ overlapRegion u (farOverlapRegion δ) := hv
      rw [indicator_of_notMem hp,indicator_of_notMem hq]

/-- Exponentially accurate first-moment typicality for the literal HS
partition truncation, proved for every even finite mixture below beta_s. -/
theorem even_hs_planted_typicality (μ : FiniteMixture)
    (heven : ∀ p ∈ μ.coeff.support, Even p) {β δ : ℝ}
    (hβ : 0 < β) (hβs : β < Thresholds.staticThreshold μ.xi) (hδ : δ ∈ Ioo (0 : ℝ) 1) :
    ∃ η γ : ℝ, 0 < η ∧ 0 < γ ∧ ∀ᶠ n : ℕ in atTop,
      1-Real.exp (-γ*((n+1 : ℕ) : ℝ)) ≤
        (plantedLaw (N := n+1) (mixtureCoefficients μ) β).real
          (hsTruncation (mixtureCoefficients μ) β δ
            (annealedExponent (n+1) (mixtureCoefficients μ) β-((n+1 : ℕ) : ℝ)*η)) := by
  obtain ⟨η₀,γ,hη₀,hγ,hprofile⟩ := even_planted_far_profile_eventually μ heven hβ hβs hδ
  refine ⟨η₀/2,γ,half_pos hη₀,hγ,?_⟩
  filter_upwards [hprofile,partitionOn_eventually_le_of_latitudeProfile_upper (half_pos hη₀),
    eventually_ge_atTop 1] with n hprofile hlap hn
  let c := mixtureCoefficients μ
  let L : ℝ := annealedExponent (n+1) c β-((n+1 : ℕ) : ℝ)*(η₀/2)
  let T := hsTruncation (N := n+1) c β δ L
  have hT : MeasurableSet T := hsTruncation_measurable c β δ L
  have hconditional (u : Vector (n+1)) (hu : ‖u‖^2=((n+1 : ℕ) : ℝ)) :
      disorderLaw (n+1) μ.maxDegree {J | (J+plantedShift c β u,u) ∈ Tᶜ} ≤
        ENNReal.ofReal (Real.exp (-γ*((n+1 : ℕ) : ℝ))) := by
    apply (measure_mono ?_).trans
      (hprofile u hu (latitudeFrameAt u) (latitudeFrameAt_orthogonal u hu))
    intro J hJ
    by_contra hbad
    have hgood : ∀ q ∈ farOverlapRegion δ, q ∈ Ioo (-1 : ℝ) 1 →
        latitudePartitionProfile n β (field c (J+plantedShift c β u)) u q ≤ β^2*μ.xi 1/2-η₀ := by
      intro q hq hq'
      apply le_of_not_gt
      intro hf
      exact hbad ⟨q,hq',hq,hf⟩
    have hZ := hlap β (field c (J+plantedShift c β u)) (field_contDiff c _).continuous
      u hu (farOverlapRegion δ) (farOverlapRegion_measurable δ) (β^2*μ.xi 1/2-η₀) hgood
    rw [← overlapPartition_far_eq_partitionOn] at hZ
    have hexp : ((n+1 : ℕ) : ℝ)*(β^2*μ.xi 1/2-η₀+η₀/2)=L := by
      dsimp [L,c,annealedExponent]
      rw [covariancePolynomial_mixture]
      ring
    rw [hexp] at hZ
    exact hJ hZ
  have hbad : (plantedLaw (N := n+1) c β).real Tᶜ ≤ Real.exp (-γ*((n+1 : ℕ) : ℝ)) := by
    rw [plantedLaw_real_eq_shift_probability (by omega) c (mixtureCoefficients_nonnegative μ) β hT.compl]
    calc
      _ ≤ ∫ _u : Vector (n+1), Real.exp (-γ*((n+1 : ℕ) : ℝ)) ∂sphereLaw (n+1) := by
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
  change 1-Real.exp (-γ*((n+1 : ℕ) : ℝ)) ≤ (plantedLaw (N := n+1) c β).real T
  linarith

/-- The exact half-mass input to the already proved truncated second-moment
pressure argument is now a theorem for even mixtures below beta_s. -/
theorem even_hs_planted_half_eventually (μ : FiniteMixture)
    (heven : ∀ p ∈ μ.coeff.support, Even p) {β δ : ℝ}
    (hβ : 0 < β) (hβs : β < Thresholds.staticThreshold μ.xi) (hδ : δ ∈ Ioo (0 : ℝ) 1) :
    ∃ η : ℝ, 0 < η ∧ ∀ᶠ n : ℕ in atTop,
      (1/2 : ℝ) ≤ (plantedLaw (N := n+1) (mixtureCoefficients μ) β).real
        (hsTruncation (mixtureCoefficients μ) β δ
          (annealedExponent (n+1) (mixtureCoefficients μ) β-((n+1 : ℕ) : ℝ)*η)) := by
  obtain ⟨η,γ,hη,hγ,hprob⟩ := even_hs_planted_typicality μ heven hβ hβs hδ
  have hN : Tendsto (fun n : ℕ => ((n+1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hexp : Tendsto (fun n : ℕ => Real.exp (-γ*((n+1 : ℕ) : ℝ))) atTop (𝓝 0) := by
    convert Real.tendsto_exp_neg_atTop_nhds_zero.comp (hN.const_mul_atTop hγ) using 1
    ext n
    simp only [Function.comp_apply,neg_mul]
  refine ⟨η,hη,?_⟩
  filter_upwards [hprob,hexp.eventually (gt_mem_nhds (show (0 : ℝ)<1/2 by norm_num))] with n hn he
  linarith

end SlowEquilibration.SphericalModel
