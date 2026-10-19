-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SphericalGeneralGoodReferences
public import SlowEquilibration.SphericalCapFrameModes

/-! The sharp spectral barrier from actual finite-mixture cap/core/collar
probabilities. The independent column exponent is retained without coupling
it to the small collar barrier. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalModel
open MeasureTheory ProbabilityTheory Set Filter SphericalForm SphericalCapFrameCount
open scoped Topology
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem general_collar_eigenvalue_of_cap_rate (μ : FiniteMixture)
    {β q₁ q₂ s c σ : ℝ}
    (hβd : Thresholds.dynamicalThreshold μ.xi<β)
    (hβs : β<Thresholds.staticThreshold μ.xi)
    (hc : IsAdmissibleCollar μ β q₁ q₂) (hsq : s≤q₁) (hpos : 0<c)
    (hσ : σ<plantedCollarGap μ β q₂)
    (hcap : ∀ᶠ N : ℕ in atTop,
      ∃ Ω : Set (Disorder N μ.maxDegree),MeasurableSet Ω ∧
        (disorderLaw N μ.maxDegree).real Ωᶜ≤Real.exp (-c*N) ∧
        ∀ J∈Ω,∀ v : Vector N,‖v‖^2=(N:ℝ) →
          (gibbsLaw N β (fieldOfMixture μ J)).real (cap v s)≤Real.exp (-c*N)) :
    ∃ a : ℝ,0<a ∧ ∀ᶠ N : ℕ in atTop,
      ∃ Ω : Set (Disorder N μ.maxDegree),MeasurableSet Ω ∧
        (disorderLaw N μ.maxDegree).real Ωᶜ≤12*Real.exp (-a*N) ∧
        ∀ J∈Ω,∀ hN : 2≤N,
          (normalizedSphericalSpectralData hN β (fieldOfMixture μ J)
            (fieldOfMixture_contDiff μ J).continuous).eigenvalue
              (Nat.floor (Real.exp ((c/2)*N)))≤Real.exp (-σ*N) := by
  let G := plantedCollarGap μ β q₂
  let δ := min ((G-σ)/8) (c/16)
  have hδ : 0<δ := lt_min (by dsimp [G];positivity) (by positivity)
  have hκ : 0<c/2 := half_pos hpos
  have hκc : c/2<c-4*δ := by
    have hd : δ≤c/16 := min_le_right _ _
    linarith
  have hσδ : σ<G-4*δ := by
    have hd : δ≤(G-σ)/8 := min_le_left _ _
    change σ<G at hσ
    linarith
  let w := (Thresholds.qStar μ.xi β-q₂)/2
  have hw : 0<w := by dsimp [w];linarith [hc.2.2.1]
  have hcore : q₂≤Thresholds.qStar μ.xi β-w := by dsimp [w];linarith [hc.2.2.1]
  obtain ⟨a₀,ha₀,hgood⟩ := general_goodCapCoreCollarEvent_eventually μ hβd hβs.le hc hδ hw
  let a := min a₀ c
  have ha : 0<a := lt_min ha₀ hpos
  have hexp : Tendsto (fun N : ℕ => Real.exp (-a₀*N)) atTop (𝓝 (0:ℝ)) := by
    simpa only [Function.comp_def,neg_mul] using Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_natCast_atTop_atTop.const_mul_atTop ha₀)
  have hindex := cap_indicator_index_eventually (J := plantedCoreCost μ β)
    hc.2.1 hκ hκc hσδ
  refine ⟨a,ha,?_⟩
  filter_upwards [hcap,hgood,hindex,eventually_ge_atTop 2,
    hexp.eventually (Iio_mem_nhds (show (0:ℝ)<1/2 by norm_num))] with N hcap hgood hindex hN hexp
  obtain ⟨Ωc,hΩc,hcFail,hcGood⟩ := hcap
  let Ωg := goodCapCoreCollarEvent (N := N) (mixtureCoefficients μ) β
    (β^2*μ.xi 1/2) (plantedCoreCost μ β) G δ q₁ q₂
    (Thresholds.qStar μ.xi β) w (Real.exp (-a₀*N))
  have hΩg : MeasurableSet Ωg := goodCapCoreCollarEvent_measurable (by omega) _ _ _ _ _ _ _ _ _ _ _
  refine ⟨Ωc∩Ωg,hΩc.inter hΩg,?_,?_⟩
  · rw [compl_inter]
    have he (r : ℝ) (hr : a≤r) : Real.exp (-r*N)≤Real.exp (-a*N) := by
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_right (neg_le_neg hr) (Nat.cast_nonneg N)
    have hf := measureReal_union_le (μ := disorderLaw N μ.maxDegree) Ωcᶜ Ωgᶜ
    have h1 := he c (min_le_right _ _)
    have h2 := he a₀ (min_le_left _ _)
    change (disorderLaw N μ.maxDegree).real Ωgᶜ≤11*Real.exp (-a₀*N) at hgood
    linarith
  · intro J hJ hN'
    obtain ⟨S,hS,_hSs,hSm,hBounds⟩ := goodCapCoreCollarEvent_has_good_set (by omega)
      (mixtureCoefficients μ) β (β^2*μ.xi 1/2) (plantedCoreCost μ β) G δ q₁ q₂
      (Thresholds.qStar μ.xi β) w (Real.exp (-a₀*N)) hJ.2
    have hMass : 1/2≤(gibbsLaw N β (fieldOfMixture μ J)).real S := by
      let : IsProbabilityMeasure (gibbsLaw N β (fieldOfMixture μ J)) :=
        gibbsLaw_probability (by omega) β (fieldOfMixture_contDiff μ J).continuous
      have hh := measureReal_add_measureReal_compl (μ := gibbsLaw N β (fieldOfMixture μ J)) hS
      rw [probReal_univ] at hh
      change (gibbsLaw N β (fieldOfMixture μ J)).real Sᶜ≤_ at hSm
      linarith
    let : IsProbabilityMeasure (gibbsLaw N β (fieldOfMixture μ J)) :=
      gibbsLaw_probability (by omega) β (fieldOfMixture_contDiff μ J).continuous
    apply hindex hN' β (fieldOfMixture μ J) ((fieldOfMixture_contDiff μ J).of_le (by simp)) S hS hMass
    · exact fun u hu => (hBounds u hu).1
    · intro u hu
      have hsub : coreBand u (Thresholds.qStar μ.xi β) w⊆cap u q₂ := by
        intro v hv
        change |overlap v u-Thresholds.qStar μ.xi β|≤w at hv
        change q₂≤overlap v u
        have hh := (abs_le.mp hv).1
        linarith
      exact (hBounds u hu).2.1.trans
        (measureReal_mono (μ := gibbsLaw N β (fieldOfMixture μ J)) hsub)
    · exact fun u hu => (hBounds u hu).2.2
    · intro x hx
      apply (measureReal_mono (show cap x q₁⊆cap x s from fun v hv => hsq.trans hv)).trans
      exact hcGood J hJ.1 x ((SphericalAging.HardSphereDynamics.onSphere_iff_norm_sq x).mp hx)

end SlowEquilibration.SphericalModel
