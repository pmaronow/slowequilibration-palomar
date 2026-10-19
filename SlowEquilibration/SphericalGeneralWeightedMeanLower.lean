-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalGeneralTaylorCore
public import SlowEquilibration.SphericalPlateauAmplitudeMeanContact

@[expose] public section

/-! # Genuine all-finite unperturbed weighted mean lower bound

The canonical thermal core supplies the literal weighted partition lower
tail for every finite mixture. Actual Gaussian concentration then supplies
the expected-pressure lower bound uniformly in the spherical reference.
No signed partition upper, pressure limit or convexity premise is needed.
-/
namespace SlowEquilibration.SphericalSourceWeightedPartition
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open SphericalModel SphericalBarycenter SphericalTaylorRemainder
open scoped Topology
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem general_sourceWeightedPlantedPressure_closed_lower_tail (μ : FiniteMixture)
    {β δ q₁ q₂ ε : ℝ} (hβ : Thresholds.dynamicalThreshold μ.xi<β)
    (hc : IsAdmissibleCollar μ β q₁ q₂) (hε : 0<ε) :
    ∃ γ : ℝ,0<γ ∧ ∀ᶠ N : ℕ in atTop,∀ x : Vector N,‖x‖^2=(N:ℝ) →
      disorderLaw N μ.maxDegree {D | sourceWeightedPlantedPressure μ β δ q₁ q₂ x D≤
        β^2*μ.xi 1/2-plantedCoreCost μ β-ε}≤6*ENNReal.ofReal (Real.exp (-γ*(N:ℝ))) := by
  let F := β^2*μ.xi 1/2
  let J := plantedCoreCost μ β
  let Q := Thresholds.qStar μ.xi β
  let w := (Q-q₂)/2
  have hq₂ : q₂<Q := hc.2.2.1
  have hw : 0<w := by dsimp only [w,Q];linarith [hc.2.2.1]
  have hcore : q₂≤Q-w := by dsimp only [w];linarith
  obtain ⟨γ,hγ,htail⟩ := GeneralFinite.qStar_shifted_core_partition_lower_tail μ hβ hw (half_pos hε)
  obtain ⟨n₀,hn₀⟩ := eventually_atTop.1 htail
  refine ⟨γ,hγ,eventually_atTop.2 ⟨n₀+3,?_⟩⟩
  intro N hN x hx
  have hNpos : 0<(N:ℝ) := by exact_mod_cast (show 0<N by omega)
  have hNat : 1≤N := by omega
  obtain ⟨n,rfl⟩ : ∃ n : ℕ,N=n+3 := ⟨N-3,by omega⟩
  have ht := hn₀ n (by omega) x hx
  have hSub : {D : Disorder (n+3) μ.maxDegree | sourceWeightedPlantedPressure μ β δ q₁ q₂ x D≤F-J-ε}⊆
      {D | partitionOn β (fieldOfMixture μ (D+plantedShift (mixtureCoefficients μ) β x))
        (coreBand x Q w)<Real.exp (((n+3:ℕ):ℝ)*(F-J-ε/2))} := by
    intro D hD
    let H := fieldOfMixture μ (D+plantedShift (mixtureCoefficients μ) β x)
    have hH : Continuous H := (fieldOfMixture_contDiff μ _).continuous
    have hW : 0<sourceWeightedPartition β H J δ q₁ q₂ x :=
      sourceWeightedPartition_pos hNat β hH J δ q₁ q₂ x
    change Real.log (sourceWeightedPartition β H J δ q₁ q₂ x)/((n+3:ℕ):ℝ)≤F-J-ε at hD
    have hlog := (div_le_iff₀ hNpos).mp hD
    have hexp := Real.exp_le_exp.mpr hlog
    rw [Real.exp_log hW] at hexp
    have hLow := core_partition_le_sourceWeightedPartition hNat β hH J δ q₁ q₂ Q w hc.2.1 hcore x
    have hStrict : Real.exp ((F-J-ε)*((n+3:ℕ):ℝ))<Real.exp (((n+3:ℕ):ℝ)*(F-J-ε/2)) := by
      apply Real.exp_lt_exp.mpr
      nlinarith
    exact lt_of_le_of_lt hLow (lt_of_le_of_lt hexp hStrict)
  have hm := (measure_mono hSub).trans (by
    simpa only [Q,F,J,plantedProfileTrial_qStar_eq] using ht)
  exact hm

private theorem generalWeighted_decay {a : ℝ} (ha : 0<a) :
    Tendsto (fun N : ℕ => Real.exp (-a*(N:ℝ))) atTop (𝓝 (0:ℝ)) := by
  convert Real.tendsto_exp_neg_atTop_nhds_zero.comp
    (tendsto_natCast_atTop_atTop.const_mul_atTop ha) using 1
  ext N
  simp only [Function.comp_apply,neg_mul]

/-- The actual unperturbed weighted pressure mean is asymptotically at
least F-J for every finite mixture, uniformly in the true reference. -/
theorem general_sourceWeightedPlantedMean_eventually_ge (μ : FiniteMixture)
    {β δ q₁ q₂ ε : ℝ} (hβ : Thresholds.dynamicalThreshold μ.xi<β)
    (hc : IsAdmissibleCollar μ β q₁ q₂) (hε : 0<ε) :
    ∀ᶠ N : ℕ in atTop,∀ x : Vector N,‖x‖^2=(N:ℝ) →
      β^2*μ.xi 1/2-plantedCoreCost μ β-ε≤
        ∫ D,sourceWeightedPlantedPressure μ β δ q₁ q₂ x D ∂disorderLaw N μ.maxDegree := by
  let s := ε/2
  have hs : 0<s := by dsimp only [s];positivity
  have hβpos : 0<β := μ.dynamicalThreshold_pos.trans hβ
  have hξ : 0<μ.xi 1 := μ.xi_pos (by norm_num)
  let c := s^2/(2*β^2*μ.xi 1)
  have hcpos : 0<c := by dsimp only [c];positivity
  obtain ⟨γ,hγ,hTail⟩ := general_sourceWeightedPlantedPressure_closed_lower_tail μ (δ := δ) hβ hc hs
  have hsum : Tendsto (fun N : ℕ => 6*Real.exp (-γ*(N:ℝ))+2*Real.exp (-c*(N:ℝ)))
      atTop (𝓝 (0:ℝ)) := by
    simpa only [mul_zero,add_zero] using ((generalWeighted_decay hγ).const_mul 6).add
      ((generalWeighted_decay hcpos).const_mul 2)
  filter_upwards [hTail,hsum.eventually (gt_mem_nhds (show (0:ℝ)<1 by norm_num)),
    eventually_ge_atTop (1:ℕ)] with N hTailN hSmall hN
  intro x hx
  let d := disorderLaw N μ.maxDegree
  let f := sourceWeightedPlantedPressure μ β δ q₁ q₂ x
  let m := ∫ D,f D ∂d
  let L := β^2*μ.xi 1/2-plantedCoreCost μ β
  let E₀ : Set (Disorder N μ.maxDegree) := {D | f D≤L-s}
  let E₁ : Set (Disorder N μ.maxDegree) := {D | s≤|f D-m|}
  have ht : d.real E₀≤6*Real.exp (-γ*(N:ℝ)) := by
    have hb := ENNReal.toReal_mono (by finiteness) (hTailN x hx)
    simpa only [d,E₀,f,L,Measure.real,ENNReal.toReal_mul,ENNReal.toReal_ofNat,
      ENNReal.toReal_ofReal (Real.exp_nonneg _)] using hb
  have hcon := (sourceWeightedPlantedPressure_integrable_concentration hN μ hβpos δ q₁ q₂ x).2 s hs
  have he : -(s^2*(N:ℝ))/(2*β^2*μ.xi 1)=-c*(N:ℝ) := by dsimp only [c];ring
  rw [he] at hcon
  have hct : d.real E₁≤2*Real.exp (-c*(N:ℝ)) := by
    have hb := ENNReal.toReal_mono ENNReal.ofReal_ne_top hcon
    simpa only [d,E₁,f,m,Measure.real,ENNReal.toReal_ofReal
      (show 0≤2*Real.exp (-c*(N:ℝ)) by positivity)] using hb
  change L-ε ≤ m
  by_contra hbad
  have hm : m<L-ε := lt_of_not_ge hbad
  have hcover : (univ : Set (Disorder N μ.maxDegree))⊆E₀∪E₁ := by
    intro D _
    by_contra hD
    have hnot₀ : D∉E₀ := fun h => hD (Or.inl h)
    have hnot₁ : D∉E₁ := fun h => hD (Or.inr h)
    have h₀ : L-s<f D := lt_of_not_ge hnot₀
    have h₁ : |f D-m|<s := lt_of_not_ge hnot₁
    have hfd := (abs_lt.mp h₁).2
    dsimp only [s] at h₀ hfd
    linarith
  have hprob := (measureReal_mono (μ := d) hcover).trans (measureReal_union_le (μ := d) E₀ E₁)
  have huniv : d.real univ=1 := probReal_univ
  rw [huniv] at hprob
  linarith

end
end SlowEquilibration.SphericalSourceWeightedPartition

namespace SlowEquilibration.SphericalPlateauAmplitudeModel
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter SphericalModel SphericalSourceWeightedPartition
open scoped Topology
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The true amplitude-one bank expected pressure has the all-finite
source contact lower, uniformly before choosing the actual reference. -/
theorem general_amplitudeExpectedPressure_one_eventually_ge (μ : FiniteMixture)
    {β δ q₁ q₂ ε : ℝ} (hβ : Thresholds.dynamicalThreshold μ.xi<β)
    (hc : IsAdmissibleCollar μ β q₁ q₂) (hε : 0<ε) (p₀ : Degree μ.maxDegree) :
    ∀ᶠ n : ℕ in atTop,∀ x : Vector (n+1),‖x‖^2=(n+1:ℝ) →
      β^2*μ.xi 1/2-plantedCoreCost μ β-ε≤
        amplitudeExpectedPressure μ β (plantedCoreCost μ β) δ q₁ q₂ x (latitudeFrameAt x) p₀ (fun _ => 1) := by
  have ht := (tendsto_add_atTop_nat 1).eventually
    (general_sourceWeightedPlantedMean_eventually_ge μ (δ := δ) hβ hc hε)
  filter_upwards [ht] with n hn
  intro x hx
  rw [amplitudeExpectedPressure_one_eq_originalMean μ β δ q₁ q₂ x hx p₀]
  exact hn x (by simpa only [Nat.cast_add,Nat.cast_one] using hx)

end
end SlowEquilibration.SphericalPlateauAmplitudeModel
