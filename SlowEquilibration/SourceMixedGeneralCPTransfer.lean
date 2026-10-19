-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourceMixedGeneralCPTransferMarks
public import SlowEquilibration.SourceMixedCriticalEntranceCPTransfer
public import SlowEquilibration.SourceReductionConsumerAsymptoticCounts
public import SlowEquilibration.SourceReductionWeightedScoreMarkedCount

/-! Mixed source `cp-transfer` for arbitrary normalized centering and
bounded counts only on the ORIGINAL compact radial window. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.SourceMixedGeneralCPTransfer

open Set MeasureTheory ProbabilityTheory Filter
open SphericalModel SphericalForm SphericalMarkedWindows SphericalGaussianJet
open ConditionedEntrance ConditionedDeterminantMoments
open SphericalOverlapExponential SphericalAging.HardSphereDynamics
open SourceMixedGeneralCPTransferMarks SourceMixedCriticalEntranceCPTransfer
open SourceMixedCenteredTrueEntranceTransfer
open SourceReductionWeightedCenterScore SourceReductionWeightedScoreMarkedCount
open SourceReductionConsumerAsymptotic SourceReductionConsumerAsymptoticCounts
open scoped Topology NNReal ENNReal

set_option autoImplicit false
set_option maxHeartbeats 1200000

theorem compact_strict_gap_uniform {U : Set ℝ} (hU : IsCompact U)
    (edge : ℝ) (hgap : ∀ k ∈ U, edge < k) :
    ∃ g : ℝ, 0 < g ∧ ∀ k ∈ U, edge+g ≤ k := by
  by_cases hne : U.Nonempty
  · obtain ⟨k,hk,hmin⟩ := hU.exists_isMinOn hne continuous_id.continuousOn
    refine ⟨k-edge,sub_pos.mpr (hgap k hk),?_⟩
    intro z hz
    have hh : k ≤ z := hmin hz
    linarith
  · refine ⟨1,by norm_num,?_⟩
    intro k hk
    exact False.elim (hne ⟨k,hk⟩)

/-- The cap and exponential horizon are chosen before both the fixed
energy-window width and the Holder order. No count bound is assumed on a
larger radial window and the center is an arbitrary convergent sequence. -/
theorem source_mixed_general_cp_weighted_rate_uniform_center
    (μ : FiniteMixture) (hd : 4 ≤ μ.minDegree) {Q β E b : ℝ}
    (hQ : 0 < Q) (hQ1 : Q ≤ 1) (hnp : μ.minDegree < μ.maxDegree)
    (hβ : 0 ≤ β) (hb : b < Real.sqrt Q)
    (U : Set ℝ) (hU : IsCompact U)
    (hgap : ∀ k ∈ U, 2*Real.sqrt (Q^2*μ.xi2 Q) < k) :
    ∃ (a γ : ℝ), 0 < a ∧ a < Real.sqrt Q-b ∧ 0 < γ ∧
      ∀ (m : ℕ → ℝ),
        Tendsto (fun n : ℕ => m n/((n+2:ℕ):ℝ)) atTop (𝓝 E) →
        (∀ M : ℝ, 0 < M →
          limsup (originalWindowExpectedCount μ Q m M U) atTop < ⊤) →
      ∀ (M r : ℝ), 0 < M → 1 < r → ∃ C : ℝ, 0 < C ∧
        ∀ᶠ n : ℕ in atTop,
          (∫⁻ J, actualWindowCenterWeightedHitSum μ Q (m n) M a β U
            (exponentialGridHorizon γ (n+2)) J ∂disorderLaw (n+2) μ.maxDegree) ≤
            ENNReal.ofReal (C*((n+2:ℕ):ℝ)^
              (-(((μ.minDegree:ℝ)-2)/2)*(1-1/r))) := by
  obtain ⟨g,hg,hgU⟩ := compact_strict_gap_uniform hU _ hgap
  obtain ⟨Z,hZ,hUZ⟩ := hU.isBounded.exists_pos_norm_le
  obtain ⟨aStar,hStar,hScales⟩ := source_mixed_general_ordinary_rate_all_small_scales
    μ hd (E := E) hQ hQ1 hnp hβ U hU
  let a := min aStar ((Real.sqrt Q-b)/2)
  have ha : 0 < a := by dsimp [a]; exact lt_min hStar (by linarith)
  have haStar : a ≤ aStar := min_le_left _ _
  have haGap : a < Real.sqrt Q-b := by
    have hh : a ≤ (Real.sqrt Q-b)/2 := min_le_right _ _
    linarith
  obtain ⟨γ,c,C,hγ,hc,hC,hRate⟩ := hScales ha haStar
  refine ⟨a,γ,ha,haGap,hγ,?_⟩
  intro m hm hcount M r hM hr
  obtain ⟨B,hB,hBound⟩ := eventually_bounded_of_limsup_lt_top _ (hcount M hM)
  let K (n : ℕ) := physicalEnergyWindow (n+2) (Icc (m n-M) (m n+M)) U
  let ψ (n : ℕ) (J : Disorder (n+2) μ.maxDegree) (u : Vector (n+2)) :=
    originalTrueCapHitProbability μ β (exponentialGridHorizon γ (n+2)) a u J
  have hK (n : ℕ) : MeasurableSet (K n) :=
    rectangularScoreWindow_measurable _ _
      (measurableSet_Icc.preimage (measurable_const_mul _)) hU.isClosed.measurableSet
  have hψ (n : ℕ) : Measurable (fun z : Disorder (n+2) μ.maxDegree × Vector (n+2) =>
      ψ n z.1 z.2) :=
    SourceMixedCenteredTrueEntranceTransfer.originalTrueCapHitProbability_joint_measurable
      μ β (exponentialGridHorizon γ (n+2)) a
  have hψ01 (n : ℕ) (J : Disorder (n+2) μ.maxDegree) (u : Vector (n+2)) :
      0 ≤ ψ n J u ∧ ψ n J u ≤ 1 :=
    originalTrueCapHitProbability_mem_unit μ β (exponentialGridHorizon γ (n+2)) a u J
  have hgapK (n : ℕ) (z : EuclideanSpace ℝ (Fin 2)) (hz : z ∈ K n) :
      2*Real.sqrt (Q^2*μ.xi2 Q)+g ≤ z 1 ∧ z 1 ≤ Z := by
    have hzU : z 1 ∈ U := hz.2
    exact ⟨hgU (z 1) hzU,(le_abs_self _).trans
      (by simpa only [Real.norm_eq_abs] using hUZ (z 1) hzU)⟩
  obtain ⟨Cdet,hCdet,hTransfer⟩ := actual_mixed_critical_entrance_cp_transfer
    μ hd hQ hnp hg hr hc hC.le hB.le K hK ψ hψ hψ01 hgapK
    (hRate m hm M hM) hBound
  refine ⟨Cdet^(1/r)*(2*C+1)^(1-1/r)*B,by positivity,?_⟩
  filter_upwards [hTransfer] with n hn
  have heq := lintegral_congr_ae
    (actualWindowCenterWeightedHitSum_ae_eq_actualScoreWindowCount
      n μ hQ (m n) M a β U (exponentialGridHorizon γ (n+2)))
  rw [heq]
  exact hn

/-- The source statement for a specified deterministic center, derived
from the stronger choice that is uniform over all centers with limit E. -/
theorem source_mixed_general_cp_weighted_rate
    (μ : FiniteMixture) (hd : 4 ≤ μ.minDegree) {Q β E b : ℝ}
    (hQ : 0 < Q) (hQ1 : Q ≤ 1) (hnp : μ.minDegree < μ.maxDegree)
    (hβ : 0 ≤ β) (hb : b < Real.sqrt Q)
    (U : Set ℝ) (hU : IsCompact U)
    (hgap : ∀ k ∈ U, 2*Real.sqrt (Q^2*μ.xi2 Q) < k)
    (m : ℕ → ℝ)
    (hm : Tendsto (fun n : ℕ => m n/((n+2:ℕ):ℝ)) atTop (𝓝 E))
    (hcount : ∀ M : ℝ, 0 < M →
      limsup (originalWindowExpectedCount μ Q m M U) atTop < ⊤) :
    ∃ (a γ : ℝ), 0 < a ∧ a < Real.sqrt Q-b ∧ 0 < γ ∧
      ∀ (M r : ℝ), 0 < M → 1 < r → ∃ C : ℝ, 0 < C ∧
        ∀ᶠ n : ℕ in atTop,
          (∫⁻ J, actualWindowCenterWeightedHitSum μ Q (m n) M a β U
            (exponentialGridHorizon γ (n+2)) J ∂disorderLaw (n+2) μ.maxDegree) ≤
            ENNReal.ofReal (C*((n+2:ℕ):ℝ)^
              (-(((μ.minDegree:ℝ)-2)/2)*(1-1/r))) := by
  obtain ⟨a,γ,ha,hag,hγ,hRate⟩ := source_mixed_general_cp_weighted_rate_uniform_center
    μ hd (E := E) hQ hQ1 hnp hβ hb U hU hgap
  exact ⟨a,γ,ha,hag,hγ,hRate m hm hcount⟩

/-- The mixed critical transfer and source capture imply the literal
physical all-time separation, for the same arbitrary center and window. -/
theorem source_mixed_general_cp_separation
    (μ : FiniteMixture) (hd : 4 ≤ μ.minDegree) {Q β E b : ℝ}
    (hQ : 0 < Q) (hQ1 : Q ≤ 1) (hnp : μ.minDegree < μ.maxDegree)
    (hβ : 0 ≤ β) (hb : b < Real.sqrt Q)
    (U : Set ℝ) (hU : IsCompact U)
    (hgap : ∀ k ∈ U, 2*Real.sqrt (Q^2*μ.xi2 Q) < k)
    (m : ℕ → ℝ)
    (hm : Tendsto (fun n : ℕ => m n/((n+2:ℕ):ℝ)) atTop (𝓝 E))
    (hcount : ∀ M : ℝ, 0 < M →
      limsup (originalWindowExpectedCount μ Q m M U) atTop < ⊤)
    (hcapture : Tendsto (fun M : ℝ => limsup (fun n : ℕ =>
      ∫ J, originalBandComplementMass μ Q (m n) M b β U J
        ∂disorderLaw (n+2) μ.maxDegree) atTop) atTop (𝓝 0)) :
    ∃ γ : ℝ, 0 < γ ∧
      VaryingConvergesInProbability (fun n => disorderLaw (n+2) μ.maxDegree)
        (fun n => originalUniformIntervalDistance μ β
          (exponentialGridHorizon γ (n+2))) (fun _ _ => 1) := by
  obtain ⟨a,γ,ha,haGap,hγ,hRate⟩ := source_mixed_general_cp_weighted_rate
    μ hd hQ hQ1 hnp hβ hb U hU hgap m hm hcount
  refine ⟨γ,hγ,?_⟩
  apply source_red_consumer_of_expected_score_tendsto_zero
    μ Q b a β hU.isClosed m (fun n => exponentialGridHorizon γ (n+2)) haGap hcapture
  intro M hM
  obtain ⟨C,hC,hRateM⟩ := hRate M 2 hM (by norm_num)
  let α : ℝ := ((μ.minDegree:ℝ)-2)/4
  have hα : 0 < α := by
    have hh : (4:ℝ) ≤ (μ.minDegree:ℝ) := by exact_mod_cast hd
    dsimp [α]
    linarith
  have hN : Tendsto (fun n : ℕ => ((n+2:ℕ):ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 2)
  have hreal : Tendsto (fun n : ℕ => C*((n+2:ℕ):ℝ)^(-α)) atTop (𝓝 0) := by
    simpa using ((tendsto_rpow_neg_atTop hα).comp hN).const_mul C
  have hENN := ENNReal.tendsto_ofReal hreal
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (by simpa using hENN) (.of_forall fun _ => zero_le)
  filter_upwards [hRateM] with n hn
  have hexp : -α = -(((μ.minDegree:ℝ)-2)/2)*(1-1/(2:ℝ)) := by dsimp [α]; ring
  simpa only [hexp,Nat.cast_add,Nat.cast_ofNat] using hn

end SlowEquilibration.SourceMixedGeneralCPTransfer
