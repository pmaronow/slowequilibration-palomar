-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourceMixedGeneralCPTransfer
public import SlowEquilibration.SourceReductionConsumerAsymptoticTimeSup

/-! The complete displayed mixed-model source CP inequality, with the
literal physical time supremum and ordinary real expectations. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.SourceMixedGeneralCPTransferTimeSup

open Set MeasureTheory ProbabilityTheory Filter
open SphericalModel SphericalOverlapExponential
open SourceMixedGeneralCPTransfer SourceReductionConsumerAsymptoticCounts
open SourceReductionConsumerAsymptotic SourceReductionConsumerAsymptoticTimeSup
open SourceReductionWeightedCenterScore SourceReductionWeightedFiberBorel
open scoped Topology NNReal ENNReal

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- Finiteness of the extended expectation identifies the ordinary
weighted-score expectation and makes the displayed source comparison
valid without exceptional-fiber conventions entering the inequality. -/
theorem original_real_mean_comparison {N : ℕ} (hN : 2 ≤ N)
    (μ : FiniteMixture) (Q m M b a β : ℝ) {U : Set ℝ}
    (hU : IsClosed U) (T : ℝ≥0) (ha : a < Real.sqrt Q-b)
    {L : ℝ} (hL : 0 ≤ L)
    (hscore : (∫⁻ J, actualWindowCenterWeightedHitSum μ Q m M a β U T J
      ∂disorderLaw N μ.maxDegree) ≤ ENNReal.ofReal L) :
    Integrable (fun J => (actualWindowCenterWeightedHitSum μ Q m M a β U T J).toReal)
      (disorderLaw N μ.maxDegree) ∧
    (∫ J, originalBandTimeSup μ Q m M b β U T J ∂disorderLaw N μ.maxDegree) ≤
      (∫ J, (actualWindowCenterWeightedHitSum μ Q m M a β U T J).toReal
        ∂disorderLaw N μ.maxDegree) ∧
    (∫ J, (actualWindowCenterWeightedHitSum μ Q m M a β U T J).toReal
      ∂disorderLaw N μ.maxDegree) ≤ L := by
  have hm : AEMeasurable (actualWindowCenterWeightedHitSum μ Q m M a β U T)
      (disorderLaw N μ.maxDegree) :=
    (actualWindowCenterWeightedHitSum_measurable hN μ Q m M a β hU T).aemeasurable
  have hfin : (∫⁻ J, actualWindowCenterWeightedHitSum μ Q m M a β U T J
      ∂disorderLaw N μ.maxDegree) ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt hscore ENNReal.ofReal_lt_top)
  have hi := integrable_toReal_of_lintegral_ne_top hm hfin
  have heq := integral_toReal hm (ae_lt_top' hm hfin)
  refine ⟨hi,?_,?_⟩
  · rw [heq]
    exact (ENNReal.ofReal_le_iff_le_toReal hfin).mp
      (originalBandTimeSup_mean_le_weighted_score hN μ Q m M b a β hU T ha)
  · rw [heq]
    exact ENNReal.toReal_le_of_le_ofReal hL hscore

/-- Source `prop:cp-transfer`, displayed inequality, for every non-pure
finite mixture. The cap and horizon depend only on the fixed data and
the limiting energy, before the choice of center, window, or Holder order. -/
theorem source_mixed_general_cp_transfer
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
          (∫ J, originalBandTimeSup μ Q (m n) M b β U
            (exponentialGridHorizon γ (n+2)) J ∂disorderLaw (n+2) μ.maxDegree) ≤
            (∫ J, (actualWindowCenterWeightedHitSum μ Q (m n) M a β U
              (exponentialGridHorizon γ (n+2)) J).toReal ∂disorderLaw (n+2) μ.maxDegree) ∧
          (∫ J, (actualWindowCenterWeightedHitSum μ Q (m n) M a β U
            (exponentialGridHorizon γ (n+2)) J).toReal ∂disorderLaw (n+2) μ.maxDegree) ≤
            C*((n+2:ℕ):ℝ)^(-(((μ.minDegree:ℝ)-2)/2)*(1-1/r)) := by
  obtain ⟨a,γ,ha,hag,hγ,hRate⟩ := source_mixed_general_cp_weighted_rate_uniform_center
    μ hd (E := E) hQ hQ1 hnp hβ hb U hU hgap
  refine ⟨a,γ,ha,hag,hγ,?_⟩
  intro m hm hcount M r hM hr
  obtain ⟨C,hC,hRateM⟩ := hRate m hm hcount M r hM hr
  refine ⟨C,hC,?_⟩
  filter_upwards [hRateM] with n hn
  exact (original_real_mean_comparison (by omega) μ Q (m n) M b a β
    hU.isClosed (exponentialGridHorizon γ (n+2)) hag
    (mul_nonneg hC.le (Real.rpow_nonneg (by positivity) _)) hn).2

end SlowEquilibration.SourceMixedGeneralCPTransferTimeSup
