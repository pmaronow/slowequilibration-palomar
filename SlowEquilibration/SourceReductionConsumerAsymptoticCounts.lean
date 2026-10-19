-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourceReductionConsumerAsymptotic
public import SlowEquilibration.SourceReductionWeightedScoreMarkedCount

/-! The count/Palm half of the literal source consumer. Finiteness is an
extended limsup condition, so divergent ordinary integrals cannot become zero. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.SourceReductionConsumerAsymptoticCounts

open Set MeasureTheory ProbabilityTheory Filter
open SphericalModel SphericalGaussianJet SphericalMarkedWindows
open SourceReductionWeightedCenterScore SourceReductionConsumerAsymptotic
open scoped Topology NNReal ENNReal

set_option autoImplicit false
set_option maxHeartbeats 700000

/-- The expected number of all original-field critical points in exactly
the specified energy and radial windows, without any enlarged window. -/
def originalWindowExpectedCount (μ : FiniteMixture) (Q : ℝ)
    (m : ℕ → ℝ) (M : ℝ) (U : Set ℝ) (n : ℕ) : ℝ≥0∞ :=
  ∫⁻ J, actualScoreWindowCount (n+1)
    (centerCoefficients (mixtureCoefficients μ) Q)
    (physicalEnergyWindow (n+2) (Icc (m n-M) (m n+M)) U)
    (fun _ _ => 1) J ∂disorderLaw (n+2) μ.maxDegree

theorem eventually_bounded_of_limsup_lt_top (f : ℕ → ℝ≥0∞)
    (hf : limsup f atTop < ⊤) :
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ n in atTop, f n ≤ ENNReal.ofReal B := by
  let B := (limsup f atTop).toReal+1
  have hB : 0 < B := by dsimp [B]; positivity
  have hlt : limsup f atTop < ENNReal.ofReal B := by
    apply (ENNReal.lt_ofReal_iff_toReal_lt hf.ne).2
    dsimp [B]
    linarith
  exact ⟨B, hB, (eventually_lt_of_limsup_lt hlt).mono fun _ h => h.le⟩

/-- Count finiteness and the determinant-weighted Palm bound imply the
literal expected weighted score tends to zero, exactly as in the source. -/
theorem expected_score_tendsto_zero_of_count_palm
    (μ : FiniteMixture) (Q a β : ℝ) (m : ℕ → ℝ)
    (M : ℝ) (U : Set ℝ) (T : ℕ → ℝ≥0)
    (hcount : limsup (originalWindowExpectedCount μ Q m M U) atTop < ⊤)
    (q : ℕ → ℝ) (hq : Tendsto q atTop (𝓝 0))
    (hpalm : ∀ᶠ n : ℕ in atTop,
      (∫⁻ J, actualWindowCenterWeightedHitSum μ Q (m n) M a β U (T n) J
        ∂disorderLaw (n+2) μ.maxDegree) ≤
        ENNReal.ofReal (q n)*originalWindowExpectedCount μ Q m M U n) :
    Tendsto (fun n : ℕ =>
      ∫⁻ J, actualWindowCenterWeightedHitSum μ Q (m n) M a β U (T n) J
        ∂disorderLaw (n+2) μ.maxDegree) atTop (𝓝 0) := by
  obtain ⟨B,hB,hbound⟩ := eventually_bounded_of_limsup_lt_top _ hcount
  have hprod : Tendsto (fun n => ENNReal.ofReal (q n)*ENNReal.ofReal B)
      atTop (𝓝 (0 : ℝ≥0∞)) := by
    simpa using ENNReal.Tendsto.mul_const (ENNReal.tendsto_ofReal hq)
      (Or.inr ENNReal.ofReal_ne_top)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hprod
    (.of_forall fun _ => zero_le)
  filter_upwards [hpalm,hbound] with n hp hn
  exact hp.trans (mul_le_mul_right hn _)

/-- Source `prop:red-consumer` on the actual spherical disorder laws.
The hypotheses are capture, finite expected-count limsup, and a vanishing
determinant-weighted hitting factor for each fixed window. -/
theorem source_red_consumer
    (μ : FiniteMixture) (Q b a β : ℝ) {U : Set ℝ}
    (hU : IsClosed U) (m : ℕ → ℝ) (T : ℕ → ℝ≥0)
    (ha : a < Real.sqrt Q-b)
    (hcapture : Tendsto (fun M : ℝ => limsup (fun n : ℕ =>
      ∫ J, originalBandComplementMass μ Q (m n) M b β U J
        ∂disorderLaw (n+2) μ.maxDegree) atTop) atTop (𝓝 0))
    (hcount : ∀ M : ℝ, 0 < M →
      limsup (originalWindowExpectedCount μ Q m M U) atTop < ⊤)
    (hpalm : ∀ M : ℝ, 0 < M → ∃ q : ℕ → ℝ,
      (∀ n, 0 ≤ q n) ∧ Tendsto q atTop (𝓝 0) ∧
      ∀ᶠ n : ℕ in atTop,
        (∫⁻ J, actualWindowCenterWeightedHitSum μ Q (m n) M a β U (T n) J
          ∂disorderLaw (n+2) μ.maxDegree) ≤
          ENNReal.ofReal (q n)*originalWindowExpectedCount μ Q m M U n) :
    (∀ M : ℝ, 0 < M → Tendsto (fun n : ℕ =>
      ∫⁻ J, actualWindowCenterWeightedHitSum μ Q (m n) M a β U (T n) J
        ∂disorderLaw (n+2) μ.maxDegree) atTop (𝓝 0)) ∧
    VaryingConvergesInProbability (fun n => disorderLaw (n+2) μ.maxDegree)
      (fun n => originalUniformIntervalDistance μ β (T n)) (fun _ _ => 1) := by
  have hscore (M : ℝ) (hM : 0 < M) : Tendsto (fun n : ℕ =>
      ∫⁻ J, actualWindowCenterWeightedHitSum μ Q (m n) M a β U (T n) J
        ∂disorderLaw (n+2) μ.maxDegree) atTop (𝓝 0) := by
    obtain ⟨q,hqnonneg,hq,hp⟩ := hpalm M hM
    exact expected_score_tendsto_zero_of_count_palm
      μ Q a β m M U T (hcount M hM) q hq hp
  exact ⟨hscore,source_red_consumer_of_expected_score_tendsto_zero
    μ Q b a β hU m T ha hcapture hscore⟩

end SlowEquilibration.SourceReductionConsumerAsymptoticCounts
