-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourceConditionedCPTransfer
public import SlowEquilibration.ConditionedEntrancePureMainTheorem

/-! The pure ordinary entrance theorem discharges the last analytical
branch premise of the complete source CP transfer for every finite mixture.
The count and capture assumptions remain exactly the source assumptions. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.SourceConditionedCPTransferUnconditional

open Set MeasureTheory ProbabilityTheory Filter
open SphericalModel SphericalMarkedWindows SphericalGaussianJet
open ConditionedEntrance ConditionedDeterminantMoments SphericalOverlapExponential
open SphericalAging.HardSphereDynamics
open SourceConditionedCPTransfer SourceConditionedCPTransferPureRate
open SourceReductionConsumerAsymptotic SourceReductionConsumerAsymptoticCounts
open SourceReductionWeightedCenterScore
open scoped Topology NNReal ENNReal

set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem pureOrdinaryEntranceRate (p : ℕ) (hp : 2 ≤ p)
    (c : ℝ) (hc : 0 < c) (hd : 4 ≤ p) {Q β E : ℝ}
    (hQ : 0 < Q) (hβ : 0 ≤ β) : PureOrdinaryEntranceRate p hp c hc Q β E := by
  obtain ⟨aStar,hStar,hScales⟩ := source_pure_cap_hitting_bound_from_uniform_initial_law
    p hp c hc hd hQ (show 0 ≤ |E|+2 by positivity) hβ
  refine ⟨aStar,hStar,?_⟩
  intro a ha hab
  obtain ⟨γ,decay,C,hγ,hdecay,hC,hRate⟩ := hScales ha hab
  refine ⟨γ,decay,C,hγ,hdecay,hC,?_⟩
  have hRate' := (tendsto_add_atTop_nat 1).eventually hRate
  filter_upwards [hRate'] with n hn
  intro u hu e he
  have hLaw : pureLaw p hp c hc Q u hu e =
      valueConditionedLaw (centerCoefficients
        (mixtureCoefficients (FiniteMixture.pure p hp c hc)) Q) u hu e := by
    unfold pureLaw valueConditionedLaw
    congr 1
  rw [hLaw]
  simpa only [show n+1+1=n+2 by omega] using
    hn u ((onSphere_iff_norm_sq u).mpr hu) e he

theorem pureBranchEntrance (μ : FiniteMixture) (hd : 4 ≤ μ.minDegree)
    {Q β E : ℝ} (hQ : 0 < Q) (hβ : 0 ≤ β) : PureBranchEntrance μ Q β E := by
  intro p hp c hc hμ
  subst μ
  have hmin : (FiniteMixture.pure p hp c hc).minDegree = p := by
    simp [FiniteMixture.minDegree,FiniteMixture.pure,Finsupp.support_single p hc.ne']
  exact pureOrdinaryEntranceRate p hp c hc (by simpa only [hmin] using hd) hQ hβ

theorem source_cp_weighted_rate
    (μ : FiniteMixture) (hd : 4 ≤ μ.minDegree) {Q β E b : ℝ}
    (hQ : 0 < Q) (hQ1 : Q ≤ 1) (hβ : 0 ≤ β) (hb : b < Real.sqrt Q)
    (U : Set ℝ) (hU : IsCompact U)
    (hgap : ∀ k ∈ U, 2*Real.sqrt (Q^2*μ.xi2 Q) < k) :
    UniformCenterCPRate μ Q β E b U :=
  source_conditioned_cp_weighted_rate μ hd hQ hQ1 hβ hb U hU hgap
    (pureBranchEntrance μ hd hQ hβ)

/-- Complete source `prop:cp-transfer`, with one cap and horizon for all
fixed original windows and Holder orders, and its same-horizon separation
consequence whenever the source iterated Gibbs capture assumption holds. -/
theorem source_cp_transfer
    (μ : FiniteMixture) (hd : 4 ≤ μ.minDegree) {Q β E b : ℝ}
    (hQ : 0 < Q) (hQ1 : Q ≤ 1) (hβ : 0 ≤ β) (hb : b < Real.sqrt Q)
    (U : Set ℝ) (hU : IsCompact U)
    (hgap : ∀ k ∈ U, 2*Real.sqrt (Q^2*μ.xi2 Q) < k) :
    ∃ (a γ : ℝ), 0 < a ∧ a < Real.sqrt Q-b ∧ 0 < γ ∧
      ∀ (m : ℕ → ℝ),
        Tendsto (fun n : ℕ => m n/((n+2:ℕ):ℝ)) atTop (𝓝 E) →
        (∀ M : ℝ, 0 < M →
          limsup (originalWindowExpectedCount μ Q m M U) atTop < ⊤) →
      (∀ (M r : ℝ), 0 < M → 1 < r → ∃ C : ℝ, 0 < C ∧
        ∀ᶠ n : ℕ in atTop,
          (∫ J, originalBandTimeSup μ Q (m n) M b β U
            (exponentialGridHorizon γ (n+2)) J ∂disorderLaw (n+2) μ.maxDegree) ≤
            (∫ J, (actualWindowCenterWeightedHitSum μ Q (m n) M a β U
              (exponentialGridHorizon γ (n+2)) J).toReal ∂disorderLaw (n+2) μ.maxDegree) ∧
          (∫ J, (actualWindowCenterWeightedHitSum μ Q (m n) M a β U
            (exponentialGridHorizon γ (n+2)) J).toReal ∂disorderLaw (n+2) μ.maxDegree) ≤
            C*((n+2:ℕ):ℝ)^(-(((μ.minDegree:ℝ)-2)/2)*(1-1/r))) ∧
      (Tendsto (fun M : ℝ => limsup (fun n : ℕ =>
        ∫ J, originalBandComplementMass μ Q (m n) M b β U J
          ∂disorderLaw (n+2) μ.maxDegree) atTop) atTop (𝓝 0) →
        VaryingConvergesInProbability (fun n => disorderLaw (n+2) μ.maxDegree)
          (fun n => originalUniformIntervalDistance μ β
            (exponentialGridHorizon γ (n+2))) (fun _ _ => 1)) :=
  source_conditioned_cp_transfer μ hd hQ hQ1 hβ hb U hU hgap
    (pureBranchEntrance μ hd hQ hβ)

end SlowEquilibration.SourceConditionedCPTransferUnconditional
