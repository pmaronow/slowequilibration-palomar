-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalMemoryCommonEvent
public import SlowEquilibration.SphericalWeightedReplicaMeasurability
public import SlowEquilibration.VaryingProbability

@[expose] public section

/-! # One actual event for the stronger plateau reduction

The moment event is a literal Borel test of the constructed reweighted law.
The original memory event retains the exponential guarantees for spectrum,
Gibbs-typical total variation and stationary information; only the upgraded
spin plateau requires the additional moment-convergence event.
-/
namespace SlowEquilibration.SphericalMemoryAssembly
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open SphericalModel SphericalForm SphericalBarycenter SphericalPhysicalSpectral
open SphericalLaplaceIdentification SphericalCenteredObservables SphericalSpinProjection
open SphericalSpinCorrelation SphericalQuantitativeTrap SphericalSourceObservablePlateau
open SphericalWeightedReplicaPlateau VaryingProbability
open SphericalAging.HardSphereDynamics
open scoped Topology NNReal ENNReal
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {N : ℕ}

/-- Literal time restriction and replacement of the two spin conclusions.
The other three conclusions retain their original disorder-event rate. -/
theorem MemoryConclusions.replace_plateau {hN : 2 ≤ N} {μ : FiniteMixture} {β : ℝ}
    {D : Disorder N μ.maxDegree} {b₀ b κ γ γ' a c C : ℝ}
    (h : MemoryConclusions hN μ β D b₀ κ γ a c C) (hγ : γ' ≤ γ)
    (hProjection : b ≤ ‖vectorCutoff hN μ D β (Real.exp (-(2*γ')*N))
      (centeredL2 (show 1 ≤ N by omega) μ D β spin (spin_contDiff.of_le (by simp)))‖^2)
    (hCorrelation : ∀ t ≤ memoryTime γ' N, b ≤ connectedSpinCorrelation μ D β t) :
    MemoryConclusions hN μ β D b κ γ' a c C := by
  have hTime : memoryTime γ' N ≤ memoryTime γ N := by
    change Real.exp (γ'*(N:ℝ)) ≤ Real.exp (γ*(N:ℝ))
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hγ (Nat.cast_nonneg N))
  refine ⟨h.eigenvalue.trans (Real.exp_le_exp.mpr ?_),hProjection,hCorrelation,?_,?_⟩
  · nlinarith [Nat.cast_nonneg (α := ℝ) N]
  · obtain ⟨X,hXm,hXs,hMass,hTV⟩ := h.typicalStartingPoints
    exact ⟨X,hXm,hXs,hMass,fun x hx t ht => hTV x hx t (ht.trans hTime)⟩
  · intro t ht htTime
    exact h.stationaryInformation t ht (htTime.trans hTime)

/-- All three genuine tests used for the upgrade, on the original disorder. -/
def plateauUpgradeEvent (μ : FiniteMixture) (β F J G δ q₁ q₂ q w a ε r m : ℝ) :
    Set (Disorder N μ.maxDegree) :=
  commonMemoryEvent μ β F J G δ q₁ q₂ q w a ε r ∩
    {D | sourceWeightedReplicaMoment μ β D J δ q₁ q₂ ≤ m}

theorem plateauUpgradeEvent_measurable (hN : 1 ≤ N) (μ : FiniteMixture)
    (β F J G δ q₁ q₂ q w a ε r m : ℝ) :
    MeasurableSet (plateauUpgradeEvent (N := N) μ β F J G δ q₁ q₂ q w a ε r m) :=
  (commonMemoryEvent_measurable hN μ β F J G δ q₁ q₂ q w a ε r).inter
    (sourceWeightedReplicaMoment_event_measurable hN μ β J δ q₁ q₂ m)

theorem plateauUpgradeEvent_failure_le (μ : FiniteMixture)
    (β F J G δ q₁ q₂ q w a ε r m : ℝ) :
    (disorderLaw N μ.maxDegree).real
      (plateauUpgradeEvent μ β F J G δ q₁ q₂ q w a ε r m)ᶜ ≤
    (disorderLaw N μ.maxDegree).real
      (goodCapCoreCollarEvent (mixtureCoefficients μ) β F J G δ q₁ q₂ q w (Real.exp (-a*N)))ᶜ+
    (disorderLaw N μ.maxDegree).real (replicaTailEvent μ β ε r)ᶜ+
    (disorderLaw N μ.maxDegree).real {D | m < sourceWeightedReplicaMoment μ β D J δ q₁ q₂} := by
  have he : (plateauUpgradeEvent (N := N) μ β F J G δ q₁ q₂ q w a ε r m)ᶜ=
      (goodCapCoreCollarEvent (mixtureCoefficients μ) β F J G δ q₁ q₂ q w (Real.exp (-a*N)))ᶜ ∪
      (replicaTailEvent μ β ε r)ᶜ ∪
      {D | m < sourceWeightedReplicaMoment μ β D J δ q₁ q₂} := by
    ext D
    simp only [plateauUpgradeEvent,commonMemoryEvent,mem_compl_iff,mem_inter_iff,mem_ofPred_eq,mem_union,not_and_or,not_le,or_assoc]
  rw [he]
  exact (measureReal_union_le _ _).trans (add_le_add (measureReal_union_le _ _) le_rfl)

/-- The actual norm-moment convergence gives the upgrade event probability
limit, with the two already exponentially controlled tests retained. -/
theorem plateauUpgradeEvent_failure_tendsto (μ : FiniteMixture)
    (β F J G δ q₁ q₂ q w a ε r m qTarget : ℝ) (hm : qTarget < m)
    (hGood : Tendsto (fun N => (disorderLaw N μ.maxDegree).real
      (goodCapCoreCollarEvent (mixtureCoefficients μ) β F J G δ q₁ q₂ q w (Real.exp (-a*N)))ᶜ)
      atTop (𝓝 (0:ℝ)))
    (hReplica : Tendsto (fun _N => (disorderLaw _N μ.maxDegree).real
      (replicaTailEvent μ β ε r)ᶜ) atTop (𝓝 (0:ℝ)))
    (hMoment : InProbability (fun N => disorderLaw N μ.maxDegree)
      (fun _N D => sourceWeightedReplicaMoment μ β D J δ q₁ q₂) qTarget) :
    Tendsto (fun N => (disorderLaw N μ.maxDegree).real
      (plateauUpgradeEvent μ β F J G δ q₁ q₂ q w a ε r m)ᶜ) atTop (𝓝 (0:ℝ)) := by
  have hTail := hMoment (m-qTarget) (sub_pos.mpr hm)
  have hMomentBound (N : ℕ) : (disorderLaw N μ.maxDegree).real
      {D | m < sourceWeightedReplicaMoment μ β D J δ q₁ q₂} ≤
      (disorderLaw N μ.maxDegree).real
      {D | m-qTarget ≤ ‖sourceWeightedReplicaMoment μ β D J δ q₁ q₂-qTarget‖} := by
    apply measureReal_mono (μ := disorderLaw N μ.maxDegree)
    intro D hD
    change m < sourceWeightedReplicaMoment μ β D J δ q₁ q₂ at hD
    change m-qTarget ≤ ‖sourceWeightedReplicaMoment μ β D J δ q₁ q₂-qTarget‖
    rw [Real.norm_eq_abs,abs_of_nonneg (by linarith)]
    linarith
  have hBound (N : ℕ) := (plateauUpgradeEvent_failure_le (N := N) μ β F J G δ q₁ q₂ q w a ε r m).trans
    (add_le_add le_rfl (hMomentBound N))
  exact squeeze_zero (fun _ => measureReal_nonneg) hBound
    (by simpa only [add_zero] using (hGood.add hReplica).add hTail)

/-- Exact upgraded projection and physical all-time correlation on the
literal intersection event, from the constructed source observable. -/
theorem constructed_plateau_upgrade_eventually (J G δ q₁ q₂ a ε bP bC r m : ℝ)
    (hJ : 0 < J) (hδ : 0 ≤ δ) (hGap : 4*δ < G) (ha : 0 < a)
    (hq₁ : 0 < q₁) (hq : q₁ < q₂) (hε : 0 ≤ ε) (hbP : 0 ≤ bP)
    (hbC : bC < bP) (hr : 0 < r) (hm : 0 < m)
    (hMargin : Real.sqrt bP*Real.sqrt m+Real.sqrt ε < q₁) :
    ∃ cE : ℝ, 0 < cE ∧ cE=min (G-4*δ) a/2 ∧
      ∀ γ : ℝ, 0 < γ → 2*γ < cE →
      ∀ᶠ N : ℕ in atTop, ∀ (hN : 2 ≤ N) (μ : FiniteMixture) (β F q w : ℝ)
        (D : Disorder N μ.maxDegree), q₂ ≤ q-w →
        D∈plateauUpgradeEvent μ β F J G δ q₁ q₂ q w a ε r m →
        bP ≤ ‖vectorCutoff hN μ D β (Real.exp (-(2*γ)*N))
          (centeredL2 (show 1 ≤ N by omega) μ D β spin (spin_contDiff.of_le (by simp)))‖^2 ∧
        ∀ t ≤ memoryTime γ N, bC ≤ connectedSpinCorrelation μ D β t := by
  obtain ⟨cE,hcE,hcEq,hBuild⟩ := constructed_weightedReplica_plateau_eventually
    J G δ q₁ q₂ a ε bP bC r m hJ hδ hGap ha hq₁ hq hε hbP hbC hr hm hMargin
  refine ⟨cE,hcE,hcEq,?_⟩
  intro γ hγ hγE
  filter_upwards [hBuild γ hγ hγE] with N hBuild
  intro hN μ β F q w D hCore hD
  exact hBuild hN μ β F q w D hCore hD.1.1 hD.1.2 hD.2

end
end SlowEquilibration.SphericalMemoryAssembly
