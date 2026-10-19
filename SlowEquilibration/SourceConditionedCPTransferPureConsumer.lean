-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourceConditionedCPTransferUnconditional
public import SlowEquilibration.SourcePureCaptureLiteralConsumer
public import SlowEquilibration.SourcePurePCCountsLiteral
public import SlowEquilibration.GammaLogAsymptotics

/-! The literal pure consumer: the printed logarithmic center has the
required normalized limit, the proved pure count theorem supplies the
original-window count hypothesis, and physical capture yields separation.
The three remaining physical capture inputs stay explicit. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.SourceConditionedCPTransferPureConsumer

open Set MeasureTheory ProbabilityTheory Filter
open SphericalModel SphericalMarkedWindows SphericalTAPCertificate
open PureStationarity TwoAtomStationarity SphericalPureCapSourceScalars
open SourcePureCaptureLiteralConsumer SourcePureCaptureWindowTransport
open SourcePureCaptureFixedCapEstimates
open SourcePureCaptureFromPhysicalInputs PureCapturePhysicalCoarseDiniAssembly
open SourceConditionedCPTransferUnconditional SourceReductionConsumerAsymptotic
open SourceReductionConsumerAsymptoticCounts SphericalOverlapExponential
open scoped Topology NNReal ENNReal

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- The logarithmic source center converges after division by dimension.
No assumption on the sign of its fixed logarithmic coefficient is needed. -/
theorem sourcePureAnalyticCenter_normalized_tendsto (E c : ℝ) :
    Tendsto (fun n : ℕ => sourcePureAnalyticCenter (n+2) E c /
      ((n+2:ℕ):ℝ)) atTop (𝓝 E) := by
  have hN : Tendsto (fun n : ℕ => ((n+2:ℕ):ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 2)
  have hlog : Tendsto (fun n : ℕ =>
      (Real.log ((n+2:ℕ):ℝ)/((n+2:ℕ):ℝ))/(2*c)) atTop (𝓝 0) := by
    simpa only [Function.comp_def,zero_div] using
      (SphereAreaAsymptotics.log_div_self_tendsto.comp hN).div_const (2*c)
  have heq : (fun n : ℕ => sourcePureAnalyticCenter (n+2) E c /
      ((n+2:ℕ):ℝ)) = (fun n : ℕ => E-
      (Real.log ((n+2:ℕ):ℝ)/((n+2:ℕ):ℝ))/(2*c)) := by
    funext n
    have hN0 : ((n+2:ℕ):ℝ) ≠ 0 := by positivity
    dsimp only [sourcePureAnalyticCenter]
    rw [sub_div,mul_div_cancel_left₀ E hN0]
    congr 1
    exact div_right_comm _ _ _
  rw [heq]
  simpa only [sub_zero] using tendsto_const_nhds.sub hlog

/-- The energy scaling used in literal pure capture is exactly the center
required by the source CP theorem, including its limit. -/
theorem pure_consumer_center_normalized_tendsto
    (p : ℕ) (hp : 4 ≤ p) {β x Q : ℝ}
    (h : Certificate (FiniteMixture.pure p (by omega) 1 (by positivity)) β x Q) :
    Tendsto (fun n : ℕ => ((Real.sqrt Q)^p*pureSourceCenter p hp n)/
      ((n+2:ℕ):ℝ)) atTop
      (𝓝 (markE (FiniteMixture.pure p (by omega) 1 (by positivity)) β x Q)) := by
  simpa only [sourcePureAnalyticCenter, pure_source_consumer_center_eq p hp h] using
    sourcePureAnalyticCenter_normalized_tendsto
      (markE (FiniteMixture.pure p (by omega) 1 (by positivity)) β x Q) (β*x)

/-- The already proved pure critical-count estimate is the exact count
input to the consumer on the original radial set U. -/
theorem pure_consumer_expected_count_limsup_lt_top
    (p : ℕ) (hp : 4 ≤ p) {β x Q : ℝ}
    (h : Certificate (FiniteMixture.pure p (by omega) 1 (by positivity)) β x Q)
    (U : Set ℝ) (hU : MeasurableSet U)
    (hcontact : markK (FiniteMixture.pure p (by omega) 1 (by positivity)) β Q ∈ interior U)
    (M : ℝ) (hM : 0 < M) :
    limsup (originalWindowExpectedCount
      (FiniteMixture.pure p (by omega) 1 (by positivity)) Q
      (fun n => (Real.sqrt Q)^p*pureSourceCenter p hp n) M U) atTop < ⊤ := by
  obtain ⟨hCount,_,_⟩ := sourcePure_prop_pc_counts_literal
    p (by omega) 1 (by positivity) h U hU hcontact
  obtain ⟨B,hB⟩ := hCount M hM
  have hbound : ∀ n : ℕ, originalWindowExpectedCount
      (FiniteMixture.pure p (by omega) 1 (by positivity)) Q
      (fun n => (Real.sqrt Q)^p*pureSourceCenter p hp n) M U n ≤ ENNReal.ofReal B := by
    intro n
    obtain ⟨hf,hv⟩ := hB n
    have hh := ENNReal.ofReal_le_ofReal hv
    rw [ENNReal.ofReal_toReal hf.ne] at hh
    simpa only [originalWindowExpectedCount,sourcePureAnalyticCenter,
      pure_source_consumer_center_eq p hp h] using hh
  exact (limsup_le_of_le (by isBoundedDefault)
    (.of_forall hbound)).trans_lt ENNReal.ofReal_lt_top

/-- Exponential-time physical TV separation for the amplitude-one pure
model, conditional only on the three still-visible physical capture inputs
besides the source certificate and the prescribed exterior radial window.
The critical-count and proper conditioned-entrance inputs are discharged. -/
theorem pure_consumer_separation_of_three_physical_inputs
    (p : ℕ) (hp : 4 ≤ p) {β x Q : ℝ}
    (h : Certificate (FiniteMixture.pure p (by omega) 1 (by positivity)) β x Q)
    (U : Set ℝ) (hU : IsCompact U)
    (hcontact : markK (FiniteMixture.pure p (by omega) 1 (by positivity)) β Q ∈ interior U)
    (hgap : ∀ k ∈ U, 2*Real.sqrt
      (Q^2*(FiniteMixture.pure p (by omega) 1 (by positivity)).xi2 Q) < k)
    (hNorm : PhysicalDirectingNormQ
      (FiniteMixture.pure p (by omega) 1 (by positivity)) β Q)
    (hMean : PhysicalReplicaMeanEnergy
      (FiniteMixture.pure p (by omega) 1 (by positivity)) β Q
      (pureEnergyConstant p (by omega)))
    (hRelocate : PhysicalHighEnergyRelocation
      (FiniteMixture.pure p (by omega) 1 (by positivity))
      (pureEnergyConstant p (by omega))) :
    let μ := FiniteMixture.pure p (by omega) 1 (by positivity)
    ∃ γ : ℝ, 0 < γ ∧
      VaryingConvergesInProbability (fun n => disorderLaw (n+2) μ.maxDegree)
        (fun n => originalUniformIntervalDistance μ β
          (exponentialGridHorizon γ (n+2))) (fun _ _ => 1) := by
  dsimp only
  let μ := FiniteMixture.pure p (by omega : 2 ≤ p) 1 (by positivity)
  obtain ⟨⟨b₀,hb₀,hCapture⟩,_⟩ := pure_consumer_capture_of_three_physical_inputs
    p hp h U hcontact hNorm hMean hRelocate
  obtain ⟨a,γ,ha,hag,hγ,hTransfer⟩ := source_cp_transfer μ h.min_degree
    (E := markE μ β x Q)
    h.overlap_range.1 h.overlap_range.2.le h.beta_pos.le hb₀.2 U hU hgap
  have hRate := hTransfer (fun n => (Real.sqrt Q)^p*pureSourceCenter p hp n)
    (pure_consumer_center_normalized_tendsto p hp h)
    (pure_consumer_expected_count_limsup_lt_top p hp h U hU.isClosed.measurableSet hcontact)
  refine ⟨γ,hγ,hRate.2 ?_⟩
  exact hCapture b₀ ⟨hb₀.1,le_rfl⟩

/-- The source certificate itself supplies a compact exterior radial
window. Thus no choice of radial window is an additional physical input. -/
theorem pure_separation_of_three_physical_inputs
    (p : ℕ) (hp : 4 ≤ p) {β x Q : ℝ}
    (h : Certificate (FiniteMixture.pure p (by omega) 1 (by positivity)) β x Q)
    (hNorm : PhysicalDirectingNormQ
      (FiniteMixture.pure p (by omega) 1 (by positivity)) β Q)
    (hMean : PhysicalReplicaMeanEnergy
      (FiniteMixture.pure p (by omega) 1 (by positivity)) β Q
      (pureEnergyConstant p (by omega)))
    (hRelocate : PhysicalHighEnergyRelocation
      (FiniteMixture.pure p (by omega) 1 (by positivity))
      (pureEnergyConstant p (by omega))) :
    let μ := FiniteMixture.pure p (by omega) 1 (by positivity)
    ∃ γ : ℝ, 0 < γ ∧
      VaryingConvergesInProbability (fun n => disorderLaw (n+2) μ.maxDegree)
        (fun n => originalUniformIntervalDistance μ β
          (exponentialGridHorizon γ (n+2))) (fun _ _ => 1) := by
  let μ := FiniteMixture.pure p (by omega : 2 ≤ p) 1 (by positivity)
  let K := markK μ β Q
  let edge := 2*Real.sqrt (Q^2*μ.xi2 Q)
  let δ := (K-edge)/2
  have hδ : 0 < δ := by
    have hh := h.edge_margin.2.2
    change 0 < K-edge at hh
    exact half_pos hh
  let U := Icc (K-δ) (K+δ)
  have hcontact : markK μ β Q ∈ interior U := by
    rw [show U=Icc (K-δ) (K+δ) from rfl,interior_Icc]
    exact ⟨by linarith,by linarith⟩
  have hgap : ∀ k ∈ U, 2*Real.sqrt (Q^2*μ.xi2 Q) < k := by
    intro k hk
    have hh := hk.1
    change K-δ ≤ k at hh
    change edge < k
    dsimp only [δ] at hδ hh
    linarith
  exact pure_consumer_separation_of_three_physical_inputs p hp h
    U isCompact_Icc hcontact hgap hNorm hMean hRelocate

end SlowEquilibration.SourceConditionedCPTransferPureConsumer
