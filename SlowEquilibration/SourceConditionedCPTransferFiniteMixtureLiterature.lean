-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourceMixedCaptureCommonWitness
public import SlowEquilibration.SourceMixedGeneralCPTransfer
public import SlowEquilibration.SourcePureMainCondensedLiterature

/-! Source `thm:main-condensed` and the field-independent clauses of
`thm:main-initial` for finite mixtures. The non-pure branch uses the proved
literature fixed-window capture and the existing mixed CP consumer.

For arbitrary pure amplitude the remaining premise is explicitly named
`PureBranchFixedWindowCapture`. Counts and conditioned entrance are proved
for every positive pure amplitude. The premise is discharged below for
amplitude one; transporting pure capture to a general positive amplitude
still requires the model and temperature scaling identifications. -/

@[expose] public section
noncomputable section

namespace SlowEquilibration.SourceConditionedCPTransferFiniteMixtureLiterature

open Set MeasureTheory ProbabilityTheory Filter
open SphericalModel SphericalTAPCertificate SphericalOrthogonalHaar
open SphericalMarkedWindows
open TwoAtomStationarity SourceReductionConsumerAsymptoticCounts
open SourceLiteratureParisi SourceLiteratureGroundState SourceLiteratureStrictTAPGap
open LiteratureSubagTAP LiteratureSubagReplicaExclusion LiteratureSubagProposition24
open SourceReductionConsumerAsymptotic SourceConditionedCPTransferInitialAdapter
open SphericalOverlapExponential SphericalAging.HardSphereDynamics
open scoped Topology NNReal

set_option autoImplicit false

/-- The only remaining pure-branch input: fixed-window Gibbs capture at
the printed logarithmic center, on a compact exterior radial window.
The implication is vacuous for non-pure mixtures. This does not assume a
count estimate, entrance estimate, or the desired dynamics separation. -/
def PureBranchFixedWindowCapture (μ : FiniteMixture) (β x Q : ℝ) : Prop :=
  ¬ μ.minDegree < μ.maxDegree →
    ∃ (U : Set ℝ) (b : ℝ),
      IsCompact U ∧
      markK μ β Q ∈ interior U ∧
      (∀ k ∈ U, 2 * Real.sqrt (Q^2 * μ.xi2 Q) < k) ∧
      0 < b ∧ b < Real.sqrt Q ∧
      Tendsto (fun M : ℝ => limsup (fun n : ℕ =>
        ∫ J, originalBandComplementMass μ Q
          (sourcePureAnalyticCenter (n+2) (markE μ β x Q) (β*x))
          M b β U J ∂disorderLaw (n+2) μ.maxDegree) atTop)
        atTop (𝓝 0)

/-- The already proved pure count theorem supplies the consumer's count
bound for every positive pure coefficient, at the printed center. -/
private theorem pure_analytic_expected_count_limsup_lt_top
    (μ : FiniteMixture) {β x Q : ℝ}
    (h : Certificate μ β x Q)
    (hnp : ¬ μ.minDegree < μ.maxDegree)
    (U : Set ℝ) (hU : MeasurableSet U)
    (hcontact : markK μ β Q ∈ interior U)
    (M : ℝ) (hM : 0 < M) :
    limsup (originalWindowExpectedCount μ Q
      (fun n => sourcePureAnalyticCenter (n+2) (markE μ β x Q) (β*x))
      M U) atTop < ⊤ := by
  obtain ⟨p, hp, c, hc, hμ⟩ :=
    SourceConditionedCPTransfer.pure_representation_of_not_nonpure μ hnp
  subst μ
  obtain ⟨hCount, _, _⟩ :=
    sourcePure_prop_pc_counts_literal p hp c hc h U hU hcontact
  obtain ⟨B, hB⟩ := hCount M hM
  have hbound : ∀ n : ℕ,
      originalWindowExpectedCount (FiniteMixture.pure p hp c hc) Q
        (fun n => sourcePureAnalyticCenter (n+2)
          (markE (FiniteMixture.pure p hp c hc) β x Q) (β*x))
        M U n ≤ ENNReal.ofReal B := by
    intro n
    obtain ⟨hf, hv⟩ := hB n
    have hh := ENNReal.ofReal_le_ofReal hv
    rw [ENNReal.ofReal_toReal hf.ne] at hh
    simpa only [originalWindowExpectedCount] using hh
  exact (limsup_le_of_le (by isBoundedDefault)
    (.of_forall hbound)).trans_lt ENNReal.ofReal_lt_top

/-- Source `thm:main-condensed` for a non-pure finite mixture, conditional
only on its strict one-step certificate and the cited literature. -/
theorem mixed_separation_of_cited_theorems
    (μ : FiniteMixture) {β x Q : ℝ}
    (h : Certificate μ β x Q)
    (hnp : μ.minDegree < μ.maxDegree)
    (hChen : Chen2013FiniteParisi)
    (hChenSen : ChenSenFiniteGround)
    (h5 : Theorem5
      (literatureThermodynamicData hChen hChenSen μ h.beta_pos.le))
    (h25 : Remark25Contrapositive μ β)
    (h24 : Proposition24 μ β Q) :
    ∃ γ : ℝ, 0 < γ ∧
      VaryingConvergesInProbability
        (fun n => disorderLaw (n+2) μ.maxDegree)
        (fun n => originalUniformIntervalDistance μ β
          (exponentialGridHorizon γ (n+2)))
        (fun _ _ => 1) := by
  obtain ⟨L, R, b₀, hEdge, _hL, _hR, hb₀, hb₀Q, m, hm, hcount, hcapture⟩ :=
    SourceMixedCaptureCommonWitness.mixed_original_fixed_window_capture_of_literature
      μ h hnp hChen hChenSen h5 h25 h24
  exact SourceMixedGeneralCPTransfer.source_mixed_general_cp_separation
    μ h.min_degree h.overlap_range.1 h.overlap_range.2.le hnp h.beta_pos.le hb₀Q
    (Icc L R) isCompact_Icc (fun k hk => hEdge.trans_le hk.1)
    m hm hcount (hcapture b₀ hb₀ le_rfl)

set_option maxHeartbeats 800000 in
/-- The explicit pure capture premise is already proved for amplitude
one, from the same certificate and cited literature as the pure main theorem. -/
theorem pure_amplitude_one_fixed_window_capture_of_cited_theorems
    (p : ℕ) (hp : 4 ≤ p) {β x Q : ℝ}
    (h : Certificate (FiniteMixture.pure p (by omega) 1 (by positivity)) β x Q)
    (hChen : Chen2013FiniteParisi) (hChenSen : ChenSenFiniteGround)
    (h5 : Theorem5 (literatureThermodynamicData hChen hChenSen
      (FiniteMixture.pure p (by omega) 1 (by positivity)) h.beta_pos.le))
    (h25 : Remark25Contrapositive
      (FiniteMixture.pure p (by omega) 1 (by positivity)) β)
    (h24 : Proposition24 (FiniteMixture.pure p (by omega) 1 (by positivity)) β Q) :
    PureBranchFixedWindowCapture
      (FiniteMixture.pure p (by omega) 1 (by positivity)) β x Q := by
  intro _hnp
  let μ := FiniteMixture.pure p (by omega : 2 ≤ p) 1 (by positivity)
  let K := markK μ β Q
  let edge := 2 * Real.sqrt (Q^2 * μ.xi2 Q)
  let δ := (K-edge)/2
  have hδ : 0 < δ := by
    have hh := h.edge_margin.2.2
    change 0 < K-edge at hh
    exact half_pos hh
  let U := Icc (K-δ) (K+δ)
  have hcontact : markK μ β Q ∈ interior U := by
    rw [show U = Icc (K-δ) (K+δ) from rfl, interior_Icc]
    exact ⟨by linarith, by linarith⟩
  have hgap : ∀ k ∈ U, 2 * Real.sqrt (Q^2 * μ.xi2 Q) < k := by
    intro k hk
    have hh := hk.1
    change K-δ ≤ k at hh
    change edge < k
    dsimp only [δ] at hδ hh
    linarith
  obtain ⟨⟨b, hb, hcapture⟩, _⟩ :=
    SourcePureCaptureLiteralConsumer.pure_consumer_capture_of_three_physical_inputs
      p hp h U hcontact
      (SourceLiteraturePhysicalNormQ.physicalDirectingNormQ_of_cited_theorems
        hChen hChenSen h h5 h25)
      (PureReplicaMeanEnergyAssembly.pure_physicalReplicaMeanEnergy_of_literature
        p hp h hChen h24)
      (PurePhysicalHighEnergyRelocation.pure_physicalHighEnergyRelocation p hp)
  refine ⟨U, b, isCompact_Icc, hcontact, hgap, hb.1, hb.2, ?_⟩
  have hc := hcapture b ⟨hb.1, le_rfl⟩
  change Tendsto (fun M : ℝ => limsup (fun n : ℕ =>
    ∫ J, originalBandComplementMass μ Q
      ((Real.sqrt Q)^p * SourcePureCaptureFixedCapEstimates.pureSourceCenter p hp n)
      M b β U J ∂disorderLaw (n+2) μ.maxDegree) atTop) atTop (𝓝 0) at hc
  simp_rw [SourcePureCaptureLiteralConsumer.pure_source_consumer_center_eq p hp h] at hc
  exact hc

/-- Finite-mixture source `thm:main-condensed`, with only pure
fixed-window capture still explicit. All cited interfaces refer to `μ`
itself. The non-pure branch has no additional physical premise. -/
theorem finiteMixture_separation_of_cited_theorems
    (μ : FiniteMixture) {β x Q : ℝ}
    (h : Certificate μ β x Q)
    (hChen : Chen2013FiniteParisi)
    (hChenSen : ChenSenFiniteGround)
    (h5 : Theorem5
      (literatureThermodynamicData hChen hChenSen μ h.beta_pos.le))
    (h25 : Remark25Contrapositive μ β)
    (h24 : Proposition24 μ β Q)
    (hPureBranchFixedWindowCapture : PureBranchFixedWindowCapture μ β x Q) :
    ∃ γ : ℝ, 0 < γ ∧
      VaryingConvergesInProbability
        (fun n => disorderLaw (n+2) μ.maxDegree)
        (fun n => originalUniformIntervalDistance μ β
          (exponentialGridHorizon γ (n+2)))
        (fun _ _ => 1) := by
  by_cases hnp : μ.minDegree < μ.maxDegree
  · exact mixed_separation_of_cited_theorems μ h hnp hChen hChenSen h5 h25 h24
  · obtain ⟨U, b, hU, hcontact, hgap, _hb, hbQ, hcapture⟩ :=
      hPureBranchFixedWindowCapture hnp
    obtain ⟨_a, γ, _ha, _hag, hγ, hTransfer⟩ :=
      SourceConditionedCPTransferUnconditional.source_cp_transfer μ h.min_degree
        (E := markE μ β x Q) h.overlap_range.1 h.overlap_range.2.le
        h.beta_pos.le hbQ U hU hgap
    refine ⟨γ, hγ, ?_⟩
    exact (hTransfer
      (fun n => sourcePureAnalyticCenter (n+2) (markE μ β x Q) (β*x))
      (SourceConditionedCPTransferPureConsumer.sourcePureAnalyticCenter_normalized_tendsto
        _ _)
      (pure_analytic_expected_count_limsup_lt_top μ h hnp U
        hU.isClosed.measurableSet hcontact)).2 hcapture

/-- The finite-mixture separation and both field-independent initial-law
clauses hold with one exponent. General pure amplitude retains exactly the
named capture premise of `finiteMixture_separation_of_cited_theorems`. -/
theorem finiteMixture_main_condensed_and_initial_of_cited_theorems
    (μ : FiniteMixture) {β x Q : ℝ}
    (h : Certificate μ β x Q)
    (hChen : Chen2013FiniteParisi)
    (hChenSen : ChenSenFiniteGround)
    (h5 : Theorem5
      (literatureThermodynamicData hChen hChenSen μ h.beta_pos.le))
    (h25 : Remark25Contrapositive μ β)
    (h24 : Proposition24 μ β Q)
    (hPureBranchFixedWindowCapture : PureBranchFixedWindowCapture μ β x Q) :
    ∃ γ : ℝ, 0 < γ ∧
      VaryingConvergesInProbability
        (fun n => disorderLaw (n+2) μ.maxDegree)
        (fun n => originalUniformIntervalDistance μ β
          (exponentialGridHorizon γ (n+2)))
        (fun _ _ => 1) ∧
      uniformSeparationInProbability μ β (fun N => exponentialGridHorizon γ N) ∧
      (∀ ε : ℝ, 0 < ε →
        Tendsto (uniformPrescribedFailure μ β
          (fun N => exponentialGridHorizon γ N) ε) atTop (𝓝 0)) ∧
      (∀ (Ω : ℕ → Type) [∀ N, MeasurableSpace (Ω N)]
          (P : ∀ N, Measure (Ω N)) [∀ N, IsProbabilityMeasure (P N)]
          (J : ∀ N, Ω N → Disorder N μ.maxDegree)
          (ν : ∀ N, Ω N → ProbabilityMeasure (Vector N)),
          (∀ N, HasLaw (J N) (disorderLaw N μ.maxDegree) (P N)) →
          (∀ N, AEMeasurable (ν N) (P N)) →
          (∀ N, IndepFun (J N) (ν N) (P N)) →
          (∀ N, 1 ≤ N → ∀ᵐ ω ∂P N, ∀ᵐ y ∂(ν N ω).toMeasure, OnSphere y) →
          ∀ ε : ℝ, 0 < ε →
            Tendsto (fun N => (P N).real
              {ω | intervalDistance μ β (exponentialGridHorizon γ N)
                (J N ω) (ν N ω) < 1-ε}) atTop (𝓝 0)) := by
  obtain ⟨γ, hγ, hsep⟩ := finiteMixture_separation_of_cited_theorems
    μ h hChen hChenSen h5 h25 h24 hPureBranchFixedWindowCapture
  refine ⟨γ, hγ, hsep, original_uniform_to_haar μ β _ hsep,
    fun ε hε => prescribed_initial_failure_of_original_uniform μ β _ hsep hε, ?_⟩
  intro Ω _ P _ J ν hJ hν hind hsphere ε hε
  exact independent_initial_failure_of_original_uniform μ β _ hsep
    P J ν hJ hν hind hsphere hε

end SlowEquilibration.SourceConditionedCPTransferFiniteMixtureLiterature
