-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourcePureAmplitudeScaling
public import SlowEquilibration.SourceInitialPolynomialMenu
public import SlowEquilibration.SourceInitialEntropyInformation

/-! Manuscript `thm:main-initial` (ii)/(iii) and `cor:cp-information` for
every certified finite mixture, conditional on the same five literature
interfaces as the finite-mixture main theorem. The mixed capture witness
and the pure capture theorem at every positive amplitude supply fixed-window
counts and capture with a common center. Quantitative CP transfer chooses
one positive exponent before all menu and initial-law data.

Polynomial menus have growth exponent less than `(d - 2) / 2`, where
`d` is the minimum degree. Random menus are independent of the full ambient
polynomial field, expressed by the product of their randomness law and
`SphericalFieldKernels.fieldLaw`; this is the field used by the existing
reductions. The information conclusion likewise concerns that full field.
-/

@[expose] public section
noncomputable section

namespace SlowEquilibration.SourceFiniteMixtureAllInitialLiterature

open Set MeasureTheory ProbabilityTheory Filter
open SphericalModel SphericalTAPCertificate SphericalMarkedWindows TwoAtomStationarity
open SourceLiteratureParisi SourceLiteratureGroundState SourceLiteratureStrictTAPGap
open LiteratureSubagTAP LiteratureSubagReplicaExclusion LiteratureSubagProposition24
open SourceReductionConsumerAsymptoticCounts SourceConditionedCPTransferInitialAdapter
open SourceInitialQuantitativeInput SourceInitialPolynomialMenu SourceInitialEntropyInformation
open SphericalOverlapExponential SphericalOrthogonalHaar SphericalAging.HardSphereDynamics
open scoped Topology NNReal ENNReal

set_option autoImplicit false

universe u v

/-- The pure critical-count theorem at arbitrary positive amplitude gives
the count input at the same analytic center as the scaled capture theorem. -/
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

/-- Retain the quantitative CP witness and uniform-start separation at
one horizon, using the common count/capture center in either branch. -/
private theorem finiteMixture_quantitative_initial_input_of_literature
    (μ : FiniteMixture) {β x Q : ℝ}
    (h : Certificate μ β x Q)
    (hChen : Chen2013FiniteParisi)
    (hChenSen : ChenSenFiniteGround)
    (h5 : Theorem5
      (literatureThermodynamicData hChen hChenSen μ h.beta_pos.le))
    (h25 : Remark25Contrapositive μ β)
    (h24 : Proposition24 μ β Q) :
    ∃ γ : ℝ, 0 < γ ∧
      ∃ B : ∀ N, ℝ → Set (SphericalFieldKernels.Field N μ × Vector N),
        QuantitativeUniformStart μ β
          (fun N => exponentialGridHorizon γ N) B ∧
        uniformSeparationInProbability μ β
          (fun N => exponentialGridHorizon γ N) := by
  by_cases hnp : μ.minDegree < μ.maxDegree
  · obtain ⟨L, R, b₀, hEdge, _hL, _hR, hb₀, hb₀Q, m, hm, hcount, hcapture⟩ :=
      SourceMixedCaptureCommonWitness.mixed_original_fixed_window_capture_of_literature
        μ h hnp hChen hChenSen h5 h25 h24
    obtain ⟨γ, hγ, S, hsep⟩ := quantitative_uniformStart_of_source_inputs
      μ h.min_degree h.overlap_range.1 h.overlap_range.2.le h.beta_pos.le hb₀Q
      (Icc L R) isCompact_Icc (fun k hk => hEdge.trans_le hk.1)
      m hm hcount (hcapture b₀ hb₀ le_rfl)
    exact ⟨γ, hγ, sourceBands μ Q m b₀ (Icc L R), S,
      original_uniform_to_haar μ β _ hsep⟩
  · obtain ⟨U, b, hU, hcontact, hgap, _hb, hbQ, hcapture⟩ :=
      SourcePureAmplitudeScaling.pureBranchFixedWindowCapture_of_cited_theorems
        μ h hChen hChenSen h5 h25 h24 hnp
    let m : ℕ → ℝ := fun n =>
      sourcePureAnalyticCenter (n+2) (markE μ β x Q) (β*x)
    obtain ⟨γ, hγ, S, hsep⟩ := quantitative_uniformStart_of_source_inputs
      μ h.min_degree h.overlap_range.1 h.overlap_range.2.le h.beta_pos.le hbQ
      U hU hgap m
      (SourceConditionedCPTransferPureConsumer.sourcePureAnalyticCenter_normalized_tendsto
        (markE μ β x Q) (β*x))
      (pure_analytic_expected_count_limsup_lt_top μ h hnp U
        hU.isClosed.measurableSet hcontact) hcapture
    exact ⟨γ, hγ, sourceBands μ Q m b U, S,
      original_uniform_to_haar μ β _ hsep⟩

/-- Source `thm:main-initial` (ii)/(iii) and `cor:cp-information` for every
certified finite mixture, together with uniform-start separation at the
same exponent. The five literature interfaces concern the original model.
Random menus are independent of the full ambient polynomial field under
the displayed product law; mutual information is with that same field. -/
theorem finiteMixture_all_initial_of_literature
    (μ : FiniteMixture) {β x Q : ℝ}
    (h : Certificate μ β x Q)
    (hChen : Chen2013FiniteParisi)
    (hChenSen : ChenSenFiniteGround)
    (h5 : Theorem5
      (literatureThermodynamicData hChen hChenSen μ h.beta_pos.le))
    (h25 : Remark25Contrapositive μ β)
    (h24 : Proposition24 μ β Q) :
    ∃ γ : ℝ, 0 < γ ∧
      uniformSeparationInProbability μ β
        (fun N => exponentialGridHorizon γ N) ∧
      (∀ (ι : ℕ → Type u) [∀ N, Fintype (ι N)] [∀ N, Nonempty (ι N)]
        (ν : ∀ N, ι N → Measure (Vector N))
        [∀ N j, IsProbabilityMeasure (ν N j)],
        (∀ N, 2 ≤ N → ∀ j, ∀ᵐ y ∂ν N j, OnSphere y) →
        ∀ κ C₀ : ℝ, 0 ≤ κ → κ < ((μ.minDegree : ℝ) - 2) / 2 → 0 < C₀ →
        (∀ᶠ N in atTop,
          (Fintype.card (ι N) : ℝ) ≤ C₀ * (N : ℝ)^κ) →
        VaryingProbability.InProbability
          (fun N => SphericalFieldKernels.fieldLaw N μ)
          (fun N => SphericalMenuReduction.physicalMenuDistance
            μ β (ν N) (exponentialGridHorizon γ N)) 1) ∧
      (∀ (ι : ℕ → Type u) [∀ N, Fintype (ι N)] [∀ N, Nonempty (ι N)]
        (R : ℕ → Type v) [∀ N, MeasurableSpace (R N)]
        (ρ : ∀ N, Measure (R N)) [∀ N, IsProbabilityMeasure (ρ N)]
        (ν : ∀ N, R N → ι N → Measure (Vector N)),
        (∀ N j, Measurable (fun r => ν N r j)) →
        ∀ [∀ N r j, IsProbabilityMeasure (ν N r j)],
        (∀ N, 2 ≤ N → ∀ r j, ∀ᵐ y ∂ν N r j, OnSphere y) →
        ∀ κ C₀ : ℝ, 0 ≤ κ → κ < ((μ.minDegree : ℝ) - 2) / 2 → 0 < C₀ →
        (∀ᶠ N in atTop,
          (Fintype.card (ι N) : ℝ) ≤ C₀ * (N : ℝ)^κ) →
        VaryingProbability.InProbability
          (fun N => (ρ N).prod (SphericalFieldKernels.fieldLaw N μ))
          (fun N z => SphericalMenuReduction.physicalMenuDistance
            μ β (ν N z.1) (exponentialGridHorizon γ N) z.2) 1) ∧
      (∀ (κ : ∀ N, Kernel (SphericalFieldKernels.Field N μ) (Vector N))
        [∀ N, IsMarkovKernel (κ N)],
        ReductionEntropy.LittleLogInProbability
          (fun N => SphericalFieldKernels.fieldLaw N μ)
          (fun N H => InformationTheory.klDiv (κ N H) (sphereLaw N)) →
        VaryingProbability.InProbability
          (fun N => SphericalFieldKernels.fieldLaw N μ)
          (fun N => SphericalFieldKernels.intervalDistance
            μ β (exponentialGridHorizon γ N) (κ N)) 1) ∧
      (∀ (κ : ∀ N, Kernel (SphericalFieldKernels.Field N μ) (Vector N))
        [∀ N, IsMarkovKernel (κ N)],
        (∀ N, 2 ≤ N → ∀ H, ∀ᵐ y ∂κ N H, OnSphere y) →
        ReductionInformation.LittleLog
          (fun N => endpointMutualInformation
            (SphericalFieldKernels.fieldLaw N μ) (κ N)) →
        VaryingProbability.InProbability
          (fun N => SphericalFieldKernels.fieldLaw N μ)
          (fun N => SphericalFieldKernels.intervalDistance
            μ β (exponentialGridHorizon γ N) (κ N)) 1) := by
  obtain ⟨γ, hγ, B, S, hsep⟩ :=
    finiteMixture_quantitative_initial_input_of_literature μ h hChen hChenSen h5 h25 h24
  refine ⟨γ, hγ, hsep, ?_, ?_, ?_, ?_⟩
  · intro ι _ _ ν _ hsupport κ C₀ hκ hκα hC₀ hcard
    exact polynomial_menu_allTime_separation μ β _ B S ν hsupport
      hκ hκα hC₀ hcard
  · intro ι _ _ R _ ρ _ ν hν _ hsupport κ C₀ hκ hκα hC₀ hcard
    exact polynomial_random_menu_allTime_separation μ β _ B S ρ ν hν hsupport
      hκ hκα hC₀ hcard
  · intro κ _ hKL
    exact small_conditional_KL_allTime_separation μ β _ B S κ hKL
  · intro κ _ hsupport hI
    exact small_field_information_allTime_separation μ β _ B S κ hsupport hI

end SlowEquilibration.SourceFiniteMixtureAllInitialLiterature
