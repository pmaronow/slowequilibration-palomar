-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourceConditionedCPTransferPureConsumer
public import SlowEquilibration.SourceConditionedCPTransferInitialAdapter
public import SlowEquilibration.SourceInitialPolynomialMenu
public import SlowEquilibration.SourceInitialEntropyInformation

/-! Manuscript `thm:main-initial` (ii)/(iii) and `cor:cp-information` for
the amplitude-one pure model. The source certificate chooses an exterior
radial window; the three physical capture premises give literal Gibbs
capture, and the proved pure count theorem supplies the count bound. The
quantitative CP transfer then gives one exponential horizon, common to
uniform initialization, every polynomial menu (including independent
random menus), small conditional KL, and small full-field information.
The three physical premises remain explicit for later literature adapters. -/

@[expose] public section
noncomputable section

namespace SlowEquilibration.SourceConditionedCPTransferPureAllInitial

open Set MeasureTheory ProbabilityTheory Filter
open SphericalModel SphericalMarkedWindows SphericalTAPCertificate PureStationarity
open TwoAtomStationarity
open PureCapturePhysicalCoarseDiniAssembly SphericalAging.HardSphereDynamics
open SourcePureCaptureLiteralConsumer SourcePureCaptureWindowTransport
open SourcePureCaptureFixedCapEstimates SourceConditionedCPTransferPureConsumer
open SourceConditionedCPTransferInitialAdapter SourceInitialQuantitativeInput
open SourceInitialPolynomialMenu SourceInitialEntropyInformation
open SphericalOverlapExponential SphericalOrthogonalHaar
open scoped Topology NNReal ENNReal

set_option autoImplicit false

universe u v

/-- The quantitative source CP input and uniform-start separation at one
common horizon, under exactly the pure consumer's three physical premises. -/
theorem pure_quantitative_initial_input_of_three_physical_inputs
    (p : ℕ) (hp : 4 ≤ p) {β x Q : ℝ}
    (h : Certificate
      (FiniteMixture.pure p (by omega) 1 (by positivity)) β x Q)
    (hNorm : PhysicalDirectingNormQ
      (FiniteMixture.pure p (by omega) 1 (by positivity)) β Q)
    (hMean : PhysicalReplicaMeanEnergy
      (FiniteMixture.pure p (by omega) 1 (by positivity))
      β Q (pureEnergyConstant p (by omega)))
    (hRelocate : PhysicalHighEnergyRelocation
      (FiniteMixture.pure p (by omega) 1 (by positivity))
      (pureEnergyConstant p (by omega))) :
    let μ := FiniteMixture.pure p (by omega) 1 (by positivity)
    ∃ γ : ℝ, 0 < γ ∧
      ∃ B : ∀ N, ℝ → Set (SphericalFieldKernels.Field N μ × Vector N),
        QuantitativeUniformStart μ β
          (fun N => exponentialGridHorizon γ N) B ∧
        SphericalOrthogonalHaar.uniformSeparationInProbability μ β
          (fun N => exponentialGridHorizon γ N) := by
  let μ := FiniteMixture.pure p (by omega : 2 ≤ p) 1 (by positivity)
  let K := markK μ β Q
  let edge := 2 * Real.sqrt (Q^2 * μ.xi2 Q)
  let δ := (K - edge) / 2
  have hδ : 0 < δ := by
    have hh := h.edge_margin.2.2
    change 0 < K - edge at hh
    exact half_pos hh
  let U := Icc (K - δ) (K + δ)
  have hcontact : markK μ β Q ∈ interior U := by
    rw [show U = Icc (K - δ) (K + δ) from rfl, interior_Icc]
    exact ⟨by linarith, by linarith⟩
  have hgap : ∀ k ∈ U, 2 * Real.sqrt (Q^2 * μ.xi2 Q) < k := by
    intro k hk
    have hh := hk.1
    change K - δ ≤ k at hh
    change edge < k
    dsimp only [δ] at hδ hh
    linarith
  obtain ⟨⟨b₀, hb₀, hCapture⟩, _⟩ :=
    pure_consumer_capture_of_three_physical_inputs
      p hp h U hcontact hNorm hMean hRelocate
  let m : ℕ → ℝ := fun n => (Real.sqrt Q)^p * pureSourceCenter p hp n
  obtain ⟨γ, hγ, S, hsep⟩ := quantitative_uniformStart_of_source_inputs
    μ h.min_degree h.overlap_range.1 h.overlap_range.2.le h.beta_pos.le
    hb₀.2 U isCompact_Icc hgap m
    (pure_consumer_center_normalized_tendsto p hp h)
    (pure_consumer_expected_count_limsup_lt_top p hp h U
      isCompact_Icc.isClosed.measurableSet hcontact)
    (hCapture b₀ ⟨hb₀.1, le_rfl⟩)
  exact ⟨γ, hγ, sourceBands μ Q m b₀ U, S,
    original_uniform_to_haar μ β _ hsep⟩

/-- Pure `thm:main-initial` (ii), including independent random menus,
(iii), and `cor:cp-information`, together with uniform-start separation.
The exponent is chosen before all initial-law data and all menu growth
exponents, so every conclusion uses the same source CP horizon. -/
theorem pure_all_initial_separation_of_three_physical_inputs
    (p : ℕ) (hp : 4 ≤ p) {β x Q : ℝ}
    (h : Certificate
      (FiniteMixture.pure p (by omega) 1 (by positivity)) β x Q)
    (hNorm : PhysicalDirectingNormQ
      (FiniteMixture.pure p (by omega) 1 (by positivity)) β Q)
    (hMean : PhysicalReplicaMeanEnergy
      (FiniteMixture.pure p (by omega) 1 (by positivity))
      β Q (pureEnergyConstant p (by omega)))
    (hRelocate : PhysicalHighEnergyRelocation
      (FiniteMixture.pure p (by omega) 1 (by positivity))
      (pureEnergyConstant p (by omega))) :
    let μ := FiniteMixture.pure p (by omega) 1 (by positivity)
    ∃ γ : ℝ, 0 < γ ∧
      SphericalOrthogonalHaar.uniformSeparationInProbability μ β
        (fun N => exponentialGridHorizon γ N) ∧
      (∀ (ι : ℕ → Type u) [∀ N, Fintype (ι N)] [∀ N, Nonempty (ι N)]
        (ν : ∀ N, ι N → Measure (Vector N))
        [∀ N j, IsProbabilityMeasure (ν N j)],
        (∀ N, 2 ≤ N → ∀ j, ∀ᵐ y ∂ν N j, OnSphere y) →
        ∀ κ C₀ : ℝ, 0 ≤ κ → κ < ((p : ℝ) - 2) / 2 → 0 < C₀ →
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
        ∀ κ C₀ : ℝ, 0 ≤ κ → κ < ((p : ℝ) - 2) / 2 → 0 < C₀ →
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
  let μ := FiniteMixture.pure p (by omega : 2 ≤ p) 1 (by positivity)
  obtain ⟨γ, hγ, B, S, hsep⟩ :=
    pure_quantitative_initial_input_of_three_physical_inputs
      p hp h hNorm hMean hRelocate
  have hα : alpha μ = ((p : ℝ) - 2) / 2 := by
    unfold alpha
    rw [(CSPureModels.pure_degrees p (by omega) 1 (by positivity)).1]
  refine ⟨γ, hγ, hsep, ?_, ?_, ?_, ?_⟩
  · intro ι _ _ ν _ hsupport κ C₀ hκ hκα hC₀ hcard
    exact polynomial_menu_allTime_separation μ β _ B S ν hsupport
      hκ (by rwa [hα]) hC₀ hcard
  · intro ι _ _ R _ ρ _ ν hν _ hsupport κ C₀ hκ hκα hC₀ hcard
    exact polynomial_random_menu_allTime_separation μ β _ B S ρ ν hν hsupport
      hκ (by rwa [hα]) hC₀ hcard
  · intro κ _ hKL
    exact small_conditional_KL_allTime_separation μ β _ B S κ hKL
  · intro κ _ hsupport hI
    exact small_field_information_allTime_separation μ β _ B S κ hsupport hI

end SlowEquilibration.SourceConditionedCPTransferPureAllInitial
