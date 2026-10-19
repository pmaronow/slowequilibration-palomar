-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.LiteratureSubagBandLowerComparison
public import SlowEquilibration.LiteratureSubagBandUpperExtraction
public import SlowEquilibration.LiteratureSubagTheorem10Final
public import SlowEquilibration.MixedReplicaMeanEnergyAssembly
public import SlowEquilibration.PureReplicaMeanEnergyAssembly
public import SlowEquilibration.PureReplicaMeansExponential
public import SlowEquilibration.SourceDirectingFamilies
public import SlowEquilibration.SourceFiniteMixtureMainLiteral
public import SlowEquilibration.SourceGaussianDeBruijn
public import SlowEquilibration.SourceGeneralContactTheorem
public import SlowEquilibration.SourceGroundProfileUniqueness
public import SlowEquilibration.SourceLiteratureGroundState
public import SlowEquilibration.SourceLiteratureGroundStateCenterBridge
public import SlowEquilibration.SourceLiteratureGroundStateExtraction
public import SlowEquilibration.SourceMainClassesDegreeWindow
public import SlowEquilibration.SourceMainClassesLiterature
public import SlowEquilibration.SourceMixedCaptureCommonWitness
public import SlowEquilibration.SourceMixedCountCapturePackage
public import SlowEquilibration.SourcePureAmplitudeScaling
public import SlowEquilibration.SourcePureMainTheoremsLiterature
public import SlowEquilibration.SourcePureSection9Literature
public import SlowEquilibration.SourcePureSeparationCorollary13Proof

/-!
# Principal manuscript endpoints after the proved literature reductions

`C` denotes `Chen2013FiniteParisi`. `B(μ,β)` denotes
`SubagBandApproximations μ β`, exactly the conjunction of the expected upper
and lower band approximations for the physical thermodynamic data.
`U(μ,β)` denotes only its upper half, at `chenThermodynamicData`.
All certificate, temperature, geometric and initial-law assumptions are
retained. Corollary 13 consumers use the proved degree range `p ≥ 4`; no
cubic separation claim is made. The conclusions below are the original endpoint conclusions.
An entry `none` means no literature or band hypothesis, including no Chen
hypothesis; the `_of_chen` suffix is retained for a uniform export convention.
The universal data quantifier in `B` adds no assumption: uniqueness of the
physical residual limit gives `subagBandApproximations_iff` at any data `D`.

| Endpoint (suffix omitted) | Manuscript label | Remaining inputs |
| --- | --- | --- |
| `finiteMixture_main_condensed_and_initial_literal` | `thm:main-condensed; thm:main-initial(i)` | C + B(μ,β) |
| `finiteMixture_all_initial_spherical` | `thm:main-initial(i)–(iii); cor:cp-information` | C + B(μ,β) |
| `pure_corollary_a_all_initial` | `cor:main-classes(a), all initial laws` | C + B(μ,β) |
| `convex_corollary_b` | `cor:main-classes(b), convexity` | C + B(μ,β) |
| `degree_window_corollary_b` | `cor:main-classes(b), degree window` | C + B(μ,β) |
| `support_four_through_eleven_corollary_b` | `cor:main-classes(b), support 4–11` | C + B(μ,β) |
| `nonconvex_corollary_d` | `cor:main-classes(d)` | C + B(μ,β) |
| `directing_norm` | `thm:dir-norm, literal directing families` | C + B(μ,β) |
| `pureBranchFixedWindowCapture` | `thm:pc-capture, arbitrary amplitude` | C + B(μ,β) |
| `source_subag_tap` | `thm:th-subag(1), whole [0,1)` | B at the supplied data + zero-contact block lower tail (still open) |
| `source_replica_criterion` | `thm:th-subag(2), whole [0,1)` | C + B(μ,β) + zero-contact block lower tail (still open) |
| `contact_iff_multiSamplable` | `thm:th-contact(1)` | C + B(μ,β) + Theorem10Forward (still open) |
| `contact_ground_profile_unique` | `thm:th-contact(2), ground profile` | C + B(μ,β) + Theorem10Forward (still open) |
| `strict_oneStep_structure` | `prop:th-structure` | C + B(μ,β) + Theorem10Forward (still open) |
| `tapValue_le_pressure_sub_gap` | `thm:th-contact(3), quantitative gap` | C |
| `strict_tap_gap` | `thm:th-contact(3), strict gap` | C |
| `compact_uniform_tap_gap` | `thm:th-contact(3), compact uniform gap` | C |
| `source_ground_limit_unique` | `thm:th-ground` | C |
| `canonical_ground_limit` | `thm:th-ground, canonical field` | C |
| `physical_residual_ground_limit` | `thm:th-ground, residual field` | C |
| `center_ground_limit` | `thm:th-ground, center field` | C |
| `pure_capture` | `thm:pc-capture` | C + U(μ,β) |
| `pure_coarse_cover` | `prop:pc-coarse` | C + U(μ,β) |
| `pure_diagonal_localization` | `lem:pc-diagonal` | C + U(μ,β) |
| `mixed_original_fixed_window_capture` | `thm:mb-capture` | C + B(μ,β) |
| `mixed_count_capture_package` | `thm:mc-counts; lem:mb-counts; thm:mb-capture, mixed` | C + B(μ,β) |
| `pure_normalized_count_capture_package` | `thm:mc-counts; lem:mb-counts; thm:mb-capture, pure` | C + B(μ,β) |
| `finiteMixture_count_capture_package` | `thm:mb-capture, all finite mixtures` | C + B(μ,β) |
| `mixed_contactReplicaMeanEnergy_exponential` | `lem:mb-replica, exponential` | C |
| `mixed_contactReplicaMeanEnergy` | `lem:mb-replica, physical input` | C |
| `pure_replica_means_exponential` | `prop:pc-replica-means, exponential` | C |
| `pure_physicalReplicaMeanEnergy` | `prop:pc-replica-means, physical input` | C |
| `pure_original_critical_separation` | `prop:pc-separation` | none |
| `pure_original_microscopic_disjointness` | `cor:pc-disjoint, microscopic bands` | none |
| `pure_original_disjoint_bands_and_bounded_count` | `cor:pc-disjoint, full package` | none |
| `geodesic_lipschitz_centered_mgf` | `lem:ent-lsi` | none |
| `observable_centered_mgf_le_sharp` | `lem:ent-latitude, sharp MGF` | none |
| `observable_hasSubgaussianMGF` | `lem:ent-latitude, sub-Gaussian predicate` | none |
| `center_latitude_mean_and_mgf` | `lem:ent-latitude, original event` | none |
| `constant_completed_center_latitude_mean_and_mgf` | `lem:ent-latitude, constant-completed event` | none |
| `full_center_latitude_mean_and_mgf` | `lem:ent-latitude, full harmonic event` | none |
| `perturbative_corollary_c` | `cor:main-classes(c)` | C + B for each resulting mixture, after the uniform cutoff |
| `physicalDirectingNormQ` | `thm:dir-norm`, physical input | C + U(μ,β) |
| `replica_exclusion_of_positive_potential` | `lem:th-replica-exclusion`, arbitrary positive potential | C + U(μ,β) |
| `source_replica_exclusion_of_strict_tap_gap` | `lem:th-replica-exclusion`, strict physical gap | U at the supplied data |
| `source_normalized_replica_exclusion` | `lem:th-replica-exclusion`, arbitrary nonsamplable overlap | B at the supplied data |
| `contact_residual_canonical` | `thm:th-contact(2)`, residual law | none |

Theorem 10 is a separate unresolved interface: the tracked
`LiteratureSubagTheorem10Proof` and `LiteratureSubagTheorem10Final` reduce it
to contact block rates/lower tails, not to the two band approximations.
Accordingly the three rows marked `Theorem10Forward` retain that original
hypothesis explicitly. The two `thm:th-subag` rows use its weaker latest
reduction: the exact block lower-tail assumption only at zero (and only at
or above the static threshold). These five rows do not claim the requested
Chen-and-bands-only reduction; the remaining rows do achieve it. In particular no contact-rate
assumption is hidden inside `SubagBandApproximations`.

The two approximation interfaces are left explicit. Proposition 24,
subsequence band extraction, block-rate comparison, Chen–Sen and the sphere
logarithmic Sobolev interface are supplied by their tracked proofs.
-/

@[expose] public section
noncomputable section

namespace SlowEquilibration.SourceMainTheoremsReducedFinal

open MeasureTheory ProbabilityTheory Filter Set
open SphericalModel SphericalTAPCertificate
open SourceLiteratureParisi SourceLiteratureGroundState
open LiteratureSubagTAP LiteratureSubagRemark25Proof LiteratureSubagTheorem5Proof
open LiteratureSubagRemark25Final
open scoped Topology NNReal ENNReal

set_option autoImplicit false
set_option maxHeartbeats 1600000

universe u v

/-- Only the two remaining expected-band approximations, for the actual
physical limits. The data quantifier is equivalent to choosing any one `D`.
In particular this definition contains no conclusion about contacts or replicas. -/
def SubagBandApproximations (μ : FiniteMixture) (β : ℝ) : Prop :=
  ∀ D : ThermodynamicData μ β,
    ExpectedBandUpperApproximation D ∧ ExpectedBandLowerApproximation D

/-- Upper approximation is independent of the choice of physical limit data. -/
theorem expectedBandUpperApproximation_iff {μ : FiniteMixture} {β : ℝ}
    (D E : ThermodynamicData μ β) :
    ExpectedBandUpperApproximation D ↔ ExpectedBandUpperApproximation E := by
  have hres (q : ℝ) (hq : q ∈ Ioo (0 : ℝ) 1) : D.residual q = E.residual q :=
    (thermodynamicData_values_unique D E).2 q hq |>.2
  constructor
  · intro h q hq
    simpa only [hres q hq] using h q hq
  · intro h q hq
    simpa only [hres q hq] using h q hq

/-- The clean mixture/temperature package is exactly the original conjunction
at any chosen thermodynamic data; it imposes no uniformity in mixture or temperature. -/
theorem subagBandApproximations_iff {μ : FiniteMixture} {β : ℝ}
    (D : ThermodynamicData μ β) :
    SubagBandApproximations μ β ↔
      ExpectedBandUpperApproximation D ∧ ExpectedBandLowerApproximation D := by
  constructor
  · exact fun h => h D
  · intro h E
    exact ⟨(expectedBandUpperApproximation_iff D E).mp h.1,
      (LiteratureSubagBandLowerComparison.expectedBandLowerApproximation_iff D E).mp h.2⟩

/-- Theorem 5 assembled with extraction and block comparison proved. -/
theorem theorem5_of_bands {μ : FiniteMixture} {β : ℝ}
    (D : ThermodynamicData μ β) (hβ : 0 < β)
    (hBands : SubagBandApproximations μ β) : Theorem5 D :=
  LiteratureSubagBandLowerComparison.Endpoints.theorem5_of_band_estimates_reduced3
    D hβ (hBands D).1 (hBands D).2
    (LiteratureSubagBandUpperExtraction.subsequenceBandExtraction D)

/-- Remark 25 assembled from the same two approximations, with no separate
Theorem 5, Proposition 24, extraction or reconstruction hypothesis. -/
theorem remark25_of_bands {μ : FiniteMixture} {β : ℝ}
    (D : ThermodynamicData μ β) (hβ : 0 < β)
    (hBands : SubagBandApproximations μ β) :
    LiteratureSubagReplicaExclusion.Remark25Contrapositive μ β :=
  LiteratureSubagBandUpperExtraction.Endpoints.remark25Contrapositive_reduced3
    D hβ (hBands D).1 (hBands D).2
    (LiteratureSubagBandLowerComparison.bandBlockRateComparison μ β)

section

open Set MeasureTheory ProbabilityTheory Filter
open SphericalModel SphericalTAPCertificate SphericalOrthogonalHaar
open SphericalEffectiveField SphericalRotationCovariance SphericalReversibility SphericalDynamics
open SourceLiteratureParisi SourceLiteratureGroundState SourceLiteratureStrictTAPGap
open LiteratureSubagTAP LiteratureSubagReplicaExclusion LiteratureSubagProposition24
open SourceReductionConsumerAsymptotic SphericalOverlapExponential
open SphericalAging.HardSphereDynamics
open scoped Topology NNReal
open SourceFiniteMixtureMainLiteral

/-- `thm:main-condensed; thm:main-initial(i)` with the proved literature inputs discharged.
Original endpoint: `SourceFiniteMixtureMainLiteral.finiteMixture_main_condensed_and_initial_literal`. -/
theorem finiteMixture_main_condensed_and_initial_literal_of_chen_and_bands
    (μ : FiniteMixture)
    {β x Q : ℝ}
    (h : Certificate μ β x Q)
    (hChen : Chen2013FiniteParisi)
    (hBands : SubagBandApproximations μ β) :
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
          (∀ N, IndepFun
            (fun ω => fun x : {x : Vector N // OnSphere x} =>
              field (mixtureCoefficients μ) (J N ω) x) (ν N) (P N)) →
          (∀ N, 1 ≤ N → ∀ᵐ ω ∂P N, ∀ᵐ y ∂(ν N ω).toMeasure, OnSphere y) →
          ∀ ε : ℝ, 0 < ε →
            Tendsto (fun N => (P N).real
              {ω | intervalDistance μ β (exponentialGridHorizon γ N)
                (J N ω) (ν N ω) < 1-ε}) atTop (𝓝 0)) := by
  have hChenSen := SourceLiteratureGroundStateExtraction.chenSenFiniteGround hChen
  have h5 : Theorem5
      (literatureThermodynamicData hChen hChenSen μ h.beta_pos.le) :=
    theorem5_of_bands _ (h.beta_pos) hBands
  have h25 : Remark25Contrapositive μ β := remark25_of_bands
    (chenThermodynamicData hChen μ (h.beta_pos).le) (h.beta_pos) hBands
  have h24 : Proposition24 μ β Q :=
    LiteratureSubagProposition24Proof.proposition24 _ (h.beta_pos)
      ⟨h.overlap_range.1.le, h.overlap_range.2⟩
  exact SourceFiniteMixtureMainLiteral.finiteMixture_main_condensed_and_initial_literal
    (μ := μ) (β := β) (x := x) (Q := Q) (h := h) (hChen := hChen) (hChenSen := hChenSen) (h5 := h5)
    (h25 := h25) (h24 := h24)

end

section

open Set Filter MeasureTheory ProbabilityTheory
open SphericalModel SphericalForm SphericalGaussianJet SphericalMarkedWindows
open SphericalTAPCertificate TwoAtomStationarity PairConditionalDeterminantMoments
open SphericalTAPCriticalBandSectionBridge SphericalTAPMixedLowSumMarkedKR
open SourceMixedLowSumBorelIndicator SourceMixedCriticalCenteredWindowCount
open SphericalTAPCriticalHeavyBandProbability SourceReductionConsumerAsymptoticCounts
open SourceReductionConsumerAsymptotic SourceReductionClosedBandGraph
open SourceReductionFiniteWindowCapture MixedHighEnergyRelocation
open MixedReplicaMeanEnergyAssembly LatitudeGroundTrial SphericalPairChartKacRice
open SourceLiteratureParisi SourceLiteratureGroundState SourceLiteratureStrictTAPGap
open LiteratureSubagTAP LiteratureSubagReplicaExclusion LiteratureSubagProposition24
open scoped Topology ENNReal NNReal
open SphericalEffectiveField SphericalFieldKernels SphericalRotationCovariance
open SphericalDynamics SphericalReversibility SphericalOrthogonalHaar SphericalOverlapExponential
open SphericalAging.HardSphereDynamics
open SourceFiniteMixtureAllInitialLiterature SourceInitialQuantitativeInput
open SourceConditionedCPTransferFiniteMixtureLiterature
open CrisantiSommers LiteratureSubagPhysicalDefinitions
open PureCapturePhysicalFullOverlapArray PureCapturePhysicalAsymptoticFullLift
open PureCapturePhysicalCoarseDiniAssembly
open SourceReductionConsumerBandBound WholeFieldRegression
open scoped RealInnerProductSpace
open SourceMixedCountCapturePackage

/-- `thm:main-initial(i)–(iii); cor:cp-information` with the proved literature inputs discharged.
Original endpoint: `SourceMixedCountCapturePackage.finiteMixture_all_initial_spherical_of_literature`. -/
theorem finiteMixture_all_initial_spherical_of_chen_and_bands
    (μ : FiniteMixture)
    {β x Q : ℝ}
    (h : Certificate μ β x Q)
    (hChen : Chen2013FiniteParisi)
    (hBands : SubagBandApproximations μ β) :
    ∃ γ : ℝ, 0 < γ ∧ SphericalInitialConclusions.{u,v} μ β γ := by
  have hChenSen := SourceLiteratureGroundStateExtraction.chenSenFiniteGround hChen
  have h5 : Theorem5 (literatureThermodynamicData hChen hChenSen μ h.beta_pos.le) :=
    theorem5_of_bands _ (h.beta_pos) hBands
  have h25 : Remark25Contrapositive μ β := remark25_of_bands
    (chenThermodynamicData hChen μ (h.beta_pos).le) (h.beta_pos) hBands
  have h24 : Proposition24 μ β Q :=
    LiteratureSubagProposition24Proof.proposition24 _ (h.beta_pos)
      ⟨h.overlap_range.1.le, h.overlap_range.2⟩
  exact SourceMixedCountCapturePackage.finiteMixture_all_initial_spherical_of_literature
    (μ := μ) (β := β) (x := x) (Q := Q) (h := h) (hChen := hChen) (hChenSen := hChenSen) (h5 := h5)
    (h25 := h25) (h24 := h24)

end

section

open Set MeasureTheory ProbabilityTheory Filter
open SphericalModel SphericalTAPCertificate PureStationarity
open PureCapturePhysicalCoarseDiniAssembly SphericalAging.HardSphereDynamics
open SourceConditionedCPTransferPureAllInitial SourceInitialQuantitativeInput
open SourceInitialPolynomialMenu SourceInitialEntropyInformation
open SourceLiteratureParisi SourceLiteratureGroundState SourceLiteratureStrictTAPGap
open SourceLiteraturePhysicalNormQ LiteratureSubagTAP LiteratureSubagReplicaExclusion
open LiteratureSubagProposition24 PureReplicaMeanEnergyAssembly PurePhysicalHighEnergyRelocation
open SphericalOverlapExponential SphericalOrthogonalHaar
open scoped Topology NNReal ENNReal
open SourcePureMainTheoremsLiterature

/-- `cor:main-classes(a), all initial laws` with the proved literature inputs discharged.
Original endpoint: `SourcePureMainTheoremsLiterature.pure_corollary_a_all_initial_of_literature`. -/
theorem pure_corollary_a_all_initial_of_chen_and_bands
    (p : ℕ)
    (hp : 4 ≤ p)
    {β : ℝ}
    (hβ : Thresholds.staticThreshold (fun r : ℝ => r ^ p) < β)
    (hChen : Chen2013FiniteParisi)
    (hBands : SubagBandApproximations (FiniteMixture.pure p (by omega) 1 (by positivity)) β) :
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
  have hβpos : 0 < β := (Classical.choose_spec (pure_certificate_above_static p hp hβ)).choose_spec.beta_pos
  have hChenSen := SourceLiteratureGroundStateExtraction.chenSenFiniteGround hChen
  have h5 : ∀ hβ₀ : 0 ≤ β, Theorem5 (literatureThermodynamicData hChen hChenSen
      (FiniteMixture.pure p (by omega) 1 (by positivity)) hβ₀) :=
    fun _ => theorem5_of_bands _ (hβpos) hBands
  have h25 : Remark25Contrapositive
      (FiniteMixture.pure p (by omega) 1 (by positivity)) β := remark25_of_bands
    (chenThermodynamicData hChen (FiniteMixture.pure p (by omega) 1 (by positivity)) (hβpos).le) (hβpos) hBands
  have h24 : ∀ q : ℝ, q ∈ Ioo (0 : ℝ) 1 →
      Proposition24 (FiniteMixture.pure p (by omega) 1 (by positivity)) β q := fun q hq =>
    LiteratureSubagProposition24Proof.proposition24 _ (hβpos) ⟨hq.1.le, hq.2⟩
  exact SourcePureMainTheoremsLiterature.pure_corollary_a_all_initial_of_literature
    (p := p) (hp := hp) (β := β) (hβ := hβ) (hChen := hChen) (hChenSen := hChenSen) (h5 := h5)
    (h25 := h25) (h24 := h24)

end

section

open Set MeasureTheory ProbabilityTheory Filter CrisantiSommers CSParisiMeasure
open SphericalModel SphericalTAPCertificate SphericalOrthogonalHaar
open SourceLiteratureParisi SourceLiteratureGroundState SourceLiteratureStrictTAPGap
open LiteratureSubagTAP LiteratureSubagReplicaExclusion LiteratureSubagProposition24
open SourceReductionConsumerAsymptotic SphericalOverlapExponential
open SourceFiniteMixtureMainLiteral CSPerturbative
open SphericalAging.HardSphereDynamics
open scoped Topology NNReal
open SourceMainClassesLiterature

/-- `cor:main-classes(b), convexity` with the proved literature inputs discharged.
Original endpoint: `SourceMainClassesLiterature.convex_corollary_b_of_literature`. -/
theorem convex_corollary_b_of_chen_and_bands
    (μ : FiniteMixture)
    (hd : 4 ≤ μ.minDegree)
    {β : ℝ}
    (hβ : Thresholds.staticThreshold μ.xi < β)
    (hξ : StrictConvexOn ℝ (Ioc 0 1)
      (InverseSqrtCalculus.inverseSqrt (deriv (deriv μ.xi))))
    (hChen : Chen2013FiniteParisi)
    (hBands : SubagBandApproximations μ β) :
    MainCondensedAndInitialLiteral μ β := by
  have hChenSen := SourceLiteratureGroundStateExtraction.chenSenFiniteGround hChen
  have h5 : ∀ hβ₀ : 0 ≤ β,
      Theorem5 (literatureThermodynamicData hChen hChenSen μ hβ₀) :=
    fun _ => theorem5_of_bands _ (μ.staticThreshold_pos.trans hβ) hBands
  have h25 : Remark25Contrapositive μ β := remark25_of_bands
    (chenThermodynamicData hChen μ (μ.staticThreshold_pos.trans hβ).le) (μ.staticThreshold_pos.trans hβ) hBands
  have h24 : ∀ q ∈ Ioo (0 : ℝ) 1, Proposition24 μ β q := fun q hq =>
    LiteratureSubagProposition24Proof.proposition24 _ (μ.staticThreshold_pos.trans hβ) ⟨hq.1.le, hq.2⟩
  exact SourceMainClassesLiterature.convex_corollary_b_of_literature
    (μ := μ) (hd := hd) (β := β) (hβ := hβ) (hξ := hξ) (hChen := hChen) (hChenSen := hChenSen)
    (h5 := h5) (h25 := h25) (h24 := h24)

end

section

open Set MeasureTheory ProbabilityTheory Filter CrisantiSommers CSParisiMeasure
open SphericalModel SphericalTAPCertificate SphericalOrthogonalHaar
open SourceLiteratureParisi SourceLiteratureGroundState SourceLiteratureStrictTAPGap
open LiteratureSubagTAP LiteratureSubagReplicaExclusion LiteratureSubagProposition24
open SourceReductionConsumerAsymptotic SphericalOverlapExponential
open SourceFiniteMixtureMainLiteral CSPerturbative
open SphericalAging.HardSphereDynamics
open scoped Topology NNReal
open SourceMainClassesLiterature

/-- `cor:main-classes(b), degree window` with the proved literature inputs discharged.
Original endpoint: `SourceMainClassesLiterature.degree_window_corollary_b_of_literature`. -/
theorem degree_window_corollary_b_of_chen_and_bands
    (μ : FiniteMixture)
    (hd : 4 ≤ μ.minDegree)
    (hwindow : ((μ.minDegree : ℝ) + μ.maxDegree - 5) ^ 2 <
      6 * ((μ.minDegree : ℝ) - 2) * ((μ.maxDegree : ℝ) - 2))
    {β : ℝ}
    (hβ : Thresholds.staticThreshold μ.xi < β)
    (hChen : Chen2013FiniteParisi)
    (hBands : SubagBandApproximations μ β) :
    MainCondensedAndInitialLiteral μ β := by
  have hChenSen := SourceLiteratureGroundStateExtraction.chenSenFiniteGround hChen
  have h5 : ∀ hβ₀ : 0 ≤ β,
      Theorem5 (literatureThermodynamicData hChen hChenSen μ hβ₀) :=
    fun _ => theorem5_of_bands _ (μ.staticThreshold_pos.trans hβ) hBands
  have h25 : Remark25Contrapositive μ β := remark25_of_bands
    (chenThermodynamicData hChen μ (μ.staticThreshold_pos.trans hβ).le) (μ.staticThreshold_pos.trans hβ) hBands
  have h24 : ∀ q ∈ Ioo (0 : ℝ) 1, Proposition24 μ β q := fun q hq =>
    LiteratureSubagProposition24Proof.proposition24 _ (μ.staticThreshold_pos.trans hβ) ⟨hq.1.le, hq.2⟩
  exact SourceMainClassesLiterature.degree_window_corollary_b_of_literature
    (μ := μ) (hd := hd) (hwindow := hwindow) (β := β) (hβ := hβ) (hChen := hChen)
    (hChenSen := hChenSen) (h5 := h5) (h25 := h25) (h24 := h24)

end

section

open Set SphericalModel SourceMainClassesLiterature
open SourceLiteratureParisi SourceLiteratureGroundState SourceLiteratureStrictTAPGap
open LiteratureSubagTAP LiteratureSubagReplicaExclusion LiteratureSubagProposition24
open SourceMainClassesDegreeWindow

/-- `cor:main-classes(b), support 4–11` with the proved literature inputs discharged.
Original endpoint: `SourceMainClassesDegreeWindow.support_four_through_eleven_corollary_b_of_literature`. -/
theorem support_four_through_eleven_corollary_b_of_chen_and_bands
    (μ : FiniteMixture)
    (hsupport : ∀ p ∈ μ.coeff.support, p ∈ Finset.Icc 4 11)
    {β : ℝ}
    (hβ : Thresholds.staticThreshold μ.xi < β)
    (hChen : Chen2013FiniteParisi)
    (hBands : SubagBandApproximations μ β) :
    MainCondensedAndInitialLiteral μ β := by
  have hChenSen := SourceLiteratureGroundStateExtraction.chenSenFiniteGround hChen
  have h5 : ∀ hβ₀ : 0 ≤ β,
      Theorem5 (literatureThermodynamicData hChen hChenSen μ hβ₀) :=
    fun _ => theorem5_of_bands _ (μ.staticThreshold_pos.trans hβ) hBands
  have h25 : Remark25Contrapositive μ β := remark25_of_bands
    (chenThermodynamicData hChen μ (μ.staticThreshold_pos.trans hβ).le) (μ.staticThreshold_pos.trans hβ) hBands
  have h24 : ∀ q ∈ Ioo (0 : ℝ) 1, Proposition24 μ β q := fun q hq =>
    LiteratureSubagProposition24Proof.proposition24 _ (μ.staticThreshold_pos.trans hβ) ⟨hq.1.le, hq.2⟩
  exact SourceMainClassesDegreeWindow.support_four_through_eleven_corollary_b_of_literature
    (μ := μ) (hsupport := hsupport) (β := β) (hβ := hβ) (hChen := hChen) (hChenSen := hChenSen)
    (h5 := h5) (h25 := h25) (h24 := h24)

end

section

open Set MeasureTheory ProbabilityTheory Filter CrisantiSommers CSParisiMeasure
open SphericalModel SphericalTAPCertificate SphericalOrthogonalHaar
open SourceLiteratureParisi SourceLiteratureGroundState SourceLiteratureStrictTAPGap
open LiteratureSubagTAP LiteratureSubagReplicaExclusion LiteratureSubagProposition24
open SourceReductionConsumerAsymptotic SphericalOverlapExponential
open SourceFiniteMixtureMainLiteral CSPerturbative
open SphericalAging.HardSphereDynamics
open scoped Topology NNReal
open SourceMainClassesLiterature

/-- `cor:main-classes(d)` with the proved literature inputs discharged.
Original endpoint: `SourceMainClassesLiterature.nonconvex_corollary_d_of_literature`. -/
theorem nonconvex_corollary_d_of_chen_and_bands
    (hChen : Chen2013FiniteParisi)
    (hBands : SubagBandApproximations NonconvexCertificate.exampleMixture NonconvexCertificate.beta) :
    MainCondensedAndInitialLiteral
      NonconvexCertificate.exampleMixture NonconvexCertificate.beta := by
  have hChenSen := SourceLiteratureGroundStateExtraction.chenSenFiniteGround hChen
  have h5 : ∀ hβ₀ : 0 ≤ NonconvexCertificate.beta,
      Theorem5 (literatureThermodynamicData hChen hChenSen
        NonconvexCertificate.exampleMixture hβ₀) :=
    fun _ => theorem5_of_bands _ (NonconvexCertificate.beta_pos) hBands
  have h25 : Remark25Contrapositive
      NonconvexCertificate.exampleMixture NonconvexCertificate.beta := remark25_of_bands
    (chenThermodynamicData hChen NonconvexCertificate.exampleMixture (NonconvexCertificate.beta_pos).le) (NonconvexCertificate.beta_pos) hBands
  have h24 : ∀ q ∈ Ioo (0 : ℝ) 1,
      Proposition24 NonconvexCertificate.exampleMixture NonconvexCertificate.beta q := fun q hq =>
    LiteratureSubagProposition24Proof.proposition24 _ (NonconvexCertificate.beta_pos) ⟨hq.1.le, hq.2⟩
  exact SourceMainClassesLiterature.nonconvex_corollary_d_of_literature
    (hChen := hChen) (hChenSen := hChenSen) (h5 := h5) (h25 := h25) (h24 := h24)

end

section

open MeasureTheory ProbabilityTheory Set Filter
open SphericalModel SphericalTAPCertificate
open PureCapturePhysicalFullOverlapArray PureCapturePhysicalAsymptoticFullLift
open PureCapturePhysicalReplicaExclusionLimit PureCapturePhysicalReplicaExclusionDirecting
open PureCaptureDirectingFullToScore PureCapturePhysicalFullToScore
open PureCaptureOverlapScoreCoordinates PureCaptureRandomDirectingScoreArray
open PureCapturePhysicalCoarseDiniAssembly DirectingPhysical
open SourceLiteratureParisi SourceLiteratureGroundState SourceLiteratureStrictTAPGap
open LiteratureSubagTAP LiteratureSubagReplicaExclusion
open SourceSphericalSelfAveraging
open scoped Topology BigOperators ENNReal
open PureCapturePhysicalInfiniteArrayTightness
open PureCapturePhysicalInfiniteAsymptoticLift
open SourceDirectingFamilies

variable {Ω H : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]

/-- `thm:dir-norm, literal directing families` with the proved literature inputs discharged.
Original endpoint: `SourceDirectingFamilies.directing_norm`. -/
theorem directing_norm_of_chen_and_bands
    (hChen : Chen2013FiniteParisi)
    {μ : FiniteMixture}
    {β x Q : ℝ}
    (h : Certificate μ β x Q)
    (d : Measure Ω)
    [IsProbabilityMeasure d]
    {L : ProbabilityMeasure InfiniteOverlapCoordinates}
    (hL : L ∈ physicalInfiniteAsymptoticLimitSet μ β)
    (F : DirectingFamily (H := H) d L)
    (hBands : SubagBandApproximations μ β) :
    ∃ Z : Set Ω, MeasurableSet Z ∧ d Z = 0 ∧
      ∀ ω ∉ Z, (F.measure ω : Measure H) {v | ‖v‖ ^ 2 = Q} = 1 := by
  have hChenSen := SourceLiteratureGroundStateExtraction.chenSenFiniteGround hChen
  have h5 : Theorem5 (literatureThermodynamicData hChen hChenSen μ h.beta_pos.le) :=
    theorem5_of_bands _ (h.beta_pos) hBands
  have h25 : Remark25Contrapositive μ β := remark25_of_bands
    (chenThermodynamicData hChen μ (h.beta_pos).le) (h.beta_pos) hBands
  exact SourceDirectingFamilies.directing_norm
    (hChen := hChen) (hChenSen := hChenSen) (μ := μ) (β := β) (x := x) (Q := Q) (h := h) (h5 := h5)
    (h25 := h25) (d := d) (L := L) (hL := hL) (F := F)

end

section

open Set MeasureTheory ProbabilityTheory Filter
open SphericalModel SphericalTAPCertificate SphericalOrthogonalHaar
open SphericalMarkedWindows TwoAtomStationarity
open SourceLiteratureParisi SourceLiteratureGroundState SourceLiteratureStrictTAPGap
open LiteratureSubagTAP LiteratureSubagReplicaExclusion LiteratureSubagProposition24
open SourceReductionConsumerAsymptotic SourceConditionedCPTransferInitialAdapter
open SphericalOverlapExponential SphericalAging.HardSphereDynamics
open SourceConditionedCPTransferFiniteMixtureLiterature
open CrisantiSommers LiteratureSubagPhysicalDefinitions
open PureCapturePhysicalFullOverlapArray PureCapturePhysicalAsymptoticFullLift
open PureCapturePhysicalCoarseDiniAssembly
open SphericalGaussianJet SphericalForm SourceReductionClosedBandGraph
open SourceReductionConsumerBandBound WholeFieldRegression
open scoped RealInnerProductSpace
open scoped Topology NNReal
open SourcePureAmplitudeScaling

/-- `thm:pc-capture, arbitrary amplitude` with the proved literature inputs discharged.
Original endpoint: `SourcePureAmplitudeScaling.pureBranchFixedWindowCapture_of_cited_theorems`. -/
theorem pureBranchFixedWindowCapture_of_chen_and_bands
    (μ : FiniteMixture)
    {β x Q : ℝ}
    (h : Certificate μ β x Q)
    (hChen : Chen2013FiniteParisi)
    (hBands : SubagBandApproximations μ β) :
    PureBranchFixedWindowCapture μ β x Q := by
  have hChenSen := SourceLiteratureGroundStateExtraction.chenSenFiniteGround hChen
  have h5 : Theorem5 (literatureThermodynamicData hChen hChenSen μ h.beta_pos.le) :=
    theorem5_of_bands _ (h.beta_pos) hBands
  have h25 : Remark25Contrapositive μ β := remark25_of_bands
    (chenThermodynamicData hChen μ (h.beta_pos).le) (h.beta_pos) hBands
  have h24 : Proposition24 μ β Q :=
    LiteratureSubagProposition24Proof.proposition24 _ (h.beta_pos)
      ⟨h.overlap_range.1.le, h.overlap_range.2⟩
  exact SourcePureAmplitudeScaling.pureBranchFixedWindowCapture_of_cited_theorems
    (μ := μ) (β := β) (x := x) (Q := Q) (h := h) (hChen := hChen) (hChenSen := hChenSen) (h5 := h5)
    (h25 := h25) (h24 := h24)

end

section

open MeasureTheory ProbabilityTheory Filter Set
open SphericalModel CrisantiSommers CSParisiMeasure
open LiteratureSubagPhysicalDefinitions LiteratureSubagContact
open LiteratureSubagTheorem10Proof
open scoped Topology BigOperators
open LiteratureSubagTheorem10Final

/-- `thm:th-subag(1), whole [0,1)` with the proved literature inputs discharged.
The separate zero-contact lower-tail input remains explicit.
Original endpoint: `LiteratureSubagTheorem10Final.source_subag_tap_reduced2`. -/
theorem source_subag_tap_of_chen_and_bands
    {μ : FiniteMixture}
    {β : ℝ}
    (D : LiteratureSubagTAP.ThermodynamicData μ β)
    (hTail : Thresholds.staticThreshold μ.xi ≤ β →
      ∀ k : ℕ, 2 ≤ k → ∀ ρ : ℝ, 0 < ρ → ∀ ε : ℝ, 0 < ε →
        Tendsto (fun N => blockLowerTailProbability N k μ β 0 ρ ε) atTop (𝓝 0))
    {q : ℝ}
    (hq : q ∈ Ico (0 : ℝ) 1)
    (hβ : 0 < β)
    (hBands : SubagBandApproximations μ β) :
    SourceSubagReplicaCriterion.sourceTAPValue D q ≤ D.pressure ∧
      (D.pressure = SourceSubagReplicaCriterion.sourceTAPValue D q ↔
        MultiSamplable μ β q) := by
  have h5 : LiteratureSubagTAP.Theorem5 D :=
    theorem5_of_bands _ (hβ) hBands
  exact LiteratureSubagTheorem10Final.source_subag_tap_reduced2
    (μ := μ) (β := β) (D := D) (h5 := h5) (hTail := hTail) (q := q) (hq := hq)

end

section

open MeasureTheory ProbabilityTheory Filter Set
open SphericalModel CrisantiSommers CSParisiMeasure
open LiteratureSubagPhysicalDefinitions LiteratureSubagContact
open LiteratureSubagTheorem10Proof
open scoped Topology BigOperators
open LiteratureSubagTheorem10Final

/-- `thm:th-subag(2), whole [0,1)` with the proved literature inputs discharged.
The separate zero-contact lower-tail input remains explicit.
Original endpoint: `LiteratureSubagTheorem10Final.source_replica_criterion_reduced2`. -/
theorem source_replica_criterion_of_chen_and_bands
    (hChen : Chen2013FiniteParisi)
    {μ : FiniteMixture}
    {β q : ℝ}
    (hTail : Thresholds.staticThreshold μ.xi ≤ β →
      ∀ k : ℕ, 2 ≤ k → ∀ ρ : ℝ, 0 < ρ → ∀ ε : ℝ, 0 < ε →
        Tendsto (fun N => blockLowerTailProbability N k μ β 0 ρ ε) atTop (𝓝 0))
    (hq : q ∈ Ico (0 : ℝ) 1)
    (hβ : 0 < β)
    (hBands : SubagBandApproximations μ β) :
    (∀ k : ℕ, 1 ≤ k → ∀ ρ : ℝ, 0 < ρ →
      limsup (fun N : ℕ => SourceSubagReplicaCriterion.replicaLogRate N k μ β q ρ)
        atTop = 0) ↔ MultiSamplable μ β q := by
  have h25 : LiteratureSubagReplicaExclusion.Remark25Contrapositive μ β := remark25_of_bands
    (chenThermodynamicData hChen μ (hβ).le) (hβ) hBands
  exact LiteratureSubagTheorem10Final.source_replica_criterion_reduced2
    (μ := μ) (β := β) (q := q) (h25 := h25) (hTail := hTail) (hq := hq)

end

section

open MeasureTheory Set Filter ProbabilityTheory CrisantiSommers
open CSTAPGroundTrialQuadratic SourceGroundProfileUniqueness
open SourceLiteratureParisi SourceLiteratureGroundState
open SourceLiteratureGroundStateCenterBridge SourceLiteratureGroundStateRadialCoefficients
open LiteratureSubagTAP LiteratureSubagContact LiteratureSubagPhysicalDefinitions
open scoped Topology
open MeasureTheory Set CrisantiSommers
open SourceGeneralContactTheorem

/-- `thm:th-contact(1)` with the proved literature inputs discharged.
The separate Theorem 10 input remains explicit.
Original endpoint: `SourceGeneralContactTheorem.contact_iff_multiSamplable`. -/
theorem contact_iff_multiSamplable_of_chen_and_bands
    (hChen : Chen2013FiniteParisi)
    {μ : FiniteMixture}
    {β : ℝ}
    (D : ThermodynamicData μ β)
    (h10 : Theorem10Forward μ β)
    {q : ℝ}
    (hq : q ∈ Ico (0 : ℝ) 1)
    (hBands : SubagBandApproximations μ β) :
    MultiSamplable μ β q ↔
      CSStructure.potential μ β (CSParisiMeasure.canonicalMinimizer μ β).law q = 0 := by
  have hChenSen := SourceLiteratureGroundStateExtraction.chenSenFiniteGround hChen
  have h5 : LiteratureSubagTAP.Theorem5 D :=
    theorem5_of_bands _ (h10.1) hBands
  exact SourceGeneralContactTheorem.contact_iff_multiSamplable
    (hChen := hChen) (hChenSen := hChenSen) (μ := μ) (β := β) (D := D) (h5 := h5) (h10 := h10)
    (q := q) (hq := hq)

end

section

open MeasureTheory Set Filter ProbabilityTheory CrisantiSommers
open CSTAPGroundTrialQuadratic SourceGroundProfileUniqueness
open SourceLiteratureParisi SourceLiteratureGroundState
open SourceLiteratureGroundStateCenterBridge SourceLiteratureGroundStateRadialCoefficients
open LiteratureSubagTAP LiteratureSubagContact LiteratureSubagPhysicalDefinitions
open scoped Topology
open MeasureTheory Set CrisantiSommers
open SourceGeneralContactTheorem

/-- `thm:th-contact(2), ground profile` with the proved literature inputs discharged.
The separate Theorem 10 input remains explicit.
Original endpoint: `SourceGeneralContactTheorem.contact_ground_profile_unique`. -/
theorem contact_ground_profile_unique_of_chen_and_bands
    (hChen : Chen2013FiniteParisi)
    {μ : FiniteMixture}
    {β q : ℝ}
    (D : ThermodynamicData μ β)
    (h10 : Theorem10Forward μ β)
    (hq : q ∈ Ioo (0 : ℝ) 1)
    (hV : CSStructure.potential μ β (CSParisiMeasure.canonicalMinimizer μ β).law q = 0)
    (hBands : SubagBandApproximations μ β) :
    let u := groundTrial (CSParisiMeasure.canonicalMinimizer μ β) h10.1 hq (le_refl (0 : ℝ))
    (∀ v : RadiusGroundProfile q, radiusFunctional μ u ≤ radiusFunctional μ v) ∧
    D.ground q = radiusFunctional μ u ∧
    (∀ v : RadiusGroundProfile q,
      (∀ w : RadiusGroundProfile q, radiusFunctional μ v ≤ radiusFunctional μ w) →
      ∀ r ∈ Icc (0 : ℝ) q,
        radiusProfile v r = β*xHat (CSParisiMeasure.canonicalMinimizer μ β).law r) := by
  have hChenSen := SourceLiteratureGroundStateExtraction.chenSenFiniteGround hChen
  have h5 : LiteratureSubagTAP.Theorem5 D :=
    theorem5_of_bands _ (h10.1) hBands
  exact SourceGeneralContactTheorem.contact_ground_profile_unique
    (hChen := hChen) (hChenSen := hChenSen) (μ := μ) (β := β) (q := q) (D := D) (h5 := h5)
    (h10 := h10) (hq := hq) (hV := hV)

end

section

open MeasureTheory Set Filter ProbabilityTheory CrisantiSommers
open CSTAPGroundTrialQuadratic SourceGroundProfileUniqueness
open SourceLiteratureParisi SourceLiteratureGroundState
open SourceLiteratureGroundStateCenterBridge SourceLiteratureGroundStateRadialCoefficients
open LiteratureSubagTAP LiteratureSubagContact LiteratureSubagPhysicalDefinitions
open scoped Topology
open MeasureTheory Set CrisantiSommers
open TwoAtomStationarity SphericalTAPCertificate
open SourceGeneralContactTheorem

/-- `prop:th-structure` with the proved literature inputs discharged.
The separate Theorem 10 input remains explicit.
Original endpoint: `SourceGeneralContactTheorem.strict_oneStep_structure`. -/
theorem strict_oneStep_structure_of_chen_and_bands
    (hChen : Chen2013FiniteParisi)
    {μ : FiniteMixture}
    {β x Q : ℝ}
    (h : Certificate μ β x Q)
    (D : ThermodynamicData μ β)
    (h10 : Theorem10Forward μ β)
    (hBands : SubagBandApproximations μ β) :
    StrictOneStepConclusions h D := by
  have hChenSen := SourceLiteratureGroundStateExtraction.chenSenFiniteGround hChen
  have h5 : LiteratureSubagTAP.Theorem5 D :=
    theorem5_of_bands _ (h.beta_pos) hBands
  exact SourceGeneralContactTheorem.strict_oneStep_structure
    (hChen := hChen) (hChenSen := hChenSen) (μ := μ) (β := β) (x := x) (Q := Q) (h := h) (D := D)
    (h5 := h5) (h10 := h10)

end

section

open MeasureTheory Set Filter ProbabilityTheory CrisantiSommers
open CSTAPGroundTrialQuadratic SourceGroundProfileUniqueness
open SourceLiteratureParisi SourceLiteratureGroundState
open SourceLiteratureGroundStateCenterBridge SourceLiteratureGroundStateRadialCoefficients
open LiteratureSubagTAP LiteratureSubagContact LiteratureSubagPhysicalDefinitions
open scoped Topology
open MeasureTheory Set CrisantiSommers
open SourceGeneralContactTheorem

/-- `thm:th-contact(3), quantitative gap` with the proved literature inputs discharged.
Original endpoint: `SourceGeneralContactTheorem.tapValue_le_pressure_sub_gap`. -/
theorem tapValue_le_pressure_sub_gap_of_chen
    (hChen : Chen2013FiniteParisi)
    {μ : FiniteMixture}
    {β q : ℝ}
    (hβ : 0 < β)
    (D : ThermodynamicData μ β)
    (hq : q ∈ Ioo (0 : ℝ) 1)
    (hV : 0 < CSStructure.potential μ β (CSParisiMeasure.canonicalMinimizer μ β).law q) :
    tapValue D q ≤ D.pressure -
      (CSStructure.potential μ β (CSParisiMeasure.canonicalMinimizer μ β).law q)^2 /
        (8*β^3*curvature β (CSParisiMeasure.canonicalMinimizer μ β).law q) := by
  have hChenSen := SourceLiteratureGroundStateExtraction.chenSenFiniteGround hChen
  exact SourceGeneralContactTheorem.tapValue_le_pressure_sub_gap
    (hChen := hChen) (hChenSen := hChenSen) (μ := μ) (β := β) (q := q) (hβ := hβ) (D := D)
    (hq := hq) (hV := hV)

end

section

open MeasureTheory Set Filter ProbabilityTheory CrisantiSommers
open CSTAPGroundTrialQuadratic SourceGroundProfileUniqueness
open SourceLiteratureParisi SourceLiteratureGroundState
open SourceLiteratureGroundStateCenterBridge SourceLiteratureGroundStateRadialCoefficients
open LiteratureSubagTAP LiteratureSubagContact LiteratureSubagPhysicalDefinitions
open scoped Topology
open MeasureTheory Set CrisantiSommers
open SourceGeneralContactTheorem

/-- `thm:th-contact(3), strict gap` with the proved literature inputs discharged.
Original endpoint: `SourceGeneralContactTheorem.strict_tap_gap`. -/
theorem strict_tap_gap_of_chen
    (hChen : Chen2013FiniteParisi)
    {μ : FiniteMixture}
    {β q : ℝ}
    (hβ : 0 < β)
    (D : ThermodynamicData μ β)
    (hq : q ∈ Ioo (0 : ℝ) 1)
    (hV : 0 < CSStructure.potential μ β (CSParisiMeasure.canonicalMinimizer μ β).law q) :
    tapValue D q < D.pressure := by
  have hChenSen := SourceLiteratureGroundStateExtraction.chenSenFiniteGround hChen
  exact SourceGeneralContactTheorem.strict_tap_gap
    (hChen := hChen) (hChenSen := hChenSen) (μ := μ) (β := β) (q := q) (hβ := hβ) (D := D)
    (hq := hq) (hV := hV)

end

section

open MeasureTheory Set Filter ProbabilityTheory CrisantiSommers
open CSTAPGroundTrialQuadratic SourceGroundProfileUniqueness
open SourceLiteratureParisi SourceLiteratureGroundState
open SourceLiteratureGroundStateCenterBridge SourceLiteratureGroundStateRadialCoefficients
open LiteratureSubagTAP LiteratureSubagContact LiteratureSubagPhysicalDefinitions
open scoped Topology
open MeasureTheory Set CrisantiSommers
open TwoAtomStationarity SphericalTAPCertificate
open SourceGeneralContactTheorem

/-- `thm:th-contact(3), compact uniform gap` with the proved literature inputs discharged.
Original endpoint: `SourceGeneralContactTheorem.compact_uniform_tap_gap`. -/
theorem compact_uniform_tap_gap_of_chen
    (hChen : Chen2013FiniteParisi)
    {μ : FiniteMixture}
    {β : ℝ}
    (hβ : 0 < β)
    (D : ThermodynamicData μ β)
    {K : Set ℝ}
    (hK : IsCompact K)
    (hKsub : K ⊆ Ioo (0 : ℝ) 1)
    (hKzero : ∀ q ∈ K,
      CSStructure.potential μ β (CSParisiMeasure.canonicalMinimizer μ β).law q ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ q ∈ K, tapValue D q ≤ D.pressure-δ := by
  have hChenSen := SourceLiteratureGroundStateExtraction.chenSenFiniteGround hChen
  exact SourceGeneralContactTheorem.compact_uniform_tap_gap
    (hChen := hChen) (hChenSen := hChenSen) (μ := μ) (β := β) (hβ := hβ) (D := D) (K := K)
    (hK := hK) (hKsub := hKsub) (hKzero := hKzero)

end

section

open MeasureTheory Set Filter SourceLiteratureGroundState
open SourceLiteratureGroundStateCenterBridge SourceLiteratureGroundStateRadialCoefficients
open SourceLiteratureGroundTrialProfile LiteratureSubagTAP
open scoped Topology
open SourceGroundProfileUniqueness

/-- `thm:th-ground` with the proved literature inputs discharged.
Original endpoint: `SourceGroundProfileUniqueness.source_ground_limit_unique`. -/
theorem source_ground_limit_unique_of_chen
    (hChen : Chen2013FiniteParisi)
    (μ : FiniteMixture)
    {q : ℝ}
    (hq : 0 < q) :
    ∃ u : RadiusGroundProfile q,
      (∀ v : RadiusGroundProfile q, radiusFunctional μ u ≤ radiusFunctional μ v) ∧
      Tendsto (fun N : ℕ => expectedCenterGroundEnergy N μ q) atTop
        (𝓝 (radiusFunctional μ u)) ∧
      (∀ v : RadiusGroundProfile q,
        (∀ w : RadiusGroundProfile q, radiusFunctional μ v ≤ radiusFunctional μ w) →
        ∀ r ∈ Icc (0 : ℝ) q, radiusProfile v r = radiusProfile u r) := by
  have hChenSen := SourceLiteratureGroundStateExtraction.chenSenFiniteGround hChen
  exact SourceGroundProfileUniqueness.source_ground_limit_unique
    (hChenSen := hChenSen) (μ := μ) (q := q) (hq := hq)

end

section

open Filter MeasureTheory ProbabilityTheory Set SphericalModel
open SphericalParisiFiniteMixtureGroundBridge
open SphericalParisiGroundRSUpper
open SphericalParisiContinuousMaximum SphericalCriticalLatitude
open FiniteTensorMixtureMaximum PureTensorJetBounds
open scoped Topology
open SourceLiteratureGroundState

/-- `thm:th-ground, canonical field` with the proved literature inputs discharged.
Original endpoint: `SourceLiteratureGroundState.canonical_ground_limit`. -/
theorem canonical_ground_limit_of_chen
    (hChen : Chen2013FiniteParisi)
    (μ : FiniteMixture) :
    ∃ u : GroundProfile,
      (∀ v : GroundProfile, groundFunctional μ u ≤ groundFunctional μ v) ∧
      Tendsto (canonicalGroundEnergy μ) atTop (𝓝 (groundFunctional μ u)) := by
  have hChenSen := SourceLiteratureGroundStateExtraction.chenSenFiniteGround hChen
  exact SourceLiteratureGroundState.canonical_ground_limit
    (hChenSen := hChenSen) (μ := μ)

end

section

open Filter MeasureTheory ProbabilityTheory Set SphericalModel
open SphericalParisiFiniteMixtureGroundBridge
open SphericalParisiGroundRSUpper
open SphericalParisiContinuousMaximum SphericalCriticalLatitude
open FiniteTensorMixtureMaximum PureTensorJetBounds
open scoped Topology
open SourceLiteratureGroundState

/-- `thm:th-ground, residual field` with the proved literature inputs discharged.
Original endpoint: `SourceLiteratureGroundState.physical_residual_ground_limit`. -/
theorem physical_residual_ground_limit_of_chen
    (hChen : Chen2013FiniteParisi)
    (μ : FiniteMixture) :
    ∃ u : GroundProfile,
      (∀ v : GroundProfile, groundFunctional μ u ≤ groundFunctional μ v) ∧
      Tendsto (physicalResidualGroundEnergy μ) atTop
        (𝓝 (groundFunctional μ u)) := by
  have hChenSen := SourceLiteratureGroundStateExtraction.chenSenFiniteGround hChen
  exact SourceLiteratureGroundState.physical_residual_ground_limit
    (hChenSen := hChenSen) (μ := μ)

end

section

open MeasureTheory ProbabilityTheory Set Filter
open SphericalModel SphericalGaussianJet SphericalCriticalLatitude
open SphericalTaylorRemainder SphericalTwoPointCovariance GaussianContinuousFieldLaw
open SphericalParisiContinuousMaximum SphericalParisiFiniteMixtureGroundBridge
open SourceLiteratureGroundState SourceLiteratureGroundStateRadialCoefficients
open LiteratureSubagTAP PureTensorJetBounds
open scoped Topology RealInnerProductSpace
open SourceLiteratureGroundStateCenterBridge

/-- `thm:th-ground, center field` with the proved literature inputs discharged.
Original endpoint: `SourceLiteratureGroundStateCenterBridge.center_ground_limit`. -/
theorem center_ground_limit_of_chen
    (hChen : Chen2013FiniteParisi)
    (μ : FiniteMixture)
    {q : ℝ}
    (hq : 0 < q) :
    ∃ u : GroundProfile,
      (∀ v : GroundProfile, groundFunctional (centerMixture μ q hq) u ≤
        groundFunctional (centerMixture μ q hq) v) ∧
      Tendsto (fun N : ℕ => expectedCenterGroundEnergy N μ q) atTop
        (𝓝 (groundFunctional (centerMixture μ q hq) u)) := by
  have hChenSen := SourceLiteratureGroundStateExtraction.chenSenFiniteGround hChen
  exact SourceLiteratureGroundStateCenterBridge.center_ground_limit
    (hChenSen := hChenSen) (μ := μ) (q := q) (hq := hq)

end

section

open Set Filter MeasureTheory SphericalModel SphericalMarkedWindows
open SphericalTAPCertificate PureStationarity TwoAtomStationarity
open SourceLiteratureParisi SourceLiteratureGroundState SourceLiteratureStrictTAPGap
open LiteratureSubagTAP LiteratureSubagReplicaExclusion LiteratureSubagProposition24
open SourceLiteraturePhysicalNormQ PureReplicaMeanEnergyAssembly
open PurePhysicalHighEnergyRelocation PureCapturePhysicalCoarseDiniAssembly
open PureCapturePhysicalDiagonalBridge SourcePureCaptureLiteralConsumer
open SourcePureCaptureWindowTransport SourcePureCaptureFixedCapEstimates
open SphericalPureCapCenteringIdentity SphericalPureCapSourceScalars
open scoped Topology
open SourcePureSection9Literature

/-- `thm:pc-capture` with the proved literature inputs discharged.
Original endpoint: `SourcePureSection9Literature.pure_capture_of_cited_theorems`. -/
theorem pure_capture_of_chen_and_bands
    (hChen : Chen2013FiniteParisi)
    (p : ℕ)
    (hp : 4 ≤ p)
    {β x Q : ℝ}
    (h : Certificate (FiniteMixture.pure p (by omega) 1 (by positivity)) β x Q)
    (U : Set ℝ)
    (hU : markK (FiniteMixture.pure p (by omega) 1 (by positivity)) β Q ∈ interior U)
    (hUpper : ExpectedBandUpperApproximation
      (chenThermodynamicData hChen (FiniteMixture.pure p (by omega) 1 (by positivity)) h.beta_pos.le)) :
    (∃ b₀ : ℝ, b₀ ∈ Ioo (0 : ℝ) (Real.sqrt Q) ∧
      ∀ b : ℝ, b ∈ Ioc (0 : ℝ) b₀ → Tendsto
        (fun M : ℝ => Filter.limsup (pureConsumerUncovered p hp β Q M b U) atTop)
        atTop (𝓝 (0 : ℝ))) ∧
    (∀ ε : ℝ, 0 < ε → ∃ M₀ w₀ : ℝ, 0 < M₀ ∧ 0 < w₀ ∧
      ∀ M w : ℝ, M₀ ≤ M → w₀ ≤ w →
        Filter.limsup (fun n => pureConsumerUncovered p hp β Q M
          (w / Real.sqrt (n+2 : ℕ)) U n) atTop ≤ ε) := by
  exact pure_consumer_capture_of_three_physical_inputs p hp h U hU
    (LiteratureSubagBandUpperExtraction.Endpoints.physicalDirectingNormQ_of_literature_reduced3 hChen h hUpper)
    (pure_physicalReplicaMeanEnergy_of_literature p hp h hChen
      (LiteratureSubagProposition24Proof.proposition24 _ h.beta_pos
        ⟨h.overlap_range.1.le, h.overlap_range.2⟩))
    (pure_physicalHighEnergyRelocation p hp)

end

section

open Set Filter MeasureTheory SphericalModel SphericalMarkedWindows
open SphericalTAPCertificate PureStationarity TwoAtomStationarity
open SourceLiteratureParisi SourceLiteratureGroundState SourceLiteratureStrictTAPGap
open LiteratureSubagTAP LiteratureSubagReplicaExclusion LiteratureSubagProposition24
open SourceLiteraturePhysicalNormQ PureReplicaMeanEnergyAssembly
open PurePhysicalHighEnergyRelocation PureCapturePhysicalCoarseDiniAssembly
open PureCapturePhysicalDiagonalBridge SourcePureCaptureLiteralConsumer
open SourcePureCaptureWindowTransport SourcePureCaptureFixedCapEstimates
open SphericalPureCapCenteringIdentity SphericalPureCapSourceScalars
open scoped Topology
open SourcePureSection9Literature

/-- `prop:pc-coarse` with the proved literature inputs discharged.
Original endpoint: `SourcePureSection9Literature.pure_coarse_cover_of_cited_theorems`. -/
theorem pure_coarse_cover_of_chen_and_bands
    (hChen : Chen2013FiniteParisi)
    (p : ℕ)
    (hp : 4 ≤ p)
    {β x Q : ℝ}
    (h : Certificate (FiniteMixture.pure p (by omega) 1 (by positivity)) β x Q)
    (hUpper : ExpectedBandUpperApproximation
      (chenThermodynamicData hChen (FiniteMixture.pure p (by omega) 1 (by positivity)) h.beta_pos.le)) :
    ∀ a : ℝ, a < Real.sqrt Q → ∀ τ : ℝ, 0 < τ →
      Tendsto (fun n => expectedUncoveredGibbsMass n
        (FiniteMixture.pure p (by omega) 1 (by positivity)) β a
        (pureEnergyConstant p (by omega)) τ) atTop (𝓝 (0 : ℝ)) := by
  intro a ha
  exact physical_coarse_cover_of_three_physical_inputs _ β h.overlap_range ha
    (LiteratureSubagBandUpperExtraction.Endpoints.physicalDirectingNormQ_of_literature_reduced3 hChen h hUpper)
    (pure_physicalReplicaMeanEnergy_of_literature p hp h hChen
      (LiteratureSubagProposition24Proof.proposition24 _ h.beta_pos
        ⟨h.overlap_range.1.le, h.overlap_range.2⟩))
    (pure_physicalHighEnergyRelocation p hp)

end

section

open Set Filter MeasureTheory SphericalModel SphericalMarkedWindows
open SphericalTAPCertificate PureStationarity TwoAtomStationarity
open SourceLiteratureParisi SourceLiteratureGroundState SourceLiteratureStrictTAPGap
open LiteratureSubagTAP LiteratureSubagReplicaExclusion LiteratureSubagProposition24
open SourceLiteraturePhysicalNormQ PureReplicaMeanEnergyAssembly
open PurePhysicalHighEnergyRelocation PureCapturePhysicalCoarseDiniAssembly
open PureCapturePhysicalDiagonalBridge SourcePureCaptureLiteralConsumer
open SourcePureCaptureWindowTransport SourcePureCaptureFixedCapEstimates
open SphericalPureCapCenteringIdentity SphericalPureCapSourceScalars
open scoped Topology
open SourcePureSection9Literature

/-- `lem:pc-diagonal` with the proved literature inputs discharged.
Original endpoint: `SourcePureSection9Literature.pure_diagonal_localization_of_cited_theorems`. -/
theorem pure_diagonal_localization_of_chen_and_bands
    (hChen : Chen2013FiniteParisi)
    (p : ℕ)
    (hp : 4 ≤ p)
    {β x Q : ℝ}
    (h : Certificate (FiniteMixture.pure p (by omega) 1 (by positivity)) β x Q)
    (a : ℝ)
    (ha : a < Real.sqrt Q)
    (hUpper : ExpectedBandUpperApproximation
      (chenThermodynamicData hChen (FiniteMixture.pure p (by omega) 1 (by positivity)) h.beta_pos.le)) :
    let μ := FiniteMixture.pure p (by omega : 2 ≤ p) 1 (by positivity)
    let e := pureEnergyConstant p (by omega : 3 ≤ p)
    let c := pureIntensityConstant p (by omega : 3 ≤ p)
    ∃ τ : ℕ → ℝ,
      (∀ n, 0 < τ n) ∧
      (∀ n, 1 ≤ ((n+2 : ℕ)*τ n)/(Real.log (n+2 : ℕ))^2) ∧
      Tendsto τ atTop (𝓝 0) ∧
      Tendsto (fun n => expectedUncoveredGibbsMass n μ β a e (τ n)) atTop (𝓝 0) ∧
      (∀ᶠ n : ℕ in atTop, 0 < (n+2 : ℕ)*τ n-Real.log (n+2 : ℕ)/(2*c)) ∧
      Tendsto (fun n => ((n+2 : ℕ)*τ n-Real.log (n+2 : ℕ)/(2*c))/(n+2 : ℕ))
        atTop (𝓝 (0 : ℝ)) ∧
      ∃ Ω : (n : ℕ) → Set (Disorder (n+2) μ.maxDegree),
        (∀ n, MeasurableSet (Ω n)) ∧
        Tendsto (fun n => (disorderLaw (n+2) μ.maxDegree).real (Ω n))
          atTop (𝓝 (1 : ℝ)) ∧
        ∀ n J, J ∈ Ω n → ∀ u : Vector (n+2), ‖u‖^2 = (n+2 : ℕ) →
          (n+2 : ℕ)*(e-τ n) ≤ field (mixtureCoefficients μ) J u →
          field (mixtureCoefficients μ) J u ∈ Icc
            (PureCaptureDiagonal.center e c n-
              ((n+2 : ℕ)*τ n-Real.log (n+2 : ℕ)/(2*c)))
            (PureCaptureDiagonal.center e c n+Real.sqrt (n+2 : ℕ)) := by
  dsimp only
  apply physical_diagonal_window_of_coarse_cover_and_upper_tightness
  · exact SphericalPureCapCenteringIdentity.pureIntensityConstant_pos p (by omega)
  · exact pure_coarse_cover_of_chen_and_bands hChen p hp h hUpper a ha
  · exact pure_original_source_maximum_upper_tightness p hp h

end

section

open Set Filter MeasureTheory ProbabilityTheory
open SphericalModel SphericalForm SphericalGaussianJet SphericalMarkedWindows
open SphericalTAPCertificate TwoAtomStationarity PairConditionalDeterminantMoments
open SphericalTAPCriticalBandSectionBridge SphericalTAPMixedLowSumMarkedKR
open SourceMixedLowSumBorelIndicator SourceMixedCriticalCenteredWindowCount
open SphericalTAPCriticalHeavyBandProbability SourceReductionConsumerAsymptoticCounts
open SourceReductionConsumerAsymptotic SourceReductionClosedBandGraph
open SourceReductionFiniteWindowCapture MixedHighEnergyRelocation
open MixedReplicaMeanEnergyAssembly
open SourceLiteratureParisi SourceLiteratureGroundState SourceLiteratureStrictTAPGap
open LiteratureSubagTAP LiteratureSubagReplicaExclusion LiteratureSubagProposition24
open scoped Topology ENNReal
open SourceMixedCaptureCommonWitness

/-- `thm:mb-capture` with the proved literature inputs discharged.
Original endpoint: `SourceMixedCaptureCommonWitness.mixed_original_fixed_window_capture_of_literature`. -/
theorem mixed_original_fixed_window_capture_of_chen_and_bands
    (μ : FiniteMixture)
    {β x Q : ℝ}
    (h : Certificate μ β x Q)
    (hnp : μ.minDegree < μ.maxDegree)
    (hChen : Chen2013FiniteParisi)
    (hBands : SubagBandApproximations μ β) :
    ∃ L R b₀ : ℝ,
      2 * Real.sqrt (Q^2 * μ.xi2 Q) < L ∧
      L < markK μ β Q ∧ markK μ β Q < R ∧
      0 < b₀ ∧ b₀ < Real.sqrt Q ∧
      ∃ m : ℕ → ℝ,
        Tendsto (fun n => m n / ((n+2 : ℕ) : ℝ))
          atTop (𝓝 (markE μ β x Q)) ∧
        (∀ M : ℝ, 0 < M →
          limsup (originalWindowExpectedCount μ Q m M (Icc L R))
            atTop < ⊤) ∧
        ∀ b : ℝ, 0 < b → b ≤ b₀ →
          Tendsto (fun M : ℝ => limsup (fun n =>
            ∫ J, originalBandComplementMass μ Q (m n) M b β
              (Icc L R) J ∂disorderLaw (n+2) μ.maxDegree) atTop)
            atTop (𝓝 0) := by
  have hChenSen := SourceLiteratureGroundStateExtraction.chenSenFiniteGround hChen
  have h5 : Theorem5
      (literatureThermodynamicData hChen hChenSen μ h.beta_pos.le) :=
    theorem5_of_bands _ (h.beta_pos) hBands
  have h25 : Remark25Contrapositive μ β := remark25_of_bands
    (chenThermodynamicData hChen μ (h.beta_pos).le) (h.beta_pos) hBands
  have h24 : Proposition24 μ β Q :=
    LiteratureSubagProposition24Proof.proposition24 _ (h.beta_pos)
      ⟨h.overlap_range.1.le, h.overlap_range.2⟩
  exact SourceMixedCaptureCommonWitness.mixed_original_fixed_window_capture_of_literature
    (μ := μ) (β := β) (x := x) (Q := Q) (h := h) (hnp := hnp) (hChen := hChen)
    (hChenSen := hChenSen) (h5 := h5) (h25 := h25) (h24 := h24)

end

section

open Set Filter MeasureTheory ProbabilityTheory
open SphericalModel SphericalForm SphericalGaussianJet SphericalMarkedWindows
open SphericalTAPCertificate TwoAtomStationarity PairConditionalDeterminantMoments
open SphericalTAPCriticalBandSectionBridge SphericalTAPMixedLowSumMarkedKR
open SourceMixedLowSumBorelIndicator SourceMixedCriticalCenteredWindowCount
open SphericalTAPCriticalHeavyBandProbability SourceReductionConsumerAsymptoticCounts
open SourceReductionConsumerAsymptotic SourceReductionClosedBandGraph
open SourceReductionFiniteWindowCapture MixedHighEnergyRelocation
open MixedReplicaMeanEnergyAssembly LatitudeGroundTrial SphericalPairChartKacRice
open SourceLiteratureParisi SourceLiteratureGroundState SourceLiteratureStrictTAPGap
open LiteratureSubagTAP LiteratureSubagReplicaExclusion LiteratureSubagProposition24
open scoped Topology ENNReal NNReal
open SourceMixedCountCapturePackage

/-- `thm:mc-counts; lem:mb-counts; thm:mb-capture, mixed` with the proved literature inputs discharged.
Original endpoint: `SourceMixedCountCapturePackage.mixed_count_capture_package_of_literature`. -/
theorem mixed_count_capture_package_of_chen_and_bands
    (μ : FiniteMixture)
    {β x Q : ℝ}
    (h : Certificate μ β x Q)
    (hnp : μ.minDegree < μ.maxDegree)
    (hChen : Chen2013FiniteParisi)
    (hBands : SubagBandApproximations μ β) :
    ∃ C cut η ε L R b₀ : ℝ,
      0 < C ∧ 0 < cut ∧ cut ≤ 1 ∧
      cut ≤ pairRadius μ h.overlap_range.1 h.min_degree ∧
      0 < η ∧ η ≤ sourceCriticalCollarOverlapLoss
        ((markK μ β Q-2*Real.sqrt (Q^2*μ.xi2 Q))/2/2) C ∧
      0 < ε ∧ ε < cut^2/2 ∧ ε < 1-η ∧
      sourceRadialEdge μ Q < L ∧ L < markK μ β Q ∧ markK μ β Q < R ∧
      0 < b₀ ∧ b₀ < Real.sqrt Q ∧
      ∃ d : SourceMaximumFirstMomentConclusions μ β x Q L R,
        CountCapturePackage μ β x Q L R b₀ d.center ∧
        ∀ t : ℝ, 0 < t → MixedSharpAtWindow μ β x Q C cut η ε L R d.center t := by
  have hChenSen := SourceLiteratureGroundStateExtraction.chenSenFiniteGround hChen
  have h5 : Theorem5 (literatureThermodynamicData hChen hChenSen μ h.beta_pos.le) :=
    theorem5_of_bands _ (h.beta_pos) hBands
  have h25 : Remark25Contrapositive μ β := remark25_of_bands
    (chenThermodynamicData hChen μ (h.beta_pos).le) (h.beta_pos) hBands
  have h24 : Proposition24 μ β Q :=
    LiteratureSubagProposition24Proof.proposition24 _ (h.beta_pos)
      ⟨h.overlap_range.1.le, h.overlap_range.2⟩
  exact SourceMixedCountCapturePackage.mixed_count_capture_package_of_literature
    (μ := μ) (β := β) (x := x) (Q := Q) (h := h) (hnp := hnp) (hChen := hChen)
    (hChenSen := hChenSen) (h5 := h5) (h25 := h25) (h24 := h24)

end

section

open Set Filter MeasureTheory ProbabilityTheory
open SphericalModel SphericalForm SphericalGaussianJet SphericalMarkedWindows
open SphericalTAPCertificate TwoAtomStationarity PairConditionalDeterminantMoments
open SphericalTAPCriticalBandSectionBridge SphericalTAPMixedLowSumMarkedKR
open SourceMixedLowSumBorelIndicator SourceMixedCriticalCenteredWindowCount
open SphericalTAPCriticalHeavyBandProbability SourceReductionConsumerAsymptoticCounts
open SourceReductionConsumerAsymptotic SourceReductionClosedBandGraph
open SourceReductionFiniteWindowCapture MixedHighEnergyRelocation
open MixedReplicaMeanEnergyAssembly LatitudeGroundTrial SphericalPairChartKacRice
open SourceLiteratureParisi SourceLiteratureGroundState SourceLiteratureStrictTAPGap
open LiteratureSubagTAP LiteratureSubagReplicaExclusion LiteratureSubagProposition24
open scoped Topology ENNReal NNReal
open SphericalEffectiveField SphericalFieldKernels SphericalRotationCovariance
open SphericalDynamics SphericalReversibility SphericalOrthogonalHaar SphericalOverlapExponential
open SphericalAging.HardSphereDynamics
open SourceFiniteMixtureAllInitialLiterature SourceInitialQuantitativeInput
open SourceConditionedCPTransferFiniteMixtureLiterature
open CrisantiSommers LiteratureSubagPhysicalDefinitions
open PureCapturePhysicalFullOverlapArray PureCapturePhysicalAsymptoticFullLift
open PureCapturePhysicalCoarseDiniAssembly
open SourceReductionConsumerBandBound WholeFieldRegression
open scoped RealInnerProductSpace
open SourceMixedCountCapturePackage

/-- `thm:mc-counts; lem:mb-counts; thm:mb-capture, pure` with the proved literature inputs discharged.
Original endpoint: `SourceMixedCountCapturePackage.pure_normalized_count_capture_package_of_literature`. -/
theorem pure_normalized_count_capture_package_of_chen_and_bands
    (p : ℕ)
    (hp : 2 ≤ p)
    (a : ℝ)
    (ha : 0 < a)
    {β x Q : ℝ}
    (h : Certificate (FiniteMixture.pure p hp a ha) β x Q)
    (hChen : Chen2013FiniteParisi)
    (hBands : SubagBandApproximations (FiniteMixture.pure p hp a ha) β) :
    let μ := FiniteMixture.pure p hp a ha
    ∃ L R b₀ C cut η ε δ : ℝ, ∃ m : ℕ → ℝ,
      sourceRadialEdge μ Q < L ∧ L < markK μ β Q ∧ markK μ β Q < R ∧
      0 < b₀ ∧ b₀ < Real.sqrt Q ∧ 0 < δ ∧
      0 < cut ∧ cut ≤ 1 ∧ 0 < ε ∧ ε < cut^2/2 ∧ ε < 1-η ∧
      CountCapturePackage μ β x Q L R b₀ m ∧
      (∀ᶠ n : ℕ in atTop, ExpectedTailCentering.tail
        (pureTruncatedLocalMaxDensity n p hp a ha Q
          ((n+2 : ℕ)*(markE μ β x Q-δ)) ((n+2 : ℕ)*(markE μ β x Q+δ))) (m n) = 1) ∧
      ∀ t : ℝ, 0 < t → PureSharpAtWindow μ β x Q C cut η ε δ m t ∧
        PureWindowIdentification μ β x Q C η ε δ L R m t := by
  have hChenSen := SourceLiteratureGroundStateExtraction.chenSenFiniteGround hChen
  have h5 : Theorem5 (literatureThermodynamicData hChen hChenSen
      (FiniteMixture.pure p hp a ha) h.beta_pos.le) :=
    theorem5_of_bands _ (h.beta_pos) hBands
  have h25 : Remark25Contrapositive (FiniteMixture.pure p hp a ha) β := remark25_of_bands
    (chenThermodynamicData hChen (FiniteMixture.pure p hp a ha) (h.beta_pos).le) (h.beta_pos) hBands
  have h24 : Proposition24 (FiniteMixture.pure p hp a ha) β Q :=
    LiteratureSubagProposition24Proof.proposition24 _ (h.beta_pos)
      ⟨h.overlap_range.1.le, h.overlap_range.2⟩
  exact SourceMixedCountCapturePackage.pure_normalized_count_capture_package_of_literature
    (p := p) (hp := hp) (a := a) (ha := ha) (β := β) (x := x) (Q := Q) (h := h) (hChen := hChen)
    (hChenSen := hChenSen) (h5 := h5) (h25 := h25) (h24 := h24)

end

section

open Set Filter MeasureTheory ProbabilityTheory
open SphericalModel SphericalForm SphericalGaussianJet SphericalMarkedWindows
open SphericalTAPCertificate TwoAtomStationarity PairConditionalDeterminantMoments
open SphericalTAPCriticalBandSectionBridge SphericalTAPMixedLowSumMarkedKR
open SourceMixedLowSumBorelIndicator SourceMixedCriticalCenteredWindowCount
open SphericalTAPCriticalHeavyBandProbability SourceReductionConsumerAsymptoticCounts
open SourceReductionConsumerAsymptotic SourceReductionClosedBandGraph
open SourceReductionFiniteWindowCapture MixedHighEnergyRelocation
open MixedReplicaMeanEnergyAssembly LatitudeGroundTrial SphericalPairChartKacRice
open SourceLiteratureParisi SourceLiteratureGroundState SourceLiteratureStrictTAPGap
open LiteratureSubagTAP LiteratureSubagReplicaExclusion LiteratureSubagProposition24
open scoped Topology ENNReal NNReal
open SphericalEffectiveField SphericalFieldKernels SphericalRotationCovariance
open SphericalDynamics SphericalReversibility SphericalOrthogonalHaar SphericalOverlapExponential
open SphericalAging.HardSphereDynamics
open SourceFiniteMixtureAllInitialLiterature SourceInitialQuantitativeInput
open SourceConditionedCPTransferFiniteMixtureLiterature
open CrisantiSommers LiteratureSubagPhysicalDefinitions
open PureCapturePhysicalFullOverlapArray PureCapturePhysicalAsymptoticFullLift
open PureCapturePhysicalCoarseDiniAssembly
open SourceReductionConsumerBandBound WholeFieldRegression
open scoped RealInnerProductSpace
open SourceMixedCountCapturePackage

/-- `thm:mb-capture, all finite mixtures` with the proved literature inputs discharged.
Original endpoint: `SourceMixedCountCapturePackage.finiteMixture_count_capture_package_of_literature`. -/
theorem finiteMixture_count_capture_package_of_chen_and_bands
    (μ : FiniteMixture)
    {β x Q : ℝ}
    (h : Certificate μ β x Q)
    (hChen : Chen2013FiniteParisi)
    (hBands : SubagBandApproximations μ β) :
    ∃ L R b₀ : ℝ, sourceRadialEdge μ Q < L ∧ L < markK μ β Q ∧
      markK μ β Q < R ∧ 0 < b₀ ∧ b₀ < Real.sqrt Q ∧
      ∃ m : ℕ → ℝ, CountCapturePackage μ β x Q L R b₀ m := by
  have hChenSen := SourceLiteratureGroundStateExtraction.chenSenFiniteGround hChen
  have h5 : Theorem5 (literatureThermodynamicData hChen hChenSen μ h.beta_pos.le) :=
    theorem5_of_bands _ (h.beta_pos) hBands
  have h25 : Remark25Contrapositive μ β := remark25_of_bands
    (chenThermodynamicData hChen μ (h.beta_pos).le) (h.beta_pos) hBands
  have h24 : Proposition24 μ β Q :=
    LiteratureSubagProposition24Proof.proposition24 _ (h.beta_pos)
      ⟨h.overlap_range.1.le, h.overlap_range.2⟩
  exact SourceMixedCountCapturePackage.finiteMixture_count_capture_package_of_literature
    (μ := μ) (β := β) (x := x) (Q := Q) (h := h) (hChen := hChen) (hChenSen := hChenSen) (h5 := h5)
    (h25 := h25) (h24 := h24)

end

section

open Set Filter MeasureTheory ProbabilityTheory SphericalModel SphericalTAPCertificate
open SourceLiteratureParisi LiteratureSubagProposition24
open PureCapturePhysicalCoarseTransfer MixedCapturePhysicalReplicaGeometry
open LiteratureSubagPhysicalDefinitions SphericalGaussianJet TwoAtomStationarity
open ReplicaMeanNetCover ReplicaBandGibbsMass ReplicaBandExpectedUpper
open SphericalAging.HardSphereDynamics
open scoped Topology BigOperators
open MixedReplicaMeanEnergyAssembly

/-- `lem:mb-replica, exponential` with the proved literature inputs discharged.
Original endpoint: `MixedReplicaMeanEnergyAssembly.mixed_contactReplicaMeanEnergy_exponential_of_literature`. -/
theorem mixed_contactReplicaMeanEnergy_exponential_of_chen
    (μ : FiniteMixture)
    {β x Q : ℝ}
    (h : Certificate μ β x Q)
    (hChen : Chen2013FiniteParisi) :
    ∀ ε : ℝ, 0 < ε → ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
      ∃ ηₖ cₖ : ℝ, 0 < ηₖ ∧ 0 < cₖ ∧
        ∀ η : ℝ, 0 < η → η ≤ ηₖ → ∀ᶠ n : ℕ in atTop,
          expectedContactReplicaMeanLowEnergy (k := k) n μ β Q η (markE μ β x Q) ε ≤
            Real.exp (-cₖ * (n + 2 : ℕ)) := by
  have h24 : Proposition24 μ β Q :=
    LiteratureSubagProposition24Proof.proposition24 _ (h.beta_pos)
      ⟨h.overlap_range.1.le, h.overlap_range.2⟩
  exact MixedReplicaMeanEnergyAssembly.mixed_contactReplicaMeanEnergy_exponential_of_literature
    (μ := μ) (β := β) (x := x) (Q := Q) (h := h) (hChen := hChen) (h24 := h24)

end

section

open Set Filter MeasureTheory ProbabilityTheory SphericalModel SphericalTAPCertificate
open SourceLiteratureParisi LiteratureSubagProposition24
open PureCapturePhysicalCoarseTransfer MixedCapturePhysicalReplicaGeometry
open LiteratureSubagPhysicalDefinitions SphericalGaussianJet TwoAtomStationarity
open ReplicaMeanNetCover ReplicaBandGibbsMass ReplicaBandExpectedUpper
open SphericalAging.HardSphereDynamics
open scoped Topology BigOperators
open MixedReplicaMeanEnergyAssembly

/-- `lem:mb-replica, physical input` with the proved literature inputs discharged.
Original endpoint: `MixedReplicaMeanEnergyAssembly.mixed_contactReplicaMeanEnergy_of_literature`. -/
theorem mixed_contactReplicaMeanEnergy_of_chen
    (μ : FiniteMixture)
    {β x Q : ℝ}
    (h : Certificate μ β x Q)
    (hChen : Chen2013FiniteParisi) :
    PhysicalContactReplicaMeanEnergy μ β Q (markE μ β x Q) := by
  have h24 : Proposition24 μ β Q :=
    LiteratureSubagProposition24Proof.proposition24 _ (h.beta_pos)
      ⟨h.overlap_range.1.le, h.overlap_range.2⟩
  exact MixedReplicaMeanEnergyAssembly.mixed_contactReplicaMeanEnergy_of_literature
    (μ := μ) (β := β) (x := x) (Q := Q) (h := h) (hChen := hChen) (h24 := h24)

end

section

open Set Filter MeasureTheory ProbabilityTheory SphericalModel SphericalTAPCertificate
open SourceLiteratureParisi LiteratureSubagProposition24
open PureCapturePhysicalCoarseTransfer MixedCapturePhysicalReplicaGeometry
open LiteratureSubagPhysicalDefinitions SphericalGaussianJet TwoAtomStationarity
open ReplicaMeanNetCover ReplicaBandGibbsMass ReplicaBandExpectedUpper
open MixedReplicaMeanEnergyAssembly SphericalBarycenter MixedCaptureReplicaGeometry
open PureStationarity
open SphericalAging.HardSphereDynamics
open scoped Topology BigOperators
open PureReplicaMeansExponential

/-- `prop:pc-replica-means, exponential` with the proved literature inputs discharged.
Original endpoint: `PureReplicaMeansExponential.pure_replica_means_exponential_of_literature`. -/
theorem pure_replica_means_exponential_of_chen
    (p : ℕ)
    (hp : 4 ≤ p)
    {β x Q : ℝ}
    (h : Certificate (FiniteMixture.pure p (by omega) 1 (by positivity)) β x Q)
    (hChen : Chen2013FiniteParisi) :
    let μ := FiniteMixture.pure p (by omega : 2 ≤ p) 1 (by positivity)
    let E₀ := pureEnergyConstant p (by omega) * (Real.sqrt Q) ^ p
    ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∃ η c : ℝ,
      1 ≤ n₀ ∧ 0 < η ∧ η < Q / 2 ∧ 0 < c ∧
      ∀ n : ℕ, n₀ ≤ n → ∀ᶠ N : ℕ in atTop,
        (∫ J : Disorder N μ.maxDegree,
          (Measure.pi (fun _ : Fin n =>
            gibbsLaw N β (field (mixtureCoefficients μ) J))).real
            {σ : Fin n → Vector N |
              (∀ i j : Fin n, i ≠ j → |overlap (σ i) (σ j) - Q| < η) ∧
              field (centerCoefficients (mixtureCoefficients μ) Q) J
                (physicalTrainingCenter σ) ≤ (N : ℝ) * (E₀ - ε)}
          ∂disorderLaw N μ.maxDegree) ≤ Real.exp (-c * (N : ℝ)) := by
  have h24 : Proposition24 (FiniteMixture.pure p (by omega) 1 (by positivity)) β Q :=
    LiteratureSubagProposition24Proof.proposition24 _ (h.beta_pos)
      ⟨h.overlap_range.1.le, h.overlap_range.2⟩
  exact PureReplicaMeansExponential.pure_replica_means_exponential_of_literature
    (p := p) (hp := hp) (β := β) (x := x) (Q := Q) (h := h) (hChen := hChen) (h24 := h24)

end

section

open Set Filter MeasureTheory SphericalModel SphericalTAPCertificate PureStationarity
open PureCapturePhysicalCoarseDiniAssembly SourceLiteratureParisi LiteratureSubagProposition24
open PureCapturePhysicalCoarseDiniLowEnergy PureCapturePhysicalCoarseTransfer
open MixedCapturePhysicalReplicaGeometry LiteratureSubagPhysicalDefinitions
open ReplicaMeanNetCover ReplicaBandGibbsMass ReplicaBandExpectedUpper
open SphericalAging.HardSphereDynamics
open scoped Topology BigOperators
open PureReplicaMeanEnergyAssembly

/-- `prop:pc-replica-means, physical input` with the proved literature inputs discharged.
Original endpoint: `PureReplicaMeanEnergyAssembly.pure_physicalReplicaMeanEnergy_of_literature`. -/
theorem pure_physicalReplicaMeanEnergy_of_chen
    (p : ℕ)
    (hp : 4 ≤ p)
    {β x Q : ℝ}
    (h : Certificate (FiniteMixture.pure p (by omega) 1 (by positivity)) β x Q)
    (hChen : Chen2013FiniteParisi) :
    PhysicalReplicaMeanEnergy (FiniteMixture.pure p (by omega) 1 (by positivity)) β Q
      (pureEnergyConstant p (by omega)) := by
  have h24 : Proposition24 (FiniteMixture.pure p (by omega) 1 (by positivity)) β Q :=
    LiteratureSubagProposition24Proof.proposition24 _ (h.beta_pos)
      ⟨h.overlap_range.1.le, h.overlap_range.2⟩
  exact PureReplicaMeanEnergyAssembly.pure_physicalReplicaMeanEnergy_of_literature
    (p := p) (hp := hp) (β := β) (x := x) (Q := Q) (h := h) (hChen := hChen) (h24 := h24)

end

section

open Set Filter MeasureTheory SphericalModel SphericalGaussianJet SphericalForm
open SphericalMarkedWindows SphericalTAPCertificate TwoAtomStationarity PureStationarity
open PairConditionalDeterminantMoments SourcePureSeparationDisjoint
open SourceMixedOnePointInterface SourceMixedFilterInterface
open SphericalPureCapSourceScalars SphericalPureCenterFieldScale
open SourcePureCaptureWindowTransport
open scoped Topology ENNReal
open SourcePureSeparationCorollary13Proof

/-- `prop:pc-separation` with the proved literature inputs discharged.
Original endpoint: `SourcePureSeparationCorollary13Proof.pure_original_critical_separation_reduced`. -/
theorem pure_original_critical_separation_of_chen
    (p : ℕ)
    (hp : 4 ≤ p)
    (ε : ℝ)
    (hε : 0 < ε) :
    ∃ d c : ℝ, 0 < d ∧ 0 < c ∧ ∀ᶠ n : ℕ in atTop,
      (disorderLaw (n+2) (FiniteMixture.pure p (by omega) 1 (by positivity)).maxDegree).real
        {J | ∃ u ∈ nearGroundCriticalSet p (by omega) n J d,
          ∃ v ∈ nearGroundCriticalSet p (by omega) n J d,
            u ≠ v ∧ u ≠ -v ∧ ε ≤ overlap u v} ≤ Real.exp (-c*(n+2 : ℕ)) := by
  exact SourcePureSeparationCorollary13Proof.pure_original_critical_separation_reduced
    (p := p) (hp := hp) (ε := ε) (hε := hε)

end

section

open Set Filter MeasureTheory SphericalModel SphericalGaussianJet SphericalForm
open SphericalMarkedWindows SphericalTAPCertificate TwoAtomStationarity PureStationarity
open PairConditionalDeterminantMoments SourcePureSeparationDisjoint
open SourceMixedOnePointInterface SourceMixedFilterInterface
open SphericalPureCapSourceScalars SphericalPureCenterFieldScale
open SourcePureCaptureWindowTransport
open scoped Topology ENNReal
open SourcePureSeparationCorollary13Proof

/-- `cor:pc-disjoint, microscopic bands` with the proved literature inputs discharged.
Original endpoint: `SourcePureSeparationCorollary13Proof.pure_original_microscopic_disjointness_reduced`. -/
theorem pure_original_microscopic_disjointness_of_chen
    (p : ℕ)
    (hp : 4 ≤ p)
    {Q : ℝ}
    (hQ : 1/2 < Q)
    (hQ1 : Q < 1)
    (L w : ℝ) :
    Tendsto (fun n : ℕ =>
      (disorderLaw (n+2) (FiniteMixture.pure p (by omega) 1 (by positivity)).maxDegree).real
        {J | (criticalWindow p hp n L J).PairwiseDisjoint (microscopicBand n Q w)})
      atTop (𝓝 (1 : ℝ)) := by
  exact SourcePureSeparationCorollary13Proof.pure_original_microscopic_disjointness_reduced
    (p := p) (hp := hp) (Q := Q) (hQ := hQ) (hQ1 := hQ1) (L := L) (w := w)

end

section

open Set Filter MeasureTheory SphericalModel SphericalGaussianJet SphericalForm
open SphericalMarkedWindows SphericalTAPCertificate TwoAtomStationarity PureStationarity
open PairConditionalDeterminantMoments SourcePureSeparationDisjoint
open SourceMixedOnePointInterface SourceMixedFilterInterface
open SphericalPureCapSourceScalars SphericalPureCenterFieldScale
open SourcePureCaptureWindowTransport
open scoped Topology ENNReal
open SourcePureSeparationCorollary13Proof

/-- `cor:pc-disjoint, full package` with the proved literature inputs discharged.
Original endpoint: `SourcePureSeparationCorollary13Proof.pure_original_disjoint_bands_and_bounded_count_reduced`. -/
theorem pure_original_disjoint_bands_and_bounded_count_of_chen
    (p : ℕ)
    (hp : 4 ≤ p)
    {β x Q : ℝ}
    (h : Certificate (FiniteMixture.pure p (by omega) 1 (by positivity)) β x Q)
    {L w : ℝ}
    (hL : 0 < L)
    (hw : 0 < w) :
    Tendsto (fun n : ℕ =>
      (disorderLaw (n+2) (FiniteMixture.pure p (by omega) 1 (by positivity)).maxDegree).real
        {J | (criticalWindow p hp n L J).PairwiseDisjoint (microscopicBand n Q w)})
      atTop (𝓝 (1 : ℝ)) ∧
    ∃ C : ℝ, ∀ n : ℕ,
      (∫⁻ J, criticalWindowCount p hp n L J
        ∂disorderLaw (n+2) (FiniteMixture.pure p (by omega) 1 (by positivity)).maxDegree) < ⊤ ∧
      (∫⁻ J, criticalWindowCount p hp n L J
        ∂disorderLaw (n+2) (FiniteMixture.pure p (by omega) 1 (by positivity)).maxDegree).toReal ≤ C := by
  exact SourcePureSeparationCorollary13Proof.pure_original_disjoint_bands_and_bounded_count_reduced
    (p := p) (hp := hp) (β := β) (x := x) (Q := Q) (h := h) (L := L) (w := w) (hL := hL) (hw := hw)

end

section

open MeasureTheory ProbabilityTheory Set Filter
open SphericalModel SourceGaussianLogSobolev SourceSphereLogSobolevProof
open scoped Topology RealInnerProductSpace NNReal
open SourceSphereSharpConcentration
open SourceGaussianDeBruijn.Endpoints

/-- `lem:ent-lsi` with the proved literature inputs discharged.
Original endpoint: `SourceGaussianDeBruijn.Endpoints.geodesic_lipschitz_centered_mgf_reduced3`. -/
theorem geodesic_lipschitz_centered_mgf_of_chen
    {m : ℕ}
    (hm : 2 ≤ m)
    (g : Vector (m+1) → ℝ)
    {L : ℝ}
    (hL : 0 ≤ L)
    (hg : GeodesicLipschitz g L)
    (t : ℝ) :
    (∫ x, Real.exp (t * (g x - ∫ y, g y ∂unitSphereLaw (m+1)))
      ∂unitSphereLaw (m+1)) ≤ Real.exp (L ^ 2 * t ^ 2 / (2 * ((m : ℝ) - 1))) := by
  exact SourceGaussianDeBruijn.Endpoints.geodesic_lipschitz_centered_mgf_reduced3
    (m := m) (hm := hm) (g := g) (L := L) (hL := hL) (hg := hg) (t := t)

end

section

open MeasureTheory ProbabilityTheory Set Filter
open SphericalModel SourceGaussianLogSobolev SourceSphereLogSobolevProof
open scoped Topology RealInnerProductSpace NNReal
open SourceSphereSharpConcentration
open SphericalGaussianJet EntranceLatitudeTangentObservable
open SourceGaussianDeBruijn.Endpoints

/-- `lem:ent-latitude, sharp MGF` with the proved literature inputs discharged.
Original endpoint: `SourceGaussianDeBruijn.Endpoints.observable_centered_mgf_le_sharp_reduced3`. -/
theorem observable_centered_mgf_le_sharp_of_chen
    {n P : ℕ}
    (hn : 3 ≤ n)
    (c : Degree P → ℝ)
    (J : Disorder (n+1) P)
    (hJ : J ∈ regularDisorder)
    (x : Vector (n+1))
    (hx : ‖x‖ ^ 2 = ((n+1 : ℕ) : ℝ))
    (e : Vector n →ₗᵢ[ℝ] Vector (n+1))
    (he : ∀ y, inner ℝ (e y) x = 0)
    {r : ℝ}
    (hr : |r| ≤ 1)
    (t : ℝ) :
    mgf (fun u => observable c J x u - ∫ v, observable c J x v ∂latitudeLaw x e r)
      (latitudeLaw x e r) t ≤
      Real.exp (9 * (derivativeConstant c) ^ 2 * ((n+1 : ℕ) : ℝ) * t ^ 2 /
        (2 * ((n : ℝ) - 2))) := by
  exact SourceGaussianDeBruijn.Endpoints.observable_centered_mgf_le_sharp_reduced3
    (n := n) (P := P) (hn := hn) (c := c) (J := J) (hJ := hJ) (x := x) (hx := hx) (e := e)
    (he := he) (r := r) (hr := hr) (t := t)

end

section

open MeasureTheory ProbabilityTheory Set Filter
open SphericalModel SourceGaussianLogSobolev SourceSphereLogSobolevProof
open scoped Topology RealInnerProductSpace NNReal
open SourceSphereSharpConcentration
open SphericalGaussianJet EntranceLatitudeTangentObservable
open SourceGaussianDeBruijn.Endpoints

/-- `lem:ent-latitude, sub-Gaussian predicate` with the proved literature inputs discharged.
Original endpoint: `SourceGaussianDeBruijn.Endpoints.observable_hasSubgaussianMGF_reduced3`. -/
theorem observable_hasSubgaussianMGF_of_chen
    {n P : ℕ}
    (hn : 5 ≤ n)
    (c : Degree P → ℝ)
    (J : Disorder (n+1) P)
    (hJ : J ∈ regularDisorder)
    (x : Vector (n+1))
    (hx : ‖x‖ ^ 2 = ((n+1 : ℕ) : ℝ))
    (e : Vector n →ₗᵢ[ℝ] Vector (n+1))
    (he : ∀ y, inner ℝ (e y) x = 0)
    {r : ℝ}
    (hr : |r| ≤ 1) :
    HasSubgaussianMGF
      (fun u => observable c J x u - ∫ v, observable c J x v ∂latitudeLaw x e r)
      (18 * (derivativeConstant c) ^ 2).toNNReal (latitudeLaw x e r) := by
  exact SourceGaussianDeBruijn.Endpoints.observable_hasSubgaussianMGF_reduced3
    (n := n) (P := P) (hn := hn) (c := c) (J := J) (hJ := hJ) (x := x) (hx := hx) (e := e)
    (he := he) (r := r) (hr := hr)

end

section

open MeasureTheory ProbabilityTheory Set Filter
open SphericalModel SourceGaussianLogSobolev SourceSphereLogSobolevProof
open scoped Topology RealInnerProductSpace NNReal
open SourceSphereSharpConcentration
open SphericalGaussianJet EntranceLatitudeTangentObservable
open SourceGaussianDeBruijn.Endpoints

/-- `lem:ent-latitude, original event` with the proved literature inputs discharged.
Original endpoint: `SourceGaussianDeBruijn.Endpoints.center_latitude_mean_and_mgf_reduced3`. -/
theorem center_latitude_mean_and_mgf_of_chen
    (μ : FiniteMixture)
    {Q : ℝ}
    (hQ : 0 ≤ Q) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ), 5 ≤ n →
      ∀ (J : Disorder (n+1) μ.maxDegree), J ∈ originalLatitudeMeanGood n μ →
      ∀ (x : Vector (n+1)), ‖x‖ ^ 2 = ((n+1 : ℕ) : ℝ) →
      ∀ r ∈ Ioo (-1 : ℝ) 1,
      let c := centerCoefficients (mixtureCoefficients μ) Q
      let lat := latitudeLaw x (latitudeFrameAt x) r
      let m := ∫ u, observable c J x u ∂lat
      |m| ≤ C * (Real.sqrt ((n+1 : ℕ) : ℝ) * |r| ^ (μ.minDegree-1) + 1) ∧
      ∀ t : ℝ, mgf (fun u => observable c J x u - m) lat t ≤ Real.exp (C * t ^ 2) := by
  exact SourceGaussianDeBruijn.Endpoints.center_latitude_mean_and_mgf_reduced3
    (μ := μ) (Q := Q) (hQ := hQ)

end

section

open MeasureTheory ProbabilityTheory Set Filter
open SphericalModel SourceGaussianLogSobolev SourceSphereLogSobolevProof
open scoped Topology RealInnerProductSpace NNReal
open SourceSphereSharpConcentration
open SphericalGaussianJet EntranceLatitudeTangentObservable
open SourceGaussianDeBruijn.Endpoints

/-- `lem:ent-latitude, constant-completed event` with the proved literature inputs discharged.
Original endpoint: `SourceGaussianDeBruijn.Endpoints.constant_completed_center_latitude_mean_and_mgf_reduced3`. -/
theorem constant_completed_center_latitude_mean_and_mgf_of_chen
    (μ : FiniteMixture)
    {Q : ℝ}
    (hQ : 0 ≤ Q) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ), 5 ≤ n →
      ∀ (J : Disorder (n+1) μ.maxDegree),
        J ∈ SourceEntranceFullEvent.constantCompletedEntranceEvent n μ →
      ∀ (x : Vector (n+1)), ‖x‖ ^ 2 = ((n+1 : ℕ) : ℝ) →
      ∀ r ∈ Ioo (-1 : ℝ) 1,
      let c := centerCoefficients (mixtureCoefficients μ) Q
      let lat := latitudeLaw x (latitudeFrameAt x) r
      let m := ∫ u, observable c J x u ∂lat
      |m| ≤ C * (Real.sqrt ((n+1 : ℕ) : ℝ) * |r| ^ (μ.minDegree-1) + 1) ∧
      ∀ t : ℝ, mgf (fun u => observable c J x u - m) lat t ≤ Real.exp (C * t ^ 2) := by
  exact SourceGaussianDeBruijn.Endpoints.constant_completed_center_latitude_mean_and_mgf_reduced3
    (μ := μ) (Q := Q) (hQ := hQ)

end

section

open MeasureTheory ProbabilityTheory Set Filter
open SphericalModel SourceGaussianLogSobolev SourceSphereLogSobolevProof
open scoped Topology RealInnerProductSpace NNReal
open SourceSphereSharpConcentration
open SphericalGaussianJet EntranceLatitudeTangentObservable
open SourceGaussianDeBruijn.Endpoints

/-- `lem:ent-latitude, full harmonic event` with the proved literature inputs discharged.
Original endpoint: `SourceGaussianDeBruijn.Endpoints.full_center_latitude_mean_and_mgf_reduced3`. -/
theorem full_center_latitude_mean_and_mgf_of_chen
    (μ : FiniteMixture)
    {Q : ℝ}
    (hQ : 0 ≤ Q) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ), 5 ≤ n →
      ∀ (J : Disorder (n+1) μ.maxDegree),
        J ∈ SourceEntranceHarmonicSectors.FullEvent.fullEntranceEvent n μ →
      ∀ (x : Vector (n+1)), ‖x‖ ^ 2 = ((n+1 : ℕ) : ℝ) →
      ∀ r ∈ Ioo (-1 : ℝ) 1,
      let c := centerCoefficients (mixtureCoefficients μ) Q
      let lat := latitudeLaw x (latitudeFrameAt x) r
      let m := ∫ u, observable c J x u ∂lat
      |m| ≤ C * (Real.sqrt ((n+1 : ℕ) : ℝ) * |r| ^ (μ.minDegree-1) + 1) ∧
      ∀ t : ℝ, mgf (fun u => observable c J x u - m) lat t ≤ Real.exp (C * t ^ 2) := by
  exact SourceGaussianDeBruijn.Endpoints.full_center_latitude_mean_and_mgf_reduced3
    (μ := μ) (Q := Q) (hQ := hQ)

end

section

open CrisantiSommers CSParisiMeasure SourceMainClassesLiterature CSPerturbative
open SphericalOrthogonalHaar
open LiteratureSubagPhysicalDefinitions
open LiteratureSubagBandUpperExtraction.Endpoints

/-- `cor:main-classes(c)`: the positive cutoff is chosen before the
normalized coefficient family and its two band approximations. -/
theorem perturbative_corollary_c_of_chen_and_bands (d P : ℕ)
    (hd : 4 ≤ d) (hdEven : Even d) (hdP : d < P) {β : ℝ}
    (hβ : Thresholds.staticThreshold (fun r : ℝ => r ^ d) < β)
    (hChen : Chen2013FiniteParisi) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ (b : EvenPerturbation d P), b.coeff.sum (fun _ c => c) = 1 →
        ∀ (ε : ℝ) (hε : 0 < ε), ε < ε₀ →
          let μ := b.covariance (by omega) ε hε.le
          SubagBandApproximations μ β → MainCondensedAndInitialLiteral μ β := by
  have hξ : (FiniteMixture.pure d (by omega) 1 (by positivity)).xi =
      (fun r : ℝ => r ^ d) := by
    funext r
    simp only [FiniteMixture.pure_xi, one_mul]
  have hβpos : 0 < β := (FiniteMixture.pure d (by omega) 1 (by positivity)).staticThreshold_pos.trans
    (by rwa [hξ])
  obtain ⟨ε₀, hε₀, hresult⟩ := perturbative_corollary_c_of_literature d P hd hdEven hdP hβ
  refine ⟨ε₀, hε₀, ?_⟩
  intro b hb ε hε hsmall
  dsimp only
  intro hBands
  let μ := b.covariance (by omega : 3 ≤ d) ε hε.le
  have hChenSen := SourceLiteratureGroundStateExtraction.chenSenFiniteGround hChen
  exact hresult b hb ε hε hsmall hChen hChenSen
    (fun _ => theorem5_of_bands _ hβpos hBands)
    (remark25_of_bands (chenThermodynamicData hChen μ hβpos.le) hβpos hBands)
    (fun q hq => LiteratureSubagProposition24Proof.proposition24 μ hβpos ⟨hq.1.le, hq.2⟩)

/-- The physical `thm:dir-norm` input needs only the upper approximation. -/
theorem physicalDirectingNormQ_of_chen_and_bands
    (hChen : Chen2013FiniteParisi) {μ : FiniteMixture} {β x Q : ℝ}
    (h : Certificate μ β x Q)
    (hUpper : ExpectedBandUpperApproximation
      (chenThermodynamicData hChen μ h.beta_pos.le)) :
    PureCapturePhysicalCoarseDiniAssembly.PhysicalDirectingNormQ μ β Q :=
  physicalDirectingNormQ_of_literature_reduced3 hChen h hUpper

/-- An exponentially rare equilateral block can always be normalized to
at least two replicas and tolerance strictly between zero and one. -/
private theorem normalize_replica_exclusion {μ : FiniteMixture} {β q : ℝ}
    (hex : ∃ k : ℕ, 1 ≤ k ∧ ∃ ρ : ℝ, 0 < ρ ∧ ∃ c : ℝ, 0 < c ∧
      ∀ᶠ N : ℕ in atTop,
        expectedOverlapBlockProbability N k μ β q ρ ≤ Real.exp (-c * (N : ℝ))) :
    ∃ k : ℕ, 2 ≤ k ∧ ∃ ρ ∈ Ioo (0 : ℝ) 1, ∃ c : ℝ, 0 < c ∧
      ∀ᶠ N : ℕ in atTop,
        expectedOverlapBlockProbability N k μ β q ρ ≤ Real.exp (-c * (N : ℝ)) := by
  obtain ⟨k, hk, ρ, hρ, c, hc, hb⟩ := hex
  have hk2 : 2 ≤ k := by
    by_contra hn
    have hk1 : k = 1 := by omega
    subst k
    obtain ⟨N, hN, hNpos⟩ := (hb.and (eventually_gt_atTop 0)).exists
    have hevent : {σ : Fin 1 → Vector N |
        ∀ i j, i ≠ j → |overlap (σ i) (σ j) - q| < ρ} = univ := by
      ext σ
      simp only [mem_ofPred_eq, mem_univ, iff_true]
      intro i j hij
      exact (hij (Subsingleton.elim i j)).elim
    rw [expectedOverlapBlockProbability, hevent, probReal_univ] at hN
    have hneg : -c * (N : ℝ) < 0 := by
      have : (0 : ℝ) < N := by exact_mod_cast hNpos
      nlinarith
    exact (not_le_of_gt (Real.exp_lt_one_iff.mpr hneg)) hN
  refine ⟨k, hk2, min ρ (1 / 2), ⟨lt_min hρ (by norm_num),
    lt_of_le_of_lt (min_le_right _ _) (by norm_num)⟩, c, hc, ?_⟩
  filter_upwards [hb] with N hN
  apply le_trans ?_ hN
  unfold expectedOverlapBlockProbability
  apply measureReal_mono (h₂ := measure_ne_top _ _)
  intro σ hσ i j hij
  exact (hσ i j hij).trans_le (min_le_left _ _)

/-- `lem:th-replica-exclusion` for every finite mixture and every positive
canonical potential. The lower approximation is unnecessary for exclusion. -/
theorem replica_exclusion_of_positive_potential_of_chen_and_bands
    (hChen : Chen2013FiniteParisi) {μ : FiniteMixture} {β q : ℝ}
    (hβ : 0 < β) (D : ThermodynamicData μ β)
    (hUpper : ExpectedBandUpperApproximation D)
    (hq : q ∈ Ioo (0 : ℝ) 1)
    (hV : 0 < CSStructure.potential μ β (canonicalMinimizer μ β).law q) :
    ∃ k : ℕ, 2 ≤ k ∧ ∃ ρ ∈ Ioo (0 : ℝ) 1, ∃ c : ℝ, 0 < c ∧
      ∀ᶠ N : ℕ in atTop,
        expectedOverlapBlockProbability N k μ β q ρ ≤ Real.exp (-c*(N : ℝ)) := by
  exact normalize_replica_exclusion
    (exponential_exclusion_of_strictTAPGap_reduced2 D hβ hUpper
      (LiteratureSubagBandUpperExtraction.subsequenceBandExtraction D) hq
      (SourceGeneralContactTheorem.strict_tap_gap hChen
        (SourceLiteratureGroundStateExtraction.chenSenFiniteGround hChen) hβ D hq hV))

/-- `lem:th-replica-exclusion` at any strict physical TAP gap, with the
printed replica count and tolerance and only the upper band approximation. -/
theorem source_replica_exclusion_of_strict_tap_gap_of_chen_and_bands
    {μ : FiniteMixture} {β q : ℝ} (D : ThermodynamicData μ β) (hβ : 0 < β)
    (hUpper : ExpectedBandUpperApproximation D) (hq : q ∈ Ioo (0 : ℝ) 1)
    (hgap : tapValue D q < D.pressure) :
    ∃ k : ℕ, 2 ≤ k ∧ ∃ ρ ∈ Ioo (0 : ℝ) 1, ∃ c : ℝ, 0 < c ∧
      ∀ᶠ N : ℕ in atTop,
        expectedOverlapBlockProbability N k μ β q ρ ≤ Real.exp (-c * (N : ℝ)) :=
  normalize_replica_exclusion
    (exponential_exclusion_of_strictTAPGap_reduced2 D hβ hUpper
      (LiteratureSubagBandUpperExtraction.subsequenceBandExtraction D) hq hgap)

/-- The general normalized non-multisamplable exclusion, with the original
conclusion and the two band approximations in place of Remark 25. -/
theorem source_normalized_replica_exclusion_of_chen_and_bands
    {μ : FiniteMixture} {β q : ℝ} (D : ThermodynamicData μ β) (hβ : 0 < β)
    (hBands : SubagBandApproximations μ β) (hq : q ∈ Ioo (0 : ℝ) 1)
    (hn : ¬ MultiSamplable μ β q) :
    ∃ k : ℕ, 2 ≤ k ∧ ∃ ρ ∈ Ioo (0 : ℝ) 1, ∃ c : ℝ, 0 < c ∧
      ∀ᶠ N : ℕ in atTop,
        expectedOverlapBlockProbability N k μ β q ρ ≤ Real.exp (-c * (N : ℝ)) :=
  SourceSubagReplicaCriterion.source_normalized_replica_exclusion
    (remark25_of_bands D hβ hBands) hq hn

/-- `thm:th-contact(2)`, residual clause: the pushforward identity already
has a deterministic proof, so even Chen and the bands are unnecessary. -/
theorem contact_residual_canonical_of_chen {μ : FiniteMixture} {β q : ℝ}
    (hq : q ∈ Ioo (0 : ℝ) 1)
    (hV : CSStructure.potential μ β (canonicalMinimizer μ β).law q = 0) :
    (canonicalMinimizer (physicalResidualMixture μ q hq) β).law =
      (canonicalMinimizer μ β).law.map (fun r => max 0 ((r-q)/(1-q))) :=
  LiteratureSubagTheorem10Proof.contact_residual_canonical_reduced hq hV

end

end SlowEquilibration.SourceMainTheoremsReducedFinal
