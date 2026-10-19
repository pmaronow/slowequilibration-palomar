-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.LiteratureSubagProposition24Proof
public import SlowEquilibration.LiteratureSubagRemark25Proof
public import SlowEquilibration.LiteratureSubagTheorem10Proof
public import SlowEquilibration.SourceGeneralTAPTelescope
public import SlowEquilibration.SourceGeneralContactTheorem

/-!
# The inequality in Subag's Theorem 5 and a reduction of its equality case

The general physical TAP upper bound is proved from the public variational
telescope and the ground trial, conditional on Chen and Chen--Sen. No Subag
interface is used for that inequality, and no certificate is needed.

The equality characterization is reduced to four explicitly unproved physical
steps: the existing upper band approximation and subsequence extraction, the
lower half of Proposition 4, and a finite-dimensional block-rate comparison
from the first part of Section 4. The last comparison retains the replica
count normalization: large counts are multiples of the requested fixed count.
Proposition 24, the passage from quenched block costs to the positivity-aware
Definition 2, and the subsequence argument in Remark 25 are discharged.
A physical comparison also supplies the upper bound in the general reduction,
so that reduction itself needs only the actual thermodynamic limit data and
the four remaining steps, without additional variational hypotheses.

This is a further reduction, not a proof of the remaining physical steps or
a Chen-only proof of Theorem 5. The downstream statements preserve their full
conclusions and replace Theorem 5, Remark 25 and Proposition 24 by those steps.
-/

@[expose] public section
noncomputable section

namespace SlowEquilibration.LiteratureSubagTheorem5Proof

open MeasureTheory ProbabilityTheory Filter Set
open SphericalModel LiteratureSubagPhysicalDefinitions LiteratureSubagTAP
open SourceLiteratureParisi SourceLiteratureGroundState
open LiteratureSubagProposition24 LiteratureSubagRemark25Proof
open LiteratureSubagTheorem10Proof
open scoped Topology

set_option autoImplicit false

/-- The inequality in Subag, Theorem 5, for arbitrary physical limit data.
The zero perturbation of the ground trial suffices, including at contacts. -/
theorem tapValue_le_pressure (hChen : Chen2013FiniteParisi)
    (hChenSen : ChenSenFiniteGround) {μ : FiniteMixture} {β q : ℝ}
    (hβ : 0 < β) (D : ThermodynamicData μ β) (hq : q ∈ Ioo (0 : ℝ) 1) :
    tapValue D q ≤ D.pressure := by
  let ζ := CSParisiMeasure.canonicalMinimizer μ β
  have hground : D.ground q ≤
      CSTAPGroundTrialQuadratic.functional μ β ζ.law q 0 := by
    obtain ⟨u, hmin, hlim, _⟩ :=
      SourceGroundProfileUniqueness.source_ground_limit_unique hChenSen μ hq.1
    have hG := tendsto_nhds_unique (D.ground_limit q hq) hlim
    rw [hG, ← SourceGeneralContactTheorem.radiusFunctional_groundTrial μ ζ hβ hq
      (le_refl (0 : ℝ))]
    exact hmin _
  have hres : D.residual q ≤
      (SourceGeneralTAPTelescope.residualTrial ζ hq).value β
        (CSTAPTelescope.residualMixture μ hq).xi := by
    have hR := tendsto_nhds_unique (D.residual_limit q hq)
      (hChen (physicalResidualMixture μ q hq) β hβ.le)
    rw [hR]
    exact CSParisiMeasure.canonicalMinimizer_isMinimizer _ β _
  have hP := tendsto_nhds_unique D.pressure_limit (hChen μ β hβ.le)
  have htel := SourceGeneralTAPTelescope.canonical_telescope μ hβ hq
  have hβg := mul_le_mul_of_nonneg_left hground hβ.le
  unfold tapValue
  rw [hP, htel]
  change β * D.ground q + Real.log (1 - q) / 2 + D.residual q ≤
    β * CSTAPGroundTrialQuadratic.functional μ β ζ.law q 0 + Real.log (1 - q) / 2 +
      (SourceGeneralTAPTelescope.residualTrial ζ hq).value β
        (CSTAPTelescope.residualMixture μ hq).xi
  linarith

/-- The lower half of Proposition 4, with fixed parameters before the
dimension limit. Arbitrarily small positive tolerances can be selected before
the count. This is a remaining hypothesis, not an asserted theorem. -/
def ExpectedBandLowerApproximation {μ : FiniteMixture} {β : ℝ}
    (D : ThermodynamicData μ β) : Prop :=
  ∀ q : ℝ, q ∈ Ioo (0 : ℝ) 1 → ∀ ε : ℝ, 0 < ε →
    ∀ δ₀ ρ₀ : ℝ, 0 < δ₀ → 0 < ρ₀ →
      ∃ δ : ℝ, 0 < δ ∧ δ ≤ δ₀ ∧ ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ ρ₀ ∧
        ∃ K : ℕ, ∀ k : ℕ, K ≤ k → ∀ᶠ N : ℕ in atTop,
          ∀ m : Vector N, ‖m‖ ^ 2 = (N : ℝ) * q →
            Real.log (1 - q) / 2 + D.residual q - ε ≤
              expectedReplicatedBandPressure k μ β q δ ρ m

/-- The remaining finite-dimensional reconstruction estimate in Section 4.
Its ingredients are the product-Gibbs band identity, concentration of the
ground maximum and pressure, uniform band concentration, and the IID
inequality `P_(n*r) ≤ P_n^r`. All quantities here are finite-dimensional;
no TAP equality or thermodynamic data are assumed. The division by `n` is
essential when the concentration threshold forces a large multiple `k`.
This statement is a named remaining hypothesis, not a proved interface. -/
def BandBlockRateComparison (μ : FiniteMixture) (β : ℝ) : Prop :=
  ∀ q : ℝ, q ∈ Ioo (0 : ℝ) 1 → Proposition24 μ β q →
    ∀ n : ℕ, 1 ≤ n → ∀ ρ ε : ℝ, 0 < ρ → 0 < ε →
      ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∃ K : ℕ,
        ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
        ∀ η : ℝ, 0 < η → η ≤ min ρ₀ ρ →
        ∀ k : ℕ, K ≤ k → n ∣ k → ∀ᶠ N : ℕ in atTop,
          ∀ m : Vector N, ‖m‖ ^ 2 = (N : ℝ) * q →
            β * expectedCenterGroundEnergy N μ q +
                expectedReplicatedBandPressure k μ β q δ η m - quenchedPressure N μ β ≤
              truncatedQuenchedBlockRate N n μ β q ρ / (n : ℝ) + ε

private theorem truncatedQuenchedBlockRate_nonpos (N k : ℕ) (μ : FiniteMixture)
    (β q ρ : ℝ) : truncatedQuenchedBlockRate N k μ β q ρ ≤ 0 := by
  apply div_nonpos_of_nonpos_of_nonneg _ (Nat.cast_nonneg N)
  apply integral_nonpos
  intro J
  apply Real.log_nonpos
  · exact le_trans (Real.exp_pos _).le (le_max_right _ _)
  · exact max_le measureReal_le_one
      (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (Nat.cast_nonneg N)))

private theorem exists_center {N : ℕ} (hN : 0 < N) {q : ℝ} (hq : 0 ≤ q) :
    ∃ m : Vector N, ‖m‖ ^ 2 = (N : ℝ) * q := by
  let : NeZero N := ⟨hN.ne'⟩
  obtain ⟨m, hm⟩ := exists_norm_eq (Vector N) (Real.sqrt_nonneg ((N : ℝ) * q))
  exact ⟨m, by rw [hm, Real.sq_sqrt (mul_nonneg (Nat.cast_nonneg N) hq)]⟩

private theorem tap_gap_lt_blockRate_add {μ : FiniteMixture} {β q : ℝ}
    (D : ThermodynamicData μ β) (hβ : 0 < β) (hq : q ∈ Ioo (0 : ℝ) 1)
    (hlower : ExpectedBandLowerApproximation D)
    (hcompare : BandBlockRateComparison μ β)
    (n : ℕ) (hn : 1 ≤ n) (ρ : ℝ) (hρ : 0 < ρ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, tapValue D q - D.pressure <
      truncatedQuenchedBlockRate N n μ β q ρ / (n : ℝ) + ε := by
  let t : ℝ := ε / 4
  have ht : 0 < t := by dsimp [t]; positivity
  have h24 := LiteratureSubagProposition24Proof.proposition24 μ hβ ⟨hq.1.le, hq.2⟩
  obtain ⟨δ₀, hδ₀, ρ₀, hρ₀, K₁, hc⟩ := hcompare q hq h24 n hn ρ t hρ ht
  obtain ⟨δ, hδ, hδsmall, η, hη, hηsmall, K₂, hl⟩ :=
    hlower q hq t ht δ₀ (min ρ₀ ρ) hδ₀ (lt_min hρ₀ hρ)
  let k := n * (max K₁ K₂ + 1)
  have hkn : n ∣ k := ⟨max K₁ K₂ + 1, rfl⟩
  have hk₁ : K₁ ≤ k := by
    dsimp [k]
    nlinarith [le_max_left K₁ K₂]
  have hk₂ : K₂ ≤ k := by
    dsimp [k]
    nlinarith [le_max_right K₁ K₂]
  have henergy := ((D.ground_limit q hq).const_mul β).sub D.pressure_limit
  have hevent : ∀ᶠ N : ℕ in atTop,
      β * D.ground q - D.pressure - t <
        β * expectedCenterGroundEnergy N μ q - quenchedPressure N μ β :=
    henergy.eventually (lt_mem_nhds (by linarith))
  filter_upwards [hc δ hδ hδsmall η hη hηsmall k hk₁ hkn,
    hl k hk₂, hevent, eventually_gt_atTop 0] with N hcN hlN heN hN
  obtain ⟨m, hm⟩ := exists_center hN hq.1.le
  have hc' := hcN m hm
  have hl' := hlN m hm
  have htt : 3 * t < ε := by dsimp [t]; linarith
  unfold tapValue
  linarith

private theorem tap_upper_of_band_estimates {μ : FiniteMixture} {β q : ℝ}
    (D : ThermodynamicData μ β) (hβ : 0 < β) (hq : q ∈ Ioo (0 : ℝ) 1)
    (hlower : ExpectedBandLowerApproximation D)
    (hcompare : BandBlockRateComparison μ β) : tapValue D q ≤ D.pressure := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨N, hN⟩ := (tap_gap_lt_blockRate_add D hβ hq hlower hcompare
    1 le_rfl 1 zero_lt_one ε hε).exists
  have hzero := truncatedQuenchedBlockRate_nonpos N 1 μ β q 1
  norm_num only [Nat.cast_one, div_one] at hN
  linarith

/-- Section 4's reconstruction direction, including the full-sequence,
positivity-aware Definition 2. The only unproved inputs are a lower band
approximation and the explicitly finite-dimensional block comparison. -/
theorem multiSamplable_of_tap_equality {μ : FiniteMixture} {β q : ℝ}
    (D : ThermodynamicData μ β) (hβ : 0 < β) (hq : q ∈ Ioo (0 : ℝ) 1)
    (hlower : ExpectedBandLowerApproximation D)
    (hcompare : BandBlockRateComparison μ β)
    (heq : D.pressure = tapValue D q) : MultiSamplable μ β q := by
  apply multiSamplable_of_truncatedQuenchedBlockRate ⟨hq.1.le, hq.2⟩
  intro n hn ρ hρ
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hnr : 0 < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  let t : ℝ := ε / (2 * (n : ℝ))
  have ht : 0 < t := by dsimp [t]; positivity
  have htn : t * (n : ℝ) = ε / 2 := by dsimp [t]; field_simp
  filter_upwards [tap_gap_lt_blockRate_add D hβ hq hlower hcompare n hn ρ hρ t ht]
    with N hN
  have hzero := truncatedQuenchedBlockRate_nonpos N n μ β q ρ
  have hscale : truncatedQuenchedBlockRate N n μ β q ρ / (n : ℝ) * (n : ℝ) =
      truncatedQuenchedBlockRate N n μ β q ρ := div_mul_cancel₀ _ hnr.ne'
  have hgap : tapValue D q - D.pressure = 0 := sub_eq_zero.mpr heq.symm
  rw [hgap] at hN
  have hlow : -t < truncatedQuenchedBlockRate N n μ β q ρ / (n : ℝ) := by linarith
  have hlow' := (mul_lt_mul_iff_left₀ hnr).mpr hlow
  rw [hscale] at hlow'
  rw [Real.dist_eq, sub_zero, abs_of_nonpos hzero]
  nlinarith [htn]

/-- The exact Theorem 5 interface, reduced to the two halves of Proposition 4
and the conditioning and reconstruction estimates of Section 4. The TAP
upper bound and every required Proposition 24 instance are proved here. -/
theorem theorem5_of_band_estimates {μ : FiniteMixture} {β : ℝ}
    (D : ThermodynamicData μ β) (hβ : 0 < β)
    (hupper : ExpectedBandUpperApproximation D)
    (hlower : ExpectedBandLowerApproximation D)
    (hextract : SubsequenceBandExtraction D)
    (hcompare : BandBlockRateComparison μ β) : Theorem5 D := by
  refine ⟨hβ, ?_⟩
  intro q hq
  have hu := tap_upper_of_band_estimates D hβ hq hlower hcompare
  refine ⟨⟨multiSamplable_of_tap_equality D hβ hq hlower hcompare, ?_⟩, hu⟩
  intro hm
  have hm' : MultiSamplableAlong μ β q id := hm
  have hl := subsequence_tap_lower_bound_of_band_estimates D hupper hextract
    q hq (LiteratureSubagProposition24Proof.proposition24 μ hβ ⟨hq.1.le, hq.2⟩)
      id strictMono_id hm'
  exact le_antisymm hl hu

/-- Remark 25 with Theorem 5 and Proposition 24 discharged by the preceding
reduction. The four remaining physical steps are stated explicitly. -/
theorem remark25Contrapositive_of_band_estimates_reduced2 {μ : FiniteMixture} {β : ℝ}
    (D : ThermodynamicData μ β) (hβ : 0 < β)
    (hupper : ExpectedBandUpperApproximation D)
    (hlower : ExpectedBandLowerApproximation D)
    (hextract : SubsequenceBandExtraction D)
    (hcompare : BandBlockRateComparison μ β) :
    LiteratureSubagReplicaExclusion.Remark25Contrapositive μ β := by
  exact LiteratureSubagRemark25Proof.remark25Contrapositive_of_band_estimates D
    (theorem5_of_band_estimates D hβ hupper hlower hextract hcompare)
    (fun q hq => LiteratureSubagProposition24Proof.proposition24 μ hβ ⟨hq.1.le, hq.2⟩)
    hupper hextract

/-- The strict-gap consequence used downstream needs only the upper half
of Proposition 4 and Section 4's subsequence extraction. Reconstruction,
the lower band approximation, Theorem 5 and Remark 25 are unnecessary here. -/
theorem exponential_exclusion_of_strictTAPGap_reduced2
    {μ : FiniteMixture} {β : ℝ} (D : ThermodynamicData μ β) (hβ : 0 < β)
    (hupper : ExpectedBandUpperApproximation D)
    (hextract : SubsequenceBandExtraction D)
    {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1) (hgap : tapValue D q < D.pressure) :
    ∃ k : ℕ, 1 ≤ k ∧ ∃ ρ : ℝ, 0 < ρ ∧ ∃ c : ℝ, 0 < c ∧
      ∀ᶠ N : ℕ in atTop,
        expectedOverlapBlockProbability N k μ β q ρ ≤ Real.exp (-c * (N : ℝ)) := by
  classical
  by_contra hnot
  have hrec : SubexponentialRecurrence μ β q := by
    intro k hk ρ hρ c hc
    have hn : ¬ ∀ᶠ N : ℕ in atTop,
        expectedOverlapBlockProbability N k μ β q ρ ≤ Real.exp (-c * (N : ℝ)) :=
      fun hb => hnot ⟨k, hk, ρ, hρ, c, hc, hb⟩
    simpa only [not_eventually, not_le] using hn
  obtain ⟨φ, hφ, hm⟩ := subsequence_multisamplable_of_recurrence hrec
  have hl := subsequence_tap_lower_bound_of_band_estimates D hupper hextract q hq
    (LiteratureSubagProposition24Proof.proposition24 μ hβ ⟨hq.1.le, hq.2⟩) φ hφ hm
  exact (not_le_of_gt hgap) hl

open SphericalTAPCertificate SourceLiteratureStrictTAPGap
open SourceReductionConsumerAsymptotic SphericalOverlapExponential
open SphericalOrthogonalHaar SphericalAging.HardSphereDynamics
open scoped NNReal

/-- The reduction specialized to exactly the literature data used by the
endpoints. The four physical steps remain hypotheses; no Subag interface does. -/
theorem theorem5_literature_reduced2
    (hChen : Chen2013FiniteParisi) (hChenSen : ChenSenFiniteGround)
    (μ : FiniteMixture) {β : ℝ} (hβ : 0 < β)
    (hupper : ExpectedBandUpperApproximation
      (literatureThermodynamicData hChen hChenSen μ hβ.le))
    (hlower : ExpectedBandLowerApproximation
      (literatureThermodynamicData hChen hChenSen μ hβ.le))
    (hextract : SubsequenceBandExtraction
      (literatureThermodynamicData hChen hChenSen μ hβ.le))
    (hcompare : BandBlockRateComparison μ β) :
    Theorem5 (literatureThermodynamicData hChen hChenSen μ hβ.le) :=
  theorem5_of_band_estimates _ hβ hupper hlower hextract hcompare

/-- The physical directing-norm endpoint with both Subag interfaces removed.
Only the upper band approximation and subsequence extraction are needed. -/
theorem physicalDirectingNormQ_of_literature_reduced2
    (hChen : Chen2013FiniteParisi) (hChenSen : ChenSenFiniteGround)
    {μ : FiniteMixture} {β x Q : ℝ} (h : Certificate μ β x Q)
    (hupper : ExpectedBandUpperApproximation
      (literatureThermodynamicData hChen hChenSen μ h.beta_pos.le))
    (hextract : SubsequenceBandExtraction
      (literatureThermodynamicData hChen hChenSen μ h.beta_pos.le)) :
    PureCapturePhysicalCoarseDiniAssembly.PhysicalDirectingNormQ μ β Q := by
  apply SourcePureCapturePhysicalNormParisiExclusion.physical_directing_normQ_of_parisi_and_replica_exclusion μ h
    (SourceLiteratureParisiTemperatureEven.finite_pressure_limit_all_real_shift hChen μ)
  intro q hq hqQ
  let D := literatureThermodynamicData hChen hChenSen μ h.beta_pos.le
  obtain ⟨k, _hk, ρ, hρ, c, hc, hb⟩ :=
    exponential_exclusion_of_strictTAPGap_reduced2 D h.beta_pos hupper hextract hq
      (strictTAPGap_of_literature hChen hChenSen h D q hq hqQ)
  exact ⟨k, ρ, hρ,
    LiteratureSubagFullOverlapAdapter.fullOverlapLaw_equilateral_tendsto_zero_of_expected
      μ β q ρ k (LiteratureSubagReplicaExclusion.expectedOverlapBlockProbability_tendsto_zero_of_exponential
        μ β q ρ c k hc hb)⟩

/-- The principal literal endpoint of `LiteratureSubagProposition24Proof`,
with its complete conclusion and four explicit remaining physical steps.
There is no Theorem 5, Remark 25 or Proposition 24 hypothesis. -/
theorem finiteMixture_main_condensed_and_initial_literal_reduced2
    (μ : FiniteMixture) {β x Q : ℝ}
    (h : Certificate μ β x Q)
    (hChen : Chen2013FiniteParisi)
    (hChenSen : ChenSenFiniteGround)
    (hupper : ExpectedBandUpperApproximation
      (literatureThermodynamicData hChen hChenSen μ h.beta_pos.le))
    (hlower : ExpectedBandLowerApproximation
      (literatureThermodynamicData hChen hChenSen μ h.beta_pos.le))
    (hextract : SubsequenceBandExtraction
      (literatureThermodynamicData hChen hChenSen μ h.beta_pos.le))
    (hcompare : BandBlockRateComparison μ β) :
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
  let D := literatureThermodynamicData hChen hChenSen μ h.beta_pos.le
  exact LiteratureSubagProposition24Proof.finiteMixture_main_condensed_and_initial_literal_reduced
    μ h hChen hChenSen
    (theorem5_of_band_estimates D h.beta_pos hupper hlower hextract hcompare)
    (remark25Contrapositive_of_band_estimates_reduced2 D h.beta_pos
      hupper hlower hextract hcompare)

universe u v

/-- The all-initial spherical endpoint, with the same universe-polymorphic
conclusion and with the three Subag interfaces replaced by the four steps. -/
theorem finiteMixture_all_initial_spherical_of_literature_reduced2
    (μ : FiniteMixture) {β x Q : ℝ} (h : Certificate μ β x Q)
    (hChen : Chen2013FiniteParisi) (hChenSen : ChenSenFiniteGround)
    (hupper : ExpectedBandUpperApproximation
      (literatureThermodynamicData hChen hChenSen μ h.beta_pos.le))
    (hlower : ExpectedBandLowerApproximation
      (literatureThermodynamicData hChen hChenSen μ h.beta_pos.le))
    (hextract : SubsequenceBandExtraction
      (literatureThermodynamicData hChen hChenSen μ h.beta_pos.le))
    (hcompare : BandBlockRateComparison μ β) :
    ∃ γ : ℝ, 0 < γ ∧ SourceMixedCountCapturePackage.SphericalInitialConclusions.{u,v} μ β γ := by
  let D := literatureThermodynamicData hChen hChenSen μ h.beta_pos.le
  exact LiteratureSubagProposition24Proof.finiteMixture_all_initial_spherical_of_literature_reduced.{u,v}
    μ h hChen hChenSen
    (theorem5_of_band_estimates D h.beta_pos hupper hlower hextract hcompare)
    (remark25Contrapositive_of_band_estimates_reduced2 D h.beta_pos
      hupper hlower hextract hcompare)

end SlowEquilibration.LiteratureSubagTheorem5Proof
