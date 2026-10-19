-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.LiteratureSubagRemark25Proof
public import SlowEquilibration.LiteratureSubagProposition24Proof
public import SlowEquilibration.SourceLiteratureGroundStateProof
public import SlowEquilibration.ReplicaBandExpectedUpper

/-!
# Further proved reductions of Subag's Remark 25

Remark 25, following the proof of Theorem 3 in Section 4 of Subag,
arXiv:1804.10576v6, uses existence of the ground-energy limit, rather
than its Chen--Sen variational identification. We construct the exact
thermodynamic data using Chen's finite-temperature formula alone.

The proved Proposition 24 removes the concentration hypothesis from the
previous reduction and its two principal downstream endpoints. We also
prove the exact expected-band upper interface when the quenched residual
equals its annealed value. This specialization is not asserted for a
general mixture and temperature.

This is a partial reduction. The general quenched expected-band upper
approximation, subsequence band extraction, and reconstruction direction
of Theorem 3 remain unproved here. Consequently the final reductions
still take the two original band interfaces and Theorem 5 as hypotheses.
The downstream strict TAP gap also still uses Chen--Sen's variational
formula; that use is separate from ground-limit existence in Remark 25.
-/

@[expose] public section
noncomputable section

namespace SlowEquilibration.LiteratureSubagRemark25Final

open MeasureTheory ProbabilityTheory Filter Set
open SphericalModel LiteratureSubagPhysicalDefinitions LiteratureSubagTAP
open LiteratureSubagReplicaExclusion LiteratureSubagRemark25Proof
open SourceLiteratureParisi SourceLiteratureGroundStateProof
open SourceLiteratureGroundStateRadialCoefficients SourceLiteratureGroundStateCenterBridge
open ReplicaBandExpectedUpper
open scoped Topology

set_option autoImplicit false

/-- The ground-limit existence used in Section 4 and Remark 25 follows
from Chen's pressure limit and the finite-dimensional Laplace comparison. -/
theorem exists_center_ground_limit
    (hChen : Chen2013FiniteParisi) (μ : FiniteMixture) {q : ℝ} (hq : 0 < q) :
    ∃ E : ℝ, Tendsto (fun N : ℕ => expectedCenterGroundEnergy N μ q)
      atTop (𝓝 E) := by
  obtain ⟨E, hE, _hzero⟩ :=
    exists_ground_and_zero_temperature_limits hChen (centerMixture μ q hq)
  refine ⟨E, hE.congr' ?_⟩
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
  exact (expectedCenterGroundEnergy_eq_canonical μ hq hN).symm

/-- Thermodynamic data of the literal original model constructed using
only Chen's finite-temperature formula, without a ground-profile minimum. -/
def chenThermodynamicData (hChen : Chen2013FiniteParisi)
    (μ : FiniteMixture) {β : ℝ} (hβ : 0 ≤ β) : ThermodynamicData μ β where
  pressure := CSParisiMeasure.variationalValue μ β
  pressure_limit := hChen μ β hβ
  ground := fun q => if hq : 0 < q then
    Classical.choose (exists_center_ground_limit hChen μ hq) else 0
  ground_limit := by
    intro q hq
    simp only [dite_eq_left hq.1]
    exact Classical.choose_spec (exists_center_ground_limit hChen μ hq.1)
  residual := fun q => if hq : q ∈ Ioo (0 : ℝ) 1 then
    CSParisiMeasure.variationalValue (physicalResidualMixture μ q hq) β
    else CSParisiMeasure.variationalValue μ β
  residual_limit := by
    intro q hq
    simp only [dite_eq_left hq]
    exact hChen _ β hβ

/-- All actual thermodynamic data agree on the domain of Remark 25.
In particular the Chen-only construction has exactly the same values as
the existing Chen--Sen construction, whenever both are supplied. -/
theorem thermodynamicData_values_unique
    {μ : FiniteMixture} {β : ℝ} (D E : ThermodynamicData μ β) :
    D.pressure = E.pressure ∧ ∀ q : ℝ, q ∈ Ioo (0 : ℝ) 1 →
      D.ground q = E.ground q ∧ D.residual q = E.residual q := by
  refine ⟨tendsto_nhds_unique D.pressure_limit E.pressure_limit, ?_⟩
  intro q hq
  exact ⟨tendsto_nhds_unique (D.ground_limit q hq) (E.ground_limit q hq),
    tendsto_nhds_unique (D.residual_limit q hq) (E.residual_limit q hq)⟩

/-- The fixed-parameter upper approximation supplied by the proved
annealed band estimate, at an overlap where the residual is annealed. -/
private theorem expected_band_upper_at_annealed_residual
    {μ : FiniteMixture} {β : ℝ} (D : ThermodynamicData μ β) (hβ : 0 < β)
    {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1)
    (hres : D.residual q = β ^ 2 * TwoAtomStationarity.residualAtOne μ q / 2)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ ρ : ℝ, 0 < ρ ∧ ∃ K : ℕ,
      ∀ k : ℕ, K ≤ k → ∀ᶠ N : ℕ in atTop,
        ∀ m : Vector N, ‖m‖ ^ 2 = (N : ℝ) * q →
          0 < (Measure.pi (fun _ : Fin k => sphereLaw N)) (ReplicatedBand k q δ ρ m) →
          expectedReplicatedBandPressure k μ β q δ ρ m ≤
            Real.log (1 - q) / 2 + D.residual q + ε := by
  obtain ⟨C, hC, hupper⟩ := expectedReplicatedBandPressure_upper μ hβ hq
  have hs : 0 < Real.sqrt q := Real.sqrt_pos.mpr hq.1
  have hs1 : Real.sqrt q < 1 := by
    nlinarith [Real.sq_sqrt hq.1.le, Real.sqrt_nonneg q, hq.2]
  let f : ℝ → ℝ := fun u => C * (Real.sqrt u +
    Real.sqrt (u + (u + Real.sqrt (8 * u)) / (1 - q)))
  have hf : ContinuousAt f 0 := by dsimp [f]; fun_prop
  have hf0 : f 0 = 0 := by simp [f]
  have hsmall : ∀ᶠ u in 𝓝 (0 : ℝ), f u < ε / 2 :=
    hf.tendsto.eventually_lt_const (by rw [hf0]; positivity)
  obtain ⟨r, hr, hnear⟩ := Metric.eventually_nhds_iff.mp hsmall
  let δ := min (Real.sqrt q / 2) (min ((1 - Real.sqrt q) / 2) (r / 2))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδq : δ ≤ Real.sqrt q / 2 := min_le_left _ _
  have hδ1 : δ ≤ (1 - Real.sqrt q) / 2 :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hδr : δ ≤ r / 2 := (min_le_right _ _).trans (min_le_right _ _)
  have hfδ : f δ < ε / 2 := hnear (by
    rw [Real.dist_eq, sub_zero, abs_of_pos hδ]
    linarith)
  have hlarge : ∀ᶠ k : ℕ in atTop, 1 ≤ k ∧ 1 / (k : ℝ) ≤ δ := by
    filter_upwards [eventually_ge_atTop (1 : ℕ),
      (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually_lt_const hδ]
      with k hk hi
    exact ⟨hk, hi.le⟩
  obtain ⟨K, hK⟩ := eventually_atTop.mp hlarge
  refine ⟨δ, hδ, δ, hδ, K, ?_⟩
  intro k hk
  obtain ⟨hk1, hi⟩ := hK k hk
  have herr : C * (Real.sqrt δ +
      Real.sqrt (1 / (k : ℝ) + (δ + Real.sqrt (8 * δ)) / (1 - q))) < ε / 2 := by
    apply lt_of_le_of_lt _ hfδ
    dsimp only [f]
    gcongr
  filter_upwards [hupper δ hδ hδq hδ1 δ hδ k hk1 (ε / 2) (by positivity)]
    with N hN
  intro m hm hvol
  have hb := hN m hm hvol
  rw [hres]
  linarith

/-- This proves the exact named upper interface in the regime where all
its quenched residuals equal their annealed values. The equality is an
explicit restriction, not a replacement of the general target interface. -/
theorem expectedBandUpperApproximation_of_annealed_residual
    {μ : FiniteMixture} {β : ℝ} (D : ThermodynamicData μ β) (hβ : 0 < β)
    (hres : ∀ q : ℝ, q ∈ Ioo (0 : ℝ) 1 →
      D.residual q = β ^ 2 * TwoAtomStationarity.residualAtOne μ q / 2) :
    ExpectedBandUpperApproximation D := by
  intro q hq ε hε
  exact expected_band_upper_at_annealed_residual D hβ hq (hres q hq) ε hε

/-- Proposition 24 is now a theorem, so the physical one-sided subsequence
inequality suffices without a separate concentration hypothesis. -/
theorem remark25Contrapositive_of_subsequence_tap_lower_bound_reduced2
    {μ : FiniteMixture} {β : ℝ} (D : ThermodynamicData μ β)
    (h5 : Theorem5 D) (hlower : SubsequenceTAPLowerBound D) :
    Remark25Contrapositive μ β := by
  apply remark25Contrapositive_of_subsequence_tap_lower_bound D h5 _ hlower
  intro q hq
  exact LiteratureSubagProposition24Proof.proposition24 μ h5.1 ⟨hq.1.le, hq.2⟩

/-- The exact previous two-band reduction with Proposition 24 discharged.
Neither of the remaining band interfaces is asserted as a theorem. -/
theorem remark25Contrapositive_of_band_estimates_reduced2
    {μ : FiniteMixture} {β : ℝ} (D : ThermodynamicData μ β)
    (h5 : Theorem5 D)
    (hupper : ExpectedBandUpperApproximation D)
    (hextract : SubsequenceBandExtraction D) : Remark25Contrapositive μ β :=
  remark25Contrapositive_of_subsequence_tap_lower_bound_reduced2 D h5
    (subsequence_tap_lower_bound_of_band_estimates D hupper hextract)

end SlowEquilibration.LiteratureSubagRemark25Final

namespace SlowEquilibration.LiteratureSubagRemark25Final.Endpoints

open SlowEquilibration.LiteratureSubagProposition24Proof

open MeasureTheory ProbabilityTheory Filter Set
open SphericalModel SphericalTAPCertificate SphericalOrthogonalHaar
open SourceLiteratureParisi SourceLiteratureGroundState SourceLiteratureStrictTAPGap
open LiteratureSubagTAP LiteratureSubagRemark25Proof LiteratureSubagRemark25Final
open SourceReductionConsumerAsymptotic SphericalOverlapExponential
open SphericalAging.HardSphereDynamics
open scoped Topology

set_option autoImplicit false

universe u v

/-- The principal literal endpoint with Remark 25 replaced by the exact
two remaining band interfaces and Proposition 24 supplied by its proof. -/
theorem finiteMixture_main_condensed_and_initial_literal_reduced2
    (μ : FiniteMixture) {β x Q : ℝ}
    (h : Certificate μ β x Q)
    (hChen : Chen2013FiniteParisi)
    (hChenSen : ChenSenFiniteGround)
    (h5 : Theorem5
      (literatureThermodynamicData hChen hChenSen μ h.beta_pos.le))
    (hupper : ExpectedBandUpperApproximation
      (literatureThermodynamicData hChen hChenSen μ h.beta_pos.le))
    (hextract : SubsequenceBandExtraction
      (literatureThermodynamicData hChen hChenSen μ h.beta_pos.le)) :
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
  exact finiteMixture_main_condensed_and_initial_literal_reduced μ h hChen hChenSen h5
    (remark25Contrapositive_of_band_estimates_reduced2 _ h5 hupper hextract)

/-- The all-initial-law endpoint has the same further reduction, with its
original common exponent and complete conclusion. -/
theorem finiteMixture_all_initial_spherical_of_literature_reduced2
    (μ : FiniteMixture) {β x Q : ℝ} (h : Certificate μ β x Q)
    (hChen : Chen2013FiniteParisi) (hChenSen : ChenSenFiniteGround)
    (h5 : Theorem5 (literatureThermodynamicData hChen hChenSen μ h.beta_pos.le))
    (hupper : ExpectedBandUpperApproximation
      (literatureThermodynamicData hChen hChenSen μ h.beta_pos.le))
    (hextract : SubsequenceBandExtraction
      (literatureThermodynamicData hChen hChenSen μ h.beta_pos.le)) :
    ∃ γ : ℝ, 0 < γ ∧
      SourceMixedCountCapturePackage.SphericalInitialConclusions.{u,v} μ β γ := by
  exact finiteMixture_all_initial_spherical_of_literature_reduced.{u,v}
    μ h hChen hChenSen h5
    (remark25Contrapositive_of_band_estimates_reduced2 _ h5 hupper hextract)

end SlowEquilibration.LiteratureSubagRemark25Final.Endpoints
