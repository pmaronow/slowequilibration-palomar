-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourceMixedCountCapturePackage

/-!
# The subsequence reduction in Subag's Remark 25

This file proves the probability-theoretic reduction in Remark 25 and
footnote 4 to Definition 2 of Subag, arXiv:1804.10576v6. Failure of every
fixed exponential bound supplies a single increasing dimension sequence
on which the literal annealed replica probabilities are positive and have
zero logarithmic rate, simultaneously for every count and tolerance.

The remaining physical steps are stated explicitly as
`ExpectedBandUpperApproximation` (the upper half of Proposition 4) and
`SubsequenceBandExtraction` (the conditioning and concentration argument
in Section 4). Neither is proved here. They imply
`SubsequenceTAPLowerBound`, which together with the existing Theorem 5 and
Proposition 24 interfaces implies exactly `Remark25Contrapositive`.
The downstream theorems ending in `_reduced` are conditional reductions,
not unconditional proofs of those endpoints.
-/

@[expose] public section
noncomputable section

namespace SlowEquilibration.LiteratureSubagRemark25Proof

open MeasureTheory ProbabilityTheory Filter Set
open SphericalModel LiteratureSubagPhysicalDefinitions LiteratureSubagTAP
open LiteratureSubagReplicaExclusion LiteratureSubagProposition24
open scoped Topology

set_option autoImplicit false

/-- The positivity-aware Definition 2 along one common dimension sequence.
The count and tolerance are fixed before taking the subsequence limit. -/
def MultiSamplableAlong (μ : FiniteMixture) (β q : ℝ) (φ : ℕ → ℕ) : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∀ ρ : ℝ, 0 < ρ →
    (∀ᶠ n : ℕ in atTop, 0 < expectedOverlapBlockProbability (φ n) k μ β q ρ) ∧
    Tendsto (fun n : ℕ =>
      Real.log (expectedOverlapBlockProbability (φ n) k μ β q ρ) / (φ n : ℝ))
      atTop (𝓝 (0 : ℝ))

/-- Every count and tolerance exceeds every fixed exponential threshold
in arbitrarily large dimensions. Strict inequality is intentional: this
is precisely the negation of the eventual upper bound in Remark 25. -/
def SubexponentialRecurrence (μ : FiniteMixture) (β q : ℝ) : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∀ ρ : ℝ, 0 < ρ → ∀ c : ℝ, 0 < c →
    ∃ᶠ N : ℕ in atTop,
      Real.exp (-c * (N : ℝ)) < expectedOverlapBlockProbability N k μ β q ρ

private theorem block_probability_le_one (N k : ℕ) (μ : FiniteMixture)
    (β q ρ : ℝ) : expectedOverlapBlockProbability N k μ β q ρ ≤ 1 := by
  exact measureReal_le_one

private theorem block_probability_mono_tolerance {N k : ℕ} (μ : FiniteMixture)
    (β q : ℝ) {ρ σ : ℝ} (hρσ : ρ ≤ σ) :
    expectedOverlapBlockProbability N k μ β q ρ ≤
      expectedOverlapBlockProbability N k μ β q σ := by
  unfold expectedOverlapBlockProbability
  exact measureReal_mono (fun v hv i j hij => (hv i j hij).trans_le hρσ)

private theorem block_probability_succ_le (N k : ℕ) (μ : FiniteMixture)
    (β q ρ : ℝ) : expectedOverlapBlockProbability N (k + 1) μ β q ρ ≤
      expectedOverlapBlockProbability N k μ β q ρ := by
  have hmeas : MeasurableSet {σ : Fin k → Vector N |
      ∀ i j, i ≠ j → |overlap (σ i) (σ j) - q| < ρ} := by
    simp only [Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro i
    apply MeasurableSet.iInter
    intro j
    apply MeasurableSet.iInter
    intro _
    exact (isOpen_lt (by unfold overlap; fun_prop) continuous_const).measurableSet
  have hprefix :=
    (GaussianReplicaKernel.initial_hasLaw (disorderLaw N μ.maxDegree)
      (allDimensionGibbsKernel (mixtureCoefficients μ) β) k).measureReal_eq hmeas
  unfold expectedOverlapBlockProbability
  calc
    _ ≤ (GaussianReplicaKernel.law (disorderLaw N μ.maxDegree)
        (allDimensionGibbsKernel (mixtureCoefficients μ) β) (k + 1)).real
      {σ : Fin (k + 1) → Vector N | ∀ i j : Fin k,
        i ≠ j → |overlap (σ i.castSucc) (σ j.castSucc) - q| < ρ} := by
      exact measureReal_mono (fun σ hσ i j hij =>
        hσ i.castSucc j.castSucc (fun heq => hij (Fin.castSucc_inj.mp heq)))
    _ = _ := by simpa only [GaussianReplicaKernel.initial] using hprefix

private theorem block_probability_antitone_count (N : ℕ) (μ : FiniteMixture)
    (β q ρ : ℝ) : Antitone (fun k => expectedOverlapBlockProbability N k μ β q ρ) :=
  antitone_nat_of_succ_le (fun k => block_probability_succ_le N k μ β q ρ)

/-- The common-subsequence step implicit in Remark 25. The diagonal uses
count `n+1`, tolerance `1/(n+1)`, and logarithmic loss `1/(n+1)`.
Prefix consistency of the actual IID replica law handles every fixed count. -/
theorem subsequence_multisamplable_of_recurrence
    {μ : FiniteMixture} {β q : ℝ} (hrec : SubexponentialRecurrence μ β q) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ MultiSamplableAlong μ β q φ := by
  have hdiagonal (n : ℕ) : ∃ᶠ N : ℕ in atTop,
      0 < N ∧ Real.exp (-(1 / ((n : ℝ) + 1)) * (N : ℝ)) <
        expectedOverlapBlockProbability N (n + 1) μ β q (1 / ((n : ℝ) + 1)) := by
    have hpos : 0 < 1 / ((n : ℝ) + 1) := by positivity
    exact ((hrec (n + 1) (by omega) _ hpos _ hpos).and_eventually
      (eventually_gt_atTop 0)).mono (fun _ h => ⟨h.2, h.1⟩)
  obtain ⟨φ, hφ, hdiag⟩ := extraction_forall_of_frequently hdiagonal
  refine ⟨φ, hφ, ?_⟩
  intro k _hk ρ hρ
  have hinv : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 (0 : ℝ)) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hsmall : ∀ᶠ n : ℕ in atTop, 1 / ((n : ℝ) + 1) ≤ ρ :=
    (hinv.eventually (gt_mem_nhds hρ)).mono (fun _ h => h.le)
  have hbound : ∀ᶠ n : ℕ in atTop,
      Real.exp (-(1 / ((n : ℝ) + 1)) * (φ n : ℝ)) <
        expectedOverlapBlockProbability (φ n) k μ β q ρ := by
    filter_upwards [eventually_ge_atTop k, hsmall] with n hkn hnρ
    exact (hdiag n).2.trans_le
      ((block_probability_antitone_count (φ n) μ β q _ (by omega : k ≤ n + 1)).trans
        (block_probability_mono_tolerance μ β q hnρ))
  have hp : ∀ᶠ n : ℕ in atTop,
      0 < expectedOverlapBlockProbability (φ n) k μ β q ρ :=
    hbound.mono (fun n hn => (Real.exp_pos _).trans hn)
  refine ⟨hp, ?_⟩
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (by simpa only [neg_zero] using hinv.neg) tendsto_const_nhds
  · filter_upwards [hbound, hp] with n hn hpn
    have hN : (0 : ℝ) < φ n := by exact_mod_cast (hdiag n).1
    have hlog := Real.log_le_log (Real.exp_pos _) hn.le
    rw [Real.log_exp] at hlog
    exact (le_div_iff₀ hN).mpr hlog
  · filter_upwards [hp] with n hn
    exact div_nonpos_of_nonpos_of_nonneg
      (Real.log_nonpos hn.le (block_probability_le_one (φ n) k μ β q ρ))
      (Nat.cast_nonneg _)

/-- Positivity prevents `Real.log 0 = 0` from creating spurious recurrent
dimensions. A zero rate along a genuine subsequence exceeds every fixed
exponential threshold infinitely often on the original dimension sequence. -/
theorem recurrence_of_subsequence_multisamplable
    {μ : FiniteMixture} {β q : ℝ} {φ : ℕ → ℕ} (hφ : StrictMono φ)
    (hm : MultiSamplableAlong μ β q φ) : SubexponentialRecurrence μ β q := by
  intro k hk ρ hρ c hc
  obtain ⟨hp, hlim⟩ := hm k hk ρ hρ
  have hrate : ∀ᶠ n : ℕ in atTop,
      -c < Real.log (expectedOverlapBlockProbability (φ n) k μ β q ρ) / (φ n : ℝ) :=
    hlim.eventually (lt_mem_nhds (neg_neg_of_pos hc))
  rw [frequently_atTop']
  intro M
  obtain ⟨n, hnpos, hnM, hpn, hrn⟩ :=
    ((hφ.tendsto_atTop.eventually (eventually_gt_atTop 0)).and
      ((hφ.tendsto_atTop.eventually (eventually_gt_atTop M)).and
        (hp.and hrate))).exists
  refine ⟨φ n, hnM, ?_⟩
  have hN : (0 : ℝ) < φ n := by exact_mod_cast hnpos
  have hlog : -c * (φ n : ℝ) <
      Real.log (expectedOverlapBlockProbability (φ n) k μ β q ρ) :=
    (lt_div_iff₀ hN).mp hrn
  exact (Real.lt_log_iff_exp_lt hpn).mp hlog

/-- Exact analytic characterization of the interface. The remaining
physical content is precisely the upgrade from one common subsequence to
the full sequence; no positivity or diagonal-selection hypothesis is needed. -/
theorem remark25Contrapositive_iff_subsequence_upgrade
    (μ : FiniteMixture) (β : ℝ) :
    Remark25Contrapositive μ β ↔
      0 < β ∧ ∀ q : ℝ, q ∈ Ioo (0 : ℝ) 1 →
        ∀ φ : ℕ → ℕ, StrictMono φ →
          MultiSamplableAlong μ β q φ → MultiSamplable μ β q := by
  classical
  constructor
  · intro h25
    refine ⟨h25.1, ?_⟩
    intro q hq φ hφ hm
    by_contra hn
    obtain ⟨k, hk, ρ, hρ, c, hc, hb⟩ := h25.2 q hq hn
    obtain ⟨N, hN, hN'⟩ :=
      ((recurrence_of_subsequence_multisamplable hφ hm k hk ρ hρ c hc).and_eventually
        hb).exists
    exact (not_lt_of_ge hN') hN
  · rintro ⟨hβ, hup⟩
    refine ⟨hβ, ?_⟩
    intro q hq hn
    by_contra hnot
    have hrec : SubexponentialRecurrence μ β q := by
      intro k hk ρ hρ c hc
      have hnot' : ¬ ∀ᶠ N : ℕ in atTop,
          expectedOverlapBlockProbability N k μ β q ρ ≤ Real.exp (-c * (N : ℝ)) := by
        intro hb
        exact hnot ⟨k, hk, ρ, hρ, c, hc, hb⟩
      simpa only [not_eventually, not_le] using hnot'
    obtain ⟨φ, hφ, hm⟩ := subsequence_multisamplable_of_recurrence hrec
    exact hn (hup q hq φ hφ hm)

/-- The unproved physical step in Section 4, (4.3)--(4.5), followed by
Remark 25's passage from a subsequence inequality to the full limits.
Proposition 24 is the actual repository concentration interface. Proving
this statement also requires the replicated-band limit from Proposition 4
and the replica conditioning and center geometry; those are not axioms here. -/
def SubsequenceTAPLowerBound {μ : FiniteMixture} {β : ℝ}
    (D : ThermodynamicData μ β) : Prop :=
  ∀ q : ℝ, q ∈ Ioo (0 : ℝ) 1 → Proposition24 μ β q →
    ∀ φ : ℕ → ℕ, StrictMono φ → MultiSamplableAlong μ β q φ →
      D.pressure ≤ tapValue D q

/-- The needed upper half of Proposition 4, at fixed parameters before the
dimension limit. The residual is the actual quenched residual value in
`D`, rather than the larger annealed residual bound. This remains unproved.
Zero-volume bands are excluded explicitly, as in the repository's existing
annealed expected-band estimate. -/
def ExpectedBandUpperApproximation {μ : FiniteMixture} {β : ℝ}
    (D : ThermodynamicData μ β) : Prop :=
  ∀ q : ℝ, q ∈ Ioo (0 : ℝ) 1 → ∀ ε : ℝ, 0 < ε →
    ∃ δ : ℝ, 0 < δ ∧ ∃ ρ : ℝ, 0 < ρ ∧ ∃ K : ℕ,
      ∀ k : ℕ, K ≤ k → ∀ᶠ N : ℕ in atTop,
        ∀ m : Vector N, ‖m‖ ^ 2 = (N : ℝ) * q →
          0 < (Measure.pi (fun _ : Fin k => sphereLaw N)) (ReplicatedBand k q δ ρ m) →
          expectedReplicatedBandPressure k μ β q δ ρ m ≤
            Real.log (1 - q) / 2 + D.residual q + ε

/-- The finite-parameter extraction needed from Section 4, (4.3)--(4.5).
For arbitrarily large fixed replica counts there must be recurrent
dimensions with a positive-volume band and a lower bound for its expected
pressure. This is a separate unproved hypothesis of the reduction, not an
assertion that Proposition 24 by itself supplies replica conditioning. -/
def SubsequenceBandExtraction {μ : FiniteMixture} {β : ℝ}
    (D : ThermodynamicData μ β) : Prop :=
  ∀ q : ℝ, q ∈ Ioo (0 : ℝ) 1 → Proposition24 μ β q →
    ∀ φ : ℕ → ℕ, StrictMono φ → MultiSamplableAlong μ β q φ →
      ∀ ε δ ρ : ℝ, 0 < ε → 0 < δ → 0 < ρ → ∀ K : ℕ,
        ∃ k : ℕ, max K 1 ≤ k ∧ ∃ᶠ n : ℕ in atTop,
          ∃ m : Vector (φ n), ‖m‖ ^ 2 = (φ n : ℝ) * q ∧
            0 < (Measure.pi (fun _ : Fin k => sphereLaw (φ n)))
              (ReplicatedBand k q δ ρ m) ∧
            D.pressure - β * D.ground q - ε ≤
              expectedReplicatedBandPressure k μ β q δ ρ m

/-- Combine the recurrent expected-band lower bound with the full-sequence
upper approximation. The intersection is taken before choosing a center,
so the center can depend on the recurrent dimension. -/
theorem subsequence_tap_lower_bound_of_band_estimates
    {μ : FiniteMixture} {β : ℝ} (D : ThermodynamicData μ β)
    (hupper : ExpectedBandUpperApproximation D)
    (hextract : SubsequenceBandExtraction D) : SubsequenceTAPLowerBound D := by
  intro q hq h24 φ hφ hm
  apply le_of_forall_pos_le_add
  intro ε hε
  have hhalf : 0 < ε / 2 := by positivity
  obtain ⟨δ, hδ, ρ, hρ, K, hu⟩ := hupper q hq (ε / 2) hhalf
  obtain ⟨k, hk, hl⟩ := hextract q hq h24 φ hφ hm (ε / 2) δ ρ hhalf hδ hρ K
  have hkK : K ≤ k := (le_max_left K 1).trans hk
  obtain ⟨n, hn, hn'⟩ := (hl.and_eventually
    (hφ.tendsto_atTop.eventually (hu k hkK))).exists
  obtain ⟨m, hnorm, hvol, hband⟩ := hn
  have hbound := hn' m hnorm hvol
  unfold tapValue
  linarith

/-- A completely proved reduction of the exact interface to the one-sided
physical subsequence inequality. The full-sequence TAP characterization
supplies the reconstruction direction of Section 4. -/
theorem remark25Contrapositive_of_subsequence_tap_lower_bound
    {μ : FiniteMixture} {β : ℝ} (D : ThermodynamicData μ β)
    (h5 : Theorem5 D)
    (h24 : ∀ q : ℝ, q ∈ Ioo (0 : ℝ) 1 → Proposition24 μ β q)
    (hlower : SubsequenceTAPLowerBound D) : Remark25Contrapositive μ β := by
  apply (remark25Contrapositive_iff_subsequence_upgrade μ β).mpr
  refine ⟨h5.1, ?_⟩
  intro q hq φ hφ hm
  apply (h5.2 q hq).1.mp
  exact le_antisymm (hlower q hq (h24 q hq) φ hφ hm) (h5.2 q hq).2

/-- Reduction of the exact Remark 25 interface to two explicit physical
band estimates, retaining the actual Proposition 24 as an intermediate
hypothesis. No new literature statement is asserted as a theorem here. -/
theorem remark25Contrapositive_of_band_estimates
    {μ : FiniteMixture} {β : ℝ} (D : ThermodynamicData μ β)
    (h5 : Theorem5 D)
    (h24 : ∀ q : ℝ, q ∈ Ioo (0 : ℝ) 1 → Proposition24 μ β q)
    (hupper : ExpectedBandUpperApproximation D)
    (hextract : SubsequenceBandExtraction D) : Remark25Contrapositive μ β :=
  remark25Contrapositive_of_subsequence_tap_lower_bound D h5 h24
    (subsequence_tap_lower_bound_of_band_estimates D hupper hextract)

end SlowEquilibration.LiteratureSubagRemark25Proof

namespace SlowEquilibration.SourceFiniteMixtureMainLiteral

open MeasureTheory ProbabilityTheory Filter Set
open SphericalModel SphericalTAPCertificate SphericalOrthogonalHaar
open SourceLiteratureParisi SourceLiteratureGroundState SourceLiteratureStrictTAPGap
open LiteratureSubagTAP LiteratureSubagProposition24 LiteratureSubagRemark25Proof
open SourceReductionConsumerAsymptotic SphericalOverlapExponential
open SphericalAging.HardSphereDynamics
open scoped Topology

set_option autoImplicit false

/-- Conditional reduction of the literal main endpoint to the two unproved
physical band estimates. Concentration is required at every positive
overlap. The other original literature inputs remain visible. -/
theorem finiteMixture_main_condensed_and_initial_literal_reduced
    (μ : FiniteMixture) {β x Q : ℝ}
    (h : Certificate μ β x Q)
    (hChen : Chen2013FiniteParisi)
    (hChenSen : ChenSenFiniteGround)
    (h5 : Theorem5
      (literatureThermodynamicData hChen hChenSen μ h.beta_pos.le))
    (h24 : ∀ q : ℝ, q ∈ Ioo (0 : ℝ) 1 → Proposition24 μ β q)
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
  exact finiteMixture_main_condensed_and_initial_literal μ h hChen hChenSen h5
    (remark25Contrapositive_of_band_estimates _ h5 h24 hupper hextract)
    (h24 Q h.overlap_range)

end SlowEquilibration.SourceFiniteMixtureMainLiteral

namespace SlowEquilibration.SourceMixedCountCapturePackage

open Set
open SphericalModel SphericalTAPCertificate
open SourceLiteratureParisi SourceLiteratureGroundState SourceLiteratureStrictTAPGap
open LiteratureSubagTAP LiteratureSubagProposition24 LiteratureSubagRemark25Proof

set_option autoImplicit false

universe u v

/-- The corresponding conditional reduction of all spherical initial-law
conclusions, with the same common exponent as the original endpoint. -/
theorem finiteMixture_all_initial_spherical_of_literature_reduced
    (μ : FiniteMixture) {β x Q : ℝ} (h : Certificate μ β x Q)
    (hChen : Chen2013FiniteParisi) (hChenSen : ChenSenFiniteGround)
    (h5 : Theorem5 (literatureThermodynamicData hChen hChenSen μ h.beta_pos.le))
    (h24 : ∀ q : ℝ, q ∈ Ioo (0 : ℝ) 1 → Proposition24 μ β q)
    (hupper : ExpectedBandUpperApproximation
      (literatureThermodynamicData hChen hChenSen μ h.beta_pos.le))
    (hextract : SubsequenceBandExtraction
      (literatureThermodynamicData hChen hChenSen μ h.beta_pos.le)) :
    ∃ γ : ℝ, 0 < γ ∧ SphericalInitialConclusions.{u,v} μ β γ := by
  exact finiteMixture_all_initial_spherical_of_literature μ h hChen hChenSen h5
    (remark25Contrapositive_of_band_estimates _ h5 h24 hupper hextract)
    (h24 Q h.overlap_range)

end SlowEquilibration.SourceMixedCountCapturePackage
