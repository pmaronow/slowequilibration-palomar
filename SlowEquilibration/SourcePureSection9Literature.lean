-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourceLiteraturePhysicalNormQ
public import SlowEquilibration.PureReplicaMeanEnergyAssembly
public import SlowEquilibration.PurePhysicalHighEnergyRelocation
public import SlowEquilibration.SourcePureCaptureLiteralConsumer
public import SlowEquilibration.SourcePureCaptureMaximumUpper

/-! Manuscript Section 9: literal fixed and microscopic band capture, coarse
cap cover, and vanishing-deficit diagonal localization, assembled from the
explicit Chen, Chen–Sen, Subag Theorem 5, Remark 25 and Proposition 24
interfaces. Theorem 10 is not needed for these pure-model conclusions.
The certificate can be obtained above the static threshold by
`SphericalTAPCertificate.pure_certificate_above_static`. -/

@[expose] public section
noncomputable section

namespace SlowEquilibration.SourcePureSection9Literature

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

set_option autoImplicit false

/-- Both parts of `thm:pc-capture`, with the prescribed radial window and
the manuscript's order of fixed and microscopic parameters. -/
theorem pure_capture_of_cited_theorems
    (hChen : Chen2013FiniteParisi) (hChenSen : ChenSenFiniteGround)
    (p : ℕ) (hp : 4 ≤ p) {β x Q : ℝ}
    (h : Certificate (FiniteMixture.pure p (by omega) 1 (by positivity)) β x Q)
    (h5 : Theorem5 (literatureThermodynamicData hChen hChenSen
      (FiniteMixture.pure p (by omega) 1 (by positivity)) h.beta_pos.le))
    (h25 : Remark25Contrapositive
      (FiniteMixture.pure p (by omega) 1 (by positivity)) β)
    (h24 : Proposition24 (FiniteMixture.pure p (by omega) 1 (by positivity)) β Q)
    (U : Set ℝ)
    (hU : markK (FiniteMixture.pure p (by omega) 1 (by positivity)) β Q ∈ interior U) :
    (∃ b₀ : ℝ, b₀ ∈ Ioo (0 : ℝ) (Real.sqrt Q) ∧
      ∀ b : ℝ, b ∈ Ioc (0 : ℝ) b₀ → Tendsto
        (fun M : ℝ => Filter.limsup (pureConsumerUncovered p hp β Q M b U) atTop)
        atTop (𝓝 (0 : ℝ))) ∧
    (∀ ε : ℝ, 0 < ε → ∃ M₀ w₀ : ℝ, 0 < M₀ ∧ 0 < w₀ ∧
      ∀ M w : ℝ, M₀ ≤ M → w₀ ≤ w →
        Filter.limsup (fun n => pureConsumerUncovered p hp β Q M
          (w / Real.sqrt (n+2 : ℕ)) U n) atTop ≤ ε) :=
  pure_consumer_capture_of_three_physical_inputs p hp h U hU
    (physicalDirectingNormQ_of_cited_theorems hChen hChenSen h h5 h25)
    (pure_physicalReplicaMeanEnergy_of_literature p hp h hChen h24)
    (pure_physicalHighEnergyRelocation p hp)

/-- `prop:pc-coarse`: every fixed positive energy deficit covers Gibbs
mass by caps at any latitude strictly below the contact latitude. -/
theorem pure_coarse_cover_of_cited_theorems
    (hChen : Chen2013FiniteParisi) (hChenSen : ChenSenFiniteGround)
    (p : ℕ) (hp : 4 ≤ p) {β x Q : ℝ}
    (h : Certificate (FiniteMixture.pure p (by omega) 1 (by positivity)) β x Q)
    (h5 : Theorem5 (literatureThermodynamicData hChen hChenSen
      (FiniteMixture.pure p (by omega) 1 (by positivity)) h.beta_pos.le))
    (h25 : Remark25Contrapositive
      (FiniteMixture.pure p (by omega) 1 (by positivity)) β)
    (h24 : Proposition24 (FiniteMixture.pure p (by omega) 1 (by positivity)) β Q) :
    ∀ a : ℝ, a < Real.sqrt Q → ∀ τ : ℝ, 0 < τ →
      Tendsto (fun n => expectedUncoveredGibbsMass n
        (FiniteMixture.pure p (by omega) 1 (by positivity)) β a
        (pureEnergyConstant p (by omega)) τ) atTop (𝓝 (0 : ℝ)) := by
  intro a ha
  exact physical_coarse_cover_of_three_physical_inputs _ β h.overlap_range ha
    (physicalDirectingNormQ_of_cited_theorems hChen hChenSen h h5 h25)
    (pure_physicalReplicaMeanEnergy_of_literature p hp h hChen h24)
    (pure_physicalHighEnergyRelocation p hp)

/-- `lem:pc-diagonal`: one deterministic deficit tends to zero, has the
logarithmic floor, covers Gibbs mass, and localizes every high-energy point
on one measurable event whose probability tends to one. -/
theorem pure_diagonal_localization_of_cited_theorems
    (hChen : Chen2013FiniteParisi) (hChenSen : ChenSenFiniteGround)
    (p : ℕ) (hp : 4 ≤ p) {β x Q : ℝ}
    (h : Certificate (FiniteMixture.pure p (by omega) 1 (by positivity)) β x Q)
    (h5 : Theorem5 (literatureThermodynamicData hChen hChenSen
      (FiniteMixture.pure p (by omega) 1 (by positivity)) h.beta_pos.le))
    (h25 : Remark25Contrapositive
      (FiniteMixture.pure p (by omega) 1 (by positivity)) β)
    (h24 : Proposition24 (FiniteMixture.pure p (by omega) 1 (by positivity)) β Q)
    (a : ℝ) (ha : a < Real.sqrt Q) :
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
  · exact pure_coarse_cover_of_cited_theorems hChen hChenSen p hp h h5 h25 h24 a ha
  · exact pure_original_source_maximum_upper_tightness p hp h

end SlowEquilibration.SourcePureSection9Literature
