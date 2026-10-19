-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourceFiniteMixtureMainLiteral
public import SlowEquilibration.CSPerturbativeStability
public import SlowEquilibration.ThermalExample

/-! Source `cor:main-classes`(b), (c), (d), conditional on the five literature
interfaces. The actual canonical-minimizer contacts, the uniform perturbative
certificate, and the explicit nonconvex degree-4/12 example are packaged into
the ordinary strict one-step `Certificate` and composed with the finite-mixture
main theorem. Each class also satisfies `thm:main-initial`(i), with the same
exponent and independence only from the Hamiltonian on the sphere.

The perturbation coefficients are normalized to total mass one, as in the
corollary; the producer in fact allows total mass at most one. The cutoff is
chosen before the coefficient family and the literature hypotheses. The
nonconvex example uses the positive inverse temperature `beta`, whose square
is the manuscript's `15000 / (729 * (4 + 12 * t))`. -/

@[expose] public section
noncomputable section

namespace SlowEquilibration.SourceMainClassesLiterature

open Set MeasureTheory ProbabilityTheory Filter CrisantiSommers CSParisiMeasure
open SphericalModel SphericalTAPCertificate SphericalOrthogonalHaar
open SourceLiteratureParisi SourceLiteratureGroundState SourceLiteratureStrictTAPGap
open LiteratureSubagTAP LiteratureSubagReplicaExclusion LiteratureSubagProposition24
open SourceReductionConsumerAsymptotic SphericalOverlapExponential
open SourceFiniteMixtureMainLiteral CSPerturbative
open SphericalAging.HardSphereDynamics
open scoped Topology NNReal

set_option autoImplicit false

/-- The literal finite-mixture conclusions of `thm:main-condensed` and
`thm:main-initial`(i), with one exponent chosen before the initial-law data. -/
abbrev MainCondensedAndInitialLiteral (μ : FiniteMixture) (β : ℝ) : Prop :=
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
              (J N ω) (ν N ω) < 1-ε}) atTop (𝓝 0))

private theorem certificate_of_canonical_contacts (μ : FiniteMixture) {β x Q : ℝ}
    (hd : 4 ≤ μ.minDegree) (hβ : 0 < β)
    (hx : x ∈ Ioo (0 : ℝ) 1) (hQ : Q ∈ Ioo (0 : ℝ) 1)
    (hlaw : (canonicalMinimizer μ β).law = twoAtom x Q)
    (hvalue : CSStructure.potential μ β (canonicalMinimizer μ β).law Q = 0)
    (hderiv : deriv (CSStructure.potential μ β (canonicalMinimizer μ β).law) Q = 0)
    (hcurv : 0 < deriv (deriv
      (CSStructure.potential μ β (canonicalMinimizer μ β).law)) Q)
    (hoff : ∀ r ∈ Ioo (0 : ℝ) 1, r ≠ Q →
      0 < CSStructure.potential μ β (canonicalMinimizer μ β).law r) :
    Certificate μ β x Q := by
  rw [hlaw] at hvalue hderiv hcurv hoff
  exact ⟨hd, hβ, hx, hQ, hvalue, hderiv, hoff, hcurv⟩

/-- Source `cor:main-classes`(b): strict convexity of `ξ''⁻¹ᐟ²` on `(0,1]`
gives slow equilibration at every inverse temperature above the static
threshold, together with the same-exponent initial-law conclusions. -/
theorem convex_corollary_b_of_literature (μ : FiniteMixture)
    (hd : 4 ≤ μ.minDegree) {β : ℝ}
    (hβ : Thresholds.staticThreshold μ.xi < β)
    (hξ : StrictConvexOn ℝ (Ioc 0 1)
      (InverseSqrtCalculus.inverseSqrt (deriv (deriv μ.xi))))
    (hChen : Chen2013FiniteParisi) (hChenSen : ChenSenFiniteGround)
    (h5 : ∀ hβ₀ : 0 ≤ β,
      Theorem5 (literatureThermodynamicData hChen hChenSen μ hβ₀))
    (h25 : Remark25Contrapositive μ β)
    (h24 : ∀ q ∈ Ioo (0 : ℝ) 1, Proposition24 μ β q) :
    MainCondensedAndInitialLiteral μ β := by
  obtain ⟨x, hx, Q, hQ, hlaw, hvalue, hderiv, hcurv, hoff⟩ :=
    canonicalMinimizer_strict_oneStep μ (by omega) hβ hξ
  have h := certificate_of_canonical_contacts μ hd
    (μ.staticThreshold_pos.trans hβ) hx hQ hlaw hvalue hderiv hcurv hoff
  exact finiteMixture_main_condensed_and_initial_literal μ h hChen hChenSen
    (h5 h.beta_pos.le) h25 (h24 Q h.overlap_range)

/-- The degree-window sufficient condition in `cor:main-classes`(b), with
the actual smallest and largest supported degrees and no parity restriction. -/
theorem degree_window_corollary_b_of_literature (μ : FiniteMixture)
    (hd : 4 ≤ μ.minDegree)
    (hwindow : ((μ.minDegree : ℝ) + μ.maxDegree - 5) ^ 2 <
      6 * ((μ.minDegree : ℝ) - 2) * ((μ.maxDegree : ℝ) - 2))
    {β : ℝ} (hβ : Thresholds.staticThreshold μ.xi < β)
    (hChen : Chen2013FiniteParisi) (hChenSen : ChenSenFiniteGround)
    (h5 : ∀ hβ₀ : 0 ≤ β,
      Theorem5 (literatureThermodynamicData hChen hChenSen μ hβ₀))
    (h25 : Remark25Contrapositive μ β)
    (h24 : ∀ q ∈ Ioo (0 : ℝ) 1, Proposition24 μ β q) :
    MainCondensedAndInitialLiteral μ β := by
  obtain ⟨x, hx, Q, hQ, hlaw, hvalue, hderiv, hcurv, hoff⟩ :=
    degree_window_canonicalMinimizer_strict_oneStep μ hd hwindow hβ
  have h := certificate_of_canonical_contacts μ hd
    (μ.staticThreshold_pos.trans hβ) hx hQ hlaw hvalue hderiv hcurv hoff
  exact finiteMixture_main_condensed_and_initial_literal μ h hChen hChenSen
    (h5 h.beta_pos.le) h25 (h24 Q h.overlap_range)

/-- Source `cor:main-classes`(c): a single positive perturbation cutoff
depends only on `d,P,β` and works for every normalized nonnegative even
coefficient family. Literature interfaces are applied to each resulting
covariance after the cutoff is fixed. -/
theorem perturbative_corollary_c_of_literature (d P : ℕ)
    (hd : 4 ≤ d) (hdEven : Even d) (hdP : d < P) {β : ℝ}
    (hβ : Thresholds.staticThreshold (fun r : ℝ => r ^ d) < β) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ (b : EvenPerturbation d P), b.coeff.sum (fun _ c => c) = 1 →
        ∀ (ε : ℝ) (hε : 0 < ε), ε < ε₀ →
          let μ := b.covariance (by omega) ε hε.le
          ∀ (hChen : Chen2013FiniteParisi) (hChenSen : ChenSenFiniteGround),
            (∀ hβ₀ : 0 ≤ β,
              Theorem5 (literatureThermodynamicData hChen hChenSen μ hβ₀)) →
            Remark25Contrapositive μ β →
            (∀ q ∈ Ioo (0 : ℝ) 1, Proposition24 μ β q) →
            MainCondensedAndInitialLiteral μ β := by
  have hpure : (FiniteMixture.pure d (by omega) 1 (by positivity)).xi =
      (fun r : ℝ => r ^ d) := by
    funext r
    simp only [FiniteMixture.pure_xi, one_mul]
  have hβpure : Thresholds.staticThreshold
      (FiniteMixture.pure d (by omega) 1 (by positivity)).xi < β := by
    simpa only [hpure] using hβ
  obtain ⟨ε₀, hε₀, hcert⟩ := small_even_perturbation_certificate_uniform hd hdEven
    hdP.le β hβpure (τ := 1) (by norm_num)
  refine ⟨ε₀, hε₀.1, ?_⟩
  intro b _ ε hε hsmall
  dsimp only
  intro hChen hChenSen h5 h25 h24
  obtain ⟨x, hx, Q, hQ, hlaw, hvalue, hderiv, hcurv, hoff, _, _⟩ :=
    hcert b ε hε.le hsmall
  let μ := b.covariance (by omega : 3 ≤ d) ε hε.le
  have hdegree : 4 ≤ μ.minDegree := by
    dsimp only [μ]
    rw [b.covariance_minDegree]
    exact hd
  have hβpos : 0 < β :=
    (FiniteMixture.pure d (by omega) 1 (by positivity)).staticThreshold_pos.trans hβpure
  have h := certificate_of_canonical_contacts μ hdegree hβpos
    hx hQ hlaw hvalue hderiv hcurv hoff
  exact finiteMixture_main_condensed_and_initial_literal μ h hChen hChenSen
    (h5 h.beta_pos.le) h25 (h24 Q h.overlap_range)

private theorem nonconvex_certificate :
    Certificate NonconvexCertificate.exampleMixture NonconvexCertificate.beta
      NonconvexCertificate.x NonconvexCertificate.Q := by
  obtain ⟨hd, hβ, hx, hQ, _⟩ := NonconvexCertificate.thermal_example
  have hxi : NonconvexCertificate.exampleMixture.xi = NonconvexCertificate.xi :=
    funext NonconvexCertificate.exampleMixture_xi
  have hpotential : ∀ r ∈ Ioo (0 : ℝ) 1,
      CSStructure.potential NonconvexCertificate.exampleMixture NonconvexCertificate.beta
        (twoAtom NonconvexCertificate.x NonconvexCertificate.Q) r =
        NonconvexCertificate.V r := by
    intro r hr
    change -firstVariation NonconvexCertificate.beta
      NonconvexCertificate.exampleMixture.xi NonconvexCertificate.exampleLaw.law r = _
    rw [hxi, NonconvexCertificate.exampleLaw_firstVariation ⟨hr.1.le, hr.2⟩, neg_neg]
  have heq : CSStructure.potential NonconvexCertificate.exampleMixture
      NonconvexCertificate.beta (twoAtom NonconvexCertificate.x NonconvexCertificate.Q)
      =ᶠ[𝓝 NonconvexCertificate.Q] NonconvexCertificate.V := by
    filter_upwards [Ioo_mem_nhds hQ.1 hQ.2] with r hr
    exact hpotential r hr
  obtain ⟨hvalue, hderiv, hoff, hcurv⟩ := NonconvexCertificate.strict_one_step_certificate
  refine ⟨by omega, hβ, hx, hQ, ?_, ?_, ?_, ?_⟩
  · rw [hpotential _ hQ]
    exact hvalue
  · rw [heq.deriv_eq]
    exact hderiv
  · intro r hr hne
    rw [hpotential r hr]
    exact hoff r hr hne
  · rw [heq.deriv.deriv_eq]
    exact hcurv

/-- Source `cor:main-classes`(d): the actual covariance `r⁴ + b r¹²`
at the explicit positive inverse temperature, with `Q=9/10`, `x=5/9`.
This example has nonconvex inverse square-root curvature. -/
theorem nonconvex_corollary_d_of_literature
    (hChen : Chen2013FiniteParisi) (hChenSen : ChenSenFiniteGround)
    (h5 : ∀ hβ₀ : 0 ≤ NonconvexCertificate.beta,
      Theorem5 (literatureThermodynamicData hChen hChenSen
        NonconvexCertificate.exampleMixture hβ₀))
    (h25 : Remark25Contrapositive
      NonconvexCertificate.exampleMixture NonconvexCertificate.beta)
    (h24 : ∀ q ∈ Ioo (0 : ℝ) 1,
      Proposition24 NonconvexCertificate.exampleMixture NonconvexCertificate.beta q) :
    MainCondensedAndInitialLiteral
      NonconvexCertificate.exampleMixture NonconvexCertificate.beta := by
  have h := nonconvex_certificate
  exact finiteMixture_main_condensed_and_initial_literal _ h hChen hChenSen
    (h5 h.beta_pos.le) h25 (h24 _ h.overlap_range)

end SlowEquilibration.SourceMainClassesLiterature
