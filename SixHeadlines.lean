-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.LiteratureSubagSlabTails
public import SlowEquilibration.LiteratureSubagLemma22Full
public import SlowEquilibration.SphericalGeneralMemory
public import SlowEquilibration.SphericalGeneralPlateau
public import SlowEquilibration.SphericalInfiniteCuspDifferential

/-! The active manuscript surface: Theorem 1.2, Corollary 1.3 and
Theorems 1.4–1.7. Other imported declarations are proof infrastructure.
Chen’s finite-mixture Parisi formula is the only literature premise in
Theorem 1.2, Corollary 1.3 and Theorem 1.4. Universal pressure lower tails
are proved internally. Theorems 1.5–1.7 have no literature premise.
Historical Challenge/Solution surfaces are not active results.
-/

@[expose] public section
noncomputable section
namespace SlowEquilibration.SixHeadlines

open Set MeasureTheory ProbabilityTheory Filter
open SphericalModel SphericalTAPCertificate SphericalOrthogonalHaar
open SourceLiteratureParisi LiteratureSubagBandLowerComplete
open SourceReductionConsumerAsymptotic SphericalOverlapExponential
open SourceFiniteMixtureMainLiteral SourceMixedCountCapturePackage
open SphericalAging.HardSphereDynamics
open CSPerturbative
open scoped Topology NNReal
universe u v

/-- The uniform-start interval separation appearing in Theorem 1.2. -/
def UniformConclusions (μ : FiniteMixture) (β : ℝ) : Prop :=
  ∃ γ : ℝ, 0 < γ ∧ uniformSeparationInProbability μ β
    (fun N => exponentialGridHorizon γ N)

/-- Theorem 1.2: the physical interval distance tends to one. -/
theorem theorem_1_2 (μ : FiniteMixture) {β x Q : ℝ}
    (h : Certificate μ β x Q) (hChen : Chen2013FiniteParisi) :
    UniformConclusions μ β := by
  obtain ⟨γ, hγ, _, hsep, _⟩ :=
    LiteratureSubagSlabTails.finiteMixture_main_condensed_and_initial_literal_of_chen_and_lemma22
      μ h hChen LiteratureSubagLemma22Full.universalPressureLowerTails
  exact ⟨γ, hγ, hsep⟩

private theorem uniform_of_main {μ : FiniteMixture} {β : ℝ}
    (h : SourceMainClassesLiterature.MainCondensedAndInitialLiteral μ β) :
    UniformConclusions μ β := by
  obtain ⟨γ, hγ, _, hsep, _⟩ := h
  exact ⟨γ, hγ, hsep⟩

/-- Corollary 1.3(a), every pure degree at least four. -/
theorem corollary_1_3_a (p : ℕ) (hp : 4 ≤ p) {β : ℝ}
    (hβ : Thresholds.staticThreshold (fun r : ℝ => r ^ p) < β)
    (hChen : Chen2013FiniteParisi) :
    UniformConclusions (FiniteMixture.pure p (by omega) 1 (by positivity)) β := by
  obtain ⟨γ, hγ, hsep, _⟩ :=
    LiteratureSubagSlabTails.pure_corollary_a_all_initial_of_chen_and_lemma22.{0,0}
      p hp hβ hChen LiteratureSubagLemma22Full.universalPressureLowerTails
  exact ⟨γ, hγ, hsep⟩

/-- Corollary 1.3(b), the strict convexity criterion. -/
theorem corollary_1_3_b
    (μ : FiniteMixture)
    (hd : 4 ≤ μ.minDegree)
    {β : ℝ}
    (hβ : Thresholds.staticThreshold μ.xi < β)
    (hξ : StrictConvexOn ℝ (Ioc 0 1)
      (InverseSqrtCalculus.inverseSqrt (deriv (deriv μ.xi))))
    (hChen : Chen2013FiniteParisi) :
    UniformConclusions μ β :=
  uniform_of_main (LiteratureSubagSlabTails.convex_corollary_b_of_chen_and_lemma22 μ hd hβ hξ hChen LiteratureSubagLemma22Full.universalPressureLowerTails)

/-- The degree-window clause of Corollary 1.3(b). -/
theorem corollary_1_3_b_degree_window
    (μ : FiniteMixture)
    (hd : 4 ≤ μ.minDegree)
    (hwindow : ((μ.minDegree : ℝ) + μ.maxDegree - 5) ^ 2 <
      6 * ((μ.minDegree : ℝ) - 2) * ((μ.maxDegree : ℝ) - 2))
    {β : ℝ}
    (hβ : Thresholds.staticThreshold μ.xi < β)
    (hChen : Chen2013FiniteParisi) :
    UniformConclusions μ β :=
  uniform_of_main (LiteratureSubagSlabTails.degree_window_corollary_b_of_chen_and_lemma22 μ hd hwindow hβ hChen LiteratureSubagLemma22Full.universalPressureLowerTails)

/-- The degrees four through eleven clause of Corollary 1.3(b). -/
theorem corollary_1_3_b_support
    (μ : FiniteMixture)
    (hsupport : ∀ p ∈ μ.coeff.support, p ∈ Finset.Icc 4 11)
    {β : ℝ}
    (hβ : Thresholds.staticThreshold μ.xi < β)
    (hChen : Chen2013FiniteParisi) :
    UniformConclusions μ β :=
  uniform_of_main (LiteratureSubagSlabTails.support_four_through_eleven_corollary_b_of_chen_and_lemma22 μ hsupport hβ hChen LiteratureSubagLemma22Full.universalPressureLowerTails)

/-- Corollary 1.3(c), the common perturbation cutoff. -/
theorem corollary_1_3_c (d P : ℕ)
    (hd : 4 ≤ d) (hdEven : Even d) (hdP : d < P) {β : ℝ}
    (hβ : Thresholds.staticThreshold (fun r : ℝ => r ^ d) < β)
    (hChen : Chen2013FiniteParisi) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ (b : EvenPerturbation d P), b.coeff.sum (fun _ c => c) = 1 →
        ∀ (ε : ℝ) (hε : 0 < ε), ε < ε₀ →
          let μ := b.covariance (by omega) ε hε.le
          UniformConclusions μ β := by
  obtain ⟨ε₀, hε₀, hresult⟩ :=
    LiteratureSubagSlabTails.perturbative_corollary_c_of_chen_and_lemma22
      d P hd hdEven hdP hβ hChen LiteratureSubagLemma22Full.universalPressureLowerTails
  exact ⟨ε₀, hε₀, fun b hb ε hε hsmall => uniform_of_main (hresult b hb ε hε hsmall)⟩

/-- Corollary 1.3(d), the explicit degree-four/twelve example. -/
theorem corollary_1_3_d
    (hChen : Chen2013FiniteParisi) :
    UniformConclusions
      NonconvexCertificate.exampleMixture NonconvexCertificate.beta :=
  uniform_of_main (LiteratureSubagSlabTails.nonconvex_corollary_d_of_chen_and_lemma22 hChen LiteratureSubagLemma22Full.universalPressureLowerTails)

/-- The three clauses of Theorem 1.4, at one common exponent.
The final information-theoretic corollary in the historical package is
intentionally omitted from this active predicate. -/
def InitialConclusions (μ : FiniteMixture) (β γ : ℝ) : Prop :=
  let T := fun N => exponentialGridHorizon γ N
  VaryingConvergesInProbability (fun n => disorderLaw (n+2) μ.maxDegree)
    (fun n => originalUniformIntervalDistance μ β (T (n+2))) (fun _ _ => 1) ∧
  uniformSeparationInProbability μ β T ∧
  (∀ ε : ℝ, 0 < ε → Tendsto (uniformPrescribedFailure μ β T ε) atTop (𝓝 0)) ∧
  (∀ (Ω : ℕ → Type) [∀ N, MeasurableSpace (Ω N)]
      (P : ∀ N, Measure (Ω N)) [∀ N, IsProbabilityMeasure (P N)]
      (J : ∀ N, Ω N → Disorder N μ.maxDegree)
      (ν : ∀ N, Ω N → ProbabilityMeasure (Vector N)),
      (∀ N, HasLaw (J N) (disorderLaw N μ.maxDegree) (P N)) →
      (∀ N, AEMeasurable (ν N) (P N)) →
      (∀ N, IndepFun (fun ω => fun y : {y : Vector N // OnSphere y} =>
        field (mixtureCoefficients μ) (J N ω) y) (ν N) (P N)) →
      (∀ N, 1 ≤ N → ∀ᵐ ω ∂P N, ∀ᵐ y ∂(ν N ω).toMeasure, OnSphere y) →
      ∀ ε : ℝ, 0 < ε → Tendsto (fun N => (P N).real
        {ω | SphericalOrthogonalHaar.intervalDistance μ β (T N) (J N ω) (ν N ω) < 1-ε})
        atTop (𝓝 0)) ∧
  (∀ (ι : ℕ → Type u) [∀ N, Fintype (ι N)] [∀ N, Nonempty (ι N)]
      (ν : ∀ N, ι N → Measure (Vector N)) [∀ N j, IsProbabilityMeasure (ν N j)],
      (∀ N, 2 ≤ N → ∀ j, ∀ᵐ y ∂ν N j, OnSphere y) →
      ∀ κ C₀ : ℝ, 0 ≤ κ → κ < ((μ.minDegree : ℝ)-2)/2 → 0 < C₀ →
      (∀ᶠ N in atTop, (Fintype.card (ι N) : ℝ) ≤ C₀*(N : ℝ)^κ) →
      VaryingProbability.InProbability (fun N => sphereFieldLaw N μ)
        (fun N => sphereMenuDistance μ β (ν N) (T N)) 1) ∧
  (∀ (ι : ℕ → Type u) [∀ N, Fintype (ι N)] [∀ N, Nonempty (ι N)]
      (R : ℕ → Type v) [∀ N, MeasurableSpace (R N)]
      (ρ : ∀ N, Measure (R N)) [∀ N, IsProbabilityMeasure (ρ N)]
      (ν : ∀ N, R N → ι N → Measure (Vector N)),
      (∀ N j, Measurable (fun r => ν N r j)) →
      ∀ [∀ N r j, IsProbabilityMeasure (ν N r j)],
      (∀ N, 2 ≤ N → ∀ r j, ∀ᵐ y ∂ν N r j, OnSphere y) →
      ∀ κ C₀ : ℝ, 0 ≤ κ → κ < ((μ.minDegree : ℝ)-2)/2 → 0 < C₀ →
      (∀ᶠ N in atTop, (Fintype.card (ι N) : ℝ) ≤ C₀*(N : ℝ)^κ) →
      VaryingProbability.InProbability (fun N => (ρ N).prod (sphereFieldLaw N μ))
        (fun N z => sphereMenuDistance μ β (ν N z.1) (T N) z.2) 1) ∧
  (∀ (κ : ∀ N, Kernel (SphereField N μ) (Vector N)) [∀ N, IsMarkovKernel (κ N)],
      (∀ N, 2 ≤ N → ∀ H, ∀ᵐ y ∂κ N H, OnSphere y) →
      ReductionEntropy.LittleLogInProbability (fun N => sphereFieldLaw N μ)
        (fun N H => InformationTheory.klDiv (κ N H) (sphereLaw N)) →
      VaryingProbability.InProbability (fun N => sphereFieldLaw N μ)
        (fun N => sphereIntervalDistance μ β (T N) (κ N)) 1)

/-- Theorem 1.4(i), the finite-dimensional Haar inequality. -/
theorem theorem_1_4_haar {N : ℕ} (hN : 1 ≤ N) (μ : FiniteMixture)
    (β : ℝ) (T : ℝ≥0) (ν : ProbabilityMeasure (Vector N))
    (hν : ∀ᵐ x ∂ν.toMeasure, OnSphere x) :
    (∫ J, 1-distance μ β T J ν ∂disorderLaw N μ.maxDegree) ≤
      ∫ J, 1-distance μ β T J (uniformInitialProbability N)
        ∂disorderLaw N μ.maxDegree :=
  finiteMixture_initial_meanDeficit_le_uniform hN μ β T ν hν

/-- Theorem 1.4(i)–(iii), including the common exponent from Theorem 1.2. -/
theorem theorem_1_4 (μ : FiniteMixture) {β x Q : ℝ}
    (h : Certificate μ β x Q) (hChen : Chen2013FiniteParisi) :
    ∃ γ : ℝ, 0 < γ ∧ InitialConclusions.{u,v} μ β γ := by
  obtain ⟨γ, hγ, hcon⟩ :=
    LiteratureSubagSlabTails.finiteMixture_all_initial_spherical_of_chen_and_lemma22.{u,v}
      μ h hChen LiteratureSubagLemma22Full.universalPressureLowerTails
  rcases hcon with ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, _⟩
  exact ⟨γ, hγ, h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩

open SphericalMemoryAssembly SphericalForm SphericalDynamics SphericalReversibility

/-- Theorem 1.5, all five finite-mixture stationary-memory conclusions. -/
theorem theorem_1_5 (μ : FiniteMixture)
    {β b : ℝ}
    (hβd : Thresholds.dynamicalThreshold μ.xi < β)
    (hβs : β < Thresholds.staticThreshold μ.xi)
    (hb : b ∈ Ioo (0 : ℝ) ((Thresholds.qStar μ.xi β)^2)) :
    ∃ κ γ a c C : ℝ, 0 < κ ∧ 0 < γ ∧ 0 < a ∧ 0 < c ∧ 0 < C ∧
      ∀ᶠ N : ℕ in atTop, ∃ Ω : Set (Disorder N μ.maxDegree), MeasurableSet Ω ∧
        (disorderLaw N μ.maxDegree).real Ωᶜ ≤ C*Real.exp (-a*N) ∧
        ∀ D ∈ Ω, ∀ hN : 2 ≤ N, MemoryConclusions hN μ β D b κ γ a c C :=
  SphericalMemoryAssembly.general_main_memory μ hβd hβs hb

/-- Theorem 1.6, the stronger finite-mixture plateau. -/
theorem theorem_1_6 (μ : FiniteMixture) {β b : ℝ}
    (hβd : Thresholds.dynamicalThreshold μ.xi<β)
    (hβs : β<Thresholds.staticThreshold μ.xi)
    (hb : b∈Ioo (0:ℝ) (Thresholds.qStar μ.xi β)) :
    ∃ κ γ a c C : ℝ,0<κ ∧ 0<γ ∧ 0<a ∧ 0<c ∧ 0<C ∧
      (∀ᶠ N : ℕ in atTop,∃ Ω₀ : Set (Disorder N μ.maxDegree),MeasurableSet Ω₀ ∧
        (disorderLaw N μ.maxDegree).real Ω₀ᶜ≤C*Real.exp (-a*N) ∧
        ∀ D∈Ω₀,∀ hN : 2≤N,PersistentMemoryConclusions hN μ β D κ γ a c C) ∧
      (∀ η : ℝ,0<η → ∀ᶠ N : ℕ in atTop,∃ Ω : Set (Disorder N μ.maxDegree),
        MeasurableSet Ω ∧ (disorderLaw N μ.maxDegree).real Ωᶜ<η ∧
        ∀ D∈Ω,∀ hN : 2≤N,MemoryConclusions hN μ β D b κ γ a c C) :=
  SphericalMemoryAssembly.general_main_plateau μ hβd hβs hb

open SphericalInfiniteModel InfiniteMixture

/-- Theorem 1.7, the literal infinite-mixture differential-operator cusp. -/
theorem theorem_1_7 (μ : InfiniteMixture)
    (hgap : Thresholds.dynamicalThreshold μ.xi<Thresholds.staticThreshold μ.xi) :
    μ.globalMaximizers.Finite ∧ (μ.globalMaximizers ⊆ Ioo (0 : ℝ) 1) ∧
      μ.qD∈μ.globalMaximizers ∧ (∀ q∈μ.globalMaximizers,q≤μ.qD) ∧
    ∃ m : ℕ,∃ a κ : ℝ,1 ≤ m ∧ 0<a ∧ 0<κ ∧
      ((fun y : ℝ => μ.A (μ.qD+y)/μ.Amax-(1-a*y^(2*m)))
        =O[𝓝 (0:ℝ)] (fun y => y^(2*m+1))) ∧
      ∀ θ∈Ioo (0:ℝ) 1,∃ ε₀ : ℝ,0<ε₀ ∧
        ∀ β : ℝ,Thresholds.dynamicalThreshold μ.xi<β → β^2*μ.Amax-1<ε₀ →
        ∃ a' : ℝ,0<a' ∧ ∃ n₀ : ℕ,1≤n₀ ∧ ∀ n : ℕ,n₀≤n →
          ∃ Ω : Set (SphericalInfiniteModel.Disorder (n+1)),MeasurableSet Ω ∧
            (SphericalInfiniteModel.disorderLaw (n+1)).real Ωᶜ≤14*Real.exp (-a'*(n+1:ℕ)) ∧
            ∀ J∈Ω,∃ hJ : J∈summableJetDisorder μ,
              IsSelfAdjoint (literalC2DifferentialOperator n μ J hJ β).closure ∧
              (literalC2DifferentialOperator n μ J hJ β).closure=literalWeakGenerator n μ J hJ β ∧
              ∀ hn : 1≤n,
                (literalSpectralSemigroupData n hn μ J hJ β).eigenvalue
                  (Nat.floor (Real.exp (κ*(n+1:ℕ))))≤
                    Real.exp (-(1-θ)*
                      ((2*(m:ℝ)*μ.qD)/((2*(m:ℝ)+1)*(1-μ.qD))*a^(-1/(2*(m:ℝ))))*
                        (β^2*μ.Amax-1)^(1+((2*m:ℕ):ℝ)⁻¹)*(n+1:ℕ)) ∧
                ∀ j : ℕ,∃ hj : (literalSpectralSemigroupData n hn μ J hJ β).basis j∈
                    (literalC2DifferentialOperator n μ J hJ β).closure.domain,
                  (literalC2DifferentialOperator n μ J hJ β).closure
                    ⟨(literalSpectralSemigroupData n hn μ J hJ β).basis j,hj⟩=
                      (literalSpectralSemigroupData n hn μ J hJ β).eigenvalue j •
                        (literalSpectralSemigroupData n hn μ J hJ β).basis j :=
  SphericalInfiniteModel.source_cusp_differential μ hgap

end SlowEquilibration.SixHeadlines
