-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.PalomarCondensedDynamics
public import SlowEquilibration.PalomarCondensedThermodynamics
public import SlowEquilibration.LiteratureSubagSlabTails

/-! Concrete source statements for the conditional condensed-phase theorem.
The dynamics and thermodynamics are independently stated in the two source
definition modules and identified there with the physical library objects. -/
@[expose] public section
noncomputable section
namespace SlowEquilibrationCondensedSource
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal

/-- Event-supremum total variation, with range [0,1] for probabilities;
there is no factor of two. All measurable ambient Borel events are tested. -/
def totalVariation {α : Type*} [MeasurableSpace α] (ν π : Measure α) : ℝ :=
  sSup {r : ℝ | ∃ B : Set α, MeasurableSet B ∧ r = |ν.real B - π.real B|}

/-- The law at nonnegative time t from an initial measure ν, obtained by
integrating the concrete Langevin transition law against ν. The theorems
use probability measures supported on the radius-√N sphere. -/
def evolvedLaw {N : ℕ} (μ : FiniteMixture) (β : ℝ) (t : ℝ≥0)
    (J : Disorder N μ.maxDegree) (ν : Measure (Vector N)) : Measure (Vector N) :=
  ν.bind (transitionLaw (field μ J) β t)

/-- Total variation between the evolved initial law and the normalized
Gibbs law at time t≥0, for the same realization of the Gaussian tensors. -/
def distance {N : ℕ} (μ : FiniteMixture) (β : ℝ) (t : ℝ≥0)
    (J : Disorder N μ.maxDegree) (ν : Measure (Vector N)) : ℝ :=
  totalVariation (evolvedLaw μ β t J ν) (gibbsLaw μ β J)

/-- Literal infimum over every real time in [0,T], not a time grid.
The conversion to nonnegative time is the identity on this interval. -/
def intervalDistance {N : ℕ} (μ : FiniteMixture) (β : ℝ) (T : ℝ≥0)
    (J : Disorder N μ.maxDegree) (ν : Measure (Vector N)) : ℝ :=
  sInf ((fun t : ℝ => distance μ β t.toNNReal J ν) '' Icc 0 (T : ℝ))

/-- The physical exponential horizon exp(Nγ), with time generator
Δ_S + β∇_S H·∇_S and no additional N or temperature rescaling. -/
def exponentialHorizon (γ : ℝ) (N : ℕ) : ℝ≥0 :=
  ⟨Real.exp ((N : ℝ)*γ), Real.exp_nonneg _⟩

/-- Convergence in probability to one under the varying tensor disorder
laws, using dimensions n+2; this cofinal shift excludes the zero sphere. -/
def uniformSeparation (μ : FiniteMixture) (β γ : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → Tendsto
    (fun n => (disorderLaw (n+2) μ.maxDegree).real
      {J | ε ≤ ‖intervalDistance μ β (exponentialHorizon γ (n+2)) J
        (sphereLaw (n+2))-1‖}) atTop (𝓝 0)

/-- Worst failure probability over prescribed Borel spherical initial
probabilities. The supremum is outside the disorder probability: the law
in this supremum is chosen before observing the Hamiltonian. -/
def prescribedFailure (μ : FiniteMixture) (β γ ε : ℝ) (N : ℕ) : ℝ :=
  sSup {r : ℝ | ∃ ν : ProbabilityMeasure (Vector N),
    (∀ᵐ x ∂ν.toMeasure, OnSphere x) ∧
    r = (disorderLaw N μ.maxDegree).real
      {J | intervalDistance μ β (exponentialHorizon γ N) J ν.toMeasure < 1-ε}}

/-- Manuscript thm:main-condensed and thm:main-initial(i), at one common
exponent. Random initial laws may be singular; they must be measurable,
spherical, and independent of the literal Hamiltonian restricted to the
sphere (with the evaluation sigma algebra). The uniform clause uses the
cofinal dimensions n+2; the initial-law clauses use the full index N. -/
def CondensedAndInitial (μ : FiniteMixture) (β γ : ℝ) : Prop :=
  uniformSeparation μ β γ ∧
  (∀ ε : ℝ, 0 < ε → Tendsto (prescribedFailure μ β γ ε) atTop (𝓝 0)) ∧
  (∀ (Ω : ℕ → Type) [∀ n, MeasurableSpace (Ω n)]
      (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
      (J : ∀ n, Ω n → Disorder n μ.maxDegree)
      (ν : ∀ n, Ω n → ProbabilityMeasure (Vector n)),
      (∀ n, HasLaw (J n) (disorderLaw n μ.maxDegree) (P n)) →
      (∀ n, AEMeasurable (ν n) (P n)) →
      (∀ n, IndepFun
        (fun ω => fun x : {x : Vector n // OnSphere x} => field μ (J n ω) x)
        (ν n) (P n)) →
      (∀ n, 1 ≤ n → ∀ᵐ ω ∂P n, ∀ᵐ y ∂(ν n ω).toMeasure, OnSphere y) →
      ∀ ε : ℝ, 0 < ε → Tendsto
        (fun n => (P n).real {ω | intervalDistance μ β
          (exponentialHorizon γ n) (J n ω) (ν n ω).toMeasure < 1-ε})
        atTop (𝓝 0))

end SlowEquilibrationCondensedSource

namespace SlowEquilibration.PalomarCondensed
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal
open SlowEquilibrationCondensedSource
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem totalVariation_eq {α : Type*} [MeasurableSpace α] (ν π : Measure α) :
    SlowEquilibrationCondensedSource.totalVariation ν π =
      SlowEquilibration.totalVariation ν π := rfl

theorem sphere_support {N : ℕ} (hN : 1 ≤ N) :
    ∀ᵐ x ∂SlowEquilibrationCondensedSource.sphereLaw N,
      SlowEquilibrationCondensedSource.OnSphere x := by
  exact (SphericalModel.sphereLaw_support hN).mono fun x hx =>
    (SphericalAging.HardSphereDynamics.onSphere_iff_norm_sq x).mpr hx

/-- Pointwise identification of the generator-characterized law with the
constructed physical diffusion; this includes every spherical starting point. -/
theorem transitionLaw_eq {N : ℕ} (hN : 1 ≤ N)
    (μ : SlowEquilibrationCondensedSource.FiniteMixture)
    (J : SlowEquilibrationCondensedSource.Disorder N μ.maxDegree)
    (β : ℝ) (t : ℝ≥0) (x : SlowEquilibrationCondensedSource.Vector N)
    (hx : SlowEquilibrationCondensedSource.OnSphere x) :
    SlowEquilibrationCondensedSource.transitionLaw
      (SlowEquilibrationCondensedSource.field μ J) β t x =
      SphericalDynamics.mixedTransitionKernel (toLibrary μ) J β t x := by
  rw [field_eq]
  exact transitionLaw_eq_physical hN (toLibrary μ) J β t x hx

theorem evolvedLaw_eq {N : ℕ} (hN : 1 ≤ N)
    (μ : SlowEquilibrationCondensedSource.FiniteMixture) (β : ℝ) (t : ℝ≥0)
    (J : SlowEquilibrationCondensedSource.Disorder N μ.maxDegree)
    (ν : Measure (SlowEquilibrationCondensedSource.Vector N))
    (hν : ∀ᵐ x ∂ν, SlowEquilibrationCondensedSource.OnSphere x) :
    SlowEquilibrationCondensedSource.evolvedLaw μ β t J ν =
      SphericalDynamics.mixedTransitionKernel (toLibrary μ) J β t ∘ₘ ν := by
  exact Measure.bind_congr_right (hν.mono fun x hx => transitionLaw_eq hN μ J β t x hx)

theorem distance_eq {N : ℕ} (hN : 1 ≤ N)
    (μ : SlowEquilibrationCondensedSource.FiniteMixture) (β : ℝ) (t : ℝ≥0)
    (J : SlowEquilibrationCondensedSource.Disorder N μ.maxDegree)
    (ν : ProbabilityMeasure (SlowEquilibrationCondensedSource.Vector N))
    (hν : ∀ᵐ x ∂ν.toMeasure, SlowEquilibrationCondensedSource.OnSphere x) :
    SlowEquilibrationCondensedSource.distance μ β t J ν.toMeasure =
      SphericalOrthogonalHaar.distance (toLibrary μ) β t J ν := by
  unfold SlowEquilibrationCondensedSource.distance SphericalOrthogonalHaar.distance
  rw [evolvedLaw_eq hN μ β t J ν.toMeasure hν]
  rfl

theorem intervalDistance_eq {N : ℕ} (hN : 1 ≤ N)
    (μ : SlowEquilibrationCondensedSource.FiniteMixture) (β : ℝ) (T : ℝ≥0)
    (J : SlowEquilibrationCondensedSource.Disorder N μ.maxDegree)
    (ν : ProbabilityMeasure (SlowEquilibrationCondensedSource.Vector N))
    (hν : ∀ᵐ x ∂ν.toMeasure, SlowEquilibrationCondensedSource.OnSphere x) :
    SlowEquilibrationCondensedSource.intervalDistance μ β T J ν.toMeasure =
      SphericalOrthogonalHaar.intervalDistance (toLibrary μ) β T J ν := by
  unfold SlowEquilibrationCondensedSource.intervalDistance SphericalOrthogonalHaar.intervalDistance
  simp_rw [distance_eq hN μ β _ J ν hν]

theorem uniform_intervalDistance_eq {N : ℕ} (hN : 1 ≤ N)
    (μ : SlowEquilibrationCondensedSource.FiniteMixture) (β : ℝ) (T : ℝ≥0)
    (J : SlowEquilibrationCondensedSource.Disorder N μ.maxDegree) :
    SlowEquilibrationCondensedSource.intervalDistance μ β T J
      (SlowEquilibrationCondensedSource.sphereLaw N) =
      SourceReductionConsumerAsymptotic.originalUniformIntervalDistance
        (toLibrary μ) β T J := by
  unfold SlowEquilibrationCondensedSource.intervalDistance
    SlowEquilibrationCondensedSource.distance
    SourceReductionConsumerAsymptotic.originalUniformIntervalDistance
  simp_rw [evolvedLaw_eq hN μ β _ J _ (sphere_support hN)]
  rfl

theorem exponentialHorizon_eq (γ : ℝ) (N : ℕ) :
    SlowEquilibrationCondensedSource.exponentialHorizon γ N =
      SphericalOverlapExponential.exponentialGridHorizon γ N := rfl

theorem prescribedFailure_eq {N : ℕ} (hN : 1 ≤ N)
    (μ : SlowEquilibrationCondensedSource.FiniteMixture) (β γ ε : ℝ) :
    SlowEquilibrationCondensedSource.prescribedFailure μ β γ ε N =
      SphericalOrthogonalHaar.uniformPrescribedFailure (toLibrary μ) β
        (fun N => SphericalOverlapExponential.exponentialGridHorizon γ N) ε N := by
  apply congrArg sSup
  ext r
  constructor
  · rintro ⟨ν, hν, rfl⟩
    refine ⟨ν, hν, ?_⟩
    simp_rw [intervalDistance_eq hN μ β _ _ ν hν]
    rfl
  · rintro ⟨ν, hν, rfl⟩
    refine ⟨ν, hν, ?_⟩
    simp_rw [intervalDistance_eq hN μ β _ _ ν hν]
    rfl

/-- Both literature hypotheses are ordinary theorem arguments, translated
universally over all auxiliary finite mixtures. -/
theorem source_main_condensed_and_initial_literal
    (μ : SlowEquilibrationCondensedSource.FiniteMixture) {β x Q : ℝ}
    (h : SlowEquilibrationCondensedSource.Certificate μ β x Q)
    (hChen : SlowEquilibrationCondensedSource.Chen2013FiniteParisi)
    (hLemma22 : ∀ μ : SlowEquilibrationCondensedSource.FiniteMixture, ∀ β : ℝ,
      SlowEquilibrationCondensedSource.PressureLowerTails μ β) :
    ∃ γ : ℝ, 0 < γ ∧ SlowEquilibrationCondensedSource.CondensedAndInitial μ β γ := by
  have hL : ∀ μ : SlowEquilibration.FiniteMixture, ∀ β : ℝ,
      LiteratureSubagBandLowerComplete.PressureLowerTails μ β := by
    intro ν b
    exact (pressureLowerTails_iff (ofLibrary ν) b).mp (hLemma22 (ofLibrary ν) b)
  obtain ⟨γ, hγ, hu, _hs, hp, hr⟩ :=
    LiteratureSubagSlabTails.finiteMixture_main_condensed_and_initial_literal_of_chen_and_lemma22
      (toLibrary μ) ((certificate_iff μ β x Q).mp h) (chen_iff.mp hChen) hL
  refine ⟨γ, hγ, ?_, ?_, ?_⟩
  · intro ε hε
    apply (hu ε hε).congr'
    filter_upwards [] with n
    congr 1
    ext J
    change (ε ≤ ‖SourceReductionConsumerAsymptotic.originalUniformIntervalDistance
      (toLibrary μ) β (exponentialHorizon γ (n+2)) J - 1‖) ↔
      (ε ≤ ‖SlowEquilibrationCondensedSource.intervalDistance μ β
        (exponentialHorizon γ (n+2)) J (SlowEquilibrationCondensedSource.sphereLaw (n+2))-1‖)
    rw [uniform_intervalDistance_eq (show 1 ≤ n+2 by omega) μ β _ J]
  · intro ε hε
    apply (hp ε hε).congr'
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
    exact (prescribedFailure_eq hN μ β γ ε).symm
  · intro Ω _ P _ J ν hJ hν hind hsphere ε hε
    have hl := hr Ω P J ν hJ hν hind hsphere ε hε
    apply hl.congr'
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
    apply measureReal_congr
    filter_upwards [hsphere N hN] with ω hω
    rw [intervalDistance_eq hN μ β _ _ _ hω]
    rfl

/-- The finite-dimensional expected-deficit inequality of
thm:main-initial(i), for every prescribed spherical Borel probability. -/
theorem source_initial_meanDeficit_le_uniform {N : ℕ} (hN : 1 ≤ N)
    (μ : SlowEquilibrationCondensedSource.FiniteMixture) (β : ℝ) (T : ℝ≥0)
    (ν : ProbabilityMeasure (SlowEquilibrationCondensedSource.Vector N))
    (hν : ∀ᵐ y ∂ν.toMeasure, SlowEquilibrationCondensedSource.OnSphere y) :
    (∫ J, 1-SlowEquilibrationCondensedSource.distance μ β T J ν.toMeasure
      ∂SlowEquilibrationCondensedSource.disorderLaw N μ.maxDegree) ≤
    ∫ J, 1-SlowEquilibrationCondensedSource.distance μ β T J
      (SlowEquilibrationCondensedSource.sphereLaw N)
      ∂SlowEquilibrationCondensedSource.disorderLaw N μ.maxDegree := by
  have he : ∀ J, SlowEquilibrationCondensedSource.distance μ β T J
      (SlowEquilibrationCondensedSource.sphereLaw N) =
      SphericalOrthogonalHaar.distance (toLibrary μ) β T J
        (SphericalOrthogonalHaar.uniformInitialProbability N) := fun J =>
    distance_eq hN μ β T J (SphericalOrthogonalHaar.uniformInitialProbability N)
      (sphere_support hN)
  simp_rw [distance_eq hN μ β T _ ν hν, he]
  exact SourceFiniteMixtureMainLiteral.finiteMixture_initial_meanDeficit_le_uniform
    hN (toLibrary μ) β T ν hν

end SlowEquilibration.PalomarCondensed
