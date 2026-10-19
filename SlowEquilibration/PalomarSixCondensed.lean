module

public import SlowEquilibration.PalomarSixClassDefinitions
public import SixHeadlines

@[expose] public section
noncomputable section
namespace SlowEquilibration.PalomarSixCondensed
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
open SlowEquilibrationCondensedSource
open PalomarCondensed

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem universalSourcePressureLowerTails :
    ∀ μ : SlowEquilibrationCondensedSource.FiniteMixture, ∀ β : ℝ,
      SlowEquilibrationCondensedSource.PressureLowerTails μ β := by
  intro μ β
  exact (pressureLowerTails_iff μ β).mpr
    (LiteratureSubagLemma22Full.pressureLowerTails (toLibrary μ) β)

theorem uniform_of_library (μ : SlowEquilibrationCondensedSource.FiniteMixture) (β : ℝ)
    (h : SixHeadlines.UniformConclusions (toLibrary μ) β) :
    SlowEquilibrationCondensedSource.UniformConclusions μ β := by
  obtain ⟨γ,hγ,hsep⟩ := h
  refine ⟨γ,hγ,?_⟩
  intro ε hε
  have ht := (hsep ε hε).comp (tendsto_add_atTop_nat 2)
  apply ht.congr'
  filter_upwards [] with n
  apply congrArg (fun s : Set (SphericalModel.Disorder (n+2) (toLibrary μ).maxDegree) =>
    (SphericalModel.disorderLaw (n+2) (toLibrary μ).maxDegree).real s)
  ext J
  have he := intervalDistance_eq (show 1 ≤ n+2 by omega) μ β
    (exponentialHorizon γ (n+2)) J
    (SphericalOrthogonalHaar.uniformInitialProbability (n+2)) (sphere_support (by omega))
  change (ε ≤ ‖SphericalOrthogonalHaar.intervalDistance (toLibrary μ) β
    (exponentialHorizon γ (n+2)) J
    (SphericalOrthogonalHaar.uniformInitialProbability (n+2))-1‖) ↔
      (ε ≤ ‖SlowEquilibrationCondensedSource.intervalDistance μ β
        (exponentialHorizon γ (n+2)) J (SlowEquilibrationCondensedSource.sphereLaw (n+2))-1‖)
  rw [← he]
  rfl

theorem theorem_1_2 (μ : SlowEquilibrationCondensedSource.FiniteMixture) {β x Q : ℝ}
    (h : SlowEquilibrationCondensedSource.Certificate μ β x Q)
    (hChen : SlowEquilibrationCondensedSource.Chen2013FiniteParisi) :
    SlowEquilibrationCondensedSource.UniformConclusions μ β :=
  uniform_of_library μ β (SixHeadlines.theorem_1_2 (toLibrary μ)
    ((certificate_iff μ β x Q).mp h) (chen_iff.mp hChen))

theorem corollary_1_3_a (p : ℕ) (hp : 4 ≤ p) {β : ℝ}
    (hβ : SlowEquilibrationCondensedSource.staticThreshold (fun r : ℝ => r^p) < β)
    (hChen : SlowEquilibrationCondensedSource.Chen2013FiniteParisi) :
    SlowEquilibrationCondensedSource.UniformConclusions (pureCovariance p (by omega)) β := by
  apply uniform_of_library
  exact SixHeadlines.corollary_1_3_a p hp hβ (chen_iff.mp hChen)

theorem corollary_1_3_b (μ : SlowEquilibrationCondensedSource.FiniteMixture)
    (hd : 4 ≤ μ.minDegree) {β : ℝ}
    (hβ : SlowEquilibrationCondensedSource.staticThreshold μ.xi < β)
    (hξ : StrictConvexOn ℝ (Ioc 0 1)
      (SlowEquilibrationCondensedSource.inverseSqrt (deriv (deriv μ.xi))))
    (hChen : SlowEquilibrationCondensedSource.Chen2013FiniteParisi) :
    SlowEquilibrationCondensedSource.UniformConclusions μ β := by
  apply uniform_of_library
  exact SixHeadlines.corollary_1_3_b (toLibrary μ) hd hβ hξ (chen_iff.mp hChen)

theorem corollary_1_3_b_degree_window (μ : SlowEquilibrationCondensedSource.FiniteMixture)
    (hd : 4 ≤ μ.minDegree)
    (hw : ((μ.minDegree : ℝ)+μ.maxDegree-5)^2 <
      6*((μ.minDegree : ℝ)-2)*((μ.maxDegree : ℝ)-2))
    {β : ℝ} (hβ : SlowEquilibrationCondensedSource.staticThreshold μ.xi < β)
    (hChen : SlowEquilibrationCondensedSource.Chen2013FiniteParisi) :
    SlowEquilibrationCondensedSource.UniformConclusions μ β := by
  apply uniform_of_library
  exact SixHeadlines.corollary_1_3_b_degree_window (toLibrary μ) hd hw hβ (chen_iff.mp hChen)

theorem corollary_1_3_b_support (μ : SlowEquilibrationCondensedSource.FiniteMixture)
    (hs : ∀ p ∈ μ.coeff.support, p ∈ Finset.Icc 4 11)
    {β : ℝ} (hβ : SlowEquilibrationCondensedSource.staticThreshold μ.xi < β)
    (hChen : SlowEquilibrationCondensedSource.Chen2013FiniteParisi) :
    SlowEquilibrationCondensedSource.UniformConclusions μ β := by
  apply uniform_of_library
  exact SixHeadlines.corollary_1_3_b_support (toLibrary μ) hs hβ (chen_iff.mp hChen)

def perturbationToLibrary {d P : ℕ} (b : ClassPerturbation d P) :
    CSPerturbative.EvenPerturbation d P :=
  ⟨b.coeff,b.nonneg,b.zero_of_le,b.zero_of_gt,b.even_supported,b.total_le_one⟩

theorem corollary_1_3_c (d P : ℕ) (hd : 4 ≤ d) (heven : Even d) (hdP : d<P)
    {β : ℝ} (hβ : SlowEquilibrationCondensedSource.staticThreshold (fun r : ℝ => r^d)<β)
    (hChen : SlowEquilibrationCondensedSource.Chen2013FiniteParisi) :
    ∃ ε₀ : ℝ, 0<ε₀ ∧ ∀ b : ClassPerturbation d P,
      b.coeff.sum (fun _ c => c)=1 → ∀ (ε : ℝ) (hε : 0<ε), ε<ε₀ →
        SlowEquilibrationCondensedSource.UniformConclusions (b.covariance (by omega) ε hε.le) β := by
  obtain ⟨ε₀,hε₀,hresult⟩ := SixHeadlines.corollary_1_3_c d P hd heven hdP hβ (chen_iff.mp hChen)
  refine ⟨ε₀,hε₀,?_⟩
  intro b hb ε hε hsmall
  apply uniform_of_library
  exact hresult (perturbationToLibrary b) hb ε hε hsmall

theorem corollary_1_3_d (hChen : SlowEquilibrationCondensedSource.Chen2013FiniteParisi) :
    SlowEquilibrationCondensedSource.UniformConclusions exampleCovariance exampleBeta := by
  apply uniform_of_library
  exact SixHeadlines.corollary_1_3_d (chen_iff.mp hChen)

theorem theorem_1_4_haar {N : ℕ} (hN : 1≤N)
    (μ : SlowEquilibrationCondensedSource.FiniteMixture) (β : ℝ) (T : ℝ≥0)
    (ν : ProbabilityMeasure (SlowEquilibrationCondensedSource.Vector N))
    (hν : ∀ᵐ x ∂ν.toMeasure, SlowEquilibrationCondensedSource.OnSphere x) :
    (∫ J, 1-SlowEquilibrationCondensedSource.distance μ β T J ν.toMeasure
      ∂SlowEquilibrationCondensedSource.disorderLaw N μ.maxDegree) ≤
      ∫ J, 1-SlowEquilibrationCondensedSource.distance μ β T J
        (SlowEquilibrationCondensedSource.sphereLaw N)
        ∂SlowEquilibrationCondensedSource.disorderLaw N μ.maxDegree :=
  source_initial_meanDeficit_le_uniform hN μ β T ν hν

universe u v
theorem theorem_1_4 (μ : SlowEquilibrationCondensedSource.FiniteMixture) {β x Q : ℝ}
    (h : SlowEquilibrationCondensedSource.Certificate μ β x Q)
    (hChen : SlowEquilibrationCondensedSource.Chen2013FiniteParisi) :
    ∃ γ : ℝ, 0<γ ∧ SixInitialConclusions.{u,v} μ β γ := by
  obtain ⟨γ,hγ,hall⟩ := source_all_initial_spherical.{u,v}
    μ h hChen universalSourcePressureLowerTails
  exact ⟨γ,hγ,hall.1,hall.2.1,hall.2.2.1,hall.2.2.2.1⟩

end SlowEquilibration.PalomarSixCondensed
