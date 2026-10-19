module
public import OverlapPaper.MixedLowerReduction
public import FourPapersCommon.MixedNearOptimalInterpolation

@[expose] public section

/-! The physical Parisi formula for the actual countable even mixed Gaussian
Hamiltonian.  The lower bound uses genuine mixed constrained interpolation,
with all signed-overlap and endpoint cases proved in the common library. -/
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open SpinGlass SpinGlass.Targets
open scoped Topology
namespace OverlapPaper
open FourPapersCommon
set_option maxHeartbeats 1000000

theorem mixedNearOptimalInterpolation (ξ : AdmissibleEvenMixture) (h : ℝ) :
    MixedNearOptimalInterpolation ξ h := by
  intro t₀ ht₀
  let T := max (0 : ℝ) t₀
  have hT : T ∈ Ico (0 : ℝ) 1 := ⟨le_max_left _ _, max_lt zero_lt_one ht₀⟩
  obtain ⟨ε, hε, Hε⟩ := mixed_nearOptimal_interpolation_all_models ξ hT
  refine ⟨ε, hε, ?_⟩
  intro k s hnear hmin t ht0 htt₀
  letI : ∀ n, MeasureSpace (Disorder n) := fun n => ⟨disorderLaw ξ n⟩
  letI : ∀ n, IsProbabilityMeasure (ℙ : Measure (Disorder n)) :=
    fun n => disorderLaw_isProbabilityMeasure ξ n
  have H := Hε s h hnear hmin Disorder (fun n => canonicalMixedDisorder ξ n) t
    ⟨ht0, htt₀.trans (le_max_right _ _)⟩
  change Tendsto (fun n => physicalMixedPhi ξ h s n t) atTop (𝓝 (mixedGuerraPsi ξ h s t))
  exact H

theorem thermodynamicPressure_eq_mixedPressure (ξ : AdmissibleEvenMixture) (h : ℝ) :
    thermodynamicPressure ξ h = mixedPressure ξ h :=
  thermodynamicPressure_eq_mixedPressure_of_nearOptimalInterpolation ξ h
    (mixedNearOptimalInterpolation ξ h)

theorem physicalParisi_formula (ξ : AdmissibleEvenMixture) (h : ℝ) :
    Tendsto (expectedFreeEnergy ξ h) atTop (𝓝 (mixedPressure ξ h)) :=
  physicalParisi_formula_of_nearOptimalInterpolation ξ h (mixedNearOptimalInterpolation ξ h)

end OverlapPaper
