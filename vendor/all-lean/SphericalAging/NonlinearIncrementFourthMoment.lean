module

public import SphericalAging.StochasticDifferenceQuotient
public import SphericalAging.LinearSDETimeFourthMoment

public section

/-! Actual fourth-moment control of increments of the constructed nonlinear
SDE, deduced from their genuine bounded secant linear equation. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal ContDiff
namespace SphericalAging.NonlinearIncrementFourthMoment
open HardSphereDynamics LocalSDE StochasticDifferenceQuotient LinearSDETimeFourthMoment
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

@[expose]  def increment (D : BrownianDriver N P F) {Kb Ks : ℝ≥0}
    {b : Fin N → State N → ℝ} {s : Fin N → Fin N → State N → ℝ}
    (hb : ∀ i, LipschitzWith Kb (b i)) (hs : ∀ i j, LipschitzWith Ks (s i j))
    (x y : State N) (T : ℝ≥0) : ℝ≥0 → Ω → State N :=
  fun t omega => GlobalSDE.horizonProcess D hb hs y T t omega-GlobalSDE.horizonProcess D hb hs x T t omega

@[expose]  def fourthConstant (N : ℕ) (Kb Ks T : ℝ≥0) : ℝ :=
  3*(T : ℝ)*Real.exp (momentExponent N Kb Ks T*T)

 theorem fourthConstant_nonneg (N : ℕ) (Kb Ks T : ℝ≥0) : 0 ≤ fourthConstant N Kb Ks T := by
  unfold fourthConstant
  positivity

/-- No moment or difference-equation premise is required: the nonlinear
processes, their secant linear equation and its fourth moments are all
constructed from the actual Brownian driver and smooth coefficients. -/
 theorem increment_fourthMoment (D₀ : BrownianDriver N P F) {Kb Ks : ℝ≥0}
    {b : Fin N → State N → ℝ} {s : Fin N → Fin N → State N → ℝ}
    (hbg : ∀ i, ContDiff ℝ ∞ (b i)) (hsg : ∀ i j, ContDiff ℝ ∞ (s i j))
    (hb : ∀ i, LipschitzWith Kb (b i)) (hs : ∀ i j, LipschitzWith Ks (s i j))
    (x y : State N) (T : ℝ≥0) (hT : 0 < T) :
    MemLp (stateTimeCut (increment (NullAugmentation.driver D₀) hb hs x y T) T) 4
      (nonnegativeLebesgueMeasure.prod P) ∧
    (∫ q,‖stateTimeCut (increment (NullAugmentation.driver D₀) hb hs x y T) T q‖^4
      ∂nonnegativeLebesgueMeasure.prod P) ≤ fourthConstant N Kb Ks T*‖y-x‖^4 := by
  obtain ⟨Z,hZ,hcommon⟩ := constructed_scaled_difference (NullAugmentation.driver D₀)
    hbg hsg hb hs x y T hT 1
  have hc : ∀ᵐ omega ∂P, ∀ t,t ≤ T → Z t omega=increment (NullAugmentation.driver D₀) hb hs x y T t omega := by
    simpa only [one_smul,increment] using hcommon
  have h4 := linear_solution_time_fourthMoment_augmented F hZ
  have heq := stateTimeCut_path_congr hc
  refine ⟨h4.1.ae_eq heq,?_⟩
  calc
    _ = ∫ q,‖stateTimeCut Z T q‖^4 ∂nonnegativeLebesgueMeasure.prod P :=
      integral_congr_ae (heq.symm.fun_comp (fun v : State N => ‖v‖^4))
    _ ≤ (T : ℝ)*momentConstant N Kb Ks T (1 • (y-x)) := h4.2
    _ = _ := by simp only [one_smul,fourthConstant,momentConstant];ring
end SphericalAging.NonlinearIncrementFourthMoment
