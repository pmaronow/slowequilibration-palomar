module

public import SphericalAging.RandomLinearSDETimeEighthMoment
public import SphericalAging.ConstructedFirstVariation

public section

/-! Actual eighth moments of initial variations and nonlinear increments.
Both come from genuine same-driver bounded linear equations. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal ContDiff
namespace SphericalAging.FlowVariationEighthMoment
open HardSphereDynamics LocalSDE StochasticDifferenceQuotient LinearSDETimeFourthMoment
set_option maxHeartbeats 1600000
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

@[expose] def eighthConstant (N : ℕ) (Kb Ks T : ℝ≥0) : ℝ :=
  (T : ℝ)*Real.exp ((RandomLinearSDETimeEighthMoment.momentRate N Kb Ks : ℝ)*T)

lemma eighthConstant_nonneg (N : ℕ) (Kb Ks T : ℝ≥0) :
    0≤eighthConstant N Kb Ks T := by unfold eighthConstant;positivity

theorem linear_solution_time_eighthMoment {Kb Ks : ℝ≥0}
    {a : Fin N → PredictableLinearCoefficient.Coefficient (N := N) (F := F) (P := P) Kb}
    {sigma : Fin N → Fin N → PredictableLinearCoefficient.Coefficient (N := N) (F := F) (P := P) Ks}
    {D : BrownianDriver N P F} {v0 : State N} {X : ℝ≥0 → Ω → State N} {T : ℝ≥0}
    (h : LinearVariationalSDE.IsStrongSolutionOn a sigma D v0 X T)
    (hnull : ∀ A : Set Ω,MeasurableSet A → P A=0 → MeasurableSet[F 0] A) :
    MemLp (stateTimeCut X T) 8 (nonnegativeLebesgueMeasure.prod P) ∧
      (∫ q,‖stateTimeCut X T q‖^8 ∂nonnegativeLebesgueMeasure.prod P)≤
        eighthConstant N Kb Ks T*‖v0‖^8 := by
  have hr : RandomLinearVariationalSDE.IsStrongSolutionOn a sigma D (fun _ => v0) X T := h
  have hh := RandomLinearSDETimeEighthMoment.linear_solution_time_eighthMoment hr
    (memLp_const v0) ‖v0‖₊ (.of_forall (fun _ => le_rfl)) hnull
  refine ⟨hh.1,?_⟩
  simpa only [RandomLinearSDETimeEighthMoment.momentConstant,integral_const,
    probReal_univ,one_smul,eighthConstant,mul_assoc,mul_comm,mul_left_comm] using hh.2

theorem first_variation_time_eighthMoment (D : BrownianDriver N P F) {Kb Ks : ℝ≥0}
    {b : Fin N → State N → ℝ} {s : Fin N → Fin N → State N → ℝ}
    (hbg : ∀ i,ContDiff ℝ ∞ (b i)) (hsg : ∀ i j,ContDiff ℝ ∞ (s i j))
    (hb : ∀ i,LipschitzWith Kb (b i)) (hs : ∀ i j,LipschitzWith Ks (s i j))
    (x : State N) (T : ℝ≥0)
    (hnull : ∀ A : Set Ω,MeasurableSet A → P A=0 → MeasurableSet[F 0] A) (v : State N) :
    MemLp (stateTimeCut (ConstructedFirstVariation.process D hbg hsg hb hs x T v) T) 8
      (nonnegativeLebesgueMeasure.prod P) ∧
      (∫ q,‖stateTimeCut (ConstructedFirstVariation.process D hbg hsg hb hs x T v) T q‖^8
        ∂nonnegativeLebesgueMeasure.prod P)≤eighthConstant N Kb Ks T*‖v‖^8 :=
  linear_solution_time_eighthMoment
    (ConstructedFirstVariation.process_strongSolution D hbg hsg hb hs x T v) hnull

theorem increment_time_eighthMoment (D₀ : BrownianDriver N P F) {Kb Ks : ℝ≥0}
    {b : Fin N → State N → ℝ} {s : Fin N → Fin N → State N → ℝ}
    (hbg : ∀ i,ContDiff ℝ ∞ (b i)) (hsg : ∀ i j,ContDiff ℝ ∞ (s i j))
    (hb : ∀ i,LipschitzWith Kb (b i)) (hs : ∀ i j,LipschitzWith Ks (s i j))
    (x y : State N) (T : ℝ≥0) (hT : 0<T) :
    MemLp (stateTimeCut (NonlinearIncrementFourthMoment.increment
      (NullAugmentation.driver D₀) hb hs x y T) T) 8 (nonnegativeLebesgueMeasure.prod P) ∧
      (∫ q,‖stateTimeCut (NonlinearIncrementFourthMoment.increment
        (NullAugmentation.driver D₀) hb hs x y T) T q‖^8
        ∂nonnegativeLebesgueMeasure.prod P)≤eighthConstant N Kb Ks T*‖y-x‖^8 := by
  obtain ⟨Z,hZ,hcommon⟩ := constructed_scaled_difference (NullAugmentation.driver D₀)
    hbg hsg hb hs x y T hT 1
  have hc : ∀ᵐ omega ∂P,∀ t,t≤T → Z t omega=NonlinearIncrementFourthMoment.increment
      (NullAugmentation.driver D₀) hb hs x y T t omega := by
    simpa only [one_smul,NonlinearIncrementFourthMoment.increment] using hcommon
  have h8 := linear_solution_time_eighthMoment hZ
    (fun _ hm hzero => NullAugmentation.augment_null_known_zero F hm hzero)
  have heq := stateTimeCut_path_congr hc
  refine ⟨h8.1.ae_eq heq,?_⟩
  calc
    _ = ∫ q,‖stateTimeCut Z T q‖^8 ∂nonnegativeLebesgueMeasure.prod P :=
      integral_congr_ae (heq.symm.fun_comp (fun v : State N => ‖v‖^8))
    _ ≤ eighthConstant N Kb Ks T*‖1 • (y-x)‖^8 := h8.2
    _ = _ := by rw [one_smul]

end SphericalAging.FlowVariationEighthMoment
