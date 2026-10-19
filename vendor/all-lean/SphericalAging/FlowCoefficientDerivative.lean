module

public import SphericalAging.TerminalLinearity

public section

/-! Actual differentiated nonlinear coefficient classes along the proved
stochastic solution map. These give terminal-time derivative identification
through the genuine continuous linear drift and Itô operators. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal ContDiff
namespace SphericalAging.FlowCoefficientDerivative
open HardSphereDynamics LocalSDE VariationalCoefficients PredictableLinearCoefficient
open StochasticFlowDerivative StochasticTaylorRemainder NonlinearIncrementFourthMoment
open LinearSDETimeFourthMoment TerminalLinearity
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

 theorem hasFDerivAt_of_quadratic_error {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (f : E → G) (L : E →L[ℝ] G) (x : E)
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ y,‖f y-f x-L (y-x)‖ ≤ C*‖y-x‖^2) :
    HasFDerivAt f L x := by
  rw [hasFDerivAt_iff_isLittleO,Asymptotics.isLittleO_iff]
  intro ε hε
  have hevent : ∀ᶠ y : E in 𝓝 x,‖y-x‖ < ε/(C+1) := by
    exact Filter.mem_of_superset (Metric.ball_mem_nhds x (div_pos hε (by linarith : 0 < C+1)))
      (fun y hy => by simpa only [Metric.mem_ball,dist_eq_norm,Set.mem_ofPred_eq] using hy)
  filter_upwards [hevent] with y hy
  apply (hbound y).trans
  have hnorm := norm_nonneg (y-x)
  have hh : C*‖y-x‖ ≤ ε := by
    have he := (lt_div_iff₀ (by linarith : 0 < C+1)).mp hy
    nlinarith
  nlinarith

/-- Actual coefficient-class Fréchet derivative along the actual nonlinear
SDE initial-state flow, identified with evaluation of its true Jacobian. -/
 theorem coefficient_hasFDerivAt_initial (D₀ : BrownianDriver N P F) {Kb Ks Lb Ls K Lg : ℝ≥0}
    {b : Fin N → State N → ℝ} {s : Fin N → Fin N → State N → ℝ} {g : State N → ℝ}
    (hbg : ∀ i, ContDiff ℝ ∞ (b i)) (hsg : ∀ i j, ContDiff ℝ ∞ (s i j))
    (hb : ∀ i, LipschitzWith Kb (b i)) (hs : ∀ i j, LipschitzWith Ks (s i j))
    (hbd : ∀ i, LipschitzWith Lb (fderiv ℝ (b i)))
    (hsd : ∀ i j, LipschitzWith Ls (fderiv ℝ (s i j)))
    (hg : ContDiff ℝ ∞ g) (hLg : LipschitzWith K g) (hgd : LipschitzWith Lg (fderiv ℝ g))
    (x : State N) (T : ℝ≥0) (hT : 0 < T) :
    HasFDerivAt
      (fun y : State N => predictableCoefficient hLg (GlobalSDE.horizonClass (NullAugmentation.driver D₀) hb hs y T) T)
      ((coefficientOperator (derivativeRow (GlobalSDE.horizonProcess (NullAugmentation.driver D₀) hb hs x T)
        (GlobalSDE.horizonProcess_stronglyAdapted (NullAugmentation.driver D₀) hb hs x T)
        (GlobalSDE.horizonProcess_continuous (NullAugmentation.driver D₀) hb hs x T) hg hLg T)).comp
        (response (NullAugmentation.driver D₀) hbg hsg hb hs x T)) x := by
  let D := NullAugmentation.driver D₀
  let X := GlobalSDE.horizonProcess D hb hs x T
  let U := GlobalSDE.horizonClass D hb hs x T
  let ha := GlobalSDE.horizonProcess_stronglyAdapted D hb hs x T
  let hc := GlobalSDE.horizonProcess_continuous D hb hs x T
  let a := derivativeRow X ha hc hg hLg T
  let L := response D hbg hsg hb hs x T
  obtain ⟨C,hC,hquad⟩ := quadratic_error_bound D₀ hbg hsg hb hs hbd hsd x T hT
  let Cr := (Lg : ℝ)*Real.sqrt (fourthConstant N Kb Ks T)
  apply hasFDerivAt_of_quadratic_error _ _ x (Cr+(K : ℝ)*C) (by dsimp [Cr];positivity)
  intro y
  let Y := GlobalSDE.horizonProcess D hb hs y T
  let V := GlobalSDE.horizonClass D hb hs y T
  have h4 := increment_fourthMoment D₀ hbg hsg hb hs x y T hT
  have hi : Integrable (fun q => ‖(Ioc (0 : ℝ≥0) T ×ˢ (univ : Set Ω)).indicator
      (fun q => Y q.1 q.2-X q.1 q.2) q‖^4) (nonnegativeLebesgueMeasure.prod P) := by
    simpa only [stateTimeCut_eq_indicator,increment] using h4.1.integrable_norm_pow (by norm_num)
  have hm : (∫ q,‖(Ioc (0 : ℝ≥0) T ×ˢ (univ : Set Ω)).indicator
      (fun q => Y q.1 q.2-X q.1 q.2) q‖^4 ∂nonnegativeLebesgueMeasure.prod P) ≤
      fourthConstant N Kb Ks T*‖y-x‖^4 := by
    simpa only [stateTimeCut_eq_indicator,increment] using h4.2
  have hr : ‖remainder ha hc hg hLg T U V‖ ≤ Cr*‖y-x‖^2 :=
    norm_remainder_le ha hc (GlobalSDE.horizonProcess_timeCut D hb hs x T)
      (GlobalSDE.horizonProcess_timeCut D hb hs y T) hg hLg hgd hi _
      (fourthConstant_nonneg N Kb Ks T) (y-x) hm
  change ‖predictableCoefficient hLg V T-predictableCoefficient hLg U T-apply a (L (y-x))‖ ≤ _
  have he : predictableCoefficient hLg V T-predictableCoefficient hLg U T-apply a (L (y-x)) =
      remainder ha hc hg hLg T U V+apply a (V-U-L (y-x)) := by
    simp only [remainder,apply_sub]
    abel
  rw [he]
  calc
    _ ≤ ‖remainder ha hc hg hLg T U V‖+‖apply a (V-U-L (y-x))‖ := norm_add_le _ _
    _ ≤ Cr*‖y-x‖^2+(K : ℝ)*(C*‖y-x‖^2) :=
      add_le_add hr ((norm_apply_le a _).trans (mul_le_mul_of_nonneg_left (hquad y) K.coe_nonneg))
    _ = _ := by ring
end SphericalAging.FlowCoefficientDerivative
