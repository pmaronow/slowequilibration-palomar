module

public import SphericalAging.StochasticLinearizationError
public import SphericalAging.NonlinearIncrementFourthMoment

public section

/-! Genuine Fréchet differentiation of the constructed nonlinear SDE
solution in its initial state, as a full-filtration predictable L² class.
The derivative is the actual Jacobian matrix SDE resolvent. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal ContDiff
namespace SphericalAging.StochasticFlowDerivative
open HardSphereDynamics LocalSDE VariationalCoefficients PredictableLinearCoefficient
open PredictableItoTime PredictableDriftTime VolterraLinearity StochasticTaylorRemainder LinearResolvent
open StochasticLinearizationError NonlinearIncrementFourthMoment LinearSDETimeFourthMoment
set_option maxHeartbeats 1600000
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

@[expose]  def driftRows (D : BrownianDriver N P F) {Kb Ks : ℝ≥0}
    {b : Fin N → State N → ℝ} {s : Fin N → Fin N → State N → ℝ}
    (hbg : ∀ i, ContDiff ℝ ∞ (b i))
    (hb : ∀ i, LipschitzWith Kb (b i)) (hs : ∀ i j, LipschitzWith Ks (s i j))
    (x : State N) (T : ℝ≥0) (i : Fin N) : Coefficient (N := N) (F := F) (P := P) Kb :=
  derivativeRow (GlobalSDE.horizonProcess D hb hs x T)
    (GlobalSDE.horizonProcess_stronglyAdapted D hb hs x T)
    (GlobalSDE.horizonProcess_continuous D hb hs x T) (hbg i) (hb i) T

@[expose]  def noiseRows (D : BrownianDriver N P F) {Kb Ks : ℝ≥0}
    {b : Fin N → State N → ℝ} {s : Fin N → Fin N → State N → ℝ}
    (hsg : ∀ i j, ContDiff ℝ ∞ (s i j))
    (hb : ∀ i, LipschitzWith Kb (b i)) (hs : ∀ i j, LipschitzWith Ks (s i j))
    (x : State N) (T : ℝ≥0) (i j : Fin N) : Coefficient (N := N) (F := F) (P := P) Ks :=
  derivativeRow (GlobalSDE.horizonProcess D hb hs x T)
    (GlobalSDE.horizonProcess_stronglyAdapted D hb hs x T)
    (GlobalSDE.horizonProcess_continuous D hb hs x T) (hsg i j) (hs i j) T

@[expose]  def response (D : BrownianDriver N P F) {Kb Ks : ℝ≥0}
    {b : Fin N → State N → ℝ} {s : Fin N → Fin N → State N → ℝ}
    (hbg : ∀ i, ContDiff ℝ ∞ (b i)) (hsg : ∀ i j, ContDiff ℝ ∞ (s i j))
    (hb : ∀ i, LipschitzWith Kb (b i)) (hs : ∀ i j, LipschitzWith Ks (s i j))
    (x : State N) (T : ℝ≥0) : State N →L[ℝ] PredictableStateL2 N F P :=
  initialResponse D (driftRows D hbg hb hs x T) (noiseRows D hsg hb hs x T) T

/-- A uniform quadratic error proves true Fréchet differentiation rather
than only directional differentiation. Its fourth-moment input is proved
for the actual nonlinear increments by the bounded secant SDE. -/
 theorem quadratic_error_bound (D₀ : BrownianDriver N P F) {Kb Ks Lb Ls : ℝ≥0}
    {b : Fin N → State N → ℝ} {s : Fin N → Fin N → State N → ℝ}
    (hbg : ∀ i, ContDiff ℝ ∞ (b i)) (hsg : ∀ i j, ContDiff ℝ ∞ (s i j))
    (hb : ∀ i, LipschitzWith Kb (b i)) (hs : ∀ i j, LipschitzWith Ks (s i j))
    (hbd : ∀ i, LipschitzWith Lb (fderiv ℝ (b i)))
    (hsd : ∀ i j, LipschitzWith Ls (fderiv ℝ (s i j)))
    (x : State N) (T : ℝ≥0) (hT : 0 < T) : ∃ C : ℝ, 0 ≤ C ∧ ∀ y : State N,
      ‖GlobalSDE.horizonClass (NullAugmentation.driver D₀) hb hs y T-
        GlobalSDE.horizonClass (NullAugmentation.driver D₀) hb hs x T-
        response (NullAugmentation.driver D₀) hbg hsg hb hs x T (y-x)‖ ≤ C*‖y-x‖^2 := by
  let D := NullAugmentation.driver D₀
  let X := GlobalSDE.horizonProcess D hb hs x T
  let U := GlobalSDE.horizonClass D hb hs x T
  let hx := GlobalSDE.horizonProcess_stronglyAdapted D hb hs x T
  let hc := GlobalSDE.horizonProcess_continuous D hb hs x T
  let a := driftRows D hbg hb hs x T
  let z := noiseRows D hsg hb hs x T
  let L := sourceLinearMap D a z T
  let Cb := (Lb : ℝ)*Real.sqrt (fourthConstant N Kb Ks T)
  let Cs := (Ls : ℝ)*Real.sqrt (fourthConstant N Kb Ks T)
  let C := ‖L‖*((N : ℝ)*T*Cb+(N : ℝ)^2*Real.sqrt T*Cs)
  refine ⟨C,by dsimp [C,Cb,Cs];positivity,?_⟩
  intro y
  let Y := GlobalSDE.horizonProcess D hb hs y T
  let V := GlobalSDE.horizonClass D hb hs y T
  let rb := fun i => remainder hx hc (hbg i) (hb i) T U V
  let rs := fun i j => remainder hx hc (hsg i j) (hs i j) T U V
  have h4 := increment_fourthMoment D₀ hbg hsg hb hs x y T hT
  have hi : Integrable (fun q => ‖(Ioc (0 : ℝ≥0) T ×ˢ (univ : Set Ω)).indicator
      (fun q => Y q.1 q.2-X q.1 q.2) q‖^4) (nonnegativeLebesgueMeasure.prod P) := by
    simpa only [stateTimeCut_eq_indicator,increment] using h4.1.integrable_norm_pow (by norm_num)
  have hm : (∫ q,‖(Ioc (0 : ℝ≥0) T ×ˢ (univ : Set Ω)).indicator
      (fun q => Y q.1 q.2-X q.1 q.2) q‖^4 ∂nonnegativeLebesgueMeasure.prod P) ≤
      fourthConstant N Kb Ks T*‖y-x‖^4 := by
    simpa only [stateTimeCut_eq_indicator,increment] using h4.2
  have hbr : ∀ i,‖rb i‖ ≤ Cb*‖y-x‖^2 := fun i =>
    norm_remainder_le hx hc (GlobalSDE.horizonProcess_timeCut D hb hs x T)
      (GlobalSDE.horizonProcess_timeCut D hb hs y T) (hbg i) (hb i) (hbd i)
      hi _ (fourthConstant_nonneg N Kb Ks T) (y-x) hm
  have hsr : ∀ i j,‖rs i j‖ ≤ Cs*‖y-x‖^2 := fun i j =>
    norm_remainder_le hx hc (GlobalSDE.horizonProcess_timeCut D hb hs x T)
      (GlobalSDE.horizonProcess_timeCut D hb hs y T) (hsg i j) (hs i j) (hsd i j)
      hi _ (fourthConstant_nonneg N Kb Ks T) (y-x) hm
  have heq : V-U = L (initialClass (y-x) T+driftSource T rb+noiseSource D T rs) :=
    nonlinear_increment_resolvent hx hc D hbg hsg hb hs T U V x y
      (GlobalSDE.horizonClass_fixedPoint D hb hs x T) (GlobalSDE.horizonClass_fixedPoint D hb hs y T)
  change ‖V-U-L (initialClass (y-x) T)‖ ≤ C*‖y-x‖^2
  rw [heq,← map_sub]
  have ha : initialClass (F := NullAugmentation.augment F P) (P := P) (y-x) T+
      driftSource T rb+noiseSource D T rs-initialClass (y-x) T = driftSource T rb+noiseSource D T rs := by abel
  rw [ha]
  calc
    _ ≤ ‖L‖*‖driftSource T rb+noiseSource D T rs‖ := L.le_opNorm _
    _ ≤ ‖L‖*(‖driftSource T rb‖+‖noiseSource D T rs‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) (norm_nonneg L)
    _ ≤ ‖L‖*((N : ℝ)*T*(Cb*‖y-x‖^2)+(N : ℝ)^2*Real.sqrt T*(Cs*‖y-x‖^2)) :=
      mul_le_mul_of_nonneg_left
        (add_le_add (driftSource_norm_le T rb _ hbr) (noiseSource_norm_le D T rs _ hsr)) (norm_nonneg L)
    _ = _ := by dsimp [C];ring

/-- The actual nonlinear solution map has the actual Jacobian linear SDE
as its Fréchet derivative in the predictable L² state space. -/
 theorem horizonClass_hasFDerivAt_initial (D₀ : BrownianDriver N P F) {Kb Ks Lb Ls : ℝ≥0}
    {b : Fin N → State N → ℝ} {s : Fin N → Fin N → State N → ℝ}
    (hbg : ∀ i, ContDiff ℝ ∞ (b i)) (hsg : ∀ i j, ContDiff ℝ ∞ (s i j))
    (hb : ∀ i, LipschitzWith Kb (b i)) (hs : ∀ i j, LipschitzWith Ks (s i j))
    (hbd : ∀ i, LipschitzWith Lb (fderiv ℝ (b i)))
    (hsd : ∀ i j, LipschitzWith Ls (fderiv ℝ (s i j)))
    (x : State N) (T : ℝ≥0) (hT : 0 < T) :
    HasFDerivAt (fun y : State N => GlobalSDE.horizonClass (NullAugmentation.driver D₀) hb hs y T)
      (response (NullAugmentation.driver D₀) hbg hsg hb hs x T) x := by
  obtain ⟨C,hC,hquad⟩ := quadratic_error_bound D₀ hbg hsg hb hs hbd hsd x T hT
  rw [hasFDerivAt_iff_isLittleO,Asymptotics.isLittleO_iff]
  intro ε hε
  have hevent : ∀ᶠ y : State N in 𝓝 x,‖y-x‖ < ε/(C+1) := by
    have hh := Metric.ball_mem_nhds x (div_pos hε (by linarith : 0 < C+1))
    exact Filter.mem_of_superset hh (fun y hy => by
      simpa only [Metric.mem_ball,dist_eq_norm,Set.mem_ofPred_eq] using hy)
  filter_upwards [hevent] with y hy
  apply (hquad y).trans
  have hnorm := norm_nonneg (y-x)
  have hh : C*‖y-x‖ ≤ ε := by
    have he := (lt_div_iff₀ (by linarith : 0 < C+1)).mp hy
    nlinarith
  nlinarith
end SphericalAging.StochasticFlowDerivative
