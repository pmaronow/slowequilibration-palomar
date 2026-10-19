module

public import SphericalAging.RandomInitialSDE
public import SphericalAging.AnnealedSDECore

public section

/-! Identify fixed-coefficient strong-solution semantics with the genuine
random-coefficient semantics used for product-law pullback and restart.
Every coefficient and terminal stochastic class is constructed from the
actual process in the input SDE. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal
namespace SphericalAging.RandomSDEConversions
open HardSphereDynamics LocalSDE RandomInitialSDE AnnealedSDECore VectorIto
open FourPapersCommon.FilteredBrownian
set_option maxHeartbeats 1200000
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

/-- Actual coefficient classes at shorter horizons are genuine terminal restrictions. -/
lemma coefficientActual_restrict {X : ℝ≥0 → Ω → State N}
    (ha : StronglyAdapted F X) (hc : ∀ᵐ ω ∂P,Continuous (fun t => X t ω))
    {g : State N → ℝ} (hg : Continuous g) {t T : ℝ≥0} (ht : t ≤ T)
    (hmT : MemLp (FourPapersCommon.continuousAdaptedTimeCut (fun r ω => g (X r ω)) T)
      2 (nonnegativeLebesgueMeasure.prod P))
    (hmt : MemLp (FourPapersCommon.continuousAdaptedTimeCut (fun r ω => g (X r ω)) t)
      2 (nonnegativeLebesgueMeasure.prod P)) :
    coefficientPredictableActual ha hc hg t hmt =
      FourPapersCommon.FilteredBrownian.predictableTimeRestrict F t
        (coefficientPredictableActual ha hc hg T hmT) := by
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [hmt.coeFn_toLp,hmT.coeFn_toLp,
    FourPapersCommon.FilteredBrownian.predictableTimeRestrict_coeFn F t
      (coefficientPredictableActual ha hc hg T hmT)] with z hsmall hlarge hcut
  change (hmt.toLp _ : ℝ≥0 × Ω → ℝ) z = _
  rw [hsmall,hcut]
  change _ = (FourPapersCommon.FilteredBrownian.predictableTimeFrame t).indicator
    (hmT.toLp _) z
  by_cases hz : z.1 ∈ Ioc (0 : ℝ≥0) t
  · simp only [FourPapersCommon.continuousAdaptedTimeCut,ite_eq_left hz,
      Set.indicator_of_mem (show z ∈ FourPapersCommon.FilteredBrownian.predictableTimeFrame t from ⟨hz,mem_univ _⟩),
      hlarge,ite_eq_left (show z.1 ∈ Ioc (0 : ℝ≥0) T from ⟨hz.1,hz.2.trans ht⟩)]
  · simp [FourPapersCommon.continuousAdaptedTimeCut,FourPapersCommon.FilteredBrownian.predictableTimeFrame,hz]

/-- Genuine random-initial strong SDE implies the actual random-coefficient
integral equation, with the same physical process and driver. -/
theorem strongSolution_to_random {b : Fin N → State N → ℝ}
    {sigma : Fin N → Fin N → State N → ℝ} {hsigma : ∀ i j,Continuous (sigma i j)}
    {D : BrownianDriver N P F} {Z0 : Ω → State N} {X : ℝ≥0 → Ω → State N} {T : ℝ≥0}
    (hb : ∀ i,Continuous (b i)) (hZ : StronglyMeasurable[F 0] Z0)
    (h : RandomInitialSDE.IsStrongSolutionOn b sigma hsigma D Z0 X T) :
    IsRandomStrongSolutionOn D (fun _ => b) (fun _ => sigma) Z0 X T := by
  rcases h with ⟨ha,hc,hm,hs,heq⟩
  refine ⟨hZ,ha,hc,fun i => coefficientPredictableActual ha hc (hb i) T (hm i),
    fun i j => coefficientPredictableActual ha hc (hsigma i j) T (hs i j T le_rfl),
    fun i => (hm i).coeFn_toLp,fun i j => (hs i j T le_rfl).coeFn_toLp,?_⟩
  intro t ht i
  have hrows : (fun j => coefficientPredictableActual ha hc (hsigma i j) t (hs i j t ht)) =
      (fun j => FourPapersCommon.FilteredBrownian.predictableTimeRestrict F t
        (coefficientPredictableActual ha hc (hsigma i j) T (hs i j T le_rfl))) :=
    funext (fun j => coefficientActual_restrict ha hc (hsigma i j) ht _ _)
  have hEq := heq t ht i
  rw [hrows] at hEq
  simpa only [vectorProcessLp,driverItoMap_apply,vectorIto,coordinateIto] using hEq

/-- The deterministic-initial physical equation is the same literal
random-coefficient SDE with a constant initial random variable. -/
theorem localStrongSolution_to_random {b : Fin N → State N → ℝ}
    {sigma : Fin N → Fin N → State N → ℝ} {hsigma : ∀ i j,Continuous (sigma i j)}
    {D : BrownianDriver N P F} {x : State N} {X : ℝ≥0 → Ω → State N} {T : ℝ≥0}
    (hb : ∀ i,Continuous (b i))
    (h : LocalSDE.IsLocalStrongSolutionOn b sigma hsigma D x X T) :
    IsRandomStrongSolutionOn D (fun _ => b) (fun _ => sigma) (fun _ => x) X T :=
  strongSolution_to_random hb stronglyMeasurable_const h

end SphericalAging.RandomSDEConversions
