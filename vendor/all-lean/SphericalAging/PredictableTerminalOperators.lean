module

public import SphericalAging.GlobalHamiltonianParameter

public section

/-! Actual deterministic and stochastic terminal values in L²(F_t).
Their continuity follows from the proved integration operators and actual
continuous versions, and will be used to construct joint solution paths.
-/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal
namespace SphericalAging.PredictableTerminalOperators
open HardSphereDynamics PredictableItoTime PredictableDriftTime
open FourPapersCommon.FilteredBrownian
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

/-- Actual drift primitive at a deterministic terminal time, with its L² class. -/
@[expose] def driftTerminal (T t : ℝ≥0) (U : PredictableProcessL2 F P) : RandomL2 P :=
  (driftVersion_memLp U T t).toLp (driftVersion U T t)

lemma driftTerminal_sub (T t : ℝ≥0) (U V : PredictableProcessL2 F P) :
    driftTerminal T t (U-V) = driftTerminal T t U-driftTerminal T t V := by
  apply Lp.ext
  filter_upwards [(driftVersion_memLp (U-V) T t).coeFn_toLp,
    (driftVersion_memLp U T t).coeFn_toLp,(driftVersion_memLp V T t).coeFn_toLp,
    driftVersion_sub_ae U V T,Lp.coeFn_sub (driftTerminal T t U) (driftTerminal T t V)]
    with ω hsub hU hV hp hd
  change ((driftVersion_memLp (U-V) T t).toLp _ : Ω → ℝ) ω = _
  rw [hsub,hd,Pi.sub_apply]
  change driftVersion (U-V) T t ω =
    ((driftVersion_memLp U T t).toLp _ : Ω → ℝ) ω-
      ((driftVersion_memLp V T t).toLp _ : Ω → ℝ) ω
  rw [hU,hV,hp t]

lemma driftTerminal_lipschitz (T t : ℝ≥0) :
    LipschitzWith (NNReal.sqrt T) (driftTerminal (F := F) (P := P) T t) := by
  apply LipschitzWith.of_dist_le_mul
  intro U V
  simp only [dist_eq_norm,← driftTerminal_sub]
  simpa only [Real.coe_sqrt,driftTerminal] using norm_driftVersion_toLp_le (U-V) T t

/-- Actual terminal drift value bundled in the actual sub-sigma-algebra F_t. -/
@[expose] def driftTerminalAdapted (T t : ℝ≥0) (U : PredictableProcessL2 F P) : lpMeas ℝ ℝ (F t) 2 P :=
  ⟨driftTerminal T t U,((driftVersion_stronglyAdapted U T t).aestronglyMeasurable).congr
    (driftVersion_memLp U T t).coeFn_toLp.symm⟩

lemma driftTerminalAdapted_lipschitz (T t : ℝ≥0) :
    LipschitzWith (NNReal.sqrt T) (driftTerminalAdapted (F := F) (P := P) T t) := by
  intro U V
  exact driftTerminal_lipschitz T t U V

lemma itoTerminalAdapted_lipschitz (D : BrownianDriver N P F) (j : Fin N) (t : ℝ≥0) :
    LipschitzWith 1 (fun U : PredictableProcessL2 F P =>
      naturalItoProcessLpMeas (D.filtered j).toIsPreBrownianReal
        (D.coordinateStronglyMeasurable j) (D.filtered j) U t) := by
  apply LipschitzWith.of_dist_le_mul
  intro U V
  change dist (naturalItoProcess (D.filtered j).toIsPreBrownianReal
      (D.coordinateStronglyMeasurable j) (D.filtered j) U t)
    (naturalItoProcess (D.filtered j).toIsPreBrownianReal
      (D.coordinateStronglyMeasurable j) (D.filtered j) V t) ≤ _
  simp only [dist_eq_norm,NNReal.coe_one,one_mul]
  unfold FourPapersCommon.FilteredBrownian.naturalItoProcess
  rw [← map_sub,← FourPapersCommon.FilteredBrownian.predictableTimeRestrict_sub]
  exact FourPapersCommon.FilteredBrownian.norm_naturalItoProcess_le _ _ _ _ _

/-- Constant initial random variable as an actual F_t-measurable L² class. -/
@[expose] def initialTerminal (t : ℝ≥0) (x : ℝ) : lpMeas ℝ ℝ (F t) 2 P :=
  ⟨Lp.const 2 P x,aestronglyMeasurable_const.congr (Lp.coeFn_const 2 P x).symm⟩

lemma initialTerminal_lipschitz (t : ℝ≥0) :
    LipschitzWith 1 (initialTerminal (F := F) (P := P) t) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  change dist (Lp.const 2 P x) (Lp.const 2 P y) ≤ _
  rw [dist_eq_norm,← (Lp.const 2 P).map_sub]
  simp only [NNReal.coe_one,one_mul,dist_eq_norm]
  simpa using Lp.norm_const_le 2 P (x-y)

/-- Lift a true scalar F_t class along one actual Euclidean basis vector. -/
@[expose] def scalarToStateTerminal (t : ℝ≥0) (i : Fin N) (U : lpMeas ℝ ℝ (F t) 2 P) :
    lpMeas (State N) ℝ (F t) 2 P :=
  ⟨(ContinuousLinearMap.toSpanSingleton ℝ (basisVector i)).compLp (U : RandomL2 P),
    ((lpMeas.aestronglyMeasurable U).smul_const (basisVector i)).congr (by
      have h := (ContinuousLinearMap.toSpanSingleton ℝ (basisVector i)).coeFn_compLp (U : RandomL2 P)
      filter_upwards [h] with ω hω
      simpa only [ContinuousLinearMap.toSpanSingleton_apply] using hω.symm)⟩

omit [IsProbabilityMeasure P] in
lemma scalarToStateTerminal_continuous (t : ℝ≥0) (i : Fin N) :
    Continuous (scalarToStateTerminal (F := F) (P := P) t i) := by
  apply continuous_induced_rng.mpr
  exact ((ContinuousLinearMap.toSpanSingleton ℝ (basisVector i)).compLpL 2 P).continuous.comp continuous_subtype_val

end SphericalAging.PredictableTerminalOperators
