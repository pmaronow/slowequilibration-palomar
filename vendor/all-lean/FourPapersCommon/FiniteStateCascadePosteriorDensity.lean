module
public import FourPapersCommon.FiniteStateCascadePosterior
public import QuantitativePaper.HistoryDensityExponential

@[expose] public section

/-! The honest fixed-reference Gaussian posterior and its exact normalized
exponential density. Both zero masses and singular Gaussian maps are kept. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal ContDiff NNReal
namespace FourPapersCommon
open OverlapPaper SpinGlass.AT
variable {S I : Type*} [Fintype S] [Fintype I] [Nonempty S]
  [MeasurableSpace S] [MeasurableSingletonClass S]
set_option maxHeartbeats 1200000

def cascadePosteriorJointDensity (V : S→ℝ) (a : ℕ→ℝ)
    (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S) (j : ℕ)
    (z : FiniteHistory (FiniteStateField S) j×S) : ℝ≥0∞ :=
  cascadePosteriorPathDensity V a L j z.1*ENNReal.ofReal (gtStateGibbs V (z.1 (Fin.last j)) z.2)

theorem measurable_cascadePosteriorJointDensity (V : S→ℝ) (a : ℕ→ℝ) (ha : ∀i,0≤a i)
    (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S) (j : ℕ) :
    Measurable (cascadePosteriorJointDensity V a L j) := by
  have hG : Measurable (fun z : FiniteStateField S×S=>gtStateGibbs V z.1 z.2) :=
    measurable_from_prod_countable_left fun σ=>(contDiff_gtStateGibbs V σ).continuous.measurable
  have hp : Measurable (fun z : FiniteHistory (FiniteStateField S) j×S=>
      (z.1 (Fin.last j),z.2)) := by fun_prop
  apply ((measurable_cascadePosteriorPathDensity V a ha L j).comp measurable_fst).mul
  exact (hG.comp hp).ennreal_ofReal

theorem cascadePosteriorLaw_density (V : S→ℝ) (a : ℕ→ℝ) (ha : ∀i,0≤a i)
    (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S) (j : ℕ) (H : FiniteStateField S) :
    cascadePosteriorLaw V a L j H=
      ((cascadePosteriorBaseHistoryLaw L j H).prod (Measure.count : Measure S)).withDensity
        (cascadePosteriorJointDensity V a L j) := by
  let w := fun (h : FiniteHistory (FiniteStateField S) j) (σ : S)=>
    ENNReal.ofReal (gtStateGibbs V (h (Fin.last j)) σ)
  have hG : Measurable (fun z : FiniteStateField S×S=>gtStateGibbs V z.1 z.2) :=
    measurable_from_prod_countable_left fun σ=>(contDiff_gtStateGibbs V σ).continuous.measurable
  have hp : Measurable (fun z : FiniteHistory (FiniteStateField S) j×S=>
      (z.1 (Fin.last j),z.2)) := by fun_prop
  have hw : Measurable (Function.uncurry w) := (hG.comp hp).ennreal_ofReal
  have he : cascadePosteriorTerminalKernel V j=
      (Kernel.const (FiniteHistory (FiniteStateField S) j) (Measure.count : Measure S)).withDensity w := by
    ext h : 1
    rw [Kernel.withDensity_apply _ hw,Kernel.const_apply]
    exact finiteStateGibbsKernel_apply V _
  haveI : IsSFiniteKernel ((Kernel.const (FiniteHistory (FiniteStateField S) j)
      (Measure.count : Measure S)).withDensity w) := by rw [←he];infer_instance
  rw [cascadePosteriorLaw,cascadePosteriorHistoryLaw_density V a ha L j H,he,
    Measure.withDensity_compProd_withDensity (measurable_cascadePosteriorPathDensity V a ha L j) hw,
    Measure.compProd_const]
  rfl

def cascadePosteriorCoordinateMap
    (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S) (j : ℕ) (H : FiniteStateField S)
    (z : (Fin j→FiniteStateGaussianInput I)×S) : FiniteHistory (FiniteStateField S) j×S :=
  (cascadePosteriorHistory L j H z.1,z.2)

theorem measurable_cascadePosteriorCoordinateMap
    (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S) (j : ℕ) (H : FiniteStateField S) :
    Measurable (cascadePosteriorCoordinateMap L j H) :=
  (measurable_cascadePosteriorHistory L j H).prodMap measurable_id

def cascadePosteriorGaussianBase (S I : Type*) [Fintype S] [Fintype I]
    [MeasurableSpace S] (j : ℕ) : Measure ((Fin j→FiniteStateGaussianInput I)×S) :=
  (Measure.pi (fun _ : Fin j=>stdGaussian (FiniteStateGaussianInput I))).prod Measure.count

def cascadePosteriorGaussianLaw (V : S→ℝ) (a : ℕ→ℝ)
    (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S) (j : ℕ) (H : FiniteStateField S) :=
  (cascadePosteriorGaussianBase S I j).withDensity
    (fun z=>cascadePosteriorJointDensity V a L j (cascadePosteriorCoordinateMap L j H z))

theorem cascadePosteriorGaussianLaw_map (V : S→ℝ) (a : ℕ→ℝ) (ha : ∀i,0≤a i)
    (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S) (j : ℕ) (H : FiniteStateField S) :
    (cascadePosteriorGaussianLaw V a L j H).map (cascadePosteriorCoordinateMap L j H)=
      cascadePosteriorLaw V a L j H := by
  rw [cascadePosteriorGaussianLaw,map_withDensity_pullback _ _
    (measurable_cascadePosteriorCoordinateMap L j H) _ (measurable_cascadePosteriorJointDensity V a ha L j)]
  change (((Measure.pi (fun _ : Fin j=>stdGaussian (FiniteStateGaussianInput I))).prod Measure.count).map
    (Prod.map (cascadePosteriorHistory L j H) id)).withDensity _=_
  rw [←Measure.map_prod_map _ _ (measurable_cascadePosteriorHistory L j H) measurable_id,
    cascadePosteriorHistory_map,Measure.map_id,cascadePosteriorLaw_density V a ha L j H]

theorem cascadePosteriorGaussianLaw_probability (V : S→ℝ) (a : ℕ→ℝ) (ha : ∀i,0≤a i)
    (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S) (j : ℕ) (H : FiniteStateField S) :
    IsProbabilityMeasure (cascadePosteriorGaussianLaw V a L j H) := by
  haveI := cascadePosteriorLaw_probability V a ha L j H
  constructor
  have hh := congrArg (fun P : Measure (FiniteHistory (FiniteStateField S) j×S)=>P univ)
    (cascadePosteriorGaussianLaw_map V a ha L j H)
  rw [Measure.map_apply (measurable_cascadePosteriorCoordinateMap L j H) MeasurableSet.univ,preimage_univ] at hh
  exact hh.trans (measure_univ (μ:=cascadePosteriorLaw V a L j H))

theorem finiteStateGaussianNormalizer_terminal_eq_exp (V : S→ℝ) (a : ℕ→ℝ) (ha : ∀i,0≤a i)
    (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S) (j : ℕ) (H : FiniteStateField S) :
    finiteStateGaussianNormalizer (a j) (L j) (finiteStateGaussianTerminalCascade V a L j) H=
      Real.exp (a j*finiteStateGaussianTerminalCascade V a L (j+1) H) := by
  unfold finiteStateGaussianNormalizer
  rw [finiteStateGaussianRawKernel_apply,integral_map (by fun_prop)
    (((contDiff_one_finiteStateGaussianTerminalCascade V a ha L j).continuous.measurable.const_mul _).exp.aestronglyMeasurable)]
  change (∫z,Real.exp (a j*finiteStateGaussianTerminalCascade V a L j (H+L j z))
    ∂stdGaussian (FiniteStateGaussianInput I))=_
  change _=Real.exp (a j*sourceLogAverage (stdGaussian (FiniteStateGaussianInput I)) (a j)
    (fun z=>finiteStateGaussianTerminalCascade V a L j (H+L j z)))
  by_cases hz : a j=0
  · simp [hz]
  · have hp := integral_exp_pos (integrable_exp_finiteStateGaussian_lipschitz
      (finiteStateGaussianTerminalCascade V a L j)
      (finiteStateGaussianTerminalCascade_lipschitz V a ha L j) (L j) H (a j))
    simp only [sourceLogAverage,hz,ite_false]
    rw [mul_div_cancel₀ _ hz,Real.exp_log hp]

end FourPapersCommon
