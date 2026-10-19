module
public import FourPapersCommon.FiniteStateCascadeExpectations
public import FourPapersCommon.FiniteHistoryDensity
public import FourPapersCommon.IndependentHistory
public import FourPapersCommon.HistoryInitial
public import FourPapersCommon.GenericFiniteStateCascadeCalculus

@[expose] public section

/-! The actual remaining Gaussian history and terminal spin posterior from
an arbitrary initial field. Its coordinate reference measure is fixed as
that initial field varies. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal ContDiff NNReal
namespace FourPapersCommon
open OverlapPaper SpinGlass.AT
variable {S I : Type*} [Fintype S] [Fintype I] [Nonempty S]
  [MeasurableSpace S] [MeasurableSingletonClass S]
set_option maxHeartbeats 1200000

abbrev CascadePosteriorNoise (I : Type*) [Fintype I] := FiniteStateGaussianInput I

def cascadePosteriorUpdate (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S)
    (j i : ℕ) (H : FiniteStateField S) (z : FiniteStateGaussianInput I) : FiniteStateField S :=
  H+L (j-1-i) z

theorem measurable_cascadePosteriorUpdate
    (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S) (j i : ℕ) :
    Measurable (Function.uncurry (cascadePosteriorUpdate L j i)) := by
  unfold cascadePosteriorUpdate
  fun_prop

def cascadePosteriorHistory
    (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S)
    (j : ℕ) (H : FiniteStateField S) (z : Fin j→FiniteStateGaussianInput I) :
    FiniteHistory (FiniteStateField S) j :=
  independentHistory (cascadePosteriorUpdate L j) j (H,z)

theorem measurable_cascadePosteriorHistory
    (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S)
    (j : ℕ) (H : FiniteStateField S) : Measurable (cascadePosteriorHistory L j H) :=
  (measurable_independentHistory _ (measurable_cascadePosteriorUpdate L j) j).comp
    (measurable_const.prodMk measurable_id)

def cascadePosteriorRawKernel
    (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S) (j i : ℕ) :=
  finiteStateGaussianRawKernel (L (j-1-i))

instance cascadePosteriorRawKernel_markov
    (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S) (j i : ℕ) :
    IsMarkovKernel (cascadePosteriorRawKernel L j i) := by
  unfold cascadePosteriorRawKernel
  infer_instance

def cascadePosteriorKernel (V : S→ℝ) (a : ℕ→ℝ)
    (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S) (j i : ℕ) :=
  finiteStateGaussianCascadeKernel a L (gtStateLogPartition V) (j-1-i)

theorem cascadePosteriorKernel_markov (V : S→ℝ) (a : ℕ→ℝ) (ha : ∀i,0≤a i)
    (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S) (j i : ℕ) :
    IsMarkovKernel (cascadePosteriorKernel V a L j i) :=
  isMarkovKernel_finiteStateGaussianTerminalCascadeKernel V a ha L _

def cascadePosteriorTransitionWeight (V : S→ℝ) (a : ℕ→ℝ)
    (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S) (j i : ℕ)
    (H Q : FiniteStateField S) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (a (j-1-i)*finiteStateGaussianTerminalCascade V a L (j-1-i) Q)/
    finiteStateGaussianNormalizer (a (j-1-i)) (L (j-1-i))
      (finiteStateGaussianTerminalCascade V a L (j-1-i)) H)

theorem measurable_cascadePosteriorTransitionWeight (V : S→ℝ) (a : ℕ→ℝ) (ha : ∀i,0≤a i)
    (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S) (j i : ℕ) :
    Measurable (Function.uncurry (cascadePosteriorTransitionWeight V a L j i)) := by
  have hU := (contDiff_one_finiteStateGaussianTerminalCascade V a ha L (j-1-i)).continuous.measurable
  have hN : Measurable (finiteStateGaussianNormalizer (a (j-1-i)) (L (j-1-i))
      (finiteStateGaussianTerminalCascade V a L (j-1-i))) :=
    ((hU.const_mul _).exp.stronglyMeasurable.integral_kernel).measurable
  exact (((hU.comp measurable_snd).const_mul _).exp.div (hN.comp measurable_fst)).ennreal_ofReal

def cascadePosteriorBaseHistoryLaw
    (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S) (j : ℕ) (H : FiniteStateField S) :=
  finiteHistoryLaw (Measure.dirac H) (cascadePosteriorRawKernel L j) j

instance cascadePosteriorBaseHistoryLaw_probability
    (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S) (j : ℕ) (H : FiniteStateField S) :
    IsProbabilityMeasure (cascadePosteriorBaseHistoryLaw L j H) :=
  isProbabilityMeasure_finiteHistoryLaw _ _ (fun i=>inferInstance) j

def cascadePosteriorHistoryLaw (V : S→ℝ) (a : ℕ→ℝ)
    (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S) (j : ℕ) (H : FiniteStateField S) :=
  finiteHistoryLaw (Measure.dirac H) (cascadePosteriorKernel V a L j) j

theorem cascadePosteriorHistoryLaw_probability (V : S→ℝ) (a : ℕ→ℝ) (ha : ∀i,0≤a i)
    (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S) (j : ℕ) (H : FiniteStateField S) :
    IsProbabilityMeasure (cascadePosteriorHistoryLaw V a L j H) :=
  isProbabilityMeasure_finiteHistoryLaw _ _ (fun i=>cascadePosteriorKernel_markov V a ha L j i) j

theorem cascadePosteriorHistory_map
    (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S) (j : ℕ) (H : FiniteStateField S) :
    (Measure.pi (fun _ : Fin j=>stdGaussian (FiniteStateGaussianInput I))).map
      (cascadePosteriorHistory L j H)=cascadePosteriorBaseHistoryLaw L j H := by
  have hh := independentHistory_law (Measure.dirac H) (stdGaussian (FiniteStateGaussianInput I))
    (cascadePosteriorUpdate L j) (measurable_cascadePosteriorUpdate L j)
    (cascadePosteriorRawKernel L j) (fun i=>inferInstance)
    (fun i H=>finiteStateGaussianRawKernel_apply _ H) j
  rw [Measure.dirac_prod,Measure.map_map
    (measurable_independentHistory _ (measurable_cascadePosteriorUpdate L j) j)
    measurable_prodMk_left] at hh
  exact hh

def cascadePosteriorPathDensity (V : S→ℝ) (a : ℕ→ℝ)
    (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S) (j : ℕ)
    (h : FiniteHistory (FiniteStateField S) j) : ℝ≥0∞ :=
  finiteHistoryDensity (cascadePosteriorTransitionWeight V a L j) j h

theorem measurable_cascadePosteriorPathDensity (V : S→ℝ) (a : ℕ→ℝ) (ha : ∀i,0≤a i)
    (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S) (j : ℕ) :
    Measurable (cascadePosteriorPathDensity V a L j) :=
  measurable_finiteHistoryDensity _ (measurable_cascadePosteriorTransitionWeight V a ha L j) j

theorem cascadePosteriorHistoryLaw_density (V : S→ℝ) (a : ℕ→ℝ) (ha : ∀i,0≤a i)
    (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S) (j : ℕ) (H : FiniteStateField S) :
    cascadePosteriorHistoryLaw V a L j H=
      (cascadePosteriorBaseHistoryLaw L j H).withDensity (cascadePosteriorPathDensity V a L j) :=
  finiteHistoryLaw_withDensity _ _ _ (fun i=>inferInstance)
    (fun i=>cascadePosteriorKernel_markov V a ha L j i) _
    (measurable_cascadePosteriorTransitionWeight V a ha L j) (fun i=>rfl) j

def cascadePosteriorTerminalKernel (V : S→ℝ) (j : ℕ) :
    Kernel (FiniteHistory (FiniteStateField S) j) S :=
  (finiteStateGibbsKernel V).comap (fun h=>h (Fin.last j)) (measurable_pi_apply _)

instance cascadePosteriorTerminalKernel_markov (V : S→ℝ) (j : ℕ) :
    IsMarkovKernel (cascadePosteriorTerminalKernel V j) := by
  haveI := isMarkovKernel_finiteStateGibbsKernel V
  unfold cascadePosteriorTerminalKernel
  infer_instance

def cascadePosteriorLaw (V : S→ℝ) (a : ℕ→ℝ)
    (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S) (j : ℕ) (H : FiniteStateField S) :
    Measure (FiniteHistory (FiniteStateField S) j×S) :=
  cascadePosteriorHistoryLaw V a L j H ⊗ₘ cascadePosteriorTerminalKernel V j

theorem cascadePosteriorLaw_probability (V : S→ℝ) (a : ℕ→ℝ) (ha : ∀i,0≤a i)
    (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S) (j : ℕ) (H : FiniteStateField S) :
    IsProbabilityMeasure (cascadePosteriorLaw V a L j H) := by
  haveI := cascadePosteriorHistoryLaw_probability V a ha L j H
  haveI := cascadePosteriorHistoryLaw_probability V a ha L j H
  unfold cascadePosteriorLaw
  infer_instance

end FourPapersCommon
