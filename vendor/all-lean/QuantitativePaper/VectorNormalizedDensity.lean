module
public import QuantitativePaper.VectorJointDensity

@[expose] public section

/-! The literal finite disorder/field/spin density relative to the unweighted
Gaussian field history and counting measure, including the initial disorder tilt. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators NNReal ENNReal
namespace QuantitativePaper
set_option maxHeartbeats 1000000
open SpinGlass SpinGlass.Targets FourPapersCommon

def vectorBaseInitialLaw (n : ℕ) : Measure (VectorState n) :=
  (completionLaw n).map (fun p => (p,0))
instance vectorBaseInitialLaw_probability (n : ℕ) : IsProbabilityMeasure (vectorBaseInitialLaw n) :=
  (Measure.isProbabilityMeasure_map_iff (by fun_prop)).mpr inferInstance

def vectorInitialStateWeight {n k : ℕ} (s : RSBScheme k) (β t a : ℝ) (p : VectorState n) : ℝ≥0∞ :=
  ENNReal.ofReal (vectorOuterWeight s β t a p.1)

theorem measurable_vectorInitialStateWeight {n k : ℕ} (s : RSBScheme k) (β t a : ℝ) :
    Measurable (vectorInitialStateWeight (n := n) s β t a) := by
  have hf : Measurable (fun p : VectorState n => vectorRecursion s β t p.1 (k+2) 0) :=
    by
      have hg : Measurable (fun p : VectorState n => (p.1,(0 : Field n))) :=
        measurable_fst.prodMk measurable_const
      have hh := (measurable_vectorRecursion (n := n) s β t (k+2)).comp hg
      simpa only [Function.comp_def] using hh
  unfold vectorInitialStateWeight vectorOuterWeight
  exact ((Real.measurable_exp.comp ((measurable_const (a := a)).mul hf)).div_const
    (vectorOuterPartition (n := n) s β t a)).ennreal_ofReal

theorem vectorInitialLaw_eq_withDensity {n k : ℕ} (s : RSBScheme k) (β t a : ℝ) :
    vectorInitialLaw (n := n) s β t a =
      (vectorBaseInitialLaw n).withDensity (vectorInitialStateWeight s β t a) := by
  exact map_withDensity_pullback (completionLaw n) (fun p => (p,0)) (by fun_prop)
    (vectorInitialStateWeight s β t a) (measurable_vectorInitialStateWeight s β t a)

def vectorBaseFieldHistoryLaw {n k : ℕ} (s : RSBScheme k) (β t : ℝ) :
    Measure (FiniteHistory (VectorState n) (k+2)) :=
  finiteHistoryLaw (vectorBaseInitialLaw n) (vectorProfileBaseKernel s β t) (k+2)

instance vectorBaseFieldHistoryLaw_probability {n k : ℕ} (s : RSBScheme k) (β t : ℝ) :
    IsProbabilityMeasure (vectorBaseFieldHistoryLaw (n := n) s β t) :=
  isProbabilityMeasure_finiteHistoryLaw _ _ (vectorProfileBaseKernel_markov s β t) _

def vectorFullHistoryDensity {n k : ℕ} (s : RSBScheme k) (β t a : ℝ)
    (history : FiniteHistory (VectorState n) (k+2)) : ℝ≥0∞ :=
  vectorInitialStateWeight s β t a (history 0)*finiteHistoryDensity (vectorProfileWeight s β t) (k+2) history

theorem measurable_vectorFullHistoryDensity {n k : ℕ} (s : RSBScheme k) (β t a : ℝ) :
    Measurable (vectorFullHistoryDensity (n := n) s β t a) :=
by
  unfold vectorFullHistoryDensity
  exact ((measurable_vectorInitialStateWeight s β t a).comp (measurable_pi_apply (0 : Fin (k+3)))).mul
    (measurable_finiteHistoryDensity _ (measurable_vectorProfileWeight s β t) (k+2))

theorem vectorFieldHistoryLaw_eq_fullDensity {n k : ℕ} (s : RSBScheme k) (β t a : ℝ) :
    vectorFieldHistoryLaw (n := n) s β t a =
      (vectorBaseFieldHistoryLaw s β t).withDensity (vectorFullHistoryDensity s β t a) := by
  have := vectorOuterLaw_probability (n := n) s β t a
  have : IsProbabilityMeasure (vectorInitialLaw (n := n) s β t a) :=
    (Measure.isProbabilityMeasure_map_iff (by fun_prop)).mpr inferInstance
  exact finiteHistoryLaw_withDensity_initial_and_transitions _ _ _ _
    (vectorProfileBaseKernel_markov s β t) (vectorProfileKernel_markov s β t)
    _ (measurable_vectorInitialStateWeight s β t a) (vectorInitialLaw_eq_withDensity s β t a)
    _ (measurable_vectorProfileWeight s β t) (vectorProfileKernel_eq_withDensity s β t) _

def vectorHistoryTerminalWeight {n k : ℕ} (_s : RSBScheme k) (β t : ℝ)
    (history : FiniteHistory (VectorState n) (k+2)) (σ : Configuration n) : ℝ≥0∞ :=
  ENNReal.ofReal (terminalWeight (vectorTerminalExponent n β t
    (history (Fin.last (k+2))).1 (history (Fin.last (k+2))).2) σ)

theorem measurable_vectorHistoryTerminalWeight {n k : ℕ} (s : RSBScheme k) (β t : ℝ) :
    Measurable (Function.uncurry (vectorHistoryTerminalWeight (n := n) s β t)) := by
  unfold vectorHistoryTerminalWeight terminalWeight terminalPartition vectorTerminalExponent
    energy Paper.skHamiltonian fieldDot
  fun_prop

def vectorNormalizedDensity {n k : ℕ} (s : RSBScheme k) (β t a : ℝ)
    (p : FiniteHistory (VectorState n) (k+2) × Configuration n) : ℝ≥0∞ :=
  vectorFullHistoryDensity s β t a p.1*vectorHistoryTerminalWeight s β t p.1 p.2

theorem vectorJointLaw_eq_normalizedDensity {n k : ℕ} (s : RSBScheme k) (β t a : ℝ) :
    vectorJointLaw (n := n) s β t a =
      ((vectorBaseFieldHistoryLaw s β t) ⊗ₘ
        Kernel.const (FiniteHistory (VectorState n) (k+2)) (Measure.count : Measure (Configuration n))).withDensity
          (vectorNormalizedDensity s β t a) := by
  let κ : Kernel (FiniteHistory (VectorState n) (k+2)) (Configuration n) :=
    (terminalSpinKernel (fun p : VectorState n => vectorTerminalExponent n β t p.1 p.2)
      (measurable_vectorTerminalExponent_state n β t)).comap
        (fun history => history (Fin.last (k+2))) (measurable_pi_apply _)
  have he : κ = (Kernel.const (FiniteHistory (VectorState n) (k+2))
      (Measure.count : Measure (Configuration n))).withDensity (vectorHistoryTerminalWeight s β t) := by
    ext history : 1
    rw [Kernel.withDensity_apply _ (measurable_vectorHistoryTerminalWeight s β t),Kernel.const_apply]
    exact terminalLaw_eq_count_withDensity _
  have : IsSFiniteKernel ((Kernel.const (FiniteHistory (VectorState n) (k+2))
      (Measure.count : Measure (Configuration n))).withDensity (vectorHistoryTerminalWeight s β t)) := by
    rw [← he]
    infer_instance
  change (vectorFieldHistoryLaw s β t a) ⊗ₘ κ = _
  rw [vectorFieldHistoryLaw_eq_fullDensity,he,Measure.withDensity_compProd_withDensity
    (measurable_vectorFullHistoryDensity s β t a) (measurable_vectorHistoryTerminalWeight s β t)]
  rfl

end QuantitativePaper
