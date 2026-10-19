module
public import QuantitativePaper.VectorPastConditionalExpectation
public import Mathlib.Probability.Martingale.Basic

@[expose] public section

/-! Genuine finite-history terminal-observable and magnetization martingales
under the actual vector joint law. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets FourPapersCommon
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128

theorem vectorPastSigma_mono {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    {i j : ℕ} (hij : i≤j) : vectorPastSigma (n := n) s β t i ≤ vectorPastSigma s β t j := by
  let π := fun h : FiniteHistory (VectorState n) j =>
    fun r : Fin (i+1) => h (Fin.castLE (Nat.succ_le_succ hij) r)
  have hπ : Measurable π := Measurable.of_eval fun _ => measurable_pi_apply _
  apply MeasurableSpace.comap_le_comap_of_eq_comp π hπ
  funext p
  funext r
  rfl

def vectorPastFiltration {n k : ℕ} (s : RSBScheme k) (β t : ℝ) :
    Filtration (Fin (k+3)) (inferInstance : MeasurableSpace (VectorGaussianSpace n k × Configuration n)) where
  seq i := vectorPastSigma s β t i
  mono' := fun _ _ hij => vectorPastSigma_mono s β t hij
  le' i := vectorPastSigma_le s β t i

def vectorTerminalMeanProcess {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (d : Configuration n → ℝ) (i : Fin (k+3)) (p : VectorGaussianSpace n k × Configuration n) : ℝ :=
  vectorBackwardMean s β t d i (vectorEuclideanStateLinear s β t i p.1)

theorem stronglyAdapted_vectorTerminalMeanProcess {n k : ℕ} (s : RSBScheme k)
    (β t : ℝ) (d : Configuration n → ℝ) :
    StronglyAdapted (vectorPastFiltration s β t) (vectorTerminalMeanProcess (n := n) s β t d) := by
  intro i
  change StronglyMeasurable[vectorPastSigma s β t i]
    (fun p : VectorGaussianSpace n k × Configuration n =>
      vectorBackwardMean s β t d i (vectorEuclideanStateLinear s β t i p.1))
  have hY : Measurable[vectorPastSigma s β t i]
      (fun p : VectorGaussianSpace n k × Configuration n => vectorEuclideanPast s β t i p.1) :=
    Measurable.of_comap_le le_rfl
  have hX := (measurable_pi_apply (Fin.last (i : ℕ))).comp hY
  have hh := ((measurable_vectorBackwardMean s β t d i).comp hX).stronglyMeasurable
  simpa only [Function.comp_def,vectorEuclideanPast_last,vectorTerminalMeanProcess] using hh

theorem martingale_vectorTerminalMeanProcess {n k : ℕ} (s : RSBScheme k)
    (β t a : ℝ) (d : Configuration n → ℝ) :
    Martingale (vectorTerminalMeanProcess s β t d) (vectorPastFiltration s β t)
      (vectorEuclideanJointLaw (n := n) s β t a) := by
  letI := vectorEuclideanJointLaw_probability (n := n) s β t a
  apply (martingale_condExp (fun p : VectorGaussianSpace n k × Configuration n => d p.2)
    (vectorPastFiltration s β t) (vectorEuclideanJointLaw s β t a)).congr
    (stronglyAdapted_vectorTerminalMeanProcess s β t d)
  intro i
  exact condExp_vector_terminal_observable_past s β t a d i (by omega)

def vectorSpinMeanProcess {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (l : Fin n) (i : Fin (k+3)) (p : VectorGaussianSpace n k × Configuration n) : ℝ :=
  vectorMagnetization s β t (vectorEuclideanStateLinear s β t i p.1).1 (k+2-i)
    (vectorEuclideanStateLinear s β t i p.1).2 l

theorem vectorSpinMeanProcess_eq_terminalMean {n k : ℕ} (s : RSBScheme k) (β t : ℝ) (l : Fin n) :
    vectorSpinMeanProcess s β t l=vectorTerminalMeanProcess s β t (fun σ => Paper.spinSign (σ l)) := by
  funext i p
  exact (vectorBackwardMean_spin s β t i _ l).symm

theorem martingale_vectorSpinMeanProcess {n k : ℕ} (s : RSBScheme k)
    (β t a : ℝ) (l : Fin n) :
    Martingale (vectorSpinMeanProcess s β t l) (vectorPastFiltration s β t)
      (vectorEuclideanJointLaw s β t a) := by
  rw [vectorSpinMeanProcess_eq_terminalMean]
  exact martingale_vectorTerminalMeanProcess s β t a _

end QuantitativePaper
