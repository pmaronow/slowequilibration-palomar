module
public import QuantitativePaper.VectorObservableResponse
public import QuantitativePaper.VectorSecondResponse

@[expose] public section

/-! Actual second terminal-observable derivatives through the finite vector
Gaussian recursion. The derivative and every integrability/measurability input
are proved for the constructed objects. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators NNReal
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets

def vectorObservableSecondResponse {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (p : Couplings n × ℝ) (b : Configuration n → ℝ) : ℕ → ℝ → Field n → ℝ
  | 0 => fun y x => terminalCovariance (terminalTilt (vectorTerminalExponent n β t p x) b y) b b
  | j+1 => fun y => vectorStepSecondResponse ((1-t)*(β^2*(s.q (k+2-j)-s.q (k+1-j))))
      (s.m (k+1-j)) (vectorPerturbedRecursion s β t p b j y)
      (vectorObservableResponse s β t p b j y) (vectorObservableSecondResponse s β t p b j y)

def observableSecondBound (R : ℝ≥0) (j : ℕ) : ℝ≥0 := (2*j+1)*R^2

theorem abs_terminalCovariance_self_le {n : ℕ} (E b : Configuration n → ℝ) (R : ℝ≥0)
    (hb : ∀ σ,|b σ| ≤ R) : |terminalCovariance E b b| ≤ (R : ℝ)^2 := by
  have hp := terminalCovariance_self_nonneg E b
  have hb2 : ∀ σ,|b σ*b σ| ≤ (R : ℝ)^2 := by
    intro σ
    rw [←pow_two,abs_of_nonneg (sq_nonneg _)]
    have hh := mul_self_le_mul_self (abs_nonneg _) (hb σ)
    simpa [←pow_two] using hh
  have hmean := (abs_le.mp (terminalMean_bound E _ ((R : ℝ)^2) hb2)).2
  rw [abs_of_nonneg hp]
  unfold terminalCovariance
  nlinarith [sq_nonneg (terminalMean E b)]

theorem measurable_vectorObservableSecondResponse {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (p : Couplings n × ℝ) (b : Configuration n → ℝ) (j : ℕ) :
    Measurable (fun q : ℝ × Field n => vectorObservableSecondResponse s β t p b j q.1 q.2) := by
  induction j with
  | zero =>
    unfold vectorObservableSecondResponse terminalCovariance terminalMean terminalWeight terminalPartition
      terminalTilt vectorTerminalExponent fieldDot
    fun_prop
  | succ j ih =>
    let f := vectorPerturbedRecursion s β t p b j
    let v := vectorObservableResponse s β t p b j
    let w := vectorObservableSecondResponse s β t p b j
    have hf : Measurable (fun q : ℝ × Field n => f q.1 q.2) := measurable_vectorPerturbedRecursion s β t p b j
    have hv : Measurable (fun q : ℝ × Field n => v q.1 q.2) := measurable_vectorObservableResponse s β t p b j
    have hw : Measurable (fun q : ℝ × Field n => w q.1 q.2) := ih
    have h1 := measurable_vectorStepResponse_parameter f w hf hw
      ((1-t)*(β^2*(s.q (k+2-j)-s.q (k+1-j)))) (s.m (k+1-j))
    have h2 := measurable_vectorStepResponse_parameter f (fun y x => v y x^2) hf (hv.pow_const 2)
      ((1-t)*(β^2*(s.q (k+2-j)-s.q (k+1-j)))) (s.m (k+1-j))
    have h3 := measurable_vectorStepResponse_parameter f v hf hv
      ((1-t)*(β^2*(s.q (k+2-j)-s.q (k+1-j)))) (s.m (k+1-j))
    exact h1.add (measurable_const.mul (h2.sub (h3.pow_const 2)))

theorem abs_vectorObservableSecondResponse_le {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (p : Couplings n × ℝ) (b : Configuration n → ℝ) (R : ℝ≥0)
    (hb : ∀ σ,|b σ| ≤ R) (j : ℕ) (y : ℝ) (x : Field n) :
    |vectorObservableSecondResponse s β t p b j y x| ≤ observableSecondBound R j := by
  induction j generalizing x with
  | zero => simpa [vectorObservableSecondResponse,observableSecondBound] using abs_terminalCovariance_self_le _ b R hb
  | succ j ih =>
    have hh := abs_vectorStepSecondResponse_le _ _ _ _
      (vectorPerturbedRecursion_lipschitz s β t p b j y) R (observableSecondBound R j)
      (fun z => abs_vectorObservableResponse_le s β t p b R hb j y z) ih
      ((1-t)*(β^2*(s.q (k+2-j)-s.q (k+1-j)))) (s.m (k+1-j)) x
    have hm := s.m_le_one (p := k+1-j) (Nat.sub_le _ _)
    have hm0 := s.m_nonneg (p := k+1-j) (Nat.sub_le _ _)
    rw [abs_of_nonneg hm0] at hh
    apply hh.trans
    have hmul := mul_le_mul_of_nonneg_right hm (sq_nonneg (R : ℝ))
    simp only [observableSecondBound,NNReal.coe_mul,NNReal.coe_add,NNReal.coe_pow,
      NNReal.coe_natCast,NNReal.coe_one,Nat.cast_add] at *
    push_cast
    nlinarith

theorem hasDerivAt_vectorObservableResponse {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (p : Couplings n × ℝ) (b : Configuration n → ℝ) (R : ℝ≥0)
    (hb : ∀ σ,|b σ| ≤ R) (j : ℕ) (y : ℝ) (x : Field n) :
    HasDerivAt (fun r => vectorObservableResponse s β t p b j r x)
      (vectorObservableSecondResponse s β t p b j y x) y := by
  induction j generalizing x y with
  | zero => exact hasDerivAt_terminalMean_tilt _ b b y
  | succ j ih =>
    exact hasDerivAt_vectorStepResponse _ _ _ _ R (observableSecondBound R j)
      (vectorPerturbedRecursion_lipschitz s β t p b j)
      (fun y => (measurable_vectorObservableResponse s β t p b j).comp
        (measurable_const.prodMk measurable_id))
      (fun y => (measurable_vectorObservableSecondResponse s β t p b j).comp
        (measurable_const.prodMk measurable_id))
      (fun y z => abs_vectorObservableResponse_le s β t p b R hb j y z)
      (fun y z => abs_vectorObservableSecondResponse_le s β t p b R hb j y z)
      (fun y z => hasDerivAt_vectorPerturbedRecursion s β t p b R hb j y z)
      (fun y z => ih y z) _ _ x y

end QuantitativePaper
