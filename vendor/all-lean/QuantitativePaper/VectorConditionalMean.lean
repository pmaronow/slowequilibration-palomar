module
public import QuantitativePaper.VectorHessianResponse
public import QuantitativePaper.VectorGaussianExpectation

@[expose] public section

/-! Actual recursive terminal-spin conditional expectations, including their
covariance and its genuine positivity. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators NNReal
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets

def vectorConditionalMean {n k : ℕ} (s : RSBScheme k) (β t : ℝ) (p : Couplings n × ℝ)
    (b d : Configuration n → ℝ) : ℕ → ℝ → Field n → ℝ
  | 0 => fun y x => terminalMean (terminalTilt (vectorTerminalExponent n β t p x) b y) d
  | j+1 => fun y => vectorStepResponse ((1-t)*(β^2*(s.q (k+2-j)-s.q (k+1-j))))
      (s.m (k+1-j)) (vectorPerturbedRecursion s β t p b j y) (vectorConditionalMean s β t p b d j y)

theorem vectorConditionalMean_self {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (p : Couplings n × ℝ) (b : Configuration n → ℝ) (j : ℕ) :
    vectorConditionalMean s β t p b b j = vectorObservableResponse s β t p b j := by
  induction j with
  | zero => rfl
  | succ j ih => simp only [vectorConditionalMean,vectorObservableResponse,ih]

theorem measurable_vectorConditionalMean {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (p : Couplings n × ℝ) (b d : Configuration n → ℝ) (j : ℕ) :
    Measurable (fun q : ℝ × Field n => vectorConditionalMean s β t p b d j q.1 q.2) := by
  induction j with
  | zero =>
    unfold vectorConditionalMean terminalMean terminalWeight terminalPartition
      terminalTilt vectorTerminalExponent fieldDot
    fun_prop
  | succ j ih =>
    exact measurable_vectorStepResponse_parameter _ _
      (measurable_vectorPerturbedRecursion s β t p b j) ih _ _

theorem abs_vectorConditionalMean_le {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (p : Couplings n × ℝ) (b d : Configuration n → ℝ) (R : ℝ)
    (hd : ∀ σ,|d σ| ≤ R) (j : ℕ) (y : ℝ) (x : Field n) :
    |vectorConditionalMean s β t p b d j y x| ≤ R := by
  induction j generalizing x with
  | zero => exact terminalMean_bound _ d R hd
  | succ j ih =>
    exact abs_vectorStepResponse_le _ _ _ (vectorPerturbedRecursion_lipschitz s β t p b j y) _ _ R ih x

def vectorObservableCovariance {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (p : Couplings n × ℝ) (b : Configuration n → ℝ) (j : ℕ) (y : ℝ) (x : Field n) : ℝ :=
  vectorConditionalMean s β t p b (fun σ => b σ^2) j y x-(vectorObservableResponse s β t p b j y x)^2

theorem measurable_vectorObservableCovariance {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (p : Couplings n × ℝ) (b : Configuration n → ℝ) (j : ℕ) :
    Measurable (fun q : ℝ × Field n => vectorObservableCovariance s β t p b j q.1 q.2) :=
  (measurable_vectorConditionalMean s β t p b _ j).sub
    ((measurable_vectorObservableResponse s β t p b j).pow_const 2)

theorem vectorObservableCovariance_nonneg {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (p : Couplings n × ℝ) (b : Configuration n → ℝ) (R : ℝ≥0)
    (hb : ∀ σ,|b σ| ≤ R) (j : ℕ) (y : ℝ) (x : Field n) :
    0 ≤ vectorObservableCovariance s β t p b j y x := by
  have hb2 : ∀ σ,|b σ^2| ≤ (R : ℝ)^2 := by
    intro σ
    rw [abs_sq]
    have hh := mul_self_le_mul_self (abs_nonneg _) (hb σ)
    simpa [←pow_two] using hh
  induction j generalizing x with
  | zero =>
    simpa only [vectorObservableCovariance,vectorConditionalMean,vectorObservableResponse,
      vectorTerminalObservable,terminalCovariance,←pow_two] using
      terminalCovariance_self_nonneg (terminalTilt (vectorTerminalExponent n β t p x) b y) b
  | succ j ih =>
    let f := vectorPerturbedRecursion s β t p b j y
    let v := vectorObservableResponse s β t p b j y
    let w := vectorConditionalMean s β t p b (fun σ => b σ^2) j y
    let c := (1-t)*(β^2*(s.q (k+2-j)-s.q (k+1-j)))
    let m := s.m (k+1-j)
    have hf := vectorPerturbedRecursion_lipschitz s β t p b j y
    have hv : Measurable v := (measurable_vectorObservableResponse s β t p b j).comp
      (measurable_const.prodMk measurable_id)
    have hw : Measurable w := (measurable_vectorConditionalMean s β t p b _ j).comp
      (measurable_const.prodMk measurable_id)
    have hvb : ∀ z,|v z| ≤ R := fun z => abs_vectorObservableResponse_le s β t p b R hb j y z
    have hv2b : ∀ z,|v z^2| ≤ (R : ℝ)^2 := by
      intro z
      rw [abs_sq]
      have hh := mul_self_le_mul_self (abs_nonneg _) (hvb z)
      simpa [←pow_two] using hh
    have hwb : ∀ z,|w z| ≤ (R : ℝ)^2 := fun z => abs_vectorConditionalMean_le s β t p b _ _ hb2 j y z
    have hle : ∀ z,v z^2 ≤ w z := fun z => by have hh := ih z;dsimp [vectorObservableCovariance] at hh;linarith
    have hm := vectorStepResponse_mono f (fun z => v z^2) w _ hf (hv.pow_const 2) hw _ _ hv2b hwb hle c m x
    have hvar := vectorStepResponse_variance_nonneg f v _ hf hv R hvb c m x
    change 0 ≤ vectorStepResponse c m f w x-(vectorStepResponse c m f v x)^2
    linarith

theorem vectorObservableCovariance_le {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (p : Couplings n × ℝ) (b : Configuration n → ℝ) (R : ℝ≥0)
    (hb : ∀ σ,|b σ| ≤ R) (j : ℕ) (y : ℝ) (x : Field n) :
    vectorObservableCovariance s β t p b j y x ≤ (R : ℝ)^2 := by
  have hb2 : ∀ σ,|b σ^2| ≤ (R : ℝ)^2 := by
    intro σ
    rw [abs_sq]
    have hh := mul_self_le_mul_self (abs_nonneg _) (hb σ)
    simpa [←pow_two] using hh
  have hh := (abs_le.mp (abs_vectorConditionalMean_le s β t p b _ _ hb2 j y x)).2
  unfold vectorObservableCovariance
  nlinarith [sq_nonneg (vectorObservableResponse s β t p b j y x)]

theorem abs_vectorObservableCovariance_le {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (p : Couplings n × ℝ) (b : Configuration n → ℝ) (R : ℝ≥0)
    (hb : ∀ σ,|b σ| ≤ R) (j : ℕ) (y : ℝ) (x : Field n) :
    |vectorObservableCovariance s β t p b j y x| ≤ (R : ℝ)^2 := by
  rw [abs_of_nonneg (vectorObservableCovariance_nonneg s β t p b R hb j y x)]
  exact vectorObservableCovariance_le s β t p b R hb j y x

end QuantitativePaper
