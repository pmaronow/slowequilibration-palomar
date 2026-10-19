module
public import QuantitativePaper.VectorResponse
public import QuantitativePaper.VectorTransitionKernel

@[expose] public section

/-! The actual first derivative of every finite vector recursion in an arbitrary
bounded terminal-spin observable direction. No derivative premise is supplied
for the recursively constructed potential or response. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators NNReal
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets

variable {n : ℕ} {A : Type*} [MeasurableSpace A]

theorem measurable_vectorStepResponse_parameter (f v : A → Field n → ℝ)
    (hf : Measurable (fun p : A × Field n => f p.1 p.2))
    (hv : Measurable (fun p : A × Field n => v p.1 p.2)) (c m : ℝ) :
    Measurable (fun p : A × Field n => vectorStepResponse c m (f p.1) (v p.1) p.2) := by
  have hs : Measurable (fun p : (A × Field n) × Field n => (p.1.1,fieldShift c p.1.2 p.2)) := by
    unfold fieldShift
    fun_prop
  have hw : Measurable (fun p : (A × Field n) × Field n =>
      vectorStepWeight c m (f p.1.1) p.1.2 p.2) :=
    (measurable_vectorStateWeight f hf c m).comp (measurable_fst.prodMk hs)
  have hprod : Measurable (fun p : (A × Field n) × Field n =>
      vectorStepWeight c m (f p.1.1) p.1.2 p.2*v p.1.1 (fieldShift c p.1.2 p.2)) :=
    hw.mul (hv.comp hs)
  exact (hprod.stronglyMeasurable.integral_prod_right' (ν := fieldGaussian n)).measurable

def vectorPerturbedTerminalPotential (n : ℕ) (β t : ℝ) (p : Couplings n × ℝ)
    (b : Configuration n → ℝ) (y : ℝ) (x : Field n) : ℝ :=
  terminalPotential (terminalTilt (vectorTerminalExponent n β t p x) b y)

def vectorTerminalObservable (n : ℕ) (β t : ℝ) (p : Couplings n × ℝ)
    (b : Configuration n → ℝ) (y : ℝ) (x : Field n) : ℝ :=
  terminalMean (terminalTilt (vectorTerminalExponent n β t p x) b y) b

theorem vectorPerturbedTerminalPotential_lipschitz (n : ℕ) (β t : ℝ)
    (p : Couplings n × ℝ) (b : Configuration n → ℝ) (y : ℝ) :
    LipschitzWith (Real.sqrt (n : ℝ)).toNNReal (vectorPerturbedTerminalPotential n β t p b y) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro x z
  rw [Real.dist_eq,dist_eq_norm,Real.coe_toNNReal _ (Real.sqrt_nonneg _)]
  apply abs_terminalPotential_sub_le
  intro σ
  have heq : terminalTilt (vectorTerminalExponent n β t p x) b y σ-
      terminalTilt (vectorTerminalExponent n β t p z) b y σ = fieldDot x σ-fieldDot z σ := by
    unfold terminalTilt vectorTerminalExponent
    ring
  rw [heq,fieldDot_sub]
  exact abs_fieldDot _ _

def vectorPerturbedRecursion {n k : ℕ} (s : RSBScheme k) (β t : ℝ) (p : Couplings n × ℝ)
    (b : Configuration n → ℝ) : ℕ → ℝ → Field n → ℝ
  | 0 => vectorPerturbedTerminalPotential n β t p b
  | j+1 => fun y => vectorColeHopfStep ((1-t)*(β^2*(s.q (k+2-j)-s.q (k+1-j))))
      (s.m (k+1-j)) (vectorPerturbedRecursion s β t p b j y)

def vectorObservableResponse {n k : ℕ} (s : RSBScheme k) (β t : ℝ) (p : Couplings n × ℝ)
    (b : Configuration n → ℝ) : ℕ → ℝ → Field n → ℝ
  | 0 => vectorTerminalObservable n β t p b
  | j+1 => fun y => vectorStepResponse ((1-t)*(β^2*(s.q (k+2-j)-s.q (k+1-j))))
      (s.m (k+1-j)) (vectorPerturbedRecursion s β t p b j y) (vectorObservableResponse s β t p b j y)

theorem vectorPerturbedRecursion_lipschitz {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (p : Couplings n × ℝ) (b : Configuration n → ℝ) (j : ℕ) (y : ℝ) :
    LipschitzWith (Real.sqrt (n : ℝ)).toNNReal (vectorPerturbedRecursion s β t p b j y) := by
  induction j with
  | zero => exact vectorPerturbedTerminalPotential_lipschitz n β t p b y
  | succ j ih => exact vectorColeHopfStep_lipschitz _ _ ih _ _ (s.m_nonneg (Nat.sub_le _ _))

theorem measurable_vectorPerturbedRecursion {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (p : Couplings n × ℝ) (b : Configuration n → ℝ) (j : ℕ) :
    Measurable (fun q : ℝ × Field n => vectorPerturbedRecursion s β t p b j q.1 q.2) := by
  induction j with
  | zero =>
    unfold vectorPerturbedRecursion vectorPerturbedTerminalPotential terminalPotential terminalPartition
      terminalTilt vectorTerminalExponent fieldDot
    fun_prop
  | succ j ih =>
    exact measurable_vectorColeHopfStep_parameter
      (vectorPerturbedRecursion s β t p b j) ih _ _

theorem measurable_vectorObservableResponse {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (p : Couplings n × ℝ) (b : Configuration n → ℝ) (j : ℕ) :
    Measurable (fun q : ℝ × Field n => vectorObservableResponse s β t p b j q.1 q.2) := by
  induction j with
  | zero =>
    unfold vectorObservableResponse vectorTerminalObservable terminalMean terminalWeight terminalPartition
      terminalTilt vectorTerminalExponent fieldDot
    fun_prop
  | succ j ih =>
    exact measurable_vectorStepResponse_parameter _ _
      (measurable_vectorPerturbedRecursion s β t p b j) ih _ _

theorem abs_vectorObservableResponse_le {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (p : Couplings n × ℝ) (b : Configuration n → ℝ) (R : ℝ)
    (hb : ∀ σ,|b σ| ≤ R) (j : ℕ) (y : ℝ) (x : Field n) :
    |vectorObservableResponse s β t p b j y x| ≤ R := by
  induction j generalizing x with
  | zero => exact terminalMean_bound _ b R hb
  | succ j ih =>
    exact abs_vectorStepResponse_le _ _ _
      (vectorPerturbedRecursion_lipschitz s β t p b j y) _ _ R ih x

theorem hasDerivAt_vectorPerturbedRecursion {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (p : Couplings n × ℝ) (b : Configuration n → ℝ) (R : ℝ≥0)
    (hb : ∀ σ,|b σ| ≤ R) (j : ℕ) (y : ℝ) (x : Field n) :
    HasDerivAt (fun r => vectorPerturbedRecursion s β t p b j r x)
      (vectorObservableResponse s β t p b j y x) y := by
  induction j generalizing x y with
  | zero => exact hasDerivAt_terminalPotential_tilt _ b y
  | succ j ih =>
    exact hasDerivAt_vectorColeHopfStep_response _ _ _ R
      (vectorPerturbedRecursion_lipschitz s β t p b j)
      (fun y => (measurable_vectorObservableResponse s β t p b j).comp
        (measurable_const.prodMk measurable_id))
      (fun y z => abs_vectorObservableResponse_le s β t p b R hb j y z)
      (fun y z => ih y z) _ _ x y

@[simp] theorem vectorPerturbedRecursion_zero {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (p : Couplings n × ℝ) (b : Configuration n → ℝ) (j : ℕ) :
    vectorPerturbedRecursion s β t p b j 0 = vectorRecursion s β t p j := by
  induction j with
  | zero =>
    funext x
    simp [vectorPerturbedRecursion,vectorPerturbedTerminalPotential,vectorRecursion,vectorTerminalPotential]
  | succ j ih => simp only [vectorPerturbedRecursion,ih,vectorRecursion]

end QuantitativePaper
