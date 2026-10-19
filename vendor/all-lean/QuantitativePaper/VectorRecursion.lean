module
public import QuantitativePaper.VectorColeHopf
public import Targets.CascadeEndpoint
public import Paper.ParisiPDEFormula

@[expose] public section

/-! The actual finite-dimensional Gaussian recursion and its two physical
endpoints. Scalar factorization is proved by transporting the Euclidean Gaussian
integrals to the independent-coordinate recursion. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators NNReal
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets

theorem integral_fieldGaussian {n : ℕ} (f : Field n → ℝ) (hf : Continuous f) :
    (∫ z,f z ∂fieldGaussian n) = ∫ z : Fin n → ℝ,f (WithLp.toLp 2 z) ∂piGauss n := by
  exact integral_map (WithLp.measurable_toLp 2 _).aemeasurable hf.aestronglyMeasurable

theorem vectorColeHopfStep_eq_pi {n : ℕ} (f : Field n → ℝ) (hf : Continuous f)
    (c m : ℝ) (x : Field n) :
    vectorColeHopfStep c m f x = parisiStepPi n m c (fun y => f (WithLp.toLp 2 y)) x.ofLp := by
  have hshift (z : Fin n → ℝ) : fieldShift c x (WithLp.toLp 2 z) =
      WithLp.toLp 2 (fun i => x i+Real.sqrt c*z i) := by
    ext i
    rfl
  unfold vectorColeHopfStep parisiStepPi
  split_ifs
  · rw [integral_fieldGaussian (fun z => f (fieldShift c x z)) (hf.comp (show Continuous (fieldShift c x) from by unfold fieldShift;fun_prop))]
    simp_rw [hshift]
  · unfold vectorStepPartition
    rw [integral_fieldGaussian (fun z => Real.exp (m*f (fieldShift c x z))) (Real.continuous_exp.comp
      (continuous_const.mul (hf.comp (show Continuous (fieldShift c x) from by unfold fieldShift;fun_prop))))]
    simp_rw [hshift]
    ring

@[simp] theorem vectorColeHopfStep_zero_variance {n : ℕ} (m : ℝ) (f : Field n → ℝ)
    (x : Field n) : vectorColeHopfStep 0 m f x = f x := by
  by_cases hm : m = 0
  · simp [vectorColeHopfStep,hm,fieldShift]
  · simp [vectorColeHopfStep,vectorStepPartition,hm,fieldShift,Real.log_exp]

def vectorRecursion {n k : ℕ} (s : RSBScheme k) (β t : ℝ) (p : Couplings n × ℝ) :
    ℕ → (Field n → ℝ)
  | 0 => vectorTerminalPotential n β t p
  | j+1 => vectorColeHopfStep ((1-t)*(β^2*(s.q (k+2-j)-s.q (k+1-j))))
      (s.m (k+1-j)) (vectorRecursion s β t p j)

theorem vectorRecursion_lipschitz {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (p : Couplings n × ℝ) (j : ℕ) :
    LipschitzWith (Real.sqrt (n : ℝ)).toNNReal (vectorRecursion s β t p j) := by
  induction j with
  | zero => exact vectorTerminalPotential_lipschitz n β t p
  | succ j ih => exact vectorColeHopfStep_lipschitz _ _ ih _ _ (s.m_nonneg (Nat.sub_le _ _))

theorem vectorRecursion_eq_cascade {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (p : Couplings n × ℝ) (j : ℕ) (x : Field n) :
    vectorRecursion s β t p j x =
      cascadeT n s β (1-t) (fun y => vectorTerminalPotential n β t p (WithLp.toLp 2 y)) j x.ofLp := by
  induction j generalizing x with
  | zero => rfl
  | succ j ih =>
    rw [vectorRecursion,vectorColeHopfStep_eq_pi _ (vectorRecursion_lipschitz s β t p j).continuous]
    simp only [cascadeT]
    congr 1
    funext y
    exact ih (WithLp.toLp 2 y)

theorem vectorTerminalPotential_zero_time (n : ℕ) (β : ℝ) (p : Couplings n × ℝ)
    (x : Field n) : vectorTerminalPotential n β 0 p x = ∑ i,Real.log (2*Real.cosh (x i)) := by
  unfold vectorTerminalPotential terminalPotential terminalPartition vectorTerminalExponent
  simp only [Real.sqrt_zero,mul_zero,zero_mul,zero_add]
  convert log_spinSum_exp x.ofLp using 1
  unfold fieldDot spin Paper.spinSign
  simp only [mul_comm]

theorem vectorRecursion_zero_time {n k : ℕ} (s : RSBScheme k) (β : ℝ)
    (p : Couplings n × ℝ) (j : ℕ) (x : Field n) :
    vectorRecursion s β 0 p j x = ∑ i,(Real.log 2+parisiF s β j (x i)) := by
  rw [vectorRecursion_eq_cascade]
  simp_rw [vectorTerminalPotential_zero_time]
  simp only [sub_zero]
  exact cascadeT_one_scale n s β j x.ofLp

theorem vectorRecursion_one_time {n k : ℕ} (s : RSBScheme k) (β : ℝ)
    (p : Couplings n × ℝ) (j : ℕ) (x : Field n) :
    vectorRecursion s β 1 p j x = vectorTerminalPotential n β 1 p x := by
  rw [vectorRecursion_eq_cascade]
  simpa only [sub_self] using cascadeT_zero_scale n s β _ j x.ofLp

theorem vectorTerminalPotential_one_time_zero (n : ℕ) (β : ℝ) (p : Couplings n × ℝ) :
    vectorTerminalPotential n β 1 p 0 = completedLogPartition n β p := by
  unfold vectorTerminalPotential terminalPotential terminalPartition vectorTerminalExponent
  simp only [Real.sqrt_one,mul_one,fieldDot,PiLp.zero_apply,zero_mul,Finset.sum_const_zero,add_zero]
  unfold completedLogPartition logPartition Paper.skPartitionFunction energy Paper.skHamiltonian
  simp only [zero_mul,add_zero]
  have he (σ : Configuration n) : β*(1/Real.sqrt (n:ℝ)*
      (∑ e : Edge n,p.1 e*Paper.spinSign (σ e.val.1)*Paper.spinSign (σ e.val.2))+p.2) =
      β/Real.sqrt (n:ℝ)*(∑ e : Edge n,p.1 e*Paper.spinSign (σ e.val.1)*Paper.spinSign (σ e.val.2))+β*p.2 := by ring
  simp_rw [he,Real.exp_add]
  rw [← Finset.sum_mul,Real.log_mul (by positivity) (Real.exp_ne_zero _),Real.log_exp]

end QuantitativePaper
