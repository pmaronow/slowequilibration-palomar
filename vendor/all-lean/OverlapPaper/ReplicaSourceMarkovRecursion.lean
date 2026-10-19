module
public import OverlapPaper.ReplicaSourceRecursion
public import Mathlib.Probability.Kernel.MeasurableIntegral

@[expose] public section

/-! Actual finite Markov-kernel source recursions and exponential domination.
The recursive functions are defined by integrals rather than supplied as
profiles with a desired inequality. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Real
namespace OverlapPaper
set_option maxHeartbeats 800000

theorem source_bounded_integrable {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (w : Ω → ℝ) (hw : Measurable w)
    (K : ℝ) (hb : ∀ x, |w x| ≤ K) : Integrable w μ := by
  refine (integrable_const K).mono' hw.aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hb x

theorem source_bounded_exp_integrable {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (w : Ω → ℝ) (hw : Measurable w)
    (K : ℝ) (hb : ∀ x, |w x| ≤ K) (a : ℝ) :
    Integrable (fun x => Real.exp (a * w x)) μ := by
  exact integrable_exp_mul_of_mem_Icc hw.aemeasurable
    (Filter.Eventually.of_forall (fun x => abs_le.mp (hb x)))

theorem sourceLogAverage_abs_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (w : Ω → ℝ) (hw : Measurable w)
    (K : ℝ) (hK : 0 ≤ K) (hb : ∀ x, |w x| ≤ K) (a : ℝ) (ha : 0 ≤ a) :
    |sourceLogAverage μ a w| ≤ K := by
  have hi := source_bounded_integrable μ w hw K hb
  by_cases ha0 : a = 0
  · simp only [sourceLogAverage, ha0, ite_true]
    calc
      _ ≤ ∫ x, |w x| ∂μ := abs_integral_le_integral_abs
      _ ≤ ∫ x, K ∂μ := integral_mono hi.abs (integrable_const _) (fun x => hb x)
      _ = K := by simp
  · have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
    have he := source_bounded_exp_integrable μ w hw K hb a
    have hpos := integral_exp_pos he
    have hlo : Real.exp (-a * K) ≤ ∫ x, Real.exp (a * w x) ∂μ := by
      calc
        _ = ∫ x, Real.exp (-a * K) ∂μ := by simp
        _ ≤ _ := integral_mono (integrable_const _) he (fun x => Real.exp_le_exp.mpr (by
          have hx := (abs_le.mp (hb x)).1
          nlinarith [mul_le_mul_of_nonneg_left hx ha]))
    have hhi : (∫ x, Real.exp (a * w x) ∂μ) ≤ Real.exp (a * K) := by
      calc
        _ ≤ ∫ x, Real.exp (a * K) ∂μ := integral_mono he (integrable_const _) (fun x => Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (abs_le.mp (hb x)).2 ha))
        _ = _ := by simp
    have HL := Real.log_le_log (Real.exp_pos _) hlo
    have HU := Real.log_le_log hpos hhi
    rw [Real.log_exp] at HL HU
    simp only [sourceLogAverage, ha0, ite_false, abs_le, le_div_iff₀ hap, div_le_iff₀ hap]
    constructor <;> nlinarith

variable {A : Type*} [MeasurableSpace A]

def sourceKernelRecursion (Q : ℕ → Kernel A A) (a : ℕ → ℝ) : ℕ → (A → ℝ) → A → ℝ
  | 0, w => w
  | k + 1, w => fun x => sourceLogAverage (Q k x) (a k) (sourceKernelRecursion Q a k w)

def sourceKernelExpectation (Q : ℕ → Kernel A A) : ℕ → (A → ℝ) → A → ℝ
  | 0, w => w
  | k + 1, w => fun x => ∫ y, sourceKernelExpectation Q k w y ∂Q k x

theorem sourceKernelRecursion_measurable (Q : ℕ → Kernel A A) (a : ℕ → ℝ)
    (w : A → ℝ) (hw : Measurable w) (k : ℕ) :
    Measurable (sourceKernelRecursion Q a k w) := by
  induction k with
  | zero => exact hw
  | succ k ih =>
    unfold sourceKernelRecursion sourceLogAverage
    by_cases ha : a k = 0
    · simp only [ha, ite_true]
      exact ih.stronglyMeasurable.integral_kernel.measurable
    · simp only [ha, ite_false]
      exact ((measurable_exp.comp (measurable_const.mul ih)).stronglyMeasurable.integral_kernel.measurable.log).div_const _

theorem sourceKernelExpectation_measurable (Q : ℕ → Kernel A A)
    (w : A → ℝ) (hw : Measurable w) (k : ℕ) :
    Measurable (sourceKernelExpectation Q k w) := by
  induction k with
  | zero => exact hw
  | succ k ih => exact ih.stronglyMeasurable.integral_kernel.measurable

theorem sourceKernelRecursion_abs_le (Q : ℕ → Kernel A A) (hQ : ∀ j, IsMarkovKernel (Q j))
    (a : ℕ → ℝ) (ha : ∀ j, 0 ≤ a j) (w : A → ℝ) (hw : Measurable w)
    (K : ℝ) (hK : 0 ≤ K) (hb : ∀ x, |w x| ≤ K) (k : ℕ) :
    ∀ x, |sourceKernelRecursion Q a k w x| ≤ K := by
  induction k with
  | zero => exact hb
  | succ k ih =>
    haveI := hQ k
    intro x
    exact sourceLogAverage_abs_le (Q k x) _ (sourceKernelRecursion_measurable Q a w hw k) K hK ih (a k) (ha k)

theorem sourceKernelExpectation_abs_le (Q : ℕ → Kernel A A) (hQ : ∀ j, IsMarkovKernel (Q j))
    (w : A → ℝ) (hw : Measurable w) (K : ℝ) (hK : 0 ≤ K) (hb : ∀ x, |w x| ≤ K) (k : ℕ) :
    ∀ x, |sourceKernelExpectation Q k w x| ≤ K := by
  induction k with
  | zero => exact hb
  | succ k ih =>
    haveI := hQ k
    intro x
    change |∫ y, sourceKernelExpectation Q k w y ∂Q k x| ≤ K
    have hi := source_bounded_integrable (Q k x) _ (sourceKernelExpectation_measurable Q w hw k) K ih
    calc
      _ ≤ ∫ y, |sourceKernelExpectation Q k w y| ∂Q k x := abs_integral_le_integral_abs
      _ ≤ ∫ y, K ∂Q k x := integral_mono hi.abs (integrable_const _) ih
      _ = K := by simp

theorem sourceKernelRecursion_exponential_domination
    (Q : ℕ → Kernel A A) (hQ : ∀ j, IsMarkovKernel (Q j))
    (a : ℕ → ℝ) (ha : ∀ j, a j ∈ Icc 0 1) (w : A → ℝ) (hw : Measurable w)
    (K : ℝ) (hK : 0 ≤ K) (hb : ∀ x, |w x| ≤ K) (k : ℕ) :
    ∀ x, Real.exp (sourceKernelRecursion Q a k w x) ≤
      sourceKernelExpectation Q k (fun y => Real.exp (w y)) x := by
  induction k with
  | zero => intro x; exact le_rfl
  | succ k ih =>
    haveI := hQ k
    intro x
    have hwm := sourceKernelRecursion_measurable Q a w hw k
    have hwb := sourceKernelRecursion_abs_le Q hQ a (fun j => (ha j).1) w hw K hK hb k
    have hi := source_bounded_integrable (Q k x) _ hwm K hwb
    have hie := source_bounded_exp_integrable (Q k x) _ hwm K hwb 1
    have hia := source_bounded_exp_integrable (Q k x) _ hwm K hwb (a k)
    have hem : Measurable (fun y => Real.exp (w y)) := measurable_exp.comp hw
    have heb (y : A) : |Real.exp (w y)| ≤ Real.exp K := by
      rw [abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.mpr ((le_abs_self _).trans (hb y))
    have hRight := source_bounded_integrable (Q k x) _ (sourceKernelExpectation_measurable Q _ hem k)
      (Real.exp K) (sourceKernelExpectation_abs_le Q hQ _ hem (Real.exp K) (Real.exp_pos _).le heb k)
    calc
      _ ≤ ∫ y, Real.exp (sourceKernelRecursion Q a k w y) ∂Q k x :=
        exp_sourceLogAverage_le (Q k x) (a k) (ha k) _ hi (by simpa only [one_mul] using hie) hia
      _ ≤ _ := integral_mono (by simpa only [one_mul] using hie) hRight ih

end OverlapPaper
