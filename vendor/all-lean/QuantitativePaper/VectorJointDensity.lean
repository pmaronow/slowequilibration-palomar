module
public import QuantitativePaper.VectorJointLaw

@[expose] public section

/-! Literal finite-profile transition densities and the actual Gibbs density
relative to counting measure. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators NNReal ENNReal
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets FourPapersCommon

variable {n : ℕ} {A : Type*} [MeasurableSpace A]

omit [MeasurableSpace A] in
theorem vectorStateWeight_eq_exp (f : A → Field n → ℝ) (K : ℝ≥0)
    (hfl : ∀ a,LipschitzWith K (f a)) (c m : ℝ) (p y : A × Field n) :
    vectorStateWeight c m f p y = Real.exp
      (m*(f p.1 y.2-vectorColeHopfStep c m (f p.1) p.2)) := by
  by_cases hm : m = 0
  · simp [vectorStateWeight,vectorStepPartition,hm]
  · unfold vectorStateWeight vectorColeHopfStep
    rw [ite_eq_right hm,mul_sub,mul_div_cancel₀ _ hm,Real.exp_sub,
      Real.exp_log (vectorStepPartition_pos (f p.1) K (hfl p.1) c m p.2)]

def vectorProfileBaseKernel {n k : ℕ} (s : RSBScheme k) (β t : ℝ) (i : ℕ) :
    Kernel (VectorState n) (VectorState n) :=
  if i ≤ k+1 then vectorGaussianStateKernel ((1-t)*(β^2*(s.q (i+1)-s.q i)))
  else Kernel.id

def vectorProfileWeight {n k : ℕ} (s : RSBScheme k) (β t : ℝ) (i : ℕ)
    (p y : VectorState n) : ℝ≥0∞ :=
  if i ≤ k+1 then ENNReal.ofReal (vectorStateWeight ((1-t)*(β^2*(s.q (i+1)-s.q i)))
    (s.m i) (fun p x => vectorRecursion s β t p (k+1-i) x) p y)
  else 1

instance vectorProfileBaseKernel_markov {n k : ℕ} (s : RSBScheme k) (β t : ℝ) (i : ℕ) :
    IsMarkovKernel (vectorProfileBaseKernel (n := n) s β t i) := by
  unfold vectorProfileBaseKernel
  split_ifs <;> infer_instance

theorem measurable_vectorProfileWeight {n k : ℕ} (s : RSBScheme k) (β t : ℝ) (i : ℕ) :
    Measurable (Function.uncurry (vectorProfileWeight (n := n) s β t i)) := by
  unfold vectorProfileWeight
  split_ifs
  · exact (measurable_vectorStateWeight _ (measurable_vectorRecursion s β t _) _ _).ennreal_ofReal
  · exact measurable_const

theorem vectorProfileKernel_eq_withDensity {n k : ℕ} (s : RSBScheme k) (β t : ℝ) (i : ℕ) :
    vectorProfileKernel (n := n) s β t i =
      (vectorProfileBaseKernel s β t i).withDensity (vectorProfileWeight s β t i) := by
  unfold vectorProfileKernel vectorProfileBaseKernel vectorProfileWeight
  split_ifs
  · rfl
  · simp

theorem vectorProfileWeight_eq_exp {n k : ℕ} (s : RSBScheme k) (β t : ℝ) (i : ℕ)
    (hi : i ≤ k+1) (p y : VectorState n) :
    vectorProfileWeight s β t i p y = ENNReal.ofReal (Real.exp (s.m i*
      (vectorRecursion s β t p.1 (k+1-i) y.2-vectorRecursion s β t p.1 (k+2-i) p.2))) := by
  rw [vectorProfileWeight,ite_eq_left hi,vectorStateWeight_eq_exp _ _
    (fun p => vectorRecursion_lipschitz s β t p _)]
  have hdepth : k+2-i = (k+1-i)+1 := by omega
  have hi1 : k+1-(k+1-i) = i := by omega
  have hi2 : k+2-(k+1-i) = i+1 := by omega
  rw [hdepth,vectorRecursion,hi1,hi2]

theorem vectorFieldHistoryLaw_eq_withDensity {n k : ℕ} (s : RSBScheme k) (β t a : ℝ) :
    vectorFieldHistoryLaw (n := n) s β t a =
      (finiteHistoryLaw (vectorInitialLaw s β t a) (vectorProfileBaseKernel s β t) (k+2)).withDensity
        (finiteHistoryDensity (vectorProfileWeight s β t) (k+2)) := by
  have := vectorOuterLaw_probability (n := n) s β t a
  have : IsProbabilityMeasure (vectorInitialLaw (n := n) s β t a) :=
    (Measure.isProbabilityMeasure_map_iff (by fun_prop)).mpr inferInstance
  exact finiteHistoryLaw_withDensity _ _ _ (vectorProfileBaseKernel_markov s β t)
    (vectorProfileKernel_markov s β t) _ (measurable_vectorProfileWeight s β t)
    (vectorProfileKernel_eq_withDensity s β t) _

theorem terminalLaw_eq_count_withDensity {n : ℕ} (E : Configuration n → ℝ) :
    terminalLaw E = (Measure.count : Measure (Configuration n)).withDensity
      (fun σ => ENNReal.ofReal (terminalWeight E σ)) := by
  ext S hS
  rw [terminalLaw,PMF.toMeasure_apply _ hS,withDensity_apply _ hS,
    ← lintegral_indicator hS,lintegral_count]
  rfl

theorem terminalWeight_eq_exp {n : ℕ} (E : Configuration n → ℝ) (σ : Configuration n) :
    terminalWeight E σ = Real.exp (E σ-terminalPotential E) := by
  unfold terminalWeight terminalPotential
  rw [Real.exp_sub,Real.exp_log (terminalPartition_pos E)]

end QuantitativePaper
