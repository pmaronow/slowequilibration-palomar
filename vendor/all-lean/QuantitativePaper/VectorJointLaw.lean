module
public import QuantitativePaper.VectorTransitionKernel
public import FourPapersCommon.FiniteHistoryDensity

@[expose] public section

/-! Actual normalized finite-profile disorder/field/spin law. Every field
coordinate and the terminal spin are retained in the joint law. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators NNReal ENNReal
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets FourPapersCommon

abbrev VectorState (n : ℕ) := (Couplings n × ℝ) × Field n

def vectorProfileKernel {n k : ℕ} (s : RSBScheme k) (β t : ℝ) (i : ℕ) :
    Kernel (VectorState n) (VectorState n) :=
  if i ≤ k+1 then
    vectorStateKernel ((1-t)*(β^2*(s.q (i+1)-s.q i))) (s.m i)
      (fun p x => vectorRecursion s β t p (k+1-i) x)
  else Kernel.id

theorem vectorProfileKernel_markov {n k : ℕ} (s : RSBScheme k) (β t : ℝ) (i : ℕ) :
    IsMarkovKernel (vectorProfileKernel (n := n) s β t i) := by
  unfold vectorProfileKernel
  split_ifs
  · exact isMarkovKernel_vectorStateKernel _ (measurable_vectorRecursion s β t _)
      (Real.sqrt (n : ℝ)).toNNReal (fun p => vectorRecursion_lipschitz s β t p _) _ _
  · infer_instance

def vectorOuterPartition {n k : ℕ} (s : RSBScheme k) (β t a : ℝ) : ℝ :=
  ∫ p,Real.exp (a*vectorRecursion s β t p (k+2) 0) ∂completionLaw n

theorem vectorOuterPartition_pos {n k : ℕ} (s : RSBScheme k) (β t a : ℝ) :
    0 < vectorOuterPartition (n := n) s β t a := by
  apply (integral_pos_iff_support_of_nonneg (fun _ => (Real.exp_pos _).le)
    (integrable_exp_vectorRecursion s β t a (k+2) 0)).mpr
  have hs : Function.support (fun p : Couplings n × ℝ =>
      Real.exp (a*vectorRecursion s β t p (k+2) 0)) = univ := by
    ext p
    simp [Function.mem_support,Real.exp_ne_zero]
  rw [hs]
  simp

def vectorOuterWeight {n k : ℕ} (s : RSBScheme k) (β t a : ℝ) (p : Couplings n × ℝ) : ℝ :=
  Real.exp (a*vectorRecursion s β t p (k+2) 0)/vectorOuterPartition (n := n) s β t a

def vectorOuterLaw {n k : ℕ} (s : RSBScheme k) (β t a : ℝ) : Measure (Couplings n × ℝ) :=
  (completionLaw n).withDensity (fun p => ENNReal.ofReal (vectorOuterWeight s β t a p))

theorem vectorOuterLaw_probability {n k : ℕ} (s : RSBScheme k) (β t a : ℝ) :
    IsProbabilityMeasure (vectorOuterLaw (n := n) s β t a) := by
  constructor
  rw [vectorOuterLaw,withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ]
  unfold vectorOuterWeight
  rw [← ofReal_integral_eq_lintegral_ofReal
      ((integrable_exp_vectorRecursion s β t a (k+2) 0).div_const _)
      (Eventually.of_forall fun p => div_nonneg (Real.exp_pos _).le (vectorOuterPartition_pos (n := n) s β t a).le)]
  rw [integral_div,← vectorOuterPartition,div_self (vectorOuterPartition_pos s β t a).ne']
  norm_num

def vectorInitialLaw {n k : ℕ} (s : RSBScheme k) (β t a : ℝ) : Measure (VectorState n) :=
  (vectorOuterLaw s β t a).map (fun p => (p,0))

def vectorFieldHistoryLaw {n k : ℕ} (s : RSBScheme k) (β t a : ℝ) :
    Measure (FiniteHistory (VectorState n) (k+2)) :=
  finiteHistoryLaw (vectorInitialLaw s β t a) (vectorProfileKernel s β t) (k+2)

theorem vectorFieldHistoryLaw_probability {n k : ℕ} (s : RSBScheme k) (β t a : ℝ) :
    IsProbabilityMeasure (vectorFieldHistoryLaw (n := n) s β t a) := by
  have := vectorOuterLaw_probability (n := n) s β t a
  have : IsProbabilityMeasure (vectorInitialLaw (n := n) s β t a) :=
    (Measure.isProbabilityMeasure_map_iff (by fun_prop)).mpr inferInstance
  exact isProbabilityMeasure_finiteHistoryLaw _ _ (vectorProfileKernel_markov s β t) _

variable {A : Type*} [MeasurableSpace A]

def terminalSpinKernel {n : ℕ} (E : A → Configuration n → ℝ)
    (hE : ∀ σ,Measurable (fun a => E a σ)) : Kernel A (Configuration n) where
  toFun a := terminalLaw (E a)
  measurable' := by
    apply Measure.measurable_of_measurable_coe
    intro S hS
    simp only [terminalLaw,PMF.toMeasure_apply _ hS,tsum_fintype]
    apply Finset.measurable_sum
    intro σ _
    classical
    by_cases hσ : σ ∈ S
    · simp only [Set.indicator_of_mem hσ,terminalPMF,PMF.ofFintype_apply,terminalWeight,
        terminalPartition]
      exact (Real.measurable_exp.comp (hE σ)).div
        (Finset.measurable_sum Finset.univ (fun τ _ => Real.measurable_exp.comp (hE τ))) |>.ennreal_ofReal
    · simp only [Set.indicator_of_notMem hσ]
      exact measurable_const

instance terminalSpinKernel_markov {n : ℕ} (E : A → Configuration n → ℝ)
    (hE : ∀ σ,Measurable (fun a => E a σ)) : IsMarkovKernel (terminalSpinKernel E hE) :=
  ⟨fun a => terminalLaw_probability (E a)⟩

theorem measurable_vectorTerminalExponent_state (n : ℕ) (β t : ℝ) (σ : Configuration n) :
    Measurable (fun p : VectorState n => vectorTerminalExponent n β t p.1 p.2 σ) := by
  unfold vectorTerminalExponent fieldDot energy Paper.skHamiltonian
  fun_prop

def vectorJointLaw {n k : ℕ} (s : RSBScheme k) (β t a : ℝ) :
    Measure (FiniteHistory (VectorState n) (k+2) × Configuration n) :=
  (vectorFieldHistoryLaw s β t a) ⊗ₘ
    ((terminalSpinKernel (fun p : VectorState n => vectorTerminalExponent n β t p.1 p.2)
      (measurable_vectorTerminalExponent_state n β t)).comap
        (fun history => history (Fin.last (k+2))) (measurable_pi_apply _))

theorem vectorJointLaw_probability {n k : ℕ} (s : RSBScheme k) (β t a : ℝ) :
    IsProbabilityMeasure (vectorJointLaw (n := n) s β t a) := by
  have := vectorFieldHistoryLaw_probability (n := n) s β t a
  unfold vectorJointLaw
  infer_instance

end QuantitativePaper
